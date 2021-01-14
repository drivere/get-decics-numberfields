#include <stdio.h>
#include "GetDecics.h"

// Needed for usleep
#include <unistd.h>



#define FAIL 1

#ifndef MIN
#define MIN(x, y) (((x) < (y)) ? (x) : (y))
#endif


#define CHECK_ERROR(status, msg, func) { if(status!=CL_SUCCESS) { printErrMsg( (status), (msg), (func), __FILE__, __LINE__); return FAIL;} }
inline void printErrMsg(int status, const char *msg, const char *funcName, const char *file, int line)
{
  fprintf(stderr, "File %s, Line %d: %s %s returned %s\n", file, line, msg, funcName, getErrorString(status));
}




//////////////////////////////////////////////////////////////////////////////////////////
//! OpenCL version of the polDisc test.
//! 
//! This function performs the polynomial discriminant test for the GetDecics program.
//! For every polynomial in the input buffer, it computes the polynomial discriminant, 
//! divides out all factors of primes from S, and then sets the polGoodFlag if
//! what's left is a perfect square.
//! 
//////////////////////////////////////////////////////////////////////////////////////////

extern "C" int
polDiscTest_gpuOpenCL(int64_t *polBuf, int numPolys, char *polGoodFlag, int numP, int *pSet)
  {
  static int numPolysPrev = 0;
  static int firstPass = 1;
  cl_int status;
  static cl_event finalEvent;  // Used to store the final event from the previous iteration.

  //printf("Entering polDiscTest_gpuOpenCL\n");
  //printf("  numPolys = %d\n", numPolys);

  if(numP>2) { fprintf(stderr, "Error: This function only supports 2 primes max."); return FAIL; }


  // If this is not the first pass then transfer the polGoodFlag from the GPU (from previous pass).
  if (!firstPass) {

    // First make sure the previous pass has finished:
    //status = clFinish(commandQueue);
    //CHECK_ERROR(status, "Error: Kernel command queue failed to finish.", "clFinish");

    // clFinish uses 100% cpu.  So create a wait loop to sleep for .1 ms intervals until the GPU is done.
    cl_int eventStatus;
    clGetEventInfo(finalEvent, CL_EVENT_COMMAND_EXECUTION_STATUS, sizeof(cl_int), &eventStatus, NULL);
    while(eventStatus!=CL_COMPLETE) {
      usleep(100);  // Sleep for .1 msec
      status = clGetEventInfo(finalEvent, CL_EVENT_COMMAND_EXECUTION_STATUS, sizeof(cl_int), &eventStatus, NULL);
      CHECK_ERROR(status, "Error: clGetEventInfo failed.", "clGetEventInfo");
      }

    // Read the flag buffer off the device and put into the polGoodFlag array
    // This is a blocking read - when the call returns, the polGoodFlag is ready to be used.
    status = clEnqueueReadBuffer(commandQueue, kernelFlagBuffer, CL_TRUE, 0, sizeof(char)*numPolysPrev, polGoodFlag, 0, NULL, NULL);
    CHECK_ERROR(status, "Error: Failed to read flag buffer.", "clEnqueueReadBuffer");
  }


  // Only invoke the GPU if there are polynomials to process.
  // If there are no polynomials, then this signifies the "last" pass.
  // We already pulled the previous results off the GPU above, so just return.
  if ( numPolys==0 )  return 0;


  firstPass = 0;
  numPolysPrev = numPolys;


  /* Write the polynomials to the device buffer.  This is a non-blocking write. */
  cl_event writePolysDone;
  status = clEnqueueWriteBuffer(commandQueue, kernelPolyBuffer, CL_FALSE, 0, numPolys*11*sizeof(int64_t), polBuf, 0, NULL, &writePolysDone);
  CHECK_ERROR(status, "Error: Failed to write polynomials to device buffer.", "clEnqueueWriteBuffer");

  /* This guarantees the write operation is started */
  status = clFlush(commandQueue);
  CHECK_ERROR(status, "Error: Command queue flush failed.", "clFlush");


  /* Determine sizing */
  /* The local size is the number of work items in a work group */
  /* Total number of work items = numPolys, but we need to bump this up to the next multiple of threadsPerBlock */
  size_t numTotalThreads = ( (numPolys+threadsPerBlock-1)/threadsPerBlock ) * threadsPerBlock;
  size_t globalSize[1] = { numTotalThreads };
  size_t localSize[1]  = { (size_t)threadsPerBlock };


  //////////////////////////////////////////////////////////////////////////////
  //
  //  Launch Kernel: Sub-resultant initialization
  //
  status = clSetKernelArg(pdtKernelSubResultantInit, 0, sizeof(int), (void *)&numPolys);
  CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantInit, 1, sizeof(cl_mem), (void *)&kernelPolyBuffer);
  CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantInit, 2, sizeof(cl_mem), (void *)&kernelPolyA);
  CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantInit, 3, sizeof(cl_mem), (void *)&kernelPolyB);
  CHECK_ERROR(status, "Error: Setting arg 3.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantInit, 4, sizeof(cl_mem), (void *)&kernelDegA);
  CHECK_ERROR(status, "Error: Setting arg 4.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantInit, 5, sizeof(cl_mem), (void *)&kernelDegB);
  CHECK_ERROR(status, "Error: Setting arg 5.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantInit, 6, sizeof(cl_mem), (void *)&kernelG);
  CHECK_ERROR(status, "Error: Setting arg 6.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantInit, 7, sizeof(cl_mem), (void *)&kernelH);
  CHECK_ERROR(status, "Error: Setting arg 7.", "clSetKernelArg");

  //status = clFinish(commandQueue);  // Make sure the previous buffer write has completed.
  //CHECK_ERROR(status, "Error: Failed to Write Buffer.", "clFinish");

  /* Queue the kernel for execution */
  cl_event srInitDone;
  status = clEnqueueNDRangeKernel(commandQueue, pdtKernelSubResultantInit, 1, NULL, globalSize, localSize, 1, &writePolysDone, &srInitDone);
  CHECK_ERROR(status, "Error: Failed to Enqueue Kernel pdtKernelSubResultantInit.", "clEnqueueNDRangeKernel");



  //////////////////////////////////////////////////////////////////////////////
  //
  //  Launch Kernel: Sub-resultant iteration when degB=8
  //
  status = clSetKernelArg(pdtKernelSubResultantDegB8, 0, sizeof(int), (void *)&numPolys);
  CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB8, 1, sizeof(cl_mem), (void *)&kernelPolyA);
  CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB8, 2, sizeof(cl_mem), (void *)&kernelPolyB);
  CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB8, 3, sizeof(cl_mem), (void *)&kernelDegA);
  CHECK_ERROR(status, "Error: Setting arg 3.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB8, 4, sizeof(cl_mem), (void *)&kernelDegB);
  CHECK_ERROR(status, "Error: Setting arg 4.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB8, 5, sizeof(cl_mem), (void *)&kernelG);
  CHECK_ERROR(status, "Error: Setting arg 5.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB8, 6, sizeof(cl_mem), (void *)&kernelH);
  CHECK_ERROR(status, "Error: Setting arg 6.", "clSetKernelArg");

  /* Queue the kernel for execution */
  cl_event srDegB8Done;
  status = clEnqueueNDRangeKernel(commandQueue, pdtKernelSubResultantDegB8, 1, NULL, globalSize, localSize, 1, &srInitDone, &srDegB8Done);
  CHECK_ERROR(status, "Error: Failed to Enqueue Kernel pdtKernelSubResultantDegB8.", "clEnqueueNDRangeKernel");



  //////////////////////////////////////////////////////////////////////////////
  //
  //  Launch Kernel: Sub-resultant multi-precision initialization
  //
  status = clSetKernelArg(pdtKernelSubResultantMpInit, 0, sizeof(int), (void *)&numPolys);
  CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantMpInit, 1, sizeof(cl_mem), (void *)&kernelFlagBuffer);
  CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantMpInit, 2, sizeof(cl_mem), (void *)&kernelPolyA);
  CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantMpInit, 3, sizeof(cl_mem), (void *)&kernelPolyB);
  CHECK_ERROR(status, "Error: Setting arg 3.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantMpInit, 4, sizeof(cl_mem), (void *)&kernelDegA);
  CHECK_ERROR(status, "Error: Setting arg 4.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantMpInit, 5, sizeof(cl_mem), (void *)&kernelDegB);
  CHECK_ERROR(status, "Error: Setting arg 5.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantMpInit, 6, sizeof(cl_mem), (void *)&kernelMpA);
  CHECK_ERROR(status, "Error: Setting arg 6.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantMpInit, 7, sizeof(cl_mem), (void *)&kernelMpB);
  CHECK_ERROR(status, "Error: Setting arg 7.", "clSetKernelArg");

  /* Queue the kernel for execution */
  cl_event srMpInitDone;
  status = clEnqueueNDRangeKernel(commandQueue, pdtKernelSubResultantMpInit, 1, NULL, globalSize, localSize, 1, &srDegB8Done, &srMpInitDone);
  CHECK_ERROR(status, "Error: Failed to Enqueue Kernel pdtKernelSubResultantMpInit.", "clEnqueueNDRangeKernel");

  /* Flush the command buffer.  This guarantees the device stays busy while queueing the rest of the commands. */
  status = clFlush(commandQueue);
  CHECK_ERROR(status, "Error: Command queue flush failed.", "clFlush");



  //////////////////////////////////////////////////////////////////////////////
  //
  //  Launch Kernel: Sub-resultant iteration when degB=7 and degA=9
  //
  status = clSetKernelArg(pdtKernelSubResultantDegB7DegA9, 0, sizeof(int), (void *)&numPolys);
  CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB7DegA9, 1, sizeof(cl_mem), (void *)&kernelDegA);
  CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB7DegA9, 2, sizeof(cl_mem), (void *)&kernelDegB);
  CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB7DegA9, 3, sizeof(cl_mem), (void *)&kernelMpA);
  CHECK_ERROR(status, "Error: Setting arg 3.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB7DegA9, 4, sizeof(cl_mem), (void *)&kernelMpB);
  CHECK_ERROR(status, "Error: Setting arg 4.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB7DegA9, 5, sizeof(cl_mem), (void *)&kernelG);
  CHECK_ERROR(status, "Error: Setting arg 5.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB7DegA9, 6, sizeof(cl_mem), (void *)&kernelH);
  CHECK_ERROR(status, "Error: Setting arg 6.", "clSetKernelArg");

  /* Queue the kernel for execution */
  cl_event srDegB7DegA9Done;
  status = clEnqueueNDRangeKernel(commandQueue, pdtKernelSubResultantDegB7DegA9, 1, NULL, globalSize, localSize, 1, &srMpInitDone, &srDegB7DegA9Done);
  CHECK_ERROR(status, "Error: Failed to Enqueue Kernel pdtKernelSubResultantDegB7DegA9.", "clEnqueueNDRangeKernel");



  //////////////////////////////////////////////////////////////////////////////
  //
  //  Launch Kernel: Sub-resultant iteration when degB=7 and degA=8
  //
  status = clSetKernelArg(pdtKernelSubResultantDegB7DegA8, 0, sizeof(int), (void *)&numPolys);
  CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB7DegA8, 1, sizeof(cl_mem), (void *)&kernelDegA);
  CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB7DegA8, 2, sizeof(cl_mem), (void *)&kernelDegB);
  CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB7DegA8, 3, sizeof(cl_mem), (void *)&kernelMpA);
  CHECK_ERROR(status, "Error: Setting arg 3.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB7DegA8, 4, sizeof(cl_mem), (void *)&kernelMpB);
  CHECK_ERROR(status, "Error: Setting arg 4.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB7DegA8, 5, sizeof(cl_mem), (void *)&kernelG);
  CHECK_ERROR(status, "Error: Setting arg 5.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB7DegA8, 6, sizeof(cl_mem), (void *)&kernelH);
  CHECK_ERROR(status, "Error: Setting arg 6.", "clSetKernelArg");

  /* Queue the kernel for execution */
  cl_event srDegB7DegA8Done;
  status = clEnqueueNDRangeKernel(commandQueue, pdtKernelSubResultantDegB7DegA8, 1, NULL, globalSize, localSize, 1, &srMpInitDone, &srDegB7DegA8Done);
  CHECK_ERROR(status, "Error: Failed to Enqueue Kernel pdtKernelSubResultantDegB7DegA8.", "clEnqueueNDRangeKernel");



  //////////////////////////////////////////////////////////////////////////////
  //
  //  Launch Kernel: Sub-resultant iteration when degB=6 and degA=9
  //

  // Setup the list of events that must complete before this kernel runs.
  cl_event degB7WaitList[2];
  degB7WaitList[0] = srDegB7DegA9Done;
  degB7WaitList[1] = srDegB7DegA8Done;

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA9, 0, sizeof(int), (void *)&numPolys);
  CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA9, 1, sizeof(cl_mem), (void *)&kernelDegA);
  CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA9, 2, sizeof(cl_mem), (void *)&kernelDegB);
  CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA9, 3, sizeof(cl_mem), (void *)&kernelMpA);
  CHECK_ERROR(status, "Error: Setting arg 3.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA9, 4, sizeof(cl_mem), (void *)&kernelMpB);
  CHECK_ERROR(status, "Error: Setting arg 4.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA9, 5, sizeof(cl_mem), (void *)&kernelG);
  CHECK_ERROR(status, "Error: Setting arg 5.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA9, 6, sizeof(cl_mem), (void *)&kernelH);
  CHECK_ERROR(status, "Error: Setting arg 6.", "clSetKernelArg");

  /* Queue the kernel for execution */
  cl_event srDegB6DegA9Done;
  status = clEnqueueNDRangeKernel(commandQueue, pdtKernelSubResultantDegB6DegA9, 1, NULL, globalSize, localSize, 2, degB7WaitList, &srDegB6DegA9Done);
  CHECK_ERROR(status, "Error: Failed to Enqueue Kernel pdtKernelSubResultantDegB6DegA9.", "clEnqueueNDRangeKernel");



  //////////////////////////////////////////////////////////////////////////////
  //
  //  Launch Kernel: Sub-resultant iteration when degB=6 and degA=8
  //
  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA8, 0, sizeof(int), (void *)&numPolys);
  CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA8, 1, sizeof(cl_mem), (void *)&kernelDegA);
  CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA8, 2, sizeof(cl_mem), (void *)&kernelDegB);
  CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA8, 3, sizeof(cl_mem), (void *)&kernelMpA);
  CHECK_ERROR(status, "Error: Setting arg 3.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA8, 4, sizeof(cl_mem), (void *)&kernelMpB);
  CHECK_ERROR(status, "Error: Setting arg 4.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA8, 5, sizeof(cl_mem), (void *)&kernelG);
  CHECK_ERROR(status, "Error: Setting arg 5.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA8, 6, sizeof(cl_mem), (void *)&kernelH);
  CHECK_ERROR(status, "Error: Setting arg 6.", "clSetKernelArg");

  /* Queue the kernel for execution */
  cl_event srDegB6DegA8Done;
  status = clEnqueueNDRangeKernel(commandQueue, pdtKernelSubResultantDegB6DegA8, 1, NULL, globalSize, localSize, 2, degB7WaitList, &srDegB6DegA8Done);
  CHECK_ERROR(status, "Error: Failed to Enqueue Kernel pdtKernelSubResultantDegB6DegA8.", "clEnqueueNDRangeKernel");



  //////////////////////////////////////////////////////////////////////////////
  //
  //  Launch Kernel: Sub-resultant iteration when degB=6 and degA=7
  //
  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA7, 0, sizeof(int), (void *)&numPolys);
  CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA7, 1, sizeof(cl_mem), (void *)&kernelDegA);
  CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA7, 2, sizeof(cl_mem), (void *)&kernelDegB);
  CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA7, 3, sizeof(cl_mem), (void *)&kernelMpA);
  CHECK_ERROR(status, "Error: Setting arg 3.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA7, 4, sizeof(cl_mem), (void *)&kernelMpB);
  CHECK_ERROR(status, "Error: Setting arg 4.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA7, 5, sizeof(cl_mem), (void *)&kernelG);
  CHECK_ERROR(status, "Error: Setting arg 5.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB6DegA7, 6, sizeof(cl_mem), (void *)&kernelH);
  CHECK_ERROR(status, "Error: Setting arg 6.", "clSetKernelArg");

  /* Queue the kernel for execution */
  cl_event srDegB6DegA7Done;
  status = clEnqueueNDRangeKernel(commandQueue, pdtKernelSubResultantDegB6DegA7, 1, NULL, globalSize, localSize, 2, degB7WaitList, &srDegB6DegA7Done);
  CHECK_ERROR(status, "Error: Failed to Enqueue Kernel pdtKernelSubResultantDegB6DegA7.", "clEnqueueNDRangeKernel");



  //////////////////////////////////////////////////////////////////////////////
  //
  //  Launch Kernel: Sub-resultant iteration when degB=5
  //

  // Setup the list of events that must complete before this kernel runs.
  cl_event degB6WaitList[3];
  degB6WaitList[0] = srDegB6DegA9Done;
  degB6WaitList[1] = srDegB6DegA8Done;
  degB6WaitList[2] = srDegB6DegA7Done;

  status = clSetKernelArg(pdtKernelSubResultantDegB5, 0, sizeof(int), (void *)&numPolys);
  CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB5, 1, sizeof(cl_mem), (void *)&kernelFlagBuffer);
  CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB5, 2, sizeof(cl_mem), (void *)&kernelDegA);
  CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB5, 3, sizeof(cl_mem), (void *)&kernelDegB);
  CHECK_ERROR(status, "Error: Setting arg 3.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB5, 4, sizeof(cl_mem), (void *)&kernelMpA);
  CHECK_ERROR(status, "Error: Setting arg 4.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB5, 5, sizeof(cl_mem), (void *)&kernelMpB);
  CHECK_ERROR(status, "Error: Setting arg 5.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB5, 6, sizeof(cl_mem), (void *)&kernelG);
  CHECK_ERROR(status, "Error: Setting arg 6.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB5, 7, sizeof(cl_mem), (void *)&kernelH);
  CHECK_ERROR(status, "Error: Setting arg 7.", "clSetKernelArg");

  /* Queue the kernel for execution */
  cl_event srDegB5Done;
  status = clEnqueueNDRangeKernel(commandQueue, pdtKernelSubResultantDegB5, 1, NULL, globalSize, localSize, 3, degB6WaitList, &srDegB5Done);
  CHECK_ERROR(status, "Error: Failed to Enqueue Kernel pdtKernelSubResultantDegB5.", "clEnqueueNDRangeKernel");



  //////////////////////////////////////////////////////////////////////////////
  //
  //  Launch Kernel: Sub-resultant iteration when degB=4.
  //                 This will complete the sub-resultant computation.
  //
  status = clSetKernelArg(pdtKernelSubResultantDegB4, 0, sizeof(int), (void *)&numPolys);
  CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB4, 1, sizeof(cl_mem), (void *)&kernelFlagBuffer);
  CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB4, 2, sizeof(cl_mem), (void *)&kernelDiscBuffer);
  CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB4, 3, sizeof(cl_mem), (void *)&kernelDegA);
  CHECK_ERROR(status, "Error: Setting arg 3.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB4, 4, sizeof(cl_mem), (void *)&kernelDegB);
  CHECK_ERROR(status, "Error: Setting arg 4.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB4, 5, sizeof(cl_mem), (void *)&kernelMpA);
  CHECK_ERROR(status, "Error: Setting arg 5.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantDegB4, 6, sizeof(cl_mem), (void *)&kernelMpB);
  CHECK_ERROR(status, "Error: Setting arg 6.", "clSetKernelArg");

  /* Queue the kernel for execution */
  cl_event srDegB4Done;
  status = clEnqueueNDRangeKernel(commandQueue, pdtKernelSubResultantDegB4, 1, NULL, globalSize, localSize, 1, &srDegB5Done, &srDegB4Done);
  CHECK_ERROR(status, "Error: Failed to Enqueue Kernel pdtKernelSubResultantDegB4.", "clEnqueueNDRangeKernel");



/*
  //////////////////////////////////////////////////////////////////////////////
  //
  //  Launch Kernel: Finish Sub-resultant
  //
  status = clSetKernelArg(pdtKernelSubResultantFinish, 0, sizeof(int), (void *)&numPolys);
  CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantFinish, 1, sizeof(cl_mem), (void *)&kernelFlagBuffer);
  CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantFinish, 2, sizeof(cl_mem), (void *)&kernelDiscBuffer);
  CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantFinish, 3, sizeof(cl_mem), (void *)&kernelDegA);
  CHECK_ERROR(status, "Error: Setting arg 3.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantFinish, 4, sizeof(cl_mem), (void *)&kernelDegB);
  CHECK_ERROR(status, "Error: Setting arg 4.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantFinish, 5, sizeof(cl_mem), (void *)&kernelMpA);
  CHECK_ERROR(status, "Error: Setting arg 5.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantFinish, 6, sizeof(cl_mem), (void *)&kernelMpB);
  CHECK_ERROR(status, "Error: Setting arg 6.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantFinish, 7, sizeof(cl_mem), (void *)&kernelG);
  CHECK_ERROR(status, "Error: Setting arg 7.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelSubResultantFinish, 8, sizeof(cl_mem), (void *)&kernelH);
  CHECK_ERROR(status, "Error: Setting arg 8.", "clSetKernelArg");

  cl_event srFinishDone;
  status = clEnqueueNDRangeKernel(commandQueue, pdtKernelSubResultantFinish, 1, NULL, globalSize, localSize, 1, &srDegB4Done, &srFinishDone);
  CHECK_ERROR(status, "Error: Failed to Enqueue Kernel pdtKernelSubResultantFinish.", "clEnqueueNDRangeKernel");
*/




  //////////////////////////////////////////////////////////////////////////////
  //
  //  Launch Stage 2 kernels.
  //
  cl_event kerEvent[3];
  kerEvent[0] = srDegB4Done;  // XXXXX Put this in later: srDegB2Done
  int ePtr = 1;
  for( int k=0; k<numP; ++k) {
    if(pSet[k]==2) {
      /* Setup the kernel arguments for Div2 */
      status = clSetKernelArg(pdtKernelDiv2, 0, sizeof(int), (void *)&numPolys);
      CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

      status = clSetKernelArg(pdtKernelDiv2, 1, sizeof(cl_mem), (void *)&kernelFlagBuffer);
      CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

      status = clSetKernelArg(pdtKernelDiv2, 2, sizeof(cl_mem), (void *)&kernelDiscBuffer);
      CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

      /* Divide out all factors of 2 */
      status = clEnqueueNDRangeKernel(commandQueue, pdtKernelDiv2, 1, NULL, globalSize, localSize, 1, &kerEvent[ePtr-1], &kerEvent[ePtr]);
      ++ePtr;
      CHECK_ERROR(status, "Error: Failed to Enqueue Kernel Div2.", "clEnqueueNDRangeKernel");
      }
    if(pSet[k]==5) {
      /* Setup the kernel arguments for Div5 */
      status = clSetKernelArg(pdtKernelDiv5, 0, sizeof(int), (void *)&numPolys);
      CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

      status = clSetKernelArg(pdtKernelDiv5, 1, sizeof(cl_mem), (void *)&kernelFlagBuffer);
      CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

      status = clSetKernelArg(pdtKernelDiv5, 2, sizeof(cl_mem), (void *)&kernelDiscBuffer);
      CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

      /* Divide out all factors of 5 */
      status = clEnqueueNDRangeKernel(commandQueue, pdtKernelDiv5, 1, NULL, globalSize, localSize, 1, &kerEvent[ePtr-1], &kerEvent[ePtr]);
      ++ePtr;
      CHECK_ERROR(status, "Error: Failed to Enqueue Kernel Div5.", "clEnqueueNDRangeKernel");
      }
    if(pSet[k]!=2 && pSet[k]!=5) {
      /* Setup the kernel arguments for DivP */
      status = clSetKernelArg(pdtKernelDivP, 0, sizeof(int), (void *)&numPolys);
      CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

      status = clSetKernelArg(pdtKernelDivP, 1, sizeof(cl_mem), (void *)&kernelFlagBuffer);
      CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

      status = clSetKernelArg(pdtKernelDivP, 2, sizeof(cl_mem), (void *)&kernelDiscBuffer);
      CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

      status = clSetKernelArg(pdtKernelDivP, 3, sizeof(int), (void *)&pSet[k]);
      CHECK_ERROR(status, "Error: Setting arg 3.", "clSetKernelArg");

      /* Divide out all factors of P */
      status = clEnqueueNDRangeKernel(commandQueue, pdtKernelDivP, 1, NULL, globalSize, localSize, 1, &kerEvent[ePtr-1], &kerEvent[ePtr]);
      ++ePtr;
      CHECK_ERROR(status, "Error: Failed to Enqueue Kernel DivP.", "clEnqueueNDRangeKernel");
      }
    }
  cl_event kerStg2Done = kerEvent[ePtr-1];



  //////////////////////////////////////////////////////////////////////////////
  //
  //  Launch Stage 3 kernel.
  //
  status = clSetKernelArg(pdtKernelStg3, 0, sizeof(int), (void *)&numPolys);
  CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelStg3, 1, sizeof(cl_mem), (void *)&kernelFlagBuffer);
  CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelStg3, 2, sizeof(cl_mem), (void *)&kernelDiscBuffer);
  CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

  /* Queue the kernel for execution.  It will wait for event kerStg2Done. */
  status = clEnqueueNDRangeKernel(commandQueue, pdtKernelStg3, 1, NULL, globalSize, localSize, 1, &kerStg2Done, &finalEvent);
  CHECK_ERROR(status, "Error: Failed to Enqueue Kernel Stage 3.", "clEnqueueNDRangeKernel");



  // Make sure all commands have been sent to device.
  status = clFlush(commandQueue);
  CHECK_ERROR(status, "Error: Command queue flush failed.", "clFlush");


  // If we make it this far, we assume success.  So return 0.
  return 0;

  }
