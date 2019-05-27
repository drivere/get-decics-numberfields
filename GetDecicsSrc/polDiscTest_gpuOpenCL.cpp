#include <stdio.h>
#include "GetDecics.h"


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
polDiscTest_gpuOpenCL(long long *polBuf, int numPolys, char *polGoodFlag, int numP, int *pSet)
  {
  static int numPolysPrev = 0;
  static int firstPass = 1;

  cl_int status;

  //printf("Entering polDiscTest_gpuOpenCL\n");
  //printf("  numPolys = %d\n", numPolys);


  // If this is not the first pass then transfer the polGoodFlag from the GPU (from previous pass).
  if (!firstPass) {

    // First make sure the previous pass has finished:
    status = clFinish(commandQueue);
    CHECK_ERROR(status, "Error: Kernel failed.", "clFinish");

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


  // Setup primes for the kernel
  int p1, p2;
  if(numP==1)       { p1=pSet[0]; p2=pSet[0]; }
  else if(numP==2)  { p1=pSet[0]; p2=pSet[1]; }
  else { printf("Error: This function only supports 2 primes max."); return FAIL; }


  /* Write the polynomials to the device buffer.  This is a non-blocking write. */
  status = clEnqueueWriteBuffer(commandQueue, kernelPolyBuffer, CL_FALSE, 0, numPolys*11*sizeof(long long), polBuf, 0, NULL, NULL);
  CHECK_ERROR(status, "Error: Failed to write polynomials to device buffer.", "clEnqueueWriteBuffer");


  //////////////////////////////////////////////////////////////////////////////
  //
  //  Launch Stage 1 kernel.
  //
  /* Setup the 4 kernel arguments */
  status = clSetKernelArg(pdtKernelStg1, 0, sizeof(int), (void *)&numPolys);
  CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelStg1, 1, sizeof(cl_mem), (void *)&kernelPolyBuffer);
  CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelStg1, 2, sizeof(cl_mem), (void *)&kernelFlagBuffer);
  CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelStg1, 3, sizeof(cl_mem), (void *)&kernelDiscBuffer);
  CHECK_ERROR(status, "Error: Setting arg 3.", "clSetKernelArg");

  /* Queue the kernel for execution */
  /* The local size is the number of work items in a work group */
  /* Total number of work items = numPolys, but we need to bump this up to the next multiple of threadsPerBlock */
  size_t numTotalThreads = ( (numPolys+threadsPerBlock-1)/threadsPerBlock ) * threadsPerBlock;
  size_t globalSize[1] = { numTotalThreads };
  size_t localSize[1]  = { (size_t)threadsPerBlock };
  status = clFinish(commandQueue);  // Make sure the previous buffer write has completed.
  CHECK_ERROR(status, "Error: Failed to Write Buffer.", "clFinish");

  cl_event ker1Done;
  status = clEnqueueNDRangeKernel(commandQueue, pdtKernelStg1, 1, NULL, globalSize, localSize, 0, NULL, &ker1Done);
  CHECK_ERROR(status, "Error: Failed to Enqueue Kernel Stage 1.", "clEnqueueNDRangeKernel");


  //////////////////////////////////////////////////////////////////////////////
  //
  //  Launch Stage 2 kernel.
  //
  /* Setup the 5 kernel arguments */
  status = clSetKernelArg(pdtKernelStg2, 0, sizeof(int), (void *)&numPolys);
  CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelStg2, 1, sizeof(cl_mem), (void *)&kernelFlagBuffer);
  CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelStg2, 2, sizeof(cl_mem), (void *)&kernelDiscBuffer);
  CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelStg2, 3, sizeof(int), (void *)&p1);
  CHECK_ERROR(status, "Error: Setting arg 3.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelStg2, 4, sizeof(int), (void *)&p2);
  CHECK_ERROR(status, "Error: Setting arg 4.", "clSetKernelArg");

  /* Launch the kernel after stage 1 is done */
  cl_event ker2Done;
  status = clEnqueueNDRangeKernel(commandQueue, pdtKernelStg2, 1, NULL, globalSize, localSize, 1, &ker1Done, &ker2Done);
  CHECK_ERROR(status, "Error: Failed to Enqueue Kernel Stage 2.", "clEnqueueNDRangeKernel");


  //////////////////////////////////////////////////////////////////////////////
  //
  //  Launch Stage 3 kernel.
  //
  /* Setup the 3 kernel arguments */
  status = clSetKernelArg(pdtKernelStg3, 0, sizeof(int), (void *)&numPolys);
  CHECK_ERROR(status, "Error: Setting arg 0.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelStg3, 1, sizeof(cl_mem), (void *)&kernelFlagBuffer);
  CHECK_ERROR(status, "Error: Setting arg 1.", "clSetKernelArg");

  status = clSetKernelArg(pdtKernelStg3, 2, sizeof(cl_mem), (void *)&kernelDiscBuffer);
  CHECK_ERROR(status, "Error: Setting arg 2.", "clSetKernelArg");

  /* Launch the kernel after stage 2 is done */
  status = clEnqueueNDRangeKernel(commandQueue, pdtKernelStg3, 1, NULL, globalSize, localSize, 1, &ker2Done, NULL);
  CHECK_ERROR(status, "Error: Failed to Enqueue Kernel Stage 3.", "clEnqueueNDRangeKernel");


  // If we make it this far, we assume success.  So return 0.
  return 0;

  }
