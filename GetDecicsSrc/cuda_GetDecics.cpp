/* Cuda Helper Functions for the GetDecics App */

#include <stdio.h>
#include <stdint.h>

#include "boinc_api.h"   /* needed for APP_INIT_DATA */
#include "cuda_GetDecics.h"


extern "C" int generateCudaGraph(void);
extern int polyBufferSize;


int initializeCuda(int argc, char** argv) {

  // First get the device ID and reserve it
  int devID = getCudaDevId(argc, argv);
  if(devID<0) {
    fprintf(stderr, "Error: failed to obtain a valid GPU device id.\n");
    return 1;
  }
  else {
    fprintf(stderr, "Setting GPU device number %d.\n", devID);
    cudaError_t error = cudaSetDevice(devID);
    if(error!=0) {
      fprintf(stderr, "Cuda Error: failed to set the device.\n");
      return 1;
    }
  }

  // Allocate Unified Memory -- accessible from both CPU and GPU
  cudaMallocManaged(&kernelPolyBuffer, polyBufferSize*11*sizeof(int64_t));
  CUDACHECK;
  cudaMallocManaged(&kernelFlagBuffer, polyBufferSize*sizeof(char));
  CUDACHECK;

  // Allocate Device only memory (intermediate data between kernel calls)
  cudaMalloc(&kernelDiscBuffer, polyBufferSize*sizeof(mp_int));


  // Create the Cuda Execution Graph
  //int status = generateCudaGraph();
  //if(status != 0) {
  //  fprintf(stderr, "Cuda Error: failed to generate the execution graph.\n");
  //  return status;
  //}


  // Create the stream
  cudaStreamCreate(&pdtStream);
  CUDACHECK;

  // Set device flags.  The blocking sync frees up the CPU while GPU is busy.
//  cudaSetDeviceFlags(cudaDeviceScheduleBlockingSync);
//  CUDACHECK;


  // If we make it this far, then return success
  return 0;
}




int getCudaDevId(int argc, char** argv) {

  APP_INIT_DATA aid;
  boinc_get_init_data(aid);

  // First check the gpu_opencl_dev_index
  if(aid.gpu_opencl_dev_index >= 0)  return aid.gpu_opencl_dev_index;

  // If that doesn't work, check the gpu_device_num
  if(aid.gpu_device_num >= 0)  return aid.gpu_device_num;

  // Finally, check the command line arguments.
  int devID = -1;  // Initialize to an invalid number
  for (int i=0; i<argc-1; i++) {
    if ((!strcmp(argv[i], "--device")) || (!strcmp(argv[i], "-device"))) {
      devID = atoi(argv[i+1]);
      break;
    }
  }
  return devID;
}



void cleanupCuda(void) {

  cudaFree(kernelPolyBuffer);
  cudaFree(kernelFlagBuffer);
  cudaFree(kernelDiscBuffer);
  cudaGraphExecDestroy(pdtExecGraph);
  cudaStreamDestroy(pdtStream);
  cudaDeviceReset();
  fprintf(stderr, "Cuda cleanup complete.\n");

}
