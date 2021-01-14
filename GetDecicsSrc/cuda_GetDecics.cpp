/* Cuda Helper Functions for the GetDecics App */

#include <stdio.h>
#include <stdint.h>

#include "boinc_api.h"   /* needed for APP_INIT_DATA */
#include "cuda_GetDecics.h"


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

  // Set device flags.  The blocking sync frees up the CPU while GPU is busy.
  cudaSetDeviceFlags(cudaDeviceScheduleBlockingSync);
  CUDACHECK;

  // Allocate Unified Memory -- accessible from both CPU and GPU
  cudaMallocManaged(&gpuPolyBuffer, polyBufferSize*11*sizeof(int64_t));
  CUDACHECK;
  cudaMallocManaged(&gpuFlagBuffer, polyBufferSize*sizeof(char));
  CUDACHECK;

  // Allocate Device only memory (intermediate data between kernel calls)
  cudaMalloc(&gpuDiscBuffer, polyBufferSize*sizeof(mp_int));
  cudaMalloc(&gpuPolyA, polyBufferSize*10*sizeof(int64_t));
  cudaMalloc(&gpuPolyB, polyBufferSize*9*sizeof(int64_t));
  cudaMalloc(&gpuDegA,  polyBufferSize*sizeof(int));
  cudaMalloc(&gpuDegB,  polyBufferSize*sizeof(int));
  cudaMalloc(&gpuG,     polyBufferSize*sizeof(int64_t));
  cudaMalloc(&gpuH,     polyBufferSize*sizeof(int64_t));
  cudaMalloc(&gpuScale, polyBufferSize*sizeof(uint64_t));
  cudaMalloc(&gpu_mpA,  polyBufferSize*10*sizeof(mp_int));
  cudaMalloc(&gpu_mpB,  polyBufferSize*9*sizeof(mp_int));

  // Create the stream
  cudaStreamCreate(&pdtStream);
  CUDACHECK;

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

  cudaFree(gpuPolyBuffer);
  cudaFree(gpuFlagBuffer);
  cudaFree(gpuDiscBuffer);
  cudaFree(gpuPolyA);
  cudaFree(gpuPolyB);
  cudaFree(gpuDegA);
  cudaFree(gpuDegB);
  cudaFree(gpuG);
  cudaFree(gpuH);
  cudaFree(gpuScale);
  cudaFree(gpu_mpA);
  cudaFree(gpu_mpB);
  cudaStreamDestroy(pdtStream);
  cudaDeviceReset();
  fprintf(stderr, "Cuda cleanup complete.\n");

}
