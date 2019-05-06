/* Cuda Data and Helper Functions for the GetDecics App */

#ifndef CUDA_GETDECICS_H
#define CUDA_GETDECICS_H


#include <cuda_runtime.h>
#include "gpuMultiPrec128.h"
//#include "gpuMultiPrec256.h"


#define FAIL  1
#define CUDACHECK {cudaError_t error = cudaGetLastError(); if(error != 0){fprintf(stderr, "Error code %d: %s file %s line %i.\n",error,cudaGetErrorString(error),__FILE__,__LINE__); return FAIL;}}


/* The global Cuda Objects */
extern int64_t *kernelPolyBuffer;
extern char    *kernelFlagBuffer;
extern mp_int  *kernelDiscBuffer;
extern cudaGraphExec_t  pdtExecGraph;
extern cudaStream_t     pdtStream;

/* Function Prototypes */
int  initializeCuda(int, char**);
int  getCudaDevId(int, char**);
void cleanupCuda(void);


#endif
