/* Cuda Data and Helper Functions for the GetDecics App */

#ifndef CUDA_GETDECICS_H
#define CUDA_GETDECICS_H


/* The multi-precision typedef, only needed for sizing below */
#include "mp_int.h"

#include <cuda_runtime.h>


#define FAIL  1
#define CUDACHECK {cudaError_t error = cudaGetLastError(); if(error != 0){fprintf(stderr, "Error code %d: %s file %s line %i.\n",error,cudaGetErrorString(error),__FILE__,__LINE__); return FAIL;}}


/* The global Cuda Objects */
extern int64_t  *gpuPolyBuffer;
extern char     *gpuFlagBuffer;
extern mp_int   *gpuDiscBuffer;
extern int64_t  *gpuPolyA;
extern int64_t  *gpuPolyB;
extern int      *gpuDegA;
extern int      *gpuDegB;
extern int64_t  *gpuG;
extern int64_t  *gpuH;
extern uint64_t *gpuScale;
extern mp_int   *gpu_mpA;
extern mp_int   *gpu_mpB;
extern cudaStream_t     pdtStream;

/* Function Prototypes */
int  initializeCuda(int, char**);
int  getCudaDevId(int, char**);
void cleanupCuda(void);


#endif
