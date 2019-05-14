#ifndef GETDECICS_H
#define GETDECICS_H


typedef long long pari_long;

/* Global variables */
extern int numBlocks;
extern int threadsPerBlock;
extern int polyBufferSize;


/* Function Prototypes */
int  do_checkpoint(pari_long*, pari_long*);
void init_globals(int, char**);


/* Setup based on GPU Vendor and Cuda vs openCL */
#ifdef APP_VERSION_GPU_CUDA
  #include "cuda_GetDecics.h"
#elif APP_VERSION_GPU_OPENCL
  #define OPENCL
  #ifdef GPU_VENDOR_NVIDIA
    #define BOINC_GPU_PLATFORM  PROC_TYPE_NVIDIA_GPU
  #elif  GPU_VENDOR_AMD
    #define BOINC_GPU_PLATFORM  PROC_TYPE_AMD_GPU
  #elif  GPU_VENDOR_INTEL
    #define BOINC_GPU_PLATFORM  PROC_TYPE_INTEL_GPU
  #endif
  #include "openCL_GetDecics.h"
#endif


// Set kernel sizing.  We use Cuda terminology.
// NumBlocks is NumWorkGroups in openCL.
// ThreadsPerBlock is Work Items Per WorkGroup in openCL.
// NumBlocks = PolyBufferSize / ThreadsPerBlock, so ThreadsPerBlock 
//    must evenly divide PolyBufferSize.
#if defined(APP_VERSION_GPU_CUDA) || defined(GPU_VENDOR_NVIDIA)
  #define DEFAULT_POLY_BUFFER_SIZE   3200  /* Size of polynomial buffer (on host) */
  #define DEFAULT_THREADS_PER_BLOCK  32
#elif GPU_VENDOR_AMD
  #define DEFAULT_POLY_BUFFER_SIZE   4096
  #define DEFAULT_THREADS_PER_BLOCK  32
#elif GPU_VENDOR_INTEL
  #define DEFAULT_POLY_BUFFER_SIZE   4096
  #define DEFAULT_THREADS_PER_BLOCK  32
#else   /* cpu version */
  #define DEFAULT_POLY_BUFFER_SIZE   10240   /* 10000 polys uses almost 1 MB */
  #define DEFAULT_THREADS_PER_BLOCK  1       /* value is unused for cpus */
#endif


#endif
