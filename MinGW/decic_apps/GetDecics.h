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



#ifdef APP_VERSION_GPU_CUDA
  #define CUDA
  #include "cuda_GetDecics.h"
  #define DEFAULT_POLY_BUFFER_SIZE   3200  //5120  /* Size of polynomial buffer (on host) */
  #define DEFAULT_THREADS_PER_BLOCK  32    //512
#elif APP_VERSION_GPU_OPENCL
  #define OPENCL
  #include "openCL_GetDecics.h"
  #define DEFAULT_POLY_BUFFER_SIZE   3200
  #define DEFAULT_THREADS_PER_BLOCK  32
#else   /* cpu version */
  #define DEFAULT_POLY_BUFFER_SIZE   10240  /* 500000 uses almost 50 MB */
  #define DEFAULT_THREADS_PER_BLOCK  1       /* value is unused for cpus */
#endif



#endif
