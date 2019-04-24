#ifndef GETDECICS_H
#define GETDECICS_H


typedef long long pari_long;

/* Global variables */
extern int numBlocks;
extern int threadsPerBlock;
extern int polyBufferSize;


/* Function Prototypes */
int  do_checkpoint(pari_long*, pari_long*);
int  getCudaDevId(int, char**);
void init_globals(int, char**);



#ifdef APP_VERSION_GPU_CUDA
  #include <cuda_runtime.h>
  #define DEFAULT_POLY_BUFFER_SIZE   5120  /* Size of polynomial buffer (on host) */
  #define DEFAULT_THREADS_PER_BLOCK  512
#elif APP_VERSION_GPU_OPENCL
  #include "openCL_GetDecics.h"
  #define DEFAULT_POLY_BUFFER_SIZE   5120
  #define DEFAULT_THREADS_PER_BLOCK  512
#else   /* cpu version */
  #define DEFAULT_POLY_BUFFER_SIZE   10240
  #define DEFAULT_THREADS_PER_BLOCK  1    /* value is unused for cpus */
#endif



#endif
