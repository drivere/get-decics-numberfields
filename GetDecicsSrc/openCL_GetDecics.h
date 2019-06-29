/* OpenCL Data and Helper Functions for the GetDecics App */

#ifndef OPENCL_GETDECICS_H
#define OPENCL_GETDECICS_H

#include <CL/opencl.h>
#include "gpuMultiPrec.h"


/* The global OpenCL Objects */
extern cl_context        context;
extern cl_command_queue  commandQueue;
extern cl_program        program;
extern cl_kernel         pdtKernelStg1;
extern cl_kernel         pdtKernelStg2;
extern cl_kernel         pdtKernelStg3;
extern cl_mem            kernelPolyBuffer;
extern cl_mem            kernelFlagBuffer;
extern cl_mem            kernelDiscBuffer;


/* Function Prototypes */
int initializeOpenCL(int, char**);
void cleanup_openCL(void);
void printBuildLog(cl_device_id);
const char *getErrorString(cl_int);
char* convert_to_string(const char*);

#ifdef GPU_VENDOR_AMD
  #define KERNEL_FILENAME "pdtKernelAMD.cl"
#else
  #define KERNEL_FILENAME "pdtKernel.cl"
#endif

#endif
