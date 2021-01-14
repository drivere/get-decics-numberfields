/* OpenCL Data and Helper Functions for the GetDecics App */

#ifndef OPENCL_GETDECICS_H
#define OPENCL_GETDECICS_H

#include <CL/opencl.h>
#include "mp_int.h"


/* The global OpenCL Objects */
extern cl_context        context;
extern cl_command_queue  commandQueue;
extern cl_program        program;
extern cl_kernel         pdtKernelSubResultantInit;
extern cl_kernel         pdtKernelSubResultantMpInit;
extern cl_kernel         pdtKernelSubResultantDegB8;
extern cl_kernel         pdtKernelSubResultantDegB7DegA9;
extern cl_kernel         pdtKernelSubResultantDegB7DegA8;
extern cl_kernel         pdtKernelSubResultantDegB6DegA9;
extern cl_kernel         pdtKernelSubResultantDegB6DegA8;
extern cl_kernel         pdtKernelSubResultantDegB6DegA7;
extern cl_kernel         pdtKernelSubResultantDegB5;
extern cl_kernel         pdtKernelSubResultantDegB4;
//extern cl_kernel         pdtKernelSubResultantDegB3;
//extern cl_kernel         pdtKernelSubResultantDegB2;
extern cl_kernel         pdtKernelSubResultantFinish;
extern cl_kernel         pdtKernelDiv2;
extern cl_kernel         pdtKernelDiv5;
extern cl_kernel         pdtKernelDivP;
extern cl_kernel         pdtKernelStg3;
extern cl_mem            kernelPolyBuffer;
extern cl_mem            kernelFlagBuffer;
extern cl_mem            kernelDiscBuffer;
extern cl_mem            kernelPolyA;
extern cl_mem            kernelPolyB;
extern cl_mem            kernelDegA;
extern cl_mem            kernelDegB;
extern cl_mem            kernelG;
extern cl_mem            kernelH;
extern cl_mem            kernelMpA;
extern cl_mem            kernelMpB;


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
