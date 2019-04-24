/* OpenCL Data and Helper Functions for the GetDecics App */

#ifndef OPENCL_GETDECICS_H
#define OPENCL_GETDECICS_H

#include <CL/opencl.h>


/* The global OpenCL Objects */
extern cl_context        context;
extern cl_command_queue  commandQueue;
extern cl_program        program;
extern cl_kernel         pdtKernel;
extern cl_mem            kernelPolyBuffer;
extern cl_mem            kernelFlagBuffer;


/* Function Prototypes */
int initializeOpenCL(int, char**);
void cleanup_openCL(void);
void printBuildLog(cl_device_id);
const char *getErrorString(cl_int);
char* convert_to_string(const char*);


#define KERNEL_FILENAME "pdtKernel.cl"


#endif
