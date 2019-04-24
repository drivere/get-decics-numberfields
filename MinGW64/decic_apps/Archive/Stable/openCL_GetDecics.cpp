/* OpenCL Helper Functions for the GetDecics App */

#define CL_USE_DEPRECATED_OPENCL_1_2_APIS


#include <CL/opencl.h>
#include "boinc_api.h"
#include "boinc_opencl.h"
#include "GetDecics.h"
#include "openCL_GetDecics.h"

int initializeOpenCL(int argc, char * argv[]) {

  /* Get the device and platform ids */
  cl_platform_id platform = NULL;
  cl_device_id device;
  int retval = boinc_get_opencl_ids(argc, argv, BOINC_GPU_PLATFORM, &device, &platform);
  if(retval) {
    fprintf(stderr, "Error: Failed to obtain OpenCL device id.\n");
    return 1;
  }

  /* Create the OpenCL context */
  cl_context_properties cps[3] = { CL_CONTEXT_PLATFORM, (cl_context_properties)platform, 0 };
  cl_int status = 0;
  context = clCreateContext(cps, 1, &device, NULL, NULL, &status);
  if (status != CL_SUCCESS) {
    fprintf(stderr, "Error: clCreateContext() returned %s\n", getErrorString(status));
    return 1; 
  }

  /* Create an OpenCL command queue */
  commandQueue = clCreateCommandQueue(context, device, 0, &status);
  if(status != CL_SUCCESS) { 
    fprintf(stderr, "Error: clCreateCommandQueue() returned %s\n", getErrorString(status));
    return 1;
  }

  /* Load CL file into a string and create the OpenCL program object */
  char *source = convert_to_string(KERNEL_FILENAME);
  size_t sourceSize[] = { strlen(source) };
  program = clCreateProgramWithSource(context, 1, (const char**)&source, sourceSize, &status);
  if (status != CL_SUCCESS) {
    fprintf(stderr, "Error: clCreateProgramWithSource() returned %s\n", getErrorString(status));
    return 1;
  }
  free(source);

  /* Build the OpenCL program executable */
  //status = clBuildProgram(program, 1, &device, "-D OPENCL", NULL, NULL);
  status = clBuildProgram(program, 1, &device, "-D OPENCL -I. -cl-std=CL1.2", NULL, NULL);
  if (status != CL_SUCCESS)  {
    fprintf(stderr, "Error: clBuildProgram() returned %s\n", getErrorString(status));
    printBuildLog(device);
    return 1;
  }
  fprintf(stderr, "Successfully Built Program.\n");


  /* Create the OpenCL kernel object */
  pdtKernel = clCreateKernel(program, "pdtKernel", &status);
  if (status != CL_SUCCESS) {
    fprintf(stderr, "Error: clCreateKernel() returned %s\n", getErrorString(status));
    return 1;
  }
  fprintf(stderr, "Successfully Created Kernel.\n");

  /* Create the OpenCL memory buffers */
  kernelPolyBuffer = clCreateBuffer(context, CL_MEM_READ_ONLY, sizeof(long long)*polyBufferSize*11, NULL, &status);
  if (status != CL_SUCCESS) {
    fprintf(stderr, "Error: Failed to create device polynomial buffer. clCreateBuffer() returned %s\n", getErrorString(status));
    return 1;
  }
  fprintf(stderr, "Successfully Created Polynomial Memory Buffer.\n");

  kernelFlagBuffer = clCreateBuffer(context, CL_MEM_WRITE_ONLY, sizeof(char)*polyBufferSize, NULL, &status);
  if (status != CL_SUCCESS) {
    fprintf(stderr, "Error: Failed to create device result buffer. clCreateBuffer() returned %s\n", getErrorString(status));
    return 1;
  }
  fprintf(stderr, "Successfully Created Output Memory Buffer.\n");

  /* If we make it this far, then return success */
  return 0;
}



void cleanup_openCL(void) {
  clReleaseMemObject(kernelPolyBuffer);
  clReleaseMemObject(kernelFlagBuffer);
  clReleaseKernel(pdtKernel);
  clReleaseCommandQueue(commandQueue);
  clReleaseProgram(program);
  clReleaseContext(context);
}



/* Print out the build log from clBuildProgram */
void printBuildLog(cl_device_id device) {
    size_t logSize;
    clGetProgramBuildInfo(program, device, CL_PROGRAM_BUILD_LOG, 0, NULL, &logSize);
    char *buildLog = (char*)malloc(logSize + 1);
    buildLog[logSize] = '\0';
    clGetProgramBuildInfo(program, device, CL_PROGRAM_BUILD_LOG, logSize+1, buildLog, NULL);
    fprintf(stderr, "Build Log:\n%s\n", buildLog);
    free(buildLog);
}



const char *getErrorString(cl_int error)
{
switch(error){
    // run-time and JIT compiler errors
    case 0: return "CL_SUCCESS";
    case -1: return "CL_DEVICE_NOT_FOUND";
    case -2: return "CL_DEVICE_NOT_AVAILABLE";
    case -3: return "CL_COMPILER_NOT_AVAILABLE";
    case -4: return "CL_MEM_OBJECT_ALLOCATION_FAILURE";
    case -5: return "CL_OUT_OF_RESOURCES";
    case -6: return "CL_OUT_OF_HOST_MEMORY";
    case -7: return "CL_PROFILING_INFO_NOT_AVAILABLE";
    case -8: return "CL_MEM_COPY_OVERLAP";
    case -9: return "CL_IMAGE_FORMAT_MISMATCH";
    case -10: return "CL_IMAGE_FORMAT_NOT_SUPPORTED";
    case -11: return "CL_BUILD_PROGRAM_FAILURE";
    case -12: return "CL_MAP_FAILURE";
    case -13: return "CL_MISALIGNED_SUB_BUFFER_OFFSET";
    case -14: return "CL_EXEC_STATUS_ERROR_FOR_EVENTS_IN_WAIT_LIST";
    case -15: return "CL_COMPILE_PROGRAM_FAILURE";
    case -16: return "CL_LINKER_NOT_AVAILABLE";
    case -17: return "CL_LINK_PROGRAM_FAILURE";
    case -18: return "CL_DEVICE_PARTITION_FAILED";
    case -19: return "CL_KERNEL_ARG_INFO_NOT_AVAILABLE";

    // compile-time errors
    case -30: return "CL_INVALID_VALUE";
    case -31: return "CL_INVALID_DEVICE_TYPE";
    case -32: return "CL_INVALID_PLATFORM";
    case -33: return "CL_INVALID_DEVICE";
    case -34: return "CL_INVALID_CONTEXT";
    case -35: return "CL_INVALID_QUEUE_PROPERTIES";
    case -36: return "CL_INVALID_COMMAND_QUEUE";
    case -37: return "CL_INVALID_HOST_PTR";
    case -38: return "CL_INVALID_MEM_OBJECT";
    case -39: return "CL_INVALID_IMAGE_FORMAT_DESCRIPTOR";
    case -40: return "CL_INVALID_IMAGE_SIZE";
    case -41: return "CL_INVALID_SAMPLER";
    case -42: return "CL_INVALID_BINARY";
    case -43: return "CL_INVALID_BUILD_OPTIONS";
    case -44: return "CL_INVALID_PROGRAM";
    case -45: return "CL_INVALID_PROGRAM_EXECUTABLE";
    case -46: return "CL_INVALID_KERNEL_NAME";
    case -47: return "CL_INVALID_KERNEL_DEFINITION";
    case -48: return "CL_INVALID_KERNEL";
    case -49: return "CL_INVALID_ARG_INDEX";
    case -50: return "CL_INVALID_ARG_VALUE";
    case -51: return "CL_INVALID_ARG_SIZE";
    case -52: return "CL_INVALID_KERNEL_ARGS";
    case -53: return "CL_INVALID_WORK_DIMENSION";
    case -54: return "CL_INVALID_WORK_GROUP_SIZE";
    case -55: return "CL_INVALID_WORK_ITEM_SIZE";
    case -56: return "CL_INVALID_GLOBAL_OFFSET";
    case -57: return "CL_INVALID_EVENT_WAIT_LIST";
    case -58: return "CL_INVALID_EVENT";
    case -59: return "CL_INVALID_OPERATION";
    case -60: return "CL_INVALID_GL_OBJECT";
    case -61: return "CL_INVALID_BUFFER_SIZE";
    case -62: return "CL_INVALID_MIP_LEVEL";
    case -63: return "CL_INVALID_GLOBAL_WORK_SIZE";
    case -64: return "CL_INVALID_PROPERTY";
    case -65: return "CL_INVALID_IMAGE_DESCRIPTOR";
    case -66: return "CL_INVALID_COMPILER_OPTIONS";
    case -67: return "CL_INVALID_LINKER_OPTIONS";
    case -68: return "CL_INVALID_DEVICE_PARTITION_COUNT";

    // extension errors
    case -1000: return "CL_INVALID_GL_SHAREGROUP_REFERENCE_KHR";
    case -1001: return "CL_PLATFORM_NOT_FOUND_KHR";
    case -1002: return "CL_INVALID_D3D10_DEVICE_KHR";
    case -1003: return "CL_INVALID_D3D10_RESOURCE_KHR";
    case -1004: return "CL_D3D10_RESOURCE_ALREADY_ACQUIRED_KHR";
    case -1005: return "CL_D3D10_RESOURCE_NOT_ACQUIRED_KHR";
    default: return "Unknown OpenCL error";
    }
}



/* Converts the contents of a file into a string */
char* convert_to_string(const char *fileName) {
  int count=0;
  char *s;
  char c;
  int i=0;

  FILE *infile=fopen(fileName,"r");
  if (!infile) {
    fprintf(stderr, "ERROR: Failed to open file %s!", fileName);
    exit(0);
  }
  fseek(infile,0,SEEK_SET);
  while (fgetc(infile)!=EOF) count++;
  s=(char *) malloc(sizeof(char)*(count+1)); //add 1 for string terminator.
  fseek(infile,0,SEEK_SET);	
  while ((c=fgetc(infile))!=EOF)  s[i++]=c;
  s[i]='\0';
  fclose(infile);
  return s;
}
