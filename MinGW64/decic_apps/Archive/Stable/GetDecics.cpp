// This is the BOINC main wrapper for the Targeted Martinet search routine.


//typedef long long pari_long;



#ifdef _WIN32
#  include "boinc_win.h"
#else
#  include "config.h"
#endif

#ifndef _WIN32
#  include <cstdio>
#  include <cctype>
#  include <ctime>
#  include <cstring>
#  include <cstdlib>
#  include <csignal>
#  include <unistd.h>
#endif

/*
#ifdef _WIN32
#  include "pari.h"
#  ifdef long
#    undef long
#  endif
#endif
*/

#include "diagnostics.h"
#include "str_util.h"
#include "util.h"
#include "filesys.h"
#include "boinc_api.h"
#include "mfile.h"

#include "GetDecics.h"
#include "TgtMartinet.h"


/* Global variables */
int numBlocks;
int threadsPerBlock;
int polyBufferSize;


#ifdef APP_VERSION_GPU_OPENCL
  /* The global OpenCL objects */
  cl_context        context;
  cl_command_queue  commandQueue;
  cl_program        program;
  cl_kernel         pdtKernel;
  cl_mem            kernelPolyBuffer;
  cl_mem            kernelFlagBuffer;
#endif


using std::string;

#define DEFAULT_CHECKPOINT_FILE "GetDecics_state"
#define INPUT_FILENAME "in"
#define OUTPUT_FILENAME "out"


string CHECKPOINT_FILE;


int main(int argc, char **argv)
  {
  int retval;
  int ChkPntFlag = 0;
  pari_long CvecIdx=0;
  pari_long N1_Start = 0, N2_Start = 0;
  pari_long k1_Start = 0, k2_Start = 0;
  pari_long L1_Start = 0, L2_Start = 0;
  pari_long m1_Start = 0, m2_Start = 0;
  pari_long SV[5] = {0,0,0,0,0};
  char input_path[512], output_path[512], chkpt_path[512];
  FILE* ChkPntFile;


  boinc_init_diagnostics(BOINC_DIAG_REDIRECTSTDERR|
                         BOINC_DIAG_MEMORYLEAKCHECKENABLED|
                         BOINC_DIAG_DUMPCALLSTACKENABLED|
                         BOINC_DIAG_TRACETOSTDERR);
  //fprintf(stderr, "APP:  Initializing boinc.\n");
  retval = boinc_init();
  if(retval) exit(retval);

  // Resolve the input and output file names
  boinc_resolve_filename(INPUT_FILENAME,  input_path,  sizeof(input_path));
  boinc_resolve_filename(OUTPUT_FILENAME, output_path, sizeof(output_path));

  // Load the application init data
  APP_INIT_DATA aid;
  boinc_get_init_data(aid);
  //fprintf(stderr, "wu_name  = %s.\n", aid.wu_name);


  // Setup the globals (polyBufferSize, numBlocks, threadsPerBlock)
  init_globals(argc, argv);


  // Setup the Device ID for GPU apps.
#ifdef APP_VERSION_GPU_CUDA
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
#endif

#ifdef APP_VERSION_GPU_OPENCL
  int status = initializeOpenCL(argc, argv);
  if(status) {
    fprintf(stderr, "Error: Failed to initialize OpenCL.\n");
    return 1;
  }
  else {
    fprintf(stderr, "OpenCL initialization was successful.\n");
  }
#endif


  // Generate a unique checkpoint filename
  CHECKPOINT_FILE = aid.wu_name;
  CHECKPOINT_FILE += "_checkpoint";
  if(CHECKPOINT_FILE.length()<13) CHECKPOINT_FILE = DEFAULT_CHECKPOINT_FILE;
  fprintf(stderr, "CHECKPOINT_FILE = %s.\n", CHECKPOINT_FILE.c_str());


  // Read the checkpoint file.
  boinc_resolve_filename(CHECKPOINT_FILE.c_str(), chkpt_path, sizeof(chkpt_path));
  ChkPntFile = boinc_fopen(chkpt_path, "r");
  if(ChkPntFile)
    {
    fprintf(stderr, "Reading checkpoint file.\n");

    fscanf(ChkPntFile, "%lld %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld %lld", 
           &CvecIdx, &N1_Start, &N2_Start, &k1_Start, &k2_Start, &L1_Start, &L2_Start, 
           &m1_Start, &m2_Start, &SV[0], &SV[1], &SV[2], &SV[3], &SV[4]);

    fclose(ChkPntFile);
    ChkPntFlag = 1;
    }


  // Print out some diagnostic information
  fprintf(stderr, "Checkpoint Flag = %d.\n",ChkPntFlag);
  if(ChkPntFlag) {
    fprintf(stderr, "Checkpoint Data:\n");
    fprintf(stderr, "   Cvec Starting Index = %lld.\n", CvecIdx);
    fprintf(stderr, "   N1 Start = %lld.\n", N1_Start);
    fprintf(stderr, "   N2 Start = %lld.\n", N2_Start);
    fprintf(stderr, "   k1 Start = %lld.\n", k1_Start);
    fprintf(stderr, "   k2 Start = %lld.\n", k2_Start);
    fprintf(stderr, "   L1 Start = %lld.\n", L1_Start);
    fprintf(stderr, "   L2 Start = %lld.\n", L2_Start);
    fprintf(stderr, "   m1 Start = %lld.\n", m1_Start);
    fprintf(stderr, "   m2 Start = %lld.\n", m2_Start);
    fprintf(stderr, "   Poly Count value = %lld.\n", SV[0]);
    fprintf(stderr, "   Poly Disc Count = %lld.\n", SV[1]);
    fprintf(stderr, "   Irreducibility Count = %lld.\n", SV[2]);
    fprintf(stderr, "   Field Disc Count = %lld.\n", SV[3]);
    fprintf(stderr, "   Elapsed Time = %lld (sec).\n", SV[4]);
    }

  // Start the search
  TgtMartinet(input_path, output_path, ChkPntFlag, CvecIdx, N1_Start, N2_Start, k1_Start, k2_Start, 
	      L1_Start, L2_Start, m1_Start, m2_Start, SV);


#ifdef APP_VERSION_GPU_OPENCL
  cleanup_openCL();
#endif

  boinc_finish(0);
  }



int do_checkpoint(pari_long *loopIdxs, pari_long *Stat)
  {
  int retval;
  string resolved_name;

  FILE* f = fopen("temp", "w");
  if(!f) return 1;

  fprintf(f, "%lld\n%lld\n%lld\n%lld\n%lld\n%lld\n%lld\n%lld\n%lld\n%lld\n%lld\n%lld\n%lld\n%lld", 
          loopIdxs[0], loopIdxs[1], loopIdxs[2], loopIdxs[3], loopIdxs[4], loopIdxs[5], loopIdxs[6], 
          loopIdxs[7], loopIdxs[8], Stat[0], Stat[1], Stat[2], Stat[3], Stat[4]);
  fclose(f);

  boinc_resolve_filename_s(CHECKPOINT_FILE.c_str(), resolved_name);
  retval = boinc_rename("temp", resolved_name.c_str());
  if(retval) return retval;

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




void  init_globals(int argc, char** argv) {

  /* Initialize using the default values */
  polyBufferSize  = DEFAULT_POLY_BUFFER_SIZE;
  threadsPerBlock = DEFAULT_THREADS_PER_BLOCK;

  /* The buffer size needs to be a multiple of the threadsPerBlock */
  polyBufferSize = ( (polyBufferSize+threadsPerBlock-1)/threadsPerBlock ) * threadsPerBlock;

  numBlocks = polyBufferSize / threadsPerBlock;

  /* Now check the command line arguments for overrides. */
  /* Two command line arguments can be overriden: numBlocks and threadsPerBlock */
  for (int i=0; i<argc-1; i++) {
    if ((!strcmp(argv[i], "--numBlocks")) || (!strcmp(argv[i], "-numBlocks"))) {
      numBlocks = atoi(argv[i+1]);
      i+=2;
    }
    if ((!strcmp(argv[i], "--threadsPerBlock")) || (!strcmp(argv[i], "-threadsPerBlock"))) {
      threadsPerBlock = atoi(argv[i+1]);
      i+=2;
    }
  }

  /* Recompute the polynomial buffer size in case of overrides */
  polyBufferSize = numBlocks * threadsPerBlock;

  /* Print out diagnostic information */
#if defined(APP_VERSION_GPU_OPENCL) || defined(APP_VERSION_GPU_CUDA)
  fprintf(stderr, "numBlocks = %d.\n", numBlocks);
  fprintf(stderr, "threadsPerBlock = %d.\n", threadsPerBlock);
#endif
  fprintf(stderr, "polyBufferSize = %d.\n", polyBufferSize);

}

