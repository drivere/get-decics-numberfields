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

#include "diagnostics.h"
#include "str_util.h"
#include "util.h"
#include "filesys.h"
#include "boinc_api.h"
#include "mfile.h"

#include "GetDecics.h"
#include "TgtMartinet.h"

#include <fstream>
using std::ifstream;


/* Global variables */
int numBlocks;
int threadsPerBlock;
int polyBufferSize;


#ifdef APP_VERSION_GPU_CUDA
  int64_t  *gpuPolyBuffer;
  char     *gpuFlagBuffer;
  mp_int   *gpuDiscBuffer;
  int64_t  *gpuPolyA;
  int64_t  *gpuPolyB;
  int      *gpuDegA;
  int      *gpuDegB;
  int64_t  *gpuG;
  int64_t  *gpuH;
  uint64_t *gpuScale;
  mp_int   *gpu_mpA;
  mp_int   *gpu_mpB;
  cudaStream_t     pdtStream;
#endif

#ifdef APP_VERSION_GPU_OPENCL
  /* The global OpenCL objects */
  cl_context        context;
  cl_command_queue  commandQueue;
  cl_program        program;
  cl_kernel         pdtKernelSubResultantInit;
  cl_kernel         pdtKernelSubResultantMpInit;
  cl_kernel         pdtKernelSubResultantDegB8;
  cl_kernel         pdtKernelSubResultantDegB7DegA9;
  cl_kernel         pdtKernelSubResultantDegB7DegA8;
  cl_kernel         pdtKernelSubResultantDegB6DegA9;
  cl_kernel         pdtKernelSubResultantDegB6DegA8;
  cl_kernel         pdtKernelSubResultantDegB6DegA7;
  cl_kernel         pdtKernelSubResultantDegB5;
  cl_kernel         pdtKernelSubResultantDegB4;
  cl_kernel         pdtKernelSubResultantDegB3;
  cl_kernel         pdtKernelSubResultantDegB2;

  cl_kernel         pdtKernelSubResultantFinish;

  cl_kernel         pdtKernelDiv2;
  cl_kernel         pdtKernelDiv5;
  cl_kernel         pdtKernelDivP;
  cl_kernel         pdtKernelStg3;
  cl_mem            kernelPolyBuffer;
  cl_mem            kernelFlagBuffer;
  cl_mem            kernelDiscBuffer;
  cl_mem            kernelPolyA;
  cl_mem            kernelPolyB;
  cl_mem            kernelDegA;
  cl_mem            kernelDegB;
  cl_mem            kernelG;
  cl_mem            kernelH;
  cl_mem            kernelMpA;
  cl_mem            kernelMpB;
#endif


using std::string;

#define DEFAULT_CHECKPOINT_FILE "GetDecics_state"
#define INPUT_FILENAME "in"
#define OUTPUT_FILENAME "out"
#define GPU_LOOKUP_TABLE_FILENAME "gpuLookupTable.txt"


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
  int status = initializeCuda(argc, argv);
  if(status) {
    fprintf(stderr, "Error: Failed to initialize Cuda.\n");
    return 1;
  }
  else {
    fprintf(stderr, "Cuda initialization was successful.\n");
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


#ifdef APP_VERSION_GPU_CUDA
  cleanupCuda();
#endif

#ifdef APP_VERSION_GPU_OPENCL
  cleanup_openCL();
#endif

  boinc_finish(0);
  }



int do_checkpoint(pari_long *loopIdxs, pari_long *Stat)
  {
  int retval;
  char resolved_name[512];

  FILE* f = fopen("temp", "w");
  if(!f) return 1;

  fprintf(f, "%lld\n%lld\n%lld\n%lld\n%lld\n%lld\n%lld\n%lld\n%lld\n%lld\n%lld\n%lld\n%lld\n%lld", 
          loopIdxs[0], loopIdxs[1], loopIdxs[2], loopIdxs[3], loopIdxs[4], loopIdxs[5], loopIdxs[6], 
          loopIdxs[7], loopIdxs[8], Stat[0], Stat[1], Stat[2], Stat[3], Stat[4]);
  fclose(f);

  boinc_resolve_filename(CHECKPOINT_FILE.c_str(), resolved_name, sizeof(resolved_name));
  retval = boinc_rename("temp", resolved_name);
  if(retval) return retval;

  return 0;
  }



void  init_globals(int argc, char** argv) {

#ifdef APP_VERSION_CPU_STD
  /* Initialize using the default values */
  numBlocks       = DEFAULT_NUM_BLOCKS;
  threadsPerBlock = DEFAULT_THREADS_PER_BLOCK;
#else
  // Otherwise this is the GPU case.  We use a lookup table.

  // First get the summary string for the host GPU.
  APP_INIT_DATA aid;
  char gpuSummary[1024];
  boinc_get_init_data(aid);
  aid.host_info.coprocs.summary_string(gpuSummary, sizeof(gpuSummary));

  // Remove all spaces from the gpu summary string.
  string gpuStr = gpuSummary;
  int idx = 0;
  for(int k = 0; gpuStr[k]; k++)  if(gpuStr[k] != ' ') gpuStr[idx++] = gpuStr[k];
  gpuStr = gpuStr.erase(idx);
  fprintf(stderr, "GPU Summary String = %s.\n", gpuStr.c_str());

  // Load the lookup table.  This allows for 64 entries.
  string gpuNameList[64];
  int numBlocksList[64], threadsPerBlockList[64];
  int numEntries = loadLookupTable(gpuNameList, numBlocksList, threadsPerBlockList);
  if(numEntries) {

    // Find the GPU in the lookup table
    int row, found = 0;
    for(int k=0; k<numEntries; ++k) {
      int idx = gpuStr.find(gpuNameList[k]);
      if(idx>0) {
        found = 1;
        row = k;
        break;  // Exit the loop once it is found
        }
      }

    if(found) {
      numBlocks       = numBlocksList[row];
      threadsPerBlock = threadsPerBlockList[row];
      fprintf(stderr, "GPU found in lookup table:\n");
      fprintf(stderr, "  GPU Name = %s.\n", gpuNameList[row].c_str());
      }
    else {
      numBlocks       = DEFAULT_NUM_BLOCKS;
      threadsPerBlock = DEFAULT_THREADS_PER_BLOCK;
      fprintf(stderr, "GPU was not found in the lookup table.  Using default values:\n");
      }

    }

  // This is the case when there was a problem with the lookup table or it was empty.
  else { 
    numBlocks       = DEFAULT_NUM_BLOCKS;
    threadsPerBlock = DEFAULT_THREADS_PER_BLOCK;
    fprintf(stderr, "Lookup table was empty.  Using default values:\n");
    }

#endif

  polyBufferSize  = numBlocks * threadsPerBlock;
  fprintf(stderr, "  numBlocks = %d.\n", numBlocks);
  fprintf(stderr, "  threadsPerBlock = %d.\n", threadsPerBlock);
  fprintf(stderr, "  polyBufferSize = %d.\n", polyBufferSize);


  /* Now check the command line arguments for overrides. */
  /* Two command line arguments can be overriden: numBlocks and threadsPerBlock */
  int modFlag = 0;
  for (int i=0; i<argc-1; i++) {
    if ((!strcmp(argv[i], "--numBlocks")) || (!strcmp(argv[i], "-numBlocks"))) {
      int numBlocksNew = atoi(argv[i+1]);
      if(numBlocksNew != numBlocks) {
        ++i;
        modFlag = 1;
        numBlocks = numBlocksNew;
        fprintf(stderr, "Command line override: Forcing numBlocks = %d.\n", numBlocks);
        continue;
      }
    }
    if ((!strcmp(argv[i], "--threadsPerBlock")) || (!strcmp(argv[i], "-threadsPerBlock"))) {
      int threadsPerBlockNew = atoi(argv[i+1]);
      if(threadsPerBlockNew != threadsPerBlock) {
        ++i;
        modFlag = 1;
        threadsPerBlock = threadsPerBlockNew;
        fprintf(stderr, "Command line override: Forcing threadsPerBlock = %d.\n", threadsPerBlock);
      }
    }
  }

  /* If parameters were modified, recompute polyBufferSize and notify the user */
  if(modFlag) {
    polyBufferSize = numBlocks * threadsPerBlock;
    fprintf(stderr, "\nFinal sizing:\n");
    fprintf(stderr, "  numBlocks = %d.\n", numBlocks);
    fprintf(stderr, "  threadsPerBlock = %d.\n", threadsPerBlock);
    fprintf(stderr, "  polyBufferSize = %d.\n", polyBufferSize);
  }


}



int loadLookupTable(string* nameList, int* numBlocksList, int* threadsPerBlockList) {

  char fullFilename[512];
  boinc_resolve_filename(GPU_LOOKUP_TABLE_FILENAME, fullFilename, sizeof(fullFilename));

  ifstream lookupTableFile(fullFilename);
  int N=0;
  if(lookupTableFile)  {
    fprintf(stderr, "Loading GPU lookup table from file.\n");

    string rowStr;

    // Skip the first 2 rows which are just headers
    getline(lookupTableFile,rowStr);
    getline(lookupTableFile,rowStr);

    // Now load 1 row at a time and extract the fields.
    while(!lookupTableFile.eof()) { // Read lines until end of file is reached.
      getline(lookupTableFile,rowStr);

      int I1 = rowStr.find("|");       // Index of 1st "|"
      int I2 = rowStr.find("|",I1+1);  // Index of 2nd "|"

      // Only extract fields if both "|" characters are found.
      if(I1>0 && I2>0) {

        string field1 = rowStr.substr(0,I1);
        string field2 = rowStr.substr(I1+1,I2-I1-1);
        string field3 = rowStr.substr(I2+1,rowStr.length()-I2-1);

        // Remove leading spaces and tabs.
	int I3 = field1.find_first_not_of(" \t");
	field1 = field1.substr(I3);

        // Remove trailing spaces and tabs.
	I3 = field1.find_last_not_of(" \t");
	field1 = field1.substr(0,I3+1);

        // Remove all spaces from the name.
        int idx = 0;
        for(int k = 0; field1[k]; k++)  if(field1[k] != ' ') field1[idx++] = field1[k];
        field1 = field1.erase(idx);

        nameList[N] = field1;
        numBlocksList[N] = atoi(field2.c_str());
        threadsPerBlockList[N] = atoi(field3.c_str());
        ++N;

        }

      }  // End of while loop


    // Useful for debugging:
    if(0) {
      fprintf(stderr, "Number of entries = %d\n", N);
      for(int k=0;k<N;++k) {
        fprintf(stderr, "k = %d\n", k);
        fprintf(stderr, "gpuName[k] = %s\n", nameList[k].c_str());
        fprintf(stderr, "numBlocks[k] = %d\n", numBlocksList[k]);
        fprintf(stderr, "threadsPerBlock[k] = %d\n", threadsPerBlockList[k]);
        }
    }

    lookupTableFile.close();
    return N;
    }
  else {
    fprintf(stderr, "Failed to load lookup table.\n");
    return 0;
  }

}

