// This is the main wrapper for the Targeted Martinet search routine.

#ifdef MINGW64
  typedef unsigned long long pari_ulong;  // We want pari longs to be 8 bytes
  typedef long long pari_long;
# define LONG_IS_64BIT
#else
  typedef unsigned long pari_ulong;
  typedef long pari_long;
#endif

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

#ifdef _WIN32
#  include "pari.h"
#  ifdef long
#    undef long
#  endif
#endif

#include "diagnostics.h"
#include "str_util.h"
#include "util.h"
#include "filesys.h"
#include "boinc_api.h"
#include "mfile.h"

#include "GetDecics.h"
#include "TgtMartinet.h"


//using namespace std;
using std::string;

#define CHECKPOINT_FILE "GetDecics_state"
#define INPUT_FILENAME "in"
#define OUTPUT_FILENAME "out"

#ifndef MINGW
#ifdef _WIN32
  // Define pari global variables.
  // Apparantly globals can't be exported to a library, even 
  // though it works on Linux???
  GEN gen_0, gen_1, gen_2, gen_m1, gen_m2, ghalf, gnil, err_e_STACK;
  GEN gpi, geuler;
  ulong hiremainder, overflow;
  THREAD GEN    bernzone;
  GEN     primetab; /* private primetable */
  byteptr diffptr;
  FILE    *pari_outfile, *pari_errfile, *pari_logfile, *pari_infile;
  char    *current_psfile, *pari_datadir;
  ulong   DEBUGFILES, DEBUGLEVEL, DEBUGMEM;
  ulong   precdl, logstyle;
  THREAD  pari_sp bot, top, avma;
  THREAD  size_t memused;
  BEGINEXTERN
    char    *current_logfile;
    ulong   compatible, precreal;
    entree  **varentries;
  ENDEXTERN
#endif
#endif


int main(int argc, char **argv)
  {
  int retval;
  int ChkPntFlag = 0;
  pari_long CvecIdx=0;
  pari_long N1_Start = 0;
  pari_long N2_Start = 0;
  pari_long SV[5] = {0,0,0,0,0};
  char input_path[512], output_path[512], chkpt_path[512];
  FILE* ChkpntFile;

  //fprintf(stderr, "APP:  Initializing diagnostics.\n");
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


    // Read the checkpoint file.
  boinc_resolve_filename(CHECKPOINT_FILE, chkpt_path, sizeof(chkpt_path));
  ChkpntFile = boinc_fopen(chkpt_path, "r");
  if(ChkpntFile)
    {
    fprintf(stderr, "Reading checkpoint file.\n");

#ifdef _WIN32
    fscanf(ChkpntFile, "%ld %ld %ld %I64d %I64d %I64d %I64d %I64d", &CvecIdx, &N2_Start, &N1_Start, 
           &SV[0], &SV[1], &SV[2], &SV[3], &SV[4]);
#else
    fscanf(ChkpntFile, "%ld %ld %ld %lld %lld %lld %lld %lld", &CvecIdx, &N2_Start, &N1_Start, 
           &SV[0], &SV[1], &SV[2], &SV[3], &SV[4]);
#endif

    fclose(ChkpntFile);
    ChkPntFlag = 1;
    }

  fprintf(stderr, "Checkpoint Flag = %d.\n",ChkPntFlag);
  fprintf(stderr, "Cvec Starting Index = %ld.\n",CvecIdx);
  fprintf(stderr, "N1 Start = %ld.\n",N1_Start);
  fprintf(stderr, "N2 Start = %ld.\n",N2_Start);

#ifdef _WIN32
  fprintf(stderr, "PolyCount starting value = %I64d.\n",SV[0]);
  fprintf(stderr, "Stat Count 1 = %I64d.\n",SV[1]);
  fprintf(stderr, "Stat Count 2 = %I64d.\n",SV[2]);
  fprintf(stderr, "Stat Count 3 = %I64d.\n",SV[3]);
  fprintf(stderr, "Elapsed Time = %I64d (sec).\n",SV[4]);
#else
  fprintf(stderr, "PolyCount starting value = %lld.\n",SV[0]);
  fprintf(stderr, "Stat Count 1 = %lld.\n",SV[1]);
  fprintf(stderr, "Stat Count 2 = %lld.\n",SV[2]);
  fprintf(stderr, "Stat Count 3 = %lld.\n",SV[3]);
  fprintf(stderr, "Elapsed Time = %lld (sec).\n",SV[4]);
#endif

    // Start the search
  TgtMartinet(input_path, output_path, ChkPntFlag, CvecIdx, N1_Start, N2_Start, SV);

  boinc_finish(0);
  }





int do_checkpoint(pari_long CvecIdx, pari_long N2, pari_long N1, pari_long Stat1, pari_long Stat2, 
                  pari_long Stat3, pari_long Stat4, pari_long Time)
  {
  int retval;
  string resolved_name;

  //fprintf(stderr, "Starting GetDecics checkpoint.\n");

  FILE* f = fopen("temp", "w");
  if(!f) return 1;

#ifdef _WIN32
  fprintf(f, "%ld\n%ld\n%ld\n%I64d\n%I64d\n%I64d\n%I64d\n%I64d", CvecIdx, N2, N1, 
          Stat1, Stat2, Stat3, Stat4, Time);
#else
  fprintf(f, "%ld\n%ld\n%ld\n%lld\n%lld\n%lld\n%lld\n%lld", CvecIdx, N2, N1, 
          Stat1, Stat2, Stat3, Stat4, Time);
#endif

  fclose(f);

  boinc_resolve_filename_s(CHECKPOINT_FILE, resolved_name);
  retval = boinc_rename("temp", resolved_name.c_str());
  if(retval) return retval;

  //fprintf(stderr, "GetDecics checkpointed.\n");
  return 0;
  }





#ifdef _WIN32
int WINAPI WinMain(HINSTANCE hInst, HINSTANCE hPrevInst, LPSTR Args, int WinMode) {
    LPSTR command_line;
    char* argv[100];
    int argc;

    //command_line = GetCommandLine();  // XXXXX EDD changed this to allow unicode
    command_line = (LPSTR)GetCommandLine();
    argc = parse_command_line( command_line, argv );
    return main(argc, argv);
}
#endif
