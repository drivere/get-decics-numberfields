// This is the main wrapper for the Martinet search routine.

#ifdef _WIN32
#include "boinc_win.h"
#else
#include "config.h"
#endif

#ifndef _WIN32
#include <cstdio>
#include <cctype>
#include <ctime>
#include <cstring>
#include <cstdlib>
#include <csignal>
#include <unistd.h>
#endif

#ifdef _WIN32
#include "pari.h"
#include "GetBoundedDecics.h"
#endif

#include "SearchRoutines.h"
#include "diagnostics.h"
#include "str_util.h"
#include "util.h"
#include "filesys.h"
#include "boinc_api.h"
#include "mfile.h"


using std::string;

#define CHECKPOINT_FILE "GetBoundedDecics_state"
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
  THREAD pari_sp bot, top, avma;
  THREAD size_t memused;
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
  int a5_Idx = 0;
  long a22_Start = -1000000000;
  long a21_Start = -1000000000;
  long a32_Start = -1000000000;
  long a31_Start = -1000000000;
  long long SV[5] = {0,0,0,0,0};
  char input_path[512], output_path[512], chkpt_path[512];
  FILE* ChkpntFile;


#ifdef _WIN32
   // XXXXX Uncomment the line below when debugging.
   // Otherwise the program may crash before you can attach to it.
//  for(;;) { }
#endif


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
    fscanf(ChkpntFile, "%d %ld %ld %ld %ld %I64d %I64d %I64d %I64d %I64d", 
           &a5_Idx, &a22_Start, &a21_Start, &a32_Start, &a31_Start, &SV[0], &SV[1], &SV[2], &SV[3], &SV[4]);
#else
    fscanf(ChkpntFile, "%d %ld %ld %ld %ld %lld %lld %lld %lld %lld", 
           &a5_Idx, &a22_Start, &a21_Start, &a32_Start, &a31_Start, &SV[0], &SV[1], &SV[2], &SV[3], &SV[4]);
#endif

    fclose(ChkpntFile);
    ChkPntFlag = 1;
    }

  fprintf(stderr, "Checkpoint Flag = %d.\n",ChkPntFlag);
  fprintf(stderr, " a5 Starting Index =  %d.\n",a5_Idx);
  fprintf(stderr, "a22 Starting Value = %ld.\n",a22_Start);
  fprintf(stderr, "a21 Starting Value = %ld.\n",a21_Start);
  fprintf(stderr, "a32 Starting Value = %ld.\n",a32_Start);
  fprintf(stderr, "a31 Starting Value = %ld.\n",a31_Start);

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


  //fprintf(stderr,"Size of void   = %d.\n",sizeof(void));
  //fprintf(stderr,"Size of Long   = %d.\n",sizeof(long));
  //fprintf(stderr,"Size of uchar  = %d.\n",sizeof(unsigned char));
  //fprintf(stderr,"Size of char   = %d.\n",sizeof(char));
  //fprintf(stderr,"Size of size_t = %d.\n",sizeof(size_t));
  //fprintf(stderr,"Size of Long*  = %d.\n",sizeof(long*));
  //fprintf(stderr,"Size of Long** = %d.\n",sizeof(long**));
  //fprintf(stderr,"Size of Long***= %d.\n",sizeof(long***));
  //fprintf(stderr,"Size of GEN    = %d.\n",sizeof(GEN));
  //fprintf(stderr,"Size of LongLong = %d.\n",sizeof(long long));


    // Start the search
  MartinetSearch(input_path, output_path, ChkPntFlag, a5_Idx, a22_Start, a21_Start, a32_Start, a31_Start, SV);

  boinc_finish(0);
  }





int do_checkpoint(int a5_Idx, long a22_Start, long a21_Start, long a32_Start, long a31_Start, long long Stat1, 
                  long long Stat2, long long Stat3, long long Stat4, long long Time)
  {
  int retval;
  string resolved_name;

  //fprintf(stderr, "APP: Starting GetBoundedDecics checkpoint.\n");

  FILE* f = fopen("temp", "w");
  if(!f) return 1;

#ifdef _WIN32
  fprintf(f, "%d\n%ld\n%ld\n%ld\n%ld\n%I64d\n%I64d\n%I64d\n%I64d\n%I64d", a5_Idx, a22_Start, a21_Start, 
          a32_Start, a31_Start, Stat1, Stat2, Stat3, Stat4, Time);
#else
  fprintf(f, "%d\n%ld\n%ld\n%ld\n%ld\n%lld\n%lld\n%lld\n%lld\n%lld", a5_Idx, a22_Start, a21_Start, 
          a32_Start, a31_Start, Stat1, Stat2, Stat3, Stat4, Time);
#endif

  fclose(f);

  boinc_resolve_filename_s(CHECKPOINT_FILE, resolved_name);
  retval = boinc_rename("temp", resolved_name.c_str());
  if(retval) return retval;

  //fprintf(stderr, "GetBoundedDecics checkpointed.\n");
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
