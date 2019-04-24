/*  This file was created by Configure. Any change made to it will be lost
 *  next time Configure is run. */
#ifndef __PARICFG_H__
#define __PARICFG_H__
#define UNIX
#define GPHELP "perl -S gphelp -detex"
#define GPDATADIR "C:\\Program Files\\PARI"
#define SHELL_Q '\"'

#define PARIVERSION "GP/PARI CALCULATOR Version 2.8.0 (development git-e5c317c)"
#define PARIINFO "amd64 running mingw (x86-64/GMP-6.0.0 kernel) 64-bit version"
#define PARI_VERSION_CODE 133120
#define PARI_VERSION(a,b,c) (((a) << 16) + ((b) << 8) + (c))
#define PARI_VERSION_SHIFT 8
#define PARI_VCSVERSION ""
#define PARI_MT_ENGINE "single"

#define PARI_DOUBLE_FORMAT -
#define GCC_VERSION "gcc version 5.1.0 20150422 (Fedora MinGW 5.1.0-2.fc22) (GCC)"
#define ASMINLINE

/*  Location of GNU gzip program (enables reading of .Z and .gz files). */
#define GNUZCAT
#define ZCAT "/bin/gzip -dc"


#undef UNIX
#define GNUZCAT
#undef ZCAT
#define ZCAT "gzip.exe -dc"

#define LONG_IS_64BIT
#define HAS_EXP2
#define HAS_LOG2
#define HAS_ISATTY
#define HAS_SYSTEM
#define USE_GETTIMEOFDAY 1
#define HAS_GETENV
#define HAS_VSNPRINTF
#define HAS_STRFTIME
#define HAS_STAT
#endif
