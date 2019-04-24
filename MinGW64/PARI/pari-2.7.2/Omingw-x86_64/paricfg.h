/*  This file was created by Configure. Any change made to it will be lost
 *  next time Configure is run. */
#ifndef __CONFIG_H__
#define __CONFIG_H__
#define UNIX
#define GPHELP "perl -S gphelp -detex"
#define GPDATADIR "C:\\Program Files\\PARI"
#define SHELL_Q '\"'

#define PARIVERSION "GP/PARI CALCULATOR Version 2.7.2 (released)"
#define PARIINFO "amd64 running mingw (x86-64 kernel) 64-bit version"
#define PARI_VERSION_CODE 132866
#define PARI_VERSION(a,b,c) (((a) << 16) + ((b) << 8) + (c))
#define PARI_VERSION_SHIFT 8
#define PARI_VCSVERSION ""
#define PARI_MT_ENGINE "single"

#define PARI_DOUBLE_FORMAT 1
#define GCC_VERSION "gcc version 4.8.3 20140522 (Fedora MinGW 4.8.3-1.fc19) (GCC) "
#define ASMINLINE

/*  Location of GNU gzip program (enables reading of .Z and .gz files). */
#define GNUZCAT
#define ZCAT "/usr/bin/gzip -dc"


#undef UNIX
#define GNUZCAT
#undef ZCAT
#define ZCAT "gzip.exe -dc"

#define READLINE "6.2"
#define LONG_IS_64BIT
#define HAS_EXP2
#define HAS_LOG2
#define HAS_ISATTY
#define HAS_GETENV
#define HAS_VSNPRINTF
#define HAS_STRFTIME
#define HAS_STAT
#endif
