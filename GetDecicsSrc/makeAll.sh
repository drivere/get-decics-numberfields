#!/bin/bash


# Make the 64 bit linux cpu app
make -f Makefile.cpu_linux64 clean
make -f Makefile.cpu_linux64


# Make the 32 bit linux cpu app
make -f Makefile.cpu_linux32 clean
make -f Makefile.cpu_linux32


# Make the gpu apps for 64 bit linux host
make -f Makefile.openCL_Nvidia clean;  make -f Makefile.openCL_Nvidia
make -f Makefile.openCL_Intel  clean;  make -f Makefile.openCL_Intel
make -f Makefile.openCL_AMD    clean;  make -f Makefile.openCL_AMD
make -f Makefile.cuda          clean;  make -f Makefile.cuda


# Make the 64 bit windows apps (including gpu)
rm -rf Omingw-x86_64/
./makeMingw64.sh


# Make the 32 bit windows apps (including gpu)
rm -rf Omingw-i686/
./makeMingw32.sh
