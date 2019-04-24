#!/bin/bash

MINGW_DIR=/home/eric/BOINC_Project/MinGW/decic_apps
FINAL_DIR=Omingw-i686/


# Just in case the directory is not there
mkdir -p $FINAL_DIR


# Copy the source code to the mingw64 directory
echo
echo "Copying source code..."
cp *.cpp *.h *.cl $MINGW_DIR



# Build it
echo
echo "Building on mingw32..."
pushd $MINGW_DIR
make -f Makefile.mingw32
# Do we really want openCL apps for old 32bit cpus?
make -f Makefile.mingw32-OpenCL_Nvidia
make -f Makefile.mingw32-OpenCL_Intel
make -f Makefile.mingw32-OpenCL_AMD



# Test the executables
echo
echo "Testing the programs..."
cd ../Test
./Test_Mingw32.bash



# Copy over the new executables
echo
echo "Copying the executables..."
popd
cp $MINGW_DIR/Omingw-i686/GetDecics.exe  $FINAL_DIR/GetDecics-i686.exe
cp $MINGW_DIR/Omingw-i686-OpenCL_Nvidia/GetDecics.exe  $FINAL_DIR/GetDecics-i686-OpenCL_Nvidia.exe
cp $MINGW_DIR/Omingw-i686-OpenCL_Intel/GetDecics.exe   $FINAL_DIR/GetDecics-i686-OpenCL_Intel.exe
cp $MINGW_DIR/Omingw-i686-OpenCL_AMD/GetDecics.exe     $FINAL_DIR/GetDecics-i686-OpenCL_AMD.exe



# Output a final reminder message
echo
echo "Reminder - verify output of the test diffs"

