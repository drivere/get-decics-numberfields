#!/bin/bash

# This is a shell script for making all the mingw64 executables

MINGW_DIR=/home/eric/BOINC_Project/MinGW64/decic_apps
FINAL_DIR=Omingw-x86_64/


# Just in case the directory is not there
mkdir -p $FINAL_DIR


# Copy the source code to the mingw64 directory
echo
echo "Copying source code..."
cp *.cpp *.h *.cl $MINGW_DIR



# Build it
echo
echo "Building on mingw64..."
pushd $MINGW_DIR
make -f Makefile.mingw64
make -f Makefile.mingw64-OpenCL_Nvidia
make -f Makefile.mingw64-OpenCL_Intel
make -f Makefile.mingw64-OpenCL_AMD



# Test the cpu executable (not sure if its possible to test the openCL versions)
echo
echo "Testing the cpu program..."
cd ../Test
./Test_Mingw64.bash



# Copy over the new executables
echo
echo "Copying the executables..."
popd
cp $MINGW_DIR/Omingw-x86_64/GetDecics.exe  $FINAL_DIR/GetDecics-x86_64.exe
cp $MINGW_DIR/Omingw-x86_64-OpenCL_Nvidia/GetDecics.exe  $FINAL_DIR/GetDecics-x86_64-OpenCL_Nvidia.exe
cp $MINGW_DIR/Omingw-x86_64-OpenCL_Intel/GetDecics.exe   $FINAL_DIR/GetDecics-x86_64-OpenCL_Intel.exe
cp $MINGW_DIR/Omingw-x86_64-OpenCL_AMD/GetDecics.exe     $FINAL_DIR/GetDecics-x86_64-OpenCL_AMD.exe



# Output a final reminder message
echo
echo "Reminder - verify output of the test diffs"

