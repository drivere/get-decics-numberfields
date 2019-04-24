#!/bin/bash

# Script file for testing the apps.
# Runs every work unit in current directory.


in_file="in"


# Copy the latest executables to the current directory
echo "Copying executables..."
cp ../decic_apps/Omingw-i686/GetDecics.exe GetDecics
echo
echo



# First test the GetBoundedDecics app
#for wu_file in wu_12E10*.dat; do
#  echo "Doing wu file: "$wu_file
#  out_file="${wu_file/.dat/}".out
#  stderr_file="${wu_file/.dat/}".stderr
#  ln -fs $wu_file $in_file
#  ./runwine32.sh ./GetBoundedDecics
#  mv out $out_file
#  mv stderr.txt $stderr_file
#  rm boinc_finish_called GetBoundedDecics_state
#done


# Then test the GetDecics app
for wu_file in DS*.dat; do
  echo "Doing wu file: "$wu_file
  out_file="${wu_file/.dat/}".out
  stderr_file="${wu_file/.dat/}".stderr
  ln -fs $wu_file $in_file
  ./runwine32.sh ./GetDecics
  mv out $out_file
  mv stderr.txt $stderr_file
  rm boinc_finish_called GetDecics_state
done

echo
echo

# Now diff the results with the truth
for truth_file in *.out.truth; do
  result_file="${truth_file/.truth/}"
  echo "Comparing result file: "$result_file
  diff -sw $truth_file $result_file
  echo
  echo
  echo
done


# Now diff the stderrs with the truth
for truth_file in *.stderr.truth; do
  stderr_file="${truth_file/.truth/}"
  echo "Comparing stderr file: "$stderr_file
  diff -sw $truth_file $stderr_file
  echo
  echo
  echo
done


exit 0
