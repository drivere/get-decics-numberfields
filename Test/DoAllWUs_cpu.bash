#!/bin/bash

# Script file for finding and processing all work units in current directory.
# This assumes executable is named GetDecics_cpu

in_file="in"

for wu_file in *DS*_Grp*.dat; do
  echo "Trying wu file: "$wu_file
  out_file=wu_"${wu_file/.dat/}".out
  ln -fs $wu_file $in_file
  ./GetDecics_cpu
  if [ -e "boinc_finish_called" ]
  then
    mv out $out_file
    rm boinc_finish_called
  else
    rm out boinc_lockfile
  fi
  rm stderr.txt
  if [ -e "GetDecics_state" ]
  then
    rm GetDecics_state
  fi
done

exit 0
