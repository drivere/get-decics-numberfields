#!/bin/bash

# Script file for diffing all results in current directory with truth

for wu_file in *DS*_Grp*.dat; do
  echo "Checking wu file: "$wu_file
  out_file=wu_"${wu_file/.dat/}".out
  truth_file="$out_file".truth
  diff $out_file $truth_file
done
