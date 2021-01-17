#!/bin/bash

# Script file for diffing all results in current directory with truth

for wu_file in *DS*_Grp*.dat; do
  echo -e "\n\n\nwu file: "$wu_file
  out_file=wu_"${wu_file/.dat/}".out
  truth_file="$out_file".truth.cudaBaseline
  diff --color $out_file $truth_file
  t1=`grep Elapsed $out_file | cut -d" " -f7`
  t2=`grep Elapsed $truth_file | cut -d" " -f7`
  p=$(echo "scale=1; 100 - 100 * $t1 / $t2" | bc)
  echo "$p% Improvement"
done
echo -e "\n\n"
