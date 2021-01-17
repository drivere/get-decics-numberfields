#!/bin/csh -f

# Use this for renaming a bunch of WU files.

foreach file (wu_*.out)
  set NewFile = `expr $file : '\(.*\).out'`.out.truth.cudaBaseline
  echo "moving "$file"  to  "$NewFile
  mv $file $NewFile
end
