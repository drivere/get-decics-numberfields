#!/bin/sh

if [ $# != 1 ]; then
  echo 'You must enter a filename.'
  echo 'This script will replace all occurances of "long" with "pari_long".'
  exit 0
fi


fileIn=$1
fileOut=$fileIn.New
echo "Converting long to pari_long in $fileIn."


# The trick is to do the replace without affecting other words that contain the text "long", such as ulong.
# This can be done with 5 separate replaces:
# 1.) " long"
# 2.) "(long"
# 3.) "{long"
# 4.) ",long"
# 5.) long is the first word on the line
# Note that long* will get replaced with pari_long*, but this is what we want.


# First replace "unsigned long" with ulong.
sed -e 's/unsigned long int /ulong /g' -e 's/unsigned long/ulong/g' < $fileIn > TMP

sed -e 's/\([ ({,]\)long/\1pari_long/g' -e 's/^long/pari_long/' < TMP > $fileOut


# The above changes longjmp to pari_longjmp.  So change it back. Overwrite the original file with the result.
sed 's/pari_longjmp/longjmp/g' < $fileOut > $fileIn


# clean up
rm TMP $fileOut
