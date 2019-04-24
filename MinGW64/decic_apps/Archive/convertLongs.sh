#!/bin/csh -f


if ($#argv != 1) then
  echo 'You must enter a filename.'
  echo 'This script will replace all occurances of "long" with "pari_long", but will leave "long*" unchanged.'
  exit 0
endif


set fileIn=$1
set fileOut=$fileIn.New
#echo "Converting $fileIn.  Writing result to $fileOut."
echo "Converting $fileIn."


# This modifies all occurances of " long", "(long", and ",long":
sed -e 's/ long/ pari_long/g' -e 's/(long/(pari_long/g' -e 's/,long/, pari_long/g' -e 's/^long/pari_long/' < $fileIn > $fileOut

mv $fileOut $fileIn


# Put all pointers back to their original
# But we don't actually want to do this.  It is better to leave it as pari_long*, 
# otherwise it requires a bunch of code changes to type cast back to long*
#sed -e 's/pari_long\*/long\*/g' -e 's/pari_long \*/long \*/g'  < TMP2 > $fileOut




# Old versions:

# Replace all occurances of " long" with " pari_long"
#sed 's/ long/ pari_long/g' < $fileIn > TMP

# Replace all occurances of "(long" with "(pari_long"
#sed 's/(long/(pari_long/g' < TMP > TMP2

# Replace all occurances of ",long" with ", pari_long"
#sed 's/,long/, pari_long/g' < TMP2 > $fileOut

# This replaces all lines that start with "long"
#sed 's/^long/pari_long/' < TMP > $fileOut


