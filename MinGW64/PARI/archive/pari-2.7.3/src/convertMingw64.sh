#!/bin/sh

# This script is intended to be run from the src directory.  It will make the following 
# changes to all source code in preperation for making on mingw64:
#   1.) Convert 32 bit constants to 64 bit constants (i.e. L->LL and UL->ULL),
#   2.) Convert labs to llabs, and
#   3.) Convert formatting in printf/sprintf/fprintf (i.e. %ld->%lld, %lu->%llu, etc).
# For gp to work right, the microsoft formatting convention had to be used. So in 
# step 3 above, %ld->%I64d and %lu->%I64u.


fileList=`find . -name "*.[ch]"`

for file in $fileList; do

  if [ "$file" != "./headers/parigen.h" ]; then

    echo converting file: $file

    # Add LL to the end of any constant with 10 or more numbers
    sed 's/\([-+({ ][0-9]\{10,\}\)\([,;:)} ]\)/\1LL\2/g' < $file > TMP

    # Convert all decimal constants ending in L or UL.
    # Note: replacing strings with lower case l breaks a couple things, namely strings like "%+1ld"
    sed -e 's/\([-+* ,()=~&|%][0-9][0-9]*\)[L]\{1,2\}/\1LL/g' -e 's/\([-+* ,()=~&|%][0-9][0-9]*\)[uU][lL]\{1,2\}/\1ULL/g' < TMP > TMP2

    # Convert all hexadecimal constants ending in L or UL.
    sed -e 's/\(0x[0-9a-fA-F][0-9a-fA-F]*\)[lL]\{1,2\}/\1LL/g' -e 's/\(0x[0-9a-fA-F][0-9a-fA-F]*\)[uU][lL]\{1,2\}/\1ULL/g' < TMP2 > TMP

    # Convert "labs(" to "llabs(", but be careful not to change "polabs("
    sed 's/\([-+* ,()=~&|%]\)labs(/\1llabs(/g' < TMP > TMP2

    # String formatting conversions: %ld -> %lld, %lu -> %llu, %lx -> %llx.  This will also handle cases like %+2ld and %0*lx
    #sed -e 's/\(%[-+]\{0,1\}[0-9]*\)ld/\1lld/g' -e 's/\(%[-+]\{0,1\}[0-9]*\)lu/\1llu/g' -e 's/\(%[-+]\{0,1\}[0-9]*\)lx/\1llx/g' -e 's/\(%[0-9]\*\)lx/\1llx/g' < TMP2 > $file
    # This version uses the microsoft formatting convention: %I64d for %lld, %I64u for %llu, etc.
    #sed -e 's/\(%[-+]\{0,1\}[0-9]*\)ld/\1I64d/g' -e 's/\(%[-+]\{0,1\}[0-9]*\)lu/\1I64u/g' -e 's/\(%[-+]\{0,1\}[0-9]*\)lx/\1I64x/g' -e 's/\(%[0-9]\*\)lx/\1I64x/g' < TMP2 > $file

    # Replace formatting with microsoft I64 convention, but only inside regular printfs (and it's variants)
    # Do nothing inside of pari_printf() or pari_sprintf().
    sed -e '/[ )][sf]*printf(/ s/\(%[-+]\{0,1\}[0-9]*\)ld/\1I64d/g' -e '/[ )][sf]*printf(/ s/\(%[-+]\{0,1\}[0-9]*\)lu/\1I64u/g' -e '/[ )][sf]*printf(/ s/\(%[-+]\{0,1\}[0-9]*\)lx/\1I64x/g' -e '/[ )][sf]*printf(/ s/\(%[0-9]\*\)lx/\1I64x/g' < TMP2 > $file

    # clean up
    rm TMP TMP2

    # The above substitution misses one line, which we now fix.
    if [ "$file" == "./language/init.c" ]; then
      sed '/ current stack size/ s/%lu/%I64u/g' < $file > TMP
      mv TMP $file
    fi

  fi

done


echo "Done."
