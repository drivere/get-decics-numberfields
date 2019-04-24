#!/bin/sh

# This script will revert the code back to it's original state before the convertMingw64.sh script was applied.
# In particular, it will:
#   1.) Convert 64 bit constants to 32 bit constants (i.e. LL->L and ULL->UL),
#   2.) Convert formatting in printf/sprintf/fprintf (i.e. %lld->%ld, %llu->%lu, etc).


fileList="`find src -name "*.[ch]"` config/endian.c"

for file in $fileList; do

    echo reverting file: $file

    # Convert all decimal constants ending in LL or ULL.
    sed -e 's/\([-+* ,({)=~&|%][0-9][0-9]*\)LL/\1L/g' -e 's/\([-+* ,({)=~&|%][0-9][0-9]*\)ULL/\1UL/g' < $file > TMP

    # Convert all hexadecimal constants ending in LL or ULL.
    sed -e 's/\(0x[0-9a-fA-F][0-9a-fA-F]*\)LL/\1L/g' -e 's/\(0x[0-9a-fA-F][0-9a-fA-F]*\)ULL/\1UL/g' < TMP > TMP2

    # Revert printf formatting (%lld->%ld, %llu->%lu, etc)
    sed -e '/\"/ s/\(%[-+]\{0,1\}[0-9]*\)lld/\1ld/g' -e '/\"/ s/\(%[-+]\{0,1\}[0-9]*\)llu/\1lu/g' -e '/\"/ s/\(%[-+]\{0,1\}[0-9]*\)llx/\1lx/g' -e '/\"/ s/\(%[0-9]\*\)llx/\1lx/g' < TMP2 > $file

    # clean up
    rm TMP TMP2

done

echo "Done."
