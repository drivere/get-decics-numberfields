#!/bin/sh


for file in basemath/*.[ch]; do
  ./convertLongs.sh $file
done

for file in gp/*.[ch]; do
  ./convertLongs.sh $file
done

for file in graph/*.[ch]; do
  ./convertLongs.sh $file
done

# Skip the parigen.h file, as this will break the pari_long typedef
for file in headers/*.[ch]; do
  if [ "$file" != "headers/parigen.h" ]; then
    ./convertLongs.sh $file
  fi
done

for file in kernel/*/*.[ch]; do
  ./convertLongs.sh $file
done

for file in language/*.[ch]; do
  ./convertLongs.sh $file
done

for file in modules/*.[ch]; do
  ./convertLongs.sh $file
done

for file in mt/*.[ch]; do
  ./convertLongs.sh $file
done

# This will break mingw.  Not sure about the other systems.
#for file in systems/*/*.[ch]; do
#  ./convertLongs.sh $file
#done

for file in test/*.[ch]; do
  ./convertLongs.sh $file
done



echo "Done."

