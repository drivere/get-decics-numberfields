#!/bin/csh -f

foreach file (basemath/*.[ch])
  ./convertLongs.csh $file
end

foreach file (gp/*.[ch])
  ./convertLongs.csh $file
end

foreach file (graph/*.[ch])
  ./convertLongs.csh $file
end

# Skip the parigen.h file, as this will break the pari_long typedef
foreach file (headers/*.[ch])
  if ($file != "headers/parigen.h") then
    ./convertLongs.csh $file
  endif
end

foreach file (kernel/*/*.[ch])
  ./convertLongs.csh $file
end

foreach file (language/*.[ch])
  ./convertLongs.csh $file
end

foreach file (modules/*.[ch])
  ./convertLongs.csh $file
end

foreach file (mt/*.[ch])
  ./convertLongs.csh $file
end

# This will break mingw.  Not sure about the other systems.
#foreach file (systems/*/*.[ch])
#  ./convertLongs.csh $file
#end

foreach file (test/*.[ch])
  ./convertLongs.csh $file
end



echo "Done."

