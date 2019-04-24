cfg=$config_dir
obj=$objdir
file="$obj/pari.nsi"
if [ -f "$cfg/$osname-pari.nsi" ]; then
  echo "Extracting $file"
  "$cfg/$osname-pari.nsi" > "$file"
fi
