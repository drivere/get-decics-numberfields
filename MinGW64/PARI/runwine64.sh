#/bin/sh
case $1 in
/*) PROG="$1";;
*) PROG="./$1";;
esac
shift
WINEDEBUG=-all wine64 $PROG "$@" 2>&1 | grep -v -F 'Application tried to create a window, but no driver could be loaded.
Make sure that your X server is running and that $DISPLAY is set correctly.' | sed -e 's/[\r]//'
