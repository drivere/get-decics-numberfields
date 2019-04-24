@echo off
::Script file for testing the apps.
::Runs every work unit in current directory.


::This is necessary for SET to work inside the for loop
SETLOCAL ENABLEDELAYEDEXPANSION


::This supposedly forces overwriting with the COPY command
SET COPYCMD=/Y


SET in_file=in


::First test the GetBoundedDecics app
FOR /F %%G IN ('DIR /b wu_12E10*.dat') DO (
  SET wu_file=%%G
  ECHO Doing wu file:  !wu_file!

  SET out_file=!wu_file:~0,-3!out
  ECHO Output File: !out_file!

  SET stderr_file=!wu_file:~0,-3!stderr
  ECHO Stderr File: !stderr_file!

  COPY !wu_file! %in_file% >NUL

  GetBoundedDecics.exe

  MOVE out !out_file! >NUL
  MOVE stderr.txt !stderr_file! >NUL
  DEL boinc_finish_called GetBoundedDecics_state

  ECHO(
)





::Next, test the GetDecics app
FOR /F %%G IN ('DIR /b DS*.dat') DO (
  SET wu_file=%%G
  ECHO Doing wu file:  !wu_file!

  SET out_file=!wu_file:~0,-3!out
  ECHO Output File: !out_file!

  SET stderr_file=!wu_file:~0,-3!stderr
  ECHO Stderr File: !stderr_file!

  COPY !wu_file! %in_file% >NUL

  GetDecics.exe

  MOVE out !out_file! >NUL
  MOVE stderr.txt !stderr_file! >NUL
  DEL boinc_finish_called GetDecics_state

  ECHO(
)





::Finally, compare all results to the truth files
FOR /F %%G IN ('DIR /b *.out.truth') DO (
  SET truth_file=%%G
  SET result_file=!truth_file:~0,-6!

  FC !result_file! !truth_file!

  ECHO(
)

