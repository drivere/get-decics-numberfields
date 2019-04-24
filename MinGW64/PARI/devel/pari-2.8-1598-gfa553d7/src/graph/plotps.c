/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*******************************************************************/
/*           HIGH RESOLUTION PLOT VIA POSTSCRIPT FILE              */
/*******************************************************************/

#include "pari.h"
#include "paripriv.h"
#include "rect.h"

void
rectdraw0(long *w, long *x, long *y, long lw)
{
  struct plot_eng plot;
  FILE *file;
  char *s, *cmd;
  const char *v;
  if (pari_daemon()) return;  /* parent process returns */
  s = pari_unique_filename("plotps");
  pari_unlink(s);
  s = stack_strcat(s, ".ps");
  file = fopen(s, "w");
  if (!file) pari_err_FILE("postscript file", s);
  psplot_init(&plot, file, 1.0, 1.0, 9);
  fprintf(file,"0 %ld translate -90 rotate\n", plot.pl->height - 50);
  gen_rectdraw0(&plot, w, x, y, lw, 1, 1);
  fprintf(file,"stroke showpage\n"); (void)fclose(file);
  v = os_getenv("GP_POSTSCRIPT_VIEWER");
  if (!v) v = "open -W";
  cmd = pari_sprintf("%s \"%s\" 2>/dev/null", v, s);
  gpsystem(cmd);
  pari_unlink(s); exit(0);
}

void
PARI_get_plot(void)
{
  if (pari_plot.init) return;
  pari_plot.width  = 400;
  pari_plot.height = 300;
  pari_plot.fheight = 9;
  pari_plot.fwidth  = 6;
  pari_plot.hunit   = 3;
  pari_plot.vunit   = 3;
  pari_plot.init = 1;
}
