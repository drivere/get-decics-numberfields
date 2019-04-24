/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"
#include "paripriv.h"
#include "gp.h"

typedef struct whatnow_t
{
  const char *name, *oldarg, *newarg;
} whatnow_t;

#define SAME NULL
#define REMOV (char *)1L
#define _REMOV {REMOV,NULL,NULL}
#define _SAME  {SAME,NULL,NULL}

#include "whatnow.h"

static void
msg(PariOUT *out, const char *s)
{
  out_term_color(out, c_HELP);
  out_print_text(out, s);
  out_putc(out, '\n');
  out_term_color(out, c_NONE);
}
/* If flag = 0 (default): check if s existed in 1.39.15 and print verbosely
 * the answer.
 * Else: return 1 if function changed, 0 otherwise, and print help message
 * plus the above. */
int
whatnow(PariOUT *out, const char *s, int flag)
{
  int n;
  const char *def;
  whatnow_t wp;
  entree *ep;

  if (flag && s[0] && !s[1]) return 0; /* special case "i" and "o" */
  n = 0;
  do
    def = (oldfonctions[n++]).name;
  while (def && strcmp(def,s));
  if (!def)
  {
    int m = 0;
    do
      def = (functions_oldgp[m++]).name;
    while (def && strcmp(def,s));
    n += m - 1;
  }
  /* Above linear search is slow, esp. if the symbol is not found. BUT no
   * point in wasting time by preallocating [ or autoloading ] a hashtable:
   * whatnow() is never used in a case where speed would be necessary */
  if (!def)
  {
    if (!flag)
      msg(out, "As far as I can recall, this function never existed");
    return 0;
  }

  wp = whatnowlist[n-1]; def = wp.name;
  if (def == SAME)
  {
    if (!flag)
      msg(out, "This function did not change");
    return 0;
  }
  if (flag)
  {
    out_term_color(out, c_NONE);
    out_print_text(out, "\nA function with that name existed in GP-1.39.15; to run in backward compatibility mode, type \"default(compatible,3)\", or set \"compatible = 3\" in your GPRC file.");
    out_putc(out, '\n');
  }

  if (def == REMOV)
  {
    msg(out, "This function was suppressed");
    return 0;
  }
  if (!strcmp(def,"x*y")) ep = NULL;
  else {
    ep = is_entry(wp.name);
    if (!ep) pari_err_BUG("whatnow");
  }
  out_puts(out, "New syntax: ");
  out_term_color(out, c_ERR);
  out_printf(out, "%s%s ===> %s%s\n\n", s, wp.oldarg, wp.name, wp.newarg);
  if (ep) msg(out, ep->help);
  out_term_color(out, c_NONE); return 1;
}
