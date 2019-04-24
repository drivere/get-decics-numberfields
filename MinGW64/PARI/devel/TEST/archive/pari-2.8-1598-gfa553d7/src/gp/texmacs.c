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
/*                                                                 */
/*                    TEXMACS-SPECIFIC STUFF                       */
/*                                                                 */
/*******************************************************************/
#include "pari.h"

#include "paripriv.h"
#include "gp.h"

#define DATA_BEGIN  ((char) 2)
#define DATA_END    ((char) 5)
#define DATA_ESCAPE ((char) 27)

/*******************************************************************/
/*                                                                 */
/*                      READLINE INTERFACE                         */
/*                                                                 */
/*******************************************************************/
static int did_complete = 0;
char **pari_completion(char *text, int START, int END);

#ifdef READLINE
BEGINEXTERN
#include <readline/readline.h>
ENDEXTERN

static void
print_escape_string(char *s)
{
  long l = strlen(s);
  char *t, *t0 = (char*)pari_malloc(l * 3 + 3);

  t = t0; *t++ = '"';
  for ( ;*s; *t++ = *s++)
    switch(*s)
    {
      case DATA_BEGIN:
      case DATA_END:
      case DATA_ESCAPE: *t++ = DATA_ESCAPE; continue;

      case '\\':
      case '"': *t++ = '\\'; continue;
    }
  *t++ = '"';
  *t = '\0'; puts(t0); pari_free(t0);
}

static char *
completion_word(long end)
{
  char *s = rl_line_buffer + end, *found_quote = NULL;
  long i;
  /* truncate at cursor position */
  *s = 0;
  /* first look for unclosed string */
  for (i=0; i < end; i++)
  {
    switch(rl_line_buffer[i])
    {
      case '"':
        found_quote = found_quote? NULL: rl_line_buffer + i;
        break;

      case '\\': i++; break;
    }

  }
  if (found_quote) return found_quote + 1; /* return next char after quote */

  /* else find beginning of word */
  while (s >  rl_line_buffer)
  {
    s--;
    if (!is_keyword_char(*s)) { s++; break; }
  }
  return s;
}

/* completion required, cursor on s + pos. Complete wrt strict left prefix */
static void
tm_completion(const char *s, long pos)
{
  char **matches, *text;

  if (rl_line_buffer) pari_free(rl_line_buffer);
  rl_line_buffer = pari_strdup(s);
  text = completion_word(pos);
  /* text = start of expression we complete */
  rl_end = strlen(s)-1;
  rl_point = pos;
  matches = pari_completion(text, text - rl_line_buffer, pos);
  printf("%cscheme:(tuple",DATA_BEGIN);
  if (matches)
  {
    long i, prelen = (rl_line_buffer+pos) - text;
    char *t = (char*)pari_malloc(prelen+1);
    strncpy(t, text, prelen); t[prelen] = 0; /* prefix */
    printf(" ");
    print_escape_string(t); pari_free(t);
    for (i = matches[1]? 1: 0; matches[i]; i++)
    {
      printf(" ");
      print_escape_string(matches[i] + prelen);
      pari_free(matches[i]);
    }
    pari_free(matches);
  }
  printf(")%c", DATA_END);
  fflush(stdout);
}
#else
/* no-op */
static void
tm_completion(const char *s, long pos) { (void)s; (void)pos; }
#endif

typedef struct {
  char *cmd;
  long n; /* number of args */
  char **v; /* args */
} tm_cmd;

static void
tm_parse_command(tm_cmd *c, const char *ch)
{
  long l = strlen(ch);
  char *t, *s = (char*)ch, *send = s+l-1;
  char **A;
  pari_stack s_A;

  if (*s != DATA_BEGIN || *send-- != DATA_END)
    pari_err(e_MISC, "missing DATA_[BEGIN | END] in TeXmacs command");
  s++;
  if (strncmp(s, "special:", 8)) pari_err(e_MISC, "unrecognized TeXmacs command");
  s += 8;
  if (*s != '(' || *send-- != ')')
    pari_err(e_MISC, "missing enclosing parentheses for TeXmacs command");
  s++; t = s;
  pari_skip_alpha(&s);
  c->cmd = pari_strndup(t, s - t);
  pari_stack_init(&s_A,sizeof(*A),(void**)&A);
  for (c->n = 0; s <= send; c->n++)
  {
    char *u = (char*)pari_malloc(strlen(s) + 1);
    pari_skip_space(&s);
    if (*s == '"') s = pari_translate_string(s, u, t);
    else
    { /* read integer */
      t = s;
      while (isdigit((int)*s)) s++;
      strncpy(u, t, s - t); u[s-t] = 0;
    }
    pari_stack_pushp(&s_A, u);
  }
  c->v = A;
}

static void
tm_free_cmd(tm_cmd *c)
{
  while (c->n--) pari_free((void*)c->v[c->n]);
  pari_free((void*)c->v);
}

static void
tm_handle_command(const char *s)
{
  tm_cmd c;
  tm_parse_command(&c, s);
  if (strcmp(c.cmd, "complete"))
    pari_err(e_MISC,"Texmacs command %s not implemented", c.cmd);
  if (c.n != 2)
    pari_err(e_MISC,"was expecting 2 arguments for Texmacs command");
  tm_completion(c.v[0], atol(c.v[1]));
  tm_free_cmd(&c);
  did_complete = 1;
}

/****/

int
tm_is_interactive() { return 0; }

static int tm_is_waiting = 0;
/* tell TeXmacs GP will start outputing data */
void
tm_start_output(void)
{
  if (!tm_is_waiting) { printf("%cverbatim:",DATA_BEGIN); fflush(stdout); }
  tm_is_waiting = 1;
}
/* tell TeXmacs GP is done and is waiting for new data */
void
tm_end_output(void)
{
  if (tm_is_waiting) { printf("%c", DATA_END); fflush(stdout); }
  tm_is_waiting = 0;
}
char *
tm_fgets(char *s, int n, FILE *f)
{
  if (!did_complete)
  { /* we need input */
    tm_start_output();
    tm_end_output();
  }
  return fgets(s,n,f);
}

int
tm_get_line(const char *prompt, const char *prompt_cont, filtre_t *F)
{
  int res = get_line_from_file(prompt, F, pari_infile);
  (void)prompt_cont;
  if (res)
  {
    char *s = F->buf->buf;
    did_complete = 0;
    if (pari_infile == stdin && *s == DATA_BEGIN)
    { tm_handle_command(s); *s = 0; }
    else
      tm_start_output();
  }
  return res;
}

void
tm_output(GEN z)
{
  char *sz = GENtoTeXstr(z);
  printf("%clatex:", DATA_BEGIN);
  printf("\\magenta\\%%%ld = ", GP_DATA->hist->total);
  printf("$\\blue %s$%c", sz,DATA_END);
  pari_free(sz); fflush(stdout);
  pari_flush();
}

void
init_texmacs(void)
{
#ifdef READLINE
  printf("%ccommand:(cas-supports-completions-set! \"pari\")%c\n",
         DATA_BEGIN, DATA_END);
#endif
  cb_pari_fgets_interactive = tm_fgets;
  cb_pari_get_line_interactive = tm_get_line;

  cb_pari_start_output = tm_start_output;
  cb_pari_end_output = tm_end_output;
  cb_pari_is_interactive = tm_is_interactive;
  cb_gp_output = tm_output;
  disable_color = 1;
  tm_start_output();
}
