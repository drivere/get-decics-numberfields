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
/*                 INTERFACE TO READLINE COMPLETION                */
/*                                                                 */
/*******************************************************************/
#include "pari.h"

#ifdef READLINE

#include "paripriv.h"
#include "gp.h"

typedef int (*RLCI)(int, int); /* rl_complete and rl_insert functions */
typedef char* (*GF)(const char*, int); /* generator function */

BEGINEXTERN
/* otherwise C++ compilers will choke on rl_message() prototype */
#define USE_VARARGS
#define PREFER_STDARG
#include <readline/readline.h>
#include <readline/history.h>
ENDEXTERN

/**************************************************************************/
static int pari_rl_back;
static int did_init_matched = 0;
static entree *current_ep = NULL;

static int
change_state(const char *msg, ulong flag, int count)
{
  int c = (GP_DATA->readline_state & flag) != 0;
  ulong state = GP_DATA->readline_state;

  switch(count)
  {
    default: c = 0; break; /* off */
    case -1: c = 1; break; /* on  */
    case -2: c = 1 - c; /* toggle */
  }
  if (c)
    GP_DATA->readline_state |= flag;
  else {
    GP_DATA->readline_state &= ~flag;
    if (!GP_DATA->readline_state && state) GP_DATA->readline_state = 1;
  }
  rl_save_prompt();
  rl_message("[%s: %s] ", msg, c? "on": "off");
  c = rl_read_key();
  rl_restore_prompt();
  rl_clear_message();
  rl_stuff_char(c); return 1;
}

/* Wrapper around rl_complete to allow toggling insertion of arguments */
static int
pari_rl_complete(int count, int key)
{
  int ret;

  pari_rl_back = 0;
  if (count <= 0)
    return change_state("complete args", DO_ARGS_COMPLETE, count);

  rl_begin_undo_group();
  if (rl_last_func == pari_rl_complete)
    rl_last_func = (RLCI) rl_complete; /* Make repeated TABs different */
  ret = ((RLCI)rl_complete)(count,key);
  if (pari_rl_back && (pari_rl_back <= rl_point))
    rl_point -= pari_rl_back;
  rl_end_undo_group(); return ret;
}

static int did_matched_insert;

static int
pari_rl_matched_insert_suspend(int count, int key)
{
  ulong state = GP_DATA->readline_state;
  (void)count; (void)key;

  did_matched_insert = (GP_DATA->readline_state & DO_MATCHED_INSERT);
  GP_DATA->readline_state &= ~DO_MATCHED_INSERT;
  if (!GP_DATA->readline_state && state) GP_DATA->readline_state = 1;
  return 1;
}

static int
pari_rl_matched_insert_restore(int count, int key)
{
  (void)count; (void)key;
  if (did_matched_insert)
    GP_DATA->readline_state |= DO_MATCHED_INSERT;
  return 1;
}

static const char paropen[] = "([{";
static const char parclose[] = ")]}";

/* To allow insertion of () with a point in between. */
static int
pari_rl_matched_insert(int count, int key)
{
  int i = 0, ret;

  if (count <= 0)
    return change_state("electric parens", DO_MATCHED_INSERT, count);
  while (paropen[i] && paropen[i] != key) i++;
  if (!paropen[i] || !(GP_DATA->readline_state & DO_MATCHED_INSERT) || GP_DATA->flags & gpd_EMACS)
    return ((RLCI)rl_insert)(count,key);
  rl_begin_undo_group();
  ((RLCI)rl_insert)(count,key);
  ret = ((RLCI)rl_insert)(count,parclose[i]);
  rl_point -= count;
  rl_end_undo_group(); return ret;
}

static int
pari_rl_default_matched_insert(int count, int key)
{
    if (!did_init_matched) {
      did_init_matched = 1;
      GP_DATA->readline_state |= DO_MATCHED_INSERT;
    }
    return pari_rl_matched_insert(count, key);
}

static int
pari_rl_forward_sexp(int count, int key)
{
  int deep = 0, dir = 1, move_point = 0, lfail;

  (void)key;
  if (count < 0)
  {
    count = -count; dir = -1;
    if (!rl_point) goto fail;
    rl_point--;
  }
  while (count || deep)
  {
    move_point = 1;        /* Need to move point if moving left. */
    lfail = 0;                /* Do not need to fail left movement yet. */
    while ( !is_keyword_char(rl_line_buffer[rl_point])
            && !strchr("\"([{}])",rl_line_buffer[rl_point])
            && !( (dir == 1)
                  ? (rl_point >= rl_end)
                  : (rl_point <= 0 && (lfail = 1))))
        rl_point += dir;
    if (lfail || !rl_line_buffer[rl_point]) goto fail;

    if (is_keyword_char(rl_line_buffer[rl_point]))
    {
      while ( is_keyword_char(rl_line_buffer[rl_point])
              && (!((dir == 1) ? (rl_point >= rl_end) : (rl_point <= 0 && (lfail = 1)))
                  || (move_point = 0)))
        rl_point += dir;
      if (deep && lfail) goto fail;
      if (!deep) count--;
    }
    else if (strchr(paropen,rl_line_buffer[rl_point]))
    {
      if (deep == 0 && dir == -1) goto fail; /* We are already out of pars. */
      rl_point += dir;
      deep++; if (!deep) count--;
    }
    else if (strchr(parclose,rl_line_buffer[rl_point]))
    {
      if (deep == 0 && dir == 1)
      {
        rl_point++; goto fail; /* Get out of pars. */
      }
      rl_point += dir;
      deep--; if (!deep) count--;
    }
    else if (rl_line_buffer[rl_point] == '\"')
    {
      int bad = 1;

      rl_point += dir;
      while ( ((rl_line_buffer[rl_point] != '\"') || (bad = 0))
              && (!((dir == 1) ? (rl_point >= rl_end) : (rl_point <= 0))
                  || (move_point = 0)) )
        rl_point += dir;
      if (bad) goto fail;
      rl_point += dir;        /* Skip the other delimiter */
      if (!deep) count--;
    }
    else
    {
      fail: rl_ding(); return 1;
    }
  }
  if (dir != 1 && move_point) rl_point++;
  return 1;
}

static int
pari_rl_backward_sexp(int count, int key)
{
  return pari_rl_forward_sexp(-count, key);
}

/* do we add () at the end of completed word? (is it a function?) */
static int
add_paren(int end)
{
  entree *ep;
  const char *s;

  if (end < 0 || rl_line_buffer[end] == '(')
    return 0; /* not from command_generator or already there */
  ep = do_alias(current_ep); /* current_ep set in command_generator */
  if (EpVALENCE(ep) < EpNEW)
  { /* is it a constant masked as a function (e.g Pi)? */
    s = ep->help; if (!s) return 1;
    while (is_keyword_char(*s)) s++;
    return (*s != '=');
  }
  switch(EpVALENCE(ep))
  {
    case EpVAR: return typ((GEN)ep->value) == t_CLOSURE;
    case EpINSTALL: return 1;
  }
  return 0;
}

static void
match_concat(char **matches, const char *s)
{
  matches[0] = (char*)pari_realloc((void*)matches[0],
                                strlen(matches[0])+strlen(s)+1);
  strcat(matches[0],s);
}

#define add_comma(x) (x==-2) /* from default_generator */

/* a single match, possibly modify matches[0] in place */
static void
treat_single(int code, char **matches)
{
  if (add_paren(code))
  {
    match_concat(matches,"()");
    pari_rl_back = 1;
    if (rl_point == rl_end)
    rl_completion_append_character = '\0'; /* Do not append space. */
  }
  else if (add_comma(code))
    match_concat(matches,",");
}
#undef add_comma


static char **
matches_for_emacs(const char *text, char **matches)
{
  if (!matches) printf("@");
  else
  {
    int i;
    printf("%s@", matches[0] + strlen(text));
    if (matches[1]) print_fun_list(matches+1,0);

   /* we don't want readline to do anything, but insert some junk
    * which will be erased by emacs.
    */
    for (i=0; matches[i]; i++) pari_free(matches[i]);
    pari_free(matches);
  }
  matches = (char **) pari_malloc(2*sizeof(char *));
  matches[0] = (char*)pari_malloc(2); sprintf(matches[0],"_");
  matches[1] = NULL; printf("@E_N_D"); pari_flush();
  return matches;
}

/* Attempt to complete on the contents of TEXT. 'code' is used to
 * differentiate between callers when a single match is found.
 * Return the array of matches, NULL if there are none. */
static char **
get_matches(int code, const char *text, GF f)
{
  char **matches = rl_completion_matches(text, f);
  if (matches && !matches[1]) treat_single(code, matches);
  if (GP_DATA->flags & gpd_EMACS) matches = matches_for_emacs(text,matches);
  return matches;
}

static char *
add_prefix(const char *name, const char *text, long junk)
{
  char *s = strncpy((char*)pari_malloc(strlen(name)+1+junk),text,junk);
  strcpy(s+junk,name); return s;
}
static void
init_prefix(const char *text, int *len, int *junk, char **TEXT)
{
  long l = strlen(text), j = l-1;
  while (j >= 0 && is_keyword_char(text[j])) j--;
  j++;
  *TEXT = (char*)text + j;
  *junk = j;
  *len  = l - j;
}

static int
is_internal(entree *ep) { return *ep->name == '_'; }

/* Generator function for command completion.  STATE lets us know whether
 * to start from scratch; without any state (i.e. STATE == 0), then we
 * start at the top of the list. */
static char *
hashtable_generator(const char *text, int state, entree **hash)
{
  static int hashpos, len, junk;
  static entree* ep;
  static char *TEXT;

 /* If this is a new word to complete, initialize now:
  *  + indexes hashpos (GP hash list) and n (keywords specific to long help).
  *  + file completion and keyword completion use different word boundaries,
  *    have TEXT point to the keyword start.
  *  + save the length of TEXT for efficiency.
  */
  if (!state)
  {
    hashpos = 0; ep = hash[hashpos];
    init_prefix(text, &len, &junk, &TEXT);
  }

  /* Return the next name which partially matches from the command list. */
  for(;;)
    if (!ep)
    {
      if (++hashpos >= functions_tblsz) return NULL; /* no names matched */
      ep = hash[hashpos];
    }
    else if (is_internal(ep) || strncmp(ep->name,TEXT,len))
      ep = ep->next;
    else
      break;
  current_ep = ep; ep = ep->next;
  return add_prefix(current_ep->name,text,junk);
}
/* Generator function for member completion.  STATE lets us know whether
 * to start from scratch; without any state (i.e. STATE == 0), then we
 * start at the top of the list. */
static char *
member_generator(const char *text, int state)
{
  static int hashpos, len, junk;
  static entree* ep;
  static char *TEXT;
  entree **hash=functions_hash;

 /* If this is a new word to complete, initialize now:
  *  + indexes hashpos (GP hash list) and n (keywords specific to long help).
  *  + file completion and keyword completion use different word boundaries,
  *    have TEXT point to the keyword start.
  *  + save the length of TEXT for efficiency.
  */
  if (!state)
  {
    hashpos = 0; ep = hash[hashpos];
    init_prefix(text, &len, &junk, &TEXT);
  }

  /* Return the next name which partially matches from the command list. */
  for(;;)
    if (!ep)
    {
      if (++hashpos >= functions_tblsz) return NULL; /* no names matched */
      ep = hash[hashpos];
    }
    else if (ep->name[0]=='_' && ep->name[1]=='.'
             && !strncmp(ep->name+2,TEXT,len))
        break;
    else
        ep = ep->next;
  current_ep = ep; ep = ep->next;
  return add_prefix(current_ep->name+2,text,junk);
}
static char *
command_generator(const char *text, int state)
{ return hashtable_generator(text,state, functions_hash); }
static char *
default_generator(const char *text,int state)
{ return hashtable_generator(text,state, defaults_hash); }

static char *
ext_help_generator(const char *text, int state)
{
  static int len, junk, n, def, key;
  static char *TEXT;
  if (!state) {
    n = 0;
    def = key = 1;
    init_prefix(text, &len, &junk, &TEXT);
  }
  if (def)
  {
    char *s = default_generator(TEXT, state);
    if (s) return add_prefix(s, text, junk);
    def = 0;
  }
  if (key)
  {
    for ( ; keyword_list[n]; n++)
      if (!strncmp(keyword_list[n],TEXT,len))
        return add_prefix(keyword_list[n++], text, junk);
    key = 0; state = 0;
  }
  return command_generator(text, state);
}

static void
rl_print_aide(char *s, int flag)
{
  int p = rl_point, e = rl_end;
  FILE *save = pari_outfile;

  rl_point = 0; rl_end = 0; pari_outfile = rl_outstream;
  rl_save_prompt();
  rl_message("%s",""); /* rl_message("") ==> "zero length format" warning */
  gp_help(s, flag);
  rl_restore_prompt();
  rl_point = p; rl_end = e; pari_outfile = save;
  rl_clear_message();
  rl_refresh_line(0,0);
}

/* add a space between \<char> and following text. Attempting completion now
 * would delete char. Hitting <TAB> again will complete properly */
static char **
add_space(int start)
{
  char **m;
  int p = rl_point + 1;
  rl_point = start + 2;
  rl_insert(1, ' '); rl_point = p;
  /*better: fake an empty completion, but don't append ' ' after it! */
  rl_completion_append_character = '\0';
  m = (char**)pari_malloc(2 * sizeof(char*));
  m[0] = (char*)pari_malloc(1); *(m[0]) = 0;
  m[1] = NULL; return m;
}

char **
pari_completion(char *text, int START, int END)
{
  int i, first=0, start=START;

  rl_completion_append_character = ' ';
  current_ep = NULL;
/* If the line does not begin by a backslash, then it is:
 * . an old command ( if preceded by "whatnow(" ).
 * . a default ( if preceded by "default(" ).
 * . a member function ( if preceded by "." + keyword_chars )
 * . a file name (in current directory) ( if preceded by 'read' or 'writexx' )
 * . a command */
  if (start >=1 && rl_line_buffer[start] != '~') start--;
  while (start && is_keyword_char(rl_line_buffer[start])) start--;
  if (rl_line_buffer[start] == '~')
  {
    GF f = (GF)rl_username_completion_function;
    for(i=start+1;i<=END;i++)
      if (rl_line_buffer[i] == '/') { f = (GF)rl_filename_completion_function; break; }
    return get_matches(-1, text, f);
  }

  while (rl_line_buffer[first] && isspace((int)rl_line_buffer[first])) first++;
  switch (rl_line_buffer[first])
  {
    case '\\':
      if (first == start) return add_space(start);
      return get_matches(-1, text, rl_filename_completion_function);
    case '?':
      if (rl_line_buffer[first+1] == '?')
        return get_matches(-1, text, ext_help_generator);
      return get_matches(-1, text, command_generator);
  }

  while (start && rl_line_buffer[start] != '('
               && rl_line_buffer[start] != ',') start--;
  if (rl_line_buffer[start] == '(' && start)
  {
    int iend, j,k;
    entree *ep;
    char buf[200];

    i = start;

    while (i && isspace((int)rl_line_buffer[i-1])) i--;
    iend = i;
    while (i && is_keyword_char(rl_line_buffer[i-1])) i--;

    if (strncmp(rl_line_buffer + i,"default",7) == 0)
      return get_matches(-2, text, default_generator);
    if ( strncmp(rl_line_buffer + i,"read",4)  == 0
      || strncmp(rl_line_buffer + i,"write",5) == 0)
      return get_matches(-1, text, rl_filename_completion_function);

    j = start + 1;
    while (j <= END && isspace((int)rl_line_buffer[j])) j++;
    k = END;
    while (k > j && isspace((int)rl_line_buffer[k])) k--;
    /* If we are in empty parens, insert the default arguments */
    if ((GP_DATA->readline_state & DO_ARGS_COMPLETE) && k == j
         && (rl_line_buffer[j] == ')' || !rl_line_buffer[j])
         && (iend - i < (long)sizeof(buf))
         && ( strncpy(buf, rl_line_buffer + i, iend - i),
              buf[iend - i] = 0, 1)
         && (ep = is_entry(buf)) && ep->help)
    {
      const char *s = ep->help;
      while (is_keyword_char(*s)) s++;
      if (*s++ == '(')
      { /* function call: insert arguments */
        const char *e = s;
        while (*e && *e != ')' && *e != '(') e++;
        if (*e == ')')
        { /* we just skipped over the arguments in short help text */
          char *str = strncpy((char*)pari_malloc(e-s + 1), s, e-s);
          char **ret = (char**)pari_malloc(sizeof(char*)*2);
          str[e-s] = 0;
          ret[0] = str; ret[1] = NULL;
          if (GP_DATA->flags & gpd_EMACS) ret = matches_for_emacs("",ret);
          return ret;
        }
      }
    }
  }
  for(i = END-1; i >= start; i--)
    if (!is_keyword_char(rl_line_buffer[i]))
    {
      if (rl_line_buffer[i] == '.')
        return get_matches(-1, text, member_generator);
      break;
    }
  return get_matches(END, text, command_generator);
}

/* long help if count < 0 */
static int
rl_short_help(int count, int key)
{
  int flag = h_RL;
  char *s = rl_line_buffer + rl_point;

  (void)key;
  /* func() with cursor on ')', e.g. following completion */
  if (s > rl_line_buffer && *s == ')' && s[-1] == '(') s--;
  while (s > rl_line_buffer && is_keyword_char(s[-1])) s--;
  /* check for '\c' */
  if (s > rl_line_buffer && s[-1] == '\\') s--;

  if (count < 0 || rl_last_func == rl_short_help) flag |= h_LONG;
  rl_print_aide(s, flag); return 0;
}

static int
rl_long_help(int count, int key) { (void)count; return rl_short_help(-1,key); }

static void
init_histfile(void)
{
  char *h = GP_DATA->histfile;
  if (h && read_history(h)) write_history(h);
}

/*******************************************************************/
/*                                                                 */
/*                   GET LINE FROM READLINE                        */
/*                                                                 */
/*******************************************************************/
static int
history_is_new(char *s)
{
  HIST_ENTRY *e;
  if (!*s) return 0;
  if (!history_length) return 1;
  e = history_get(history_length);
  /* paranoia: e != NULL, unless readline is in a weird state */
  return e? strcmp(s, e->line): 0;
}

static void
gp_add_history(char *s)
{
  if (history_is_new(s)) { add_history(s); append_history(1,GP_DATA->histfile); }
}

/* Read line; returns a malloc()ed string of the user input or NULL on EOF.
   Increments the buffer size appropriately if needed; fix *endp if so. */
static char *
gprl_input(char **endp, int first, input_method *IM, filtre_t *F)
{
  pari_sp av = avma;
  Buffer *b = F->buf;
  ulong used = *endp - b->buf;
  ulong left = b->len - used, l;
  const char *p;
  char *s, *t;

  if (first) p = IM->prompt;
  else {
    p = F->in_comment ? GP_DATA->prompt_comment: IM->prompt_cont;
    p = gp_format_prompt(p);
  }
  if (! (s = readline(p)) ) { avma = av; return NULL; } /* EOF */
  gp_add_history(s); /* Makes a copy */
  l = strlen(s) + 1;
  /* put back \n that readline stripped. This is needed for
   * { print("a
   *   b"); }
   * and conforms with the other input methods anyway. */
  t = (char*)pari_malloc(l + 1);
  strncpy(t, s, l-1);
  t[l-1] = '\n';
  t[l]   = 0; /* equivalent to sprintf(t,"%s\n", s) */
  if (left < l)
  {
    ulong incr = b->len;
    if (incr < l) incr = l;
    fix_buffer(b, b->len + incr);
    *endp = b->buf + used;
  }
  avma = av; return t;
}

/* request one line interactively.
 * Return 0: EOF
 *        1: got one line from readline or pari_infile */
int
get_line_from_readline(const char *prompt, const char *prompt_cont, filtre_t *F)
{
  const int index = history_length;
  char *s;
  input_method IM;

  if (!GP_DATA->use_readline)
  {
    pari_puts(prompt); pari_flush();
    return get_line_from_file(prompt, F, pari_infile);
  }

  IM.prompt      = prompt;
  IM.prompt_cont = prompt_cont;
  IM.getline = &gprl_input;
  IM.free = 1;
  if (! input_loop(F,&IM)) { pari_puts("\n"); return 0; }

  s = F->buf->buf;
  if (*s)
  {
    if (history_length > index+1)
    { /* Multi-line input. Remove incomplete lines */
      int i = history_length;
      while (i > index) {
        HIST_ENTRY *e = remove_history(--i);
        pari_free(e->line); pari_free(e);
      }
      gp_add_history(s);
    }
    gp_echo_and_log(prompt, s);
  }
  return 1;
}

void
init_readline(void)
{
  static int init_done = 0;

  if (init_done) return;
  if (! GP_DATA->use_readline) GP_DATA->readline_state = 0;
  init_done = 1;
  init_histfile();
  cb_pari_init_histfile = init_histfile;
  cb_pari_get_line_interactive = get_line_from_readline;

  /* Allow conditional parsing of the ~/.inputrc file. */
  rl_readline_name = "Pari-GP";

  /* added ~, ? and , */
  rl_basic_word_break_characters = " \t\n\"\\'`@$><=;|&{(?~";
  rl_special_prefixes = "~";

  /* custom completer */
  rl_attempted_completion_function = (rl_completion_func_t*) pari_completion;

  /* we always want the whole list of completions under emacs */
  if (GP_DATA->flags & gpd_EMACS) rl_completion_query_items = 0x8fff;

  rl_add_defun("short-help", rl_short_help, -1);
  rl_add_defun("long-help", rl_long_help, -1);
  rl_add_defun("pari-complete", pari_rl_complete, '\t');
  rl_add_defun("pari-matched-insert", pari_rl_default_matched_insert, -1);
  rl_add_defun("pari-matched-insert-suspend", pari_rl_matched_insert_suspend, -1);
  rl_add_defun("pari-matched-insert-restore", pari_rl_matched_insert_restore, -1);
  rl_add_defun("pari-forward-sexp", pari_rl_forward_sexp, -1);
  rl_add_defun("pari-backward-sexp", pari_rl_backward_sexp, -1);

  rl_bind_key_in_map('h', rl_short_help, emacs_meta_keymap);
  rl_bind_key_in_map('H', rl_long_help,  emacs_meta_keymap);

#define KSbind(s,f,k) rl_generic_bind(ISFUNC, (s), (char*)(f), (k))

  KSbind("OP",   rl_short_help,  emacs_meta_keymap); /* f1, vt100 */
  KSbind("[11~", rl_short_help,  emacs_meta_keymap); /* f1, xterm */
  KSbind("OP",   rl_short_help,  vi_movement_keymap); /* f1, vt100 */
  KSbind("[11~", rl_short_help,  vi_movement_keymap); /* f1, xterm */
  /* XTerm may signal start/end of paste by emitting F200/F201
   * TODO: check to what extent this patch has been applied */
  /* FIXME: For vi mode something more intelligent is needed - to switch to the
     insert mode - and back when restoring. */
  KSbind("[200~", pari_rl_matched_insert_suspend,  emacs_meta_keymap);  /* pre-paste xterm */
  KSbind("[200~", pari_rl_matched_insert_suspend,  vi_movement_keymap); /* pre-paste xterm */
  KSbind("[201~", pari_rl_matched_insert_restore,  emacs_meta_keymap);  /* post-paste xterm */
  KSbind("[201~", pari_rl_matched_insert_restore,  vi_movement_keymap); /* post-paste xterm */
  rl_bind_key_in_map('(', pari_rl_matched_insert, emacs_standard_keymap);
  rl_bind_key_in_map('[', pari_rl_matched_insert, emacs_standard_keymap);
  rl_bind_key_in_map(6, pari_rl_forward_sexp,  emacs_meta_keymap); /* M-C-f */
  rl_bind_key_in_map(2, pari_rl_backward_sexp, emacs_meta_keymap); /* M-C-b */
}
#endif
