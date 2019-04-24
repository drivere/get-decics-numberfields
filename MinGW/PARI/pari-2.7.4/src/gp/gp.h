/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*************************************************************************/
/*                                                                       */
/*                      GP-SPECIFIC DECLARATIONS                         */
/*                                                                       */
/*************************************************************************/
BEGINEXTERN

void aide(const char *s, long flag);
void echo_and_log(const char *prompt, const char *s);
int  get_line_from_readline(const char *prompt, const char *prompt_cont, filtre_t *F);
void readline_prompt_color(char *s, int c);
void gp_output(GEN z, gp_data *G);
void init_readline(void);
void texmacs_completion(const char *s, long pos);
void print_fun_list(char **list, long nbli);

/* aide() */
#define h_REGULAR 0
#define h_LONG    1
#define h_APROPOS 2
#define h_RL      4

/* readline completions */
extern const char *keyword_list[];

/* TeXmacs */
#define DATA_BEGIN  ((char) 2)
#define DATA_END    ((char) 5)
#define DATA_ESCAPE ((char) 27)

/* gp specific routines */
void alarm0(long s);
void dbg_down(long k);
GEN  dbg_err(void);
void dbg_up(long k);
GEN  extern0(const char *cmd);
GEN  externstr(const char *cmd);
GEN  gp_alarm(long s, GEN code);
void gp_quit(long exitcode);
GEN  input0(void);
void pari_breakpoint(void);
GEN  read0(const char *s);
GEN  readstr(const char *s);
void system0(const char *cmd);
int  whatnow(PariOUT *out, const char *s, int silent);
GEN sd_breakloop(const char *v, long flag);
GEN sd_echo(const char *v, long flag);
GEN sd_graphcolormap(const char *v, long flag);
GEN sd_graphcolors(const char *v, long flag);
GEN sd_help(const char *v, long flag);
GEN sd_histfile(const char *v, long flag);
GEN sd_lines(const char *v, long flag);
GEN sd_linewrap(const char *v, long flag);
GEN sd_prompt(const char *v, long flag);
GEN sd_prompt_cont(const char *v, long flag);
GEN sd_psfile(const char *v, long flag);
GEN sd_readline(const char *v, long flag);
GEN sd_recover(const char *v, long flag);
GEN sd_timer(const char *v, long flag);
#define MAX_PROMPT_LEN 128
const char *do_prompt(char *buf, const char *prompt, filtre_t *F);

extern entree  functions_highlevel[];
/* list of GP-specific defaults */
extern entree functions_gp_default[], functions_gp_rl_default[];
/* list of GP-specific functions */
extern entree  functions_gp[];
/* list of old GP-specific fonctions (up to 1.39.15) */
extern entree functions_oldgp[];

ENDEXTERN
