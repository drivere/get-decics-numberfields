#include <stdio.h>
#include <pari/pari.h>
#include <readline/readline.h>
#include <readline/history.h>
#include <setjmp.h>

char * prompt = NULL;
int chrono = 0;
jmp_buf env;

GEN sd_prompt(const char *v, long flag)
{
  if (v) { pari_free(prompt); prompt = strdup(v); }
  if (flag == d_RETURN) return strtoGENstr(prompt);
  else if (flag == d_ACKNOWLEDGE)
    pari_printf("   prompt = \"%s\"\n", prompt);
  return gnil;
}
GEN
sd_timer(const char *v, long flag)
{ return sd_toggle(v,flag,"timer", &chrono); }
void gp_err_recover(long numerr) { longjmp(env, numerr); }
void gp_quit(long exitcode) { exit(exitcode); }
void help(const char *s)
{
  entree *ep = is_entry(s);
  if (ep && ep->help)
    pari_printf("%s\n",ep->help);
  else
    pari_printf("Function %s not found\n",s);
}

entree functions_gp[]={
  {"quit",0,(void*)gp_quit,11,"vD0,L,","quit({status = 0}): quit, return to the system with exit status 'status'."},
  {"help",0,(void*)help,11,"vr","help(fun): display help for function fun"},
  {NULL,0,NULL,0,NULL,NULL}};

entree default_gp[]={
  {"prompt",0,(void*)sd_prompt,16,"","(default) string to be printed as prompt"},
  {"timer",0,(void*)sd_timer,16,"","(default) toggle timer on/off"},
  {NULL,0,NULL,0,NULL,NULL}};

#define col(a) term_get_color(NULL, a)

int main(int argc, char **argv)
{
  pari_init(8000000,500000);
  pari_add_module(functions_gp);
  pari_add_defaults_module(default_gp);
  sd_colors("lightbg",d_INITRC);
  sd_prompt("? ",d_INITRC);
  pari_printf("Welcome to minigp!\n");
  cb_pari_err_recover = gp_err_recover;
  (void)setjmp(env);
  while(1)
  {
    GEN z;
    char *pr = pari_sprintf("%s%s%s",col(c_PROMPT),prompt,col(c_INPUT));
    char *in = readline(pr);
    pari_timer T;
    long time;

    if (!in) break;
    if (!*in) continue;

    add_history(in);
    timer_start(&T); z = gp_read_str(in); time = timer_delay(&T);
    pari_add_hist(z, time);
    if (z != gnil && in[strlen(in)-1] != ';')
    {
      pari_printf("%s%%%lu = %s",col(c_HIST),pari_nb_hist(),col(c_OUTPUT));
      output(z);
    }
    if (chrono && time)
      pari_printf("%stime = %s%ld ms%s.\n",
                  col(c_NONE),col(c_TIME),time,col(c_NONE));
    free(in); avma = top;
  }
  return 0;
}
