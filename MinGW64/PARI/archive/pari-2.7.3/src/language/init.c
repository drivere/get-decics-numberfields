/* Copyright (C) 2000-2003  The PARI group.

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
/*        INITIALIZING THE SYSTEM, ERRORS, STACK MANAGEMENT        */
/*                                                                 */
/*******************************************************************/
#include <string.h>
#include "pari.h"
#include "paripriv.h"
#include "anal.h"
#if defined(_WIN32) || defined(__CYGWIN32__)
#  include "../systems/mingw/mingw.h"
#  ifndef WINCE
#    include <process.h>
#  endif
#endif

const double LOG2    = 0.6931471805599453; /* log(2) */
const double LOG10_2 = 0.3010299956639812; /* log_10(2) */
const double LOG2_10 = 3.321928094887362;  /* log_2(10) */

GEN gnil, gen_0, gen_1, gen_m1, gen_2, gen_m2, ghalf, err_e_STACK;

static const ulong readonly_constants[] = {
  evaltyp(t_INT) | _evallg(2),  /* gen_0 */
  evallgefint(2),
  evaltyp(t_INT) | _evallg(2),  /* gnil */
  evallgefint(2),
  evaltyp(t_INT) | _evallg(3),  /* gen_1 */
  evalsigne(1) | evallgefint(3),
  1,
  evaltyp(t_INT) | _evallg(3),  /* gen_2 */
  evalsigne(1) | evallgefint(3),
  2,
  evaltyp(t_INT) | _evallg(3),  /* gen_m1 */
  evalsigne(-1) | evallgefint(3),
  1,
  evaltyp(t_INT) | _evallg(3),  /* gen_m2 */
  evalsigne(-1) | evallgefint(3),
  2,
};
static const pari_long readonly_ghalf[] = {
  evaltyp(t_FRAC) | _evallg(3), /* ghalf */
  (pari_long)(readonly_constants+4),
  (pari_long)(readonly_constants+7)
};
static const ulong readonly_err_STACK[] = {
  evaltyp(t_ERROR) | _evallg(2),
  e_STACK
};
THREAD GEN    bernzone;
GEN     primetab; /* private primetable */
byteptr diffptr;
FILE    *pari_outfile, *pari_errfile, *pari_logfile, *pari_infile;
char    *current_logfile, *current_psfile, *pari_datadir;
pari_long    gp_colors[c_LAST];
int     disable_color;
ulong   DEBUGFILES, DEBUGLEVEL, DEBUGMEM;
pari_long    DEBUGVAR;
ulong   pari_mt_nbthreads;
ulong   compatible, precreal, precdl, logstyle;
gp_data *GP_DATA;

GEN pari_colormap, pari_graphcolors;

entree  **varentries;

THREAD pari_sp bot, top, avma;
THREAD size_t memused;

static void ** MODULES, ** OLDMODULES;
static pari_stack s_MODULES, s_OLDMODULES;
const pari_long functions_tblsz = 135; /* size of functions_hash */
entree **functions_hash, **defaults_hash;

void (*cb_pari_ask_confirm)(const char *);
int  (*cb_pari_handle_exception)(pari_long);
int  (*cb_pari_whatnow)(PariOUT *out, const char *, int);
void (*cb_pari_sigint)(void);
void (*cb_pari_pre_recover)(pari_long);
void (*cb_pari_err_recover)(pari_long);
const char * pari_library_path = NULL;

static THREAD GEN global_err_data;
THREAD jmp_buf *iferr_env;
const pari_long CATCH_ALL = -1;

/*********************************************************************/
/*                                                                   */
/*                       BLOCKS & CLONES                             */
/*                                                                   */
/*********************************************************************/
/*#define DEBUG*/
static THREAD pari_long next_block;
static THREAD GEN cur_block; /* current block in block list */
#ifdef DEBUG
static THREAD pari_long NUM;
#endif

static void
pari_init_blocks(void)
{
  next_block = 0; cur_block = NULL;
#ifdef DEBUG
  NUM = 0;
#endif
}

static void
pari_close_blocks(void)
{
  while (cur_block) killblock(cur_block);
}

/* Return x, where:
 * x[-4]: reference count
 * x[-3]: adress of next block
 * x[-2]: adress of preceding block.
 * x[-1]: number of allocated blocs.
 * x[0..n-1]: malloc-ed memory. */
GEN
newblock(size_t n)
{
  pari_long *x = (pari_long *) pari_malloc((n + BL_HEAD)*sizeof(pari_long)) + BL_HEAD;

  bl_refc(x) = 1;
  bl_next(x) = NULL;
  bl_prev(x) = cur_block;
  bl_num(x)  = next_block++;
  if (cur_block) bl_next(cur_block) = x;
#ifdef DEBUG
  err_printf("+ %ld\n", ++NUM);
#endif
  if (DEBUGMEM)
  {
    if (!n) pari_warn(warner,"mallocing NULL object in newblock");
    if (DEBUGMEM > 2)
      err_printf("new block, size %6lu (no %ld): %08lx\n", n, next_block-1, x);
  }
  return cur_block = x;
}

GEN
gcloneref(GEN x)
{
  if (isclone(x)) { ++bl_refc(x); return x; }
  else return gclone(x);
}

void
gclone_refc(GEN x) { ++bl_refc(x); }

void
gunclone(GEN x)
{
  if (--bl_refc(x) > 0) return;
  BLOCK_SIGINT_START;
  if (bl_next(x)) bl_prev(bl_next(x)) = bl_prev(x);
  else
  {
    cur_block = bl_prev(x);
    next_block = bl_num(x);
  }
  if (bl_prev(x)) bl_next(bl_prev(x)) = bl_next(x);
  if (DEBUGMEM > 2)
    err_printf("killing block (no %ld): %08lx\n", bl_num(x), x);
  free((void*)bl_base(x)); /* pari_free not needed: we already block */
  BLOCK_SIGINT_END;
#ifdef DEBUG
  err_printf("- %ld\n", NUM--);
#endif
}

/* Recursively look for clones in the container and kill them. Then kill
 * container if clone. SIGINT could be blocked until it returns */
void
gunclone_deep(GEN x)
{
  pari_long i, lx;
  GEN v;
  if (isclone(x) && bl_refc(x) > 1) { --bl_refc(x); return; }
  BLOCK_SIGINT_START;
  switch(typ(x))
  {
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x);
      for (i=1;i<lx;i++) gunclone_deep(gel(x,i));
      break;
    case t_LIST:
      v = list_data(x); lx = v? lg(v): 1;
      for (i=1;i<lx;i++) gunclone_deep(gel(v,i));
      pari_free(v); break;
  }
  if (isclone(x)) gunclone(x);
  BLOCK_SIGINT_END;
}

int
pop_entree_block(entree *ep, pari_long loc)
{
  GEN x = (GEN)ep->value;
  if (bl_num(x) < loc) return 0; /* older */
  if (DEBUGMEM>2)
    err_printf("popping %s (block no %ld)\n", ep->name, bl_num(x));
  gunclone_deep(x); return 1;
}

/*********************************************************************/
/*                                                                   */
/*                       C STACK SIZE CONTROL                        */
/*                                                                   */
/*********************************************************************/
/* Avoid core dump on deep recursion. Adapted Perl code by Dominic Dunlop */
THREAD void *PARI_stack_limit = NULL;

#ifdef STACK_CHECK

#  ifdef __EMX__                                /* Emulate */
void
pari_stackcheck_init(void *pari_stack_base)
{
  (void) pari_stack_base;
  if (!pari_stack_base) { PARI_stack_limit = NULL; return; }
  PARI_stack_limit = get_stack(1./16, 32*1024);
}
#  else /* !__EMX__ */
#include <sys/types.h>
#include <sys/time.h>
#include <sys/resource.h>

/* Set PARI_stack_limit to (a little above) the lowest safe address that can be
 * used on the stack. Leave PARI_stack_limit at its initial value (NULL) to
 * show no check should be made [init failed]. Assume stack grows downward. */
void
pari_stackcheck_init(void *pari_stack_base)
{
  struct rlimit rip;
  ulong size;
  if (!pari_stack_base) { PARI_stack_limit = NULL; return; }
  if (getrlimit(RLIMIT_STACK, &rip)) return;
  size = rip.rlim_cur;
  if (size == (ulong)RLIM_INFINITY || size > (ulong)pari_stack_base)
    PARI_stack_limit = (void*)(((ulong)pari_stack_base) / 16);
  else
    PARI_stack_limit = (void*)((ulong)pari_stack_base - (size/16)*15);
}
#  endif /* !__EMX__ */

#else
void
pari_stackcheck_init(void *pari_stack_base)
{
  (void) pari_stack_base; PARI_stack_limit = NULL;
}
#endif /* STACK_CHECK */

/*******************************************************************/
/*                         HEAP TRAVERSAL                          */
/*******************************************************************/
struct getheap_t { pari_long n, l; };
static void
f_getheap(GEN x, void *D)
{
  struct getheap_t *T = (struct getheap_t*)D;
  T->n++;
  T->l += gsizeword(x);
}
GEN
getheap(void)
{
  struct getheap_t T = { 0, 0 };
  traverseheap(&f_getheap, &T);
  return mkvec2s(T.n, T.l + BL_HEAD * T.n);
}

void
traverseheap( void(*f)(GEN, void *), void *data )
{
  GEN x;
  for (x = cur_block; x; x = bl_prev(x)) f(x, data);
}

/*********************************************************************/
/*                          DAEMON / FORK                            */
/*********************************************************************/
#if defined(HAS_WAITPID) && defined(HAS_SETSID)
#  include <sys/wait.h>
/* Properly fork a process, detaching from main process group without creating
 * zombies on exit. Parent returns 1, son returns 0 */
int
pari_daemon(void)
{
  pid_t pid = fork();
  switch(pid) {
      case -1: return 1; /* father, fork failed */
      case 0:
        (void)setsid(); /* son becomes process group leader */
        if (fork()) exit(0); /* now son exits, also when fork fails */
        break; /* grandson: its father is the son, which exited,
                * hence father becomes 'init', that'll take care of it */
      default: /* father, fork succeeded */
        (void)waitpid(pid,NULL,0); /* wait for son to exit, immediate */
        return 1;
  }
  /* grandson */
  return 0;
}
#else
int
pari_daemon(void)
{
  pari_err_IMPL("pari_daemon without waitpid & setsid");
  return 0;
}
#endif

/*********************************************************************/
/*                                                                   */
/*                       SYSTEM INITIALIZATION                       */
/*                                                                   */
/*********************************************************************/
static int try_to_recover = 0;
THREAD VOLATILE int PARI_SIGINT_block = 0, PARI_SIGINT_pending = 0;
static void pari_sighandler(int sig);

/*********************************************************************/
/*                         SIGNAL HANDLERS                           */
/*********************************************************************/
static void
dflt_sigint_fun(void) { pari_err(e_MISC, "user interrupt"); }

#if defined(_WIN32) || defined(__CYGWIN32__)
int win32ctrlc = 0;
void
dowin32ctrlc(void)
{
  win32ctrlc = 0;
  cb_pari_sigint();
}
#endif

static void
pari_handle_SIGINT(void)
{
#ifdef _WIN32
  if (++win32ctrlc >= 5) _exit(3);
#else
  cb_pari_sigint();
#endif
}

static void
pari_sighandler(int sig)
{
  const char *msg;
#ifndef HAS_SIGACTION
  /*SYSV reset the signal handler in the handler*/
  (void)os_signal(sig,pari_sighandler);
#endif
  switch(sig)
  {
#ifdef SIGBREAK
    case SIGBREAK:
      if (PARI_SIGINT_block==1)
      {
        PARI_SIGINT_pending=SIGBREAK;
        mt_sigint();
      }
      else pari_handle_SIGINT();
      return;
#endif

#ifdef SIGINT
    case SIGINT:
      if (PARI_SIGINT_block==1)
      {
        PARI_SIGINT_pending=SIGINT;
        mt_sigint();
      }
      else pari_handle_SIGINT();
      return;
#endif

#ifdef SIGSEGV
    case SIGSEGV:
      msg="PARI/GP (Segmentation Fault)"; break;
#endif
#ifdef SIGBUS
    case SIGBUS:
      msg="PARI/GP (Bus Error)"; break;
#endif
#ifdef SIGFPE
    case SIGFPE:
      msg="PARI/GP (Floating Point Exception)"; break;
#endif

#ifdef SIGPIPE
    case SIGPIPE:
    {
      pariFILE *f = GP_DATA->pp->file;
      if (f && pari_outfile == f->file)
      {
        GP_DATA->pp->file = NULL; /* to avoid oo recursion on error */
        pari_outfile = stdout; pari_fclose(f);
        pari_err(e_MISC, "Broken Pipe, resetting file stack...");
      }
      return; /* not reached */
    }
#endif

    default: msg="signal handling"; break;
  }
  pari_err_BUG(msg);
}

void
pari_sig_init(void (*f)(int))
{
#ifdef SIGBUS
  (void)os_signal(SIGBUS,f);
#endif
#ifdef SIGFPE
  (void)os_signal(SIGFPE,f);
#endif
#ifdef SIGINT
  (void)os_signal(SIGINT,f);
#endif
#ifdef SIGBREAK
  (void)os_signal(SIGBREAK,f);
#endif
#ifdef SIGPIPE
  (void)os_signal(SIGPIPE,f);
#endif
#ifdef SIGSEGV
  (void)os_signal(SIGSEGV,f);
#endif
}

/*********************************************************************/
/*                      STACK AND UNIVERSAL CONSTANTS                */
/*********************************************************************/
static void
init_universal_constants(void)
{
  gen_0  = (GEN)readonly_constants;
  gnil   = (GEN)readonly_constants+2;
  gen_1  = (GEN)readonly_constants+4;
  gen_2  = (GEN)readonly_constants+7;
  gen_m1 = (GEN)readonly_constants+10;
  gen_m2 = (GEN)readonly_constants+13;
  ghalf  = (GEN)readonly_ghalf;
  err_e_STACK = (GEN)readonly_err_STACK;
}

static const size_t MIN_STACK = 500032;
static size_t
fix_size(size_t a)
{
  size_t b = a & (~0x3fULL); /* Align */
  if (b < MIN_STACK) b = MIN_STACK;
  return b;
}
/* old = current stack size (0 = unallocated), size = new size */
void
pari_init_stack(size_t size, size_t old)
{
  size_t s = fix_size(size);
  if (old != s) {
    BLOCK_SIGINT_START;
    if (old) pari_free((void*)bot);
    for (;;)
    {
      char buf[128];
      if (s < MIN_STACK) pari_err(e_MEM); /* no way out. Die */
      bot = (pari_sp)malloc(s); /* NOT pari_malloc, e_MEM would be deadly */
      if (bot) break;
      /* must use sprintf: pari stack is currently dead */
      s = fix_size(s>>1);
      sprintf(buf, "not enough memory, new stack %I64u", (ulong)s);
      pari_warn(warner, buf, s);
    }
    BLOCK_SIGINT_END;
  }
  avma = top = bot+s;
  memused = 0;
}

static void
pari_init_errcatch(void)
{
  iferr_env = NULL;
  global_err_data = NULL;
}

void
allocatemem(ulong newsize)
{
  size_t s, old = top - bot;

  evalstate_reset();
  if (!newsize) newsize = old << 1;
  pari_init_stack(newsize, old);
  s = top - bot;
  pari_warn(warner,"new stack size = %lu (%.3f Mbytes)", s, s/1048576.);
  if (cb_pari_pre_recover) cb_pari_pre_recover(-1);
  pari_init_errcatch();
  cb_pari_err_recover(-1);
}

/*********************************************************************/
/*                           INIT DEFAULTS                           */
/*********************************************************************/
void
pari_init_defaults(void)
{
  pari_long i;
  initout(1);

#ifdef LONG_IS_64BIT
  precreal = 4;
#else
  precreal = 5;
#endif

  precdl = 16;
  compatible = NONE;
  DEBUGFILES = DEBUGLEVEL = DEBUGMEM = 0;
  disable_color = 1;
  logstyle = logstyle_none;

  current_psfile = pari_strdup("pari.ps");
  current_logfile= pari_strdup("pari.log");
  pari_logfile = NULL;

  pari_datadir = os_getenv("GP_DATA_DIR");
  if (!pari_datadir)
  {
#if defined(_WIN32) || defined(__CYGWIN32__)
    if (paricfg_datadir[0]=='@' && paricfg_datadir[1]==0)
      pari_datadir = win32_datadir();
    else
#endif
      pari_datadir = pari_strdup(paricfg_datadir);
  }
  else pari_datadir= pari_strdup(pari_datadir);
  for (i=0; i<c_LAST; i++) gp_colors[i] = c_NONE;
  pari_colormap = NULL; pari_graphcolors = NULL;
}

/*********************************************************************/
/*                   FUNCTION HASHTABLES, MODULES                    */
/*********************************************************************/

/* Initialize hashtable */
static void
init_hashtable(entree **table, pari_long tblsz)
{
  pari_long i;
  for (i = 0; i < tblsz; i++)
  {
    entree *last = NULL, *ep = table[i];
    table[i] = NULL;
    while (ep)
    {
      entree *EP = ep->next;
      switch(EpVALENCE(ep))
      {
        case EpVAR: case EpINSTALL:
        /* keep: attach it to last entree seen */
          if (last)
            last->next = ep;
          else
            table[i] = ep;
          ep->next = NULL; last = ep;
          break;
        default: freeep(ep);
      }
      ep = EP;
    }
  }
}
/* Load in hashtable hash the modules contained in A */
static int
gp_init_entrees(pari_stack *p_A, entree **hash)
{
  pari_long i;
  entree **v = (entree **)*pari_stack_base(p_A);
  init_hashtable(hash, functions_tblsz);
  for (i = 0; i < p_A->n; i++) pari_fill_hashtable(hash, v[i]);
  return (hash == functions_hash);
}
int
gp_init_functions(void)
{
  return gp_init_entrees(new_fun_set? &s_MODULES: &s_OLDMODULES, functions_hash);
}

extern entree functions_basic[], functions_default[];
static void
pari_init_functions(void)
{
  pari_stack_init(&s_MODULES, sizeof(*MODULES),(void**)&MODULES);
  pari_stack_pushp(&s_MODULES,functions_basic);
  pari_stack_init(&s_OLDMODULES, sizeof(*OLDMODULES),(void**)&OLDMODULES);
  pari_stack_pushp(&s_OLDMODULES,oldfonctions);
  functions_hash = (entree**) pari_calloc(sizeof(entree*)*functions_tblsz);
  pari_fill_hashtable(functions_hash,
                      new_fun_set? functions_basic: oldfonctions);
  defaults_hash = (entree**) pari_calloc(sizeof(entree*)*functions_tblsz);
  pari_add_defaults_module(functions_default);
}

void
pari_add_module(entree *ep)
{
  if (new_fun_set)
    pari_fill_hashtable(functions_hash, ep);
  pari_stack_pushp(&s_MODULES, ep);
}

void
pari_add_defaults_module(entree *ep)
{ pari_fill_hashtable(defaults_hash, ep); }

void
pari_add_oldmodule(entree *ep)
{
  if (!new_fun_set)
    pari_fill_hashtable(functions_hash, ep);
  pari_stack_pushp(&s_OLDMODULES, ep);
}

/*********************************************************************/
/*                       PARI THREAD                                 */
/*********************************************************************/

static void
pari_mainstack_alloc(struct pari_mainstack *st, size_t s)
{
  st->bot = (pari_sp)pari_malloc(s);
  st->avma = st->top = st->bot+s;
  st->memused = 0;
}

static void
pari_mainstack_free(struct pari_mainstack *st)
{
  pari_free((void*)st->bot);
  st->avma = st->top = st->bot = 0;
}

static void
pari_mainstack_use(struct pari_mainstack *st)
{
  bot = st->bot; top = st->top; avma = st->avma;
  memused = st->memused;
}

/* Initial PARI thread structure t with a stack of size s and
 * argument arg */

void
pari_thread_alloc(struct pari_thread *t, size_t s, GEN arg)
{
  pari_mainstack_alloc(&t->st,s);
  t->data = arg;
}

void
pari_thread_free(struct pari_thread *t)
{
  pari_mainstack_free(&t->st);
}

void
pari_thread_init(void)
{
  pari_init_blocks();
  pari_init_errcatch();
  pari_init_rand();
  pari_init_floats();
  pari_init_parser();
  pari_init_compiler();
  pari_init_evaluator();
  pari_init_files();
}

void
pari_thread_close(void)
{
  pari_close_files();
  pari_close_evaluator();
  pari_close_compiler();
  pari_close_parser();
  pari_close_floats();
  pari_close_blocks();
}

GEN
pari_thread_start(struct pari_thread *t)
{
  pari_mainstack_use(&t->st);
  pari_thread_init();
  return t->data;
}

/*********************************************************************/
/*                       LIBPARI INIT / CLOSE                        */
/*********************************************************************/

static void
pari_exit(void)
{
  err_printf("  ***   Error in the PARI system. End of program.\n");
  exit(1);
}

static void
dflt_err_recover(pari_long errnum) { (void) errnum; pari_exit(); }

/* initialize PARI data. Initialize [new|old]fun to NULL for default set. */
void
pari_init_opts(size_t parisize, ulong maxprime, ulong init_opts)
{
  ulong u;

  cb_pari_whatnow = NULL;
  cb_pari_pre_recover = NULL;
  cb_pari_sigint = dflt_sigint_fun;
  if (init_opts&INIT_JMPm) cb_pari_err_recover = dflt_err_recover;

  pari_stackcheck_init(&u);
  pari_init_homedir();
  if (init_opts&INIT_DFTm) {
    pari_init_defaults();
    GP_DATA = default_gp_data();
    gp_expand_path(GP_DATA->path);
  }

  if (init_opts&INIT_SIGm) pari_sig_init(pari_sighandler);
  pari_init_stack(parisize, 0);
  init_universal_constants();
  diffptr = NULL;
  if (!(init_opts&INIT_noPRIMEm)) initprimetable(maxprime);
  pari_kernel_init();

  primetab = cgetalloc(t_VEC, 1);
  varentries = (entree**) pari_calloc((MAXVARN+1)*sizeof(entree*));
  pari_thread_init();
  pari_init_seadata();
  pari_init_functions();
  pari_var_init();
  (void)getabstime();
  try_to_recover = 1;
  if (!(init_opts&INIT_noIMTm)) pari_mt_init();
}

void
pari_init(size_t parisize, ulong maxprime)
{ pari_init_opts(parisize, maxprime, INIT_JMPm | INIT_SIGm | INIT_DFTm); }

void
pari_close_opts(ulong init_opts)
{
  pari_long i;

  BLOCK_SIGINT_START;
  if ((init_opts&INIT_SIGm)) pari_sig_init(SIG_DFL);
  if (!(init_opts&INIT_noIMTm)) pari_mt_close();

  while (delete_var()) /* empty */;
  for (i = 0; i < functions_tblsz; i++)
  {
    entree *ep = functions_hash[i];
    while (ep) {
      entree *EP = ep->next;
      if (!EpSTATIC(ep)) { freeep(ep); free(ep); }
      ep = EP;
    }
  }
  free((void*)varentries);
  free((void*)primetab);
  pari_close_seadata();
  pari_thread_close();
  pari_kernel_close();

  free((void*)functions_hash);
  free((void*)defaults_hash);
  free((void*)bot);
  if (diffptr) free((void*)diffptr);
  free(current_logfile);
  free(current_psfile);
  pari_stack_delete(&s_MODULES);
  pari_stack_delete(&s_OLDMODULES);
  pari_close_homedir();
  if (pari_datadir) free(pari_datadir);
  if (init_opts&INIT_DFTm)
  { /* delete GP_DATA */
    if (GP_DATA->hist->v) free((void*)GP_DATA->hist->v);
    if (GP_DATA->pp->cmd) free((void*)GP_DATA->pp->cmd);
    delete_dirs(GP_DATA->path);
    free((void*)GP_DATA->path->PATH);
  }
  BLOCK_SIGINT_END;
}

void
pari_close(void)
{ pari_close_opts(INIT_JMPm | INIT_SIGm | INIT_DFTm); }

/*******************************************************************/
/*                                                                 */
/*                         ERROR RECOVERY                          */
/*                                                                 */
/*******************************************************************/
void
gp_context_save(struct gp_context* rec)
{
  rec->file = pari_last_tmp_file();
  if (DEBUGFILES>1)
    err_printf("gp_context_save: %s\n", rec->file ? rec->file->name: "NULL");
  rec->prettyp = GP_DATA->fmt->prettyp;
  rec->listloc = next_block;
  rec->iferr_env = iferr_env;
  rec->err_data  = global_err_data;
  evalstate_save(&rec->eval);
  parsestate_save(&rec->parse);
}

void
gp_context_restore(struct gp_context* rec)
{
  pari_long i;

  if (!try_to_recover) return;
  /* disable gp_context_restore() and SIGINT */
  try_to_recover = 0;
  BLOCK_SIGINT_START
  if (DEBUGMEM>2) err_printf("entering recover(), loc = %ld\n", rec->listloc);
  evalstate_restore(&rec->eval);
  parsestate_restore(&rec->parse);
  filestate_restore(rec->file);
  global_err_data = rec->err_data;
  iferr_env = rec->iferr_env;
  GP_DATA->fmt->prettyp = rec->prettyp;

  for (i = 0; i < functions_tblsz; i++)
  {
    entree *ep = functions_hash[i];
    while (ep)
    {
      entree *EP = ep->next;
      switch(EpVALENCE(ep))
      {
        case EpVAR:
          while (pop_val_if_newer(ep,rec->listloc)) /* empty */;
          break;
        case EpNEW: break;
      }
      ep = EP;
    }
  }
  if (DEBUGMEM>2) err_printf("leaving recover()\n");
  BLOCK_SIGINT_END
  try_to_recover = 1;
}

static void
err_recover(pari_long numerr)
{
  if (cb_pari_pre_recover)
    cb_pari_pre_recover(numerr);
  evalstate_reset();
  killallfiles();
  pari_init_errcatch();
  out_puts(pariErr, "\n");
  pariErr->flush();

  cb_pari_err_recover(numerr);
}

static void
err_init(void)
{
  /* make sure pari_err msg starts at the beginning of line */
  if (!pari_last_was_newline()) pari_putc('\n');
  pariOut->flush();
  pariErr->flush();
  out_term_color(pariErr, c_ERR);
}

static void
err_init_msg(int numerr, int user)
{
  const char *gp_function_name;
  out_puts(pariErr, "  *** ");
  if (numerr != user && (gp_function_name = closure_func_err()))
    out_printf(pariErr, "%s: ", gp_function_name);
  else
    out_puts(pariErr, "  ");
}

void
pari_warn(int numerr, ...)
{
  char *ch1;
  va_list ap;

  va_start(ap,numerr);

  err_init();
  err_init_msg(numerr, warnuser);
  switch (numerr)
  {
    case warnuser:
      out_puts(pariErr, "user warning: ");
      out_print0(pariErr, NULL, va_arg(ap, GEN), f_RAW);
      break;

    case warnmem:
      out_puts(pariErr, "collecting garbage in "); ch1=va_arg(ap, char*);
      out_vprintf(pariErr, ch1,ap); out_putc(pariErr, '.');
      break;

    case warner:
      out_puts(pariErr, "Warning: "); ch1=va_arg(ap, char*);
      out_vprintf(pariErr, ch1,ap); out_putc(pariErr, '.');
      break;

    case warnprec:
      out_vprintf(pariErr, "Warning: increasing prec in %s; new prec = %ld",
                      ap);
      break;

    case warnfile:
      out_puts(pariErr, "Warning: failed to "),
      ch1 = va_arg(ap, char*);
      out_printf(pariErr, "%s: %s", ch1, va_arg(ap, char*));
      break;
  }
  va_end(ap);
  out_term_color(pariErr, c_NONE);
  out_putc(pariErr, '\n');
  pariErr->flush();
}
void
pari_sigint(const char *time_s)
{
  int recover=0;
  BLOCK_SIGALRM_START
  err_init();
  closure_err(0);
  err_init_msg(e_MISC, e_USER);
  out_puts(pariErr, "user interrupt after ");
  out_puts(pariErr, time_s);
  out_term_color(pariErr, c_NONE);
  pariErr->flush();
  if (cb_pari_handle_exception)
    recover = cb_pari_handle_exception(-1);
  if (!recover && !block)
    PARI_SIGINT_pending = 0;
  BLOCK_SIGINT_END
  if (!recover) err_recover(e_MISC);
}

#define retmkerr2(x,y)\
  do { GEN _v = cgetg(3, t_ERROR);\
       _v[1] = (x);\
       gel(_v,2) = (y); return _v; } while(0)
#define retmkerr3(x,y,z)\
  do { GEN _v = cgetg(4, t_ERROR);\
       _v[1] = (x);\
       gel(_v,2) = (y);\
       gel(_v,3) = (z); return _v; } while(0)
#define retmkerr4(x,y,z,t)\
  do { GEN _v = cgetg(5, t_ERROR);\
       _v[1] = (x);\
       gel(_v,2) = (y);\
       gel(_v,3) = (z);\
       gel(_v,4) = (t); return _v; } while(0)
#define retmkerr5(x,y,z,t,u)\
  do { GEN _v = cgetg(6, t_ERROR);\
       _v[1] = (x);\
       gel(_v,2) = (y);\
       gel(_v,3) = (z);\
       gel(_v,4) = (t);\
       gel(_v,5) = (u); return _v; } while(0)
#define retmkerr6(x,y,z,t,u,v)\
  do { GEN _v = cgetg(7, t_ERROR);\
       _v[1] = (x);\
       gel(_v,2) = (y);\
       gel(_v,3) = (z);\
       gel(_v,4) = (t);\
       gel(_v,5) = (u);\
       gel(_v,6) = (v); return _v; } while(0)

static GEN
pari_err2GEN(pari_long numerr, va_list ap)
{
  switch ((enum err_list) numerr)
  {
  case e_SYNTAX:
    {
      const char *msg = va_arg(ap, char*);
      const char *s = va_arg(ap,char *);
      const char *entry = va_arg(ap,char *);
      retmkerr3(numerr,strtoGENstr(msg), mkvecsmall2((pari_long)s,(pari_long)entry));
    }
  case e_MISC: case e_ALARM:
    {
      const char *ch1 = va_arg(ap, char*);
      retmkerr2(numerr, gvsprintf(ch1,ap));
    }
  case e_NOTFUNC:
  case e_USER:
    retmkerr2(numerr,va_arg(ap, GEN));
  case e_FILE:
    {
      const char *f = va_arg(ap, const char*);
      retmkerr3(numerr, strtoGENstr(f), strtoGENstr(va_arg(ap, char*)));
    }
  case e_OVERFLOW:
  case e_IMPL:
  case e_DIM:
  case e_CONSTPOL:
  case e_ROOTS0:
  case e_FLAG:
  case e_PREC:
  case e_BUG:
  case e_ARCH:
  case e_PACKAGE:
    retmkerr2(numerr, strtoGENstr(va_arg(ap, char*)));
  case e_MODULUS:
  case e_VAR:
    {
      const char *f = va_arg(ap, const char*);
      GEN x = va_arg(ap, GEN);
      GEN y = va_arg(ap, GEN);
      retmkerr4(numerr, strtoGENstr(f), x,y);
    }
  case e_INV:
  case e_IRREDPOL:
  case e_PRIME:
  case e_SQRTN:
  case e_TYPE:
    {
      const char *f = va_arg(ap, const char*);
      GEN x = va_arg(ap, GEN);
      retmkerr3(numerr, strtoGENstr(f), x);
    }
  case e_COPRIME: case e_OP: case e_TYPE2:
    {
      const char *f = va_arg(ap, const char*);
      GEN x = va_arg(ap, GEN);
      GEN y = va_arg(ap, GEN);
      retmkerr4(numerr,strtoGENstr(f),x,y);
    }
  case e_COMPONENT:
    {
      const char *f= va_arg(ap, const char *);
      const char *op = va_arg(ap, const char *);
      GEN l = va_arg(ap, GEN);
      GEN x = va_arg(ap, GEN);
      retmkerr5(numerr,strtoGENstr(f),strtoGENstr(op),l,x);
    }
  case e_DOMAIN:
    {
      const char *f = va_arg(ap, const char*);
      const char *v = va_arg(ap, const char *);
      const char *op = va_arg(ap, const char *);
      GEN l = va_arg(ap, GEN);
      GEN x = va_arg(ap, GEN);
      retmkerr6(numerr,strtoGENstr(f),strtoGENstr(v),strtoGENstr(op),l,x);
    }
  case e_PRIORITY:
    {
      const char *f = va_arg(ap, const char*);
      GEN x = va_arg(ap, GEN);
      const char *op = va_arg(ap, const char *);
      pari_long v = va_arg(ap, pari_long);
      retmkerr5(numerr,strtoGENstr(f),x,strtoGENstr(op),stoi(v));
    }
  case e_MAXPRIME:
    retmkerr2(numerr, utoi(va_arg(ap, ulong)));
  case e_STACK:
    return err_e_STACK;
  default:
    return mkerr(numerr);
  }
}

static char *
type_dim(GEN x)
{
  char *v = stack_malloc(64);
  switch(typ(x))
  {
    case t_MAT:
    {
      pari_long l = lg(x), r = (l == 1)? 1: lgcols(x);
      sprintf(v, "t_MAT (%I64dx%I64d)", r-1,l-1);
      break;
    }
    case t_COL:
      sprintf(v, "t_COL (%I64d elts)", lg(x)-1);
      break;
    case t_VEC:
      sprintf(v, "t_VEC (%I64d elts)", lg(x)-1);
      break;
    default:
      v = (char*)type_name(typ(x));
  }
  return v;
}

char *
pari_err2str(GEN e)
{
  pari_long numerr = err_get_num(e);
  switch ((enum err_list) numerr)
  {
  case e_ALARM:
    return pari_sprintf("alarm interrupt after %Ps.",gel(e,2));
  case e_MISC:
    return pari_sprintf("%Ps.",gel(e,2));

  case e_ARCH:
    return pari_sprintf("sorry, '%Ps' not available on this system.",gel(e,2));
  case e_BUG:
    return pari_sprintf("bug in %Ps, please report.",gel(e,2));
  case e_CONSTPOL:
    return pari_sprintf("constant polynomial in %Ps.", gel(e,2));
  case e_COPRIME:
    return pari_sprintf("elements not coprime in %Ps:\n    %Ps\n    %Ps",
                        gel(e,2), gel(e,3), gel(e,4));
  case e_DIM:
    return pari_sprintf("inconsistent dimensions in %Ps.", gel(e,2));
  case e_FILE:
    return pari_sprintf("error opening %Ps: `%Ps'.", gel(e,2), gel(e,3));
  case e_FLAG:
    return pari_sprintf("invalid flag in %Ps.", gel(e,2));
  case e_IMPL:
    return pari_sprintf("sorry, %Ps is not yet implemented.", gel(e,2));
  case e_PACKAGE:
    return pari_sprintf("package %Ps is required, please install it.", gel(e,2));
  case e_INV:
    return pari_sprintf("impossible inverse in %Ps: %Ps.", gel(e,2), gel(e,3));
  case e_IRREDPOL:
    return pari_sprintf("not an irreducible polynomial in %Ps: %Ps.",
                        gel(e,2), gel(e,3));
  case e_MAXPRIME:
    {
      const char * msg = "not enough precomputed primes";
      ulong c = itou(gel(e,2));
      if (c) return pari_sprintf("%s, need primelimit ~ %lu.",msg, c);
      else   return pari_strdup(msg);
    }
  case e_MEM:
    return pari_strdup("not enough memory");
  case e_MODULUS:
    {
      GEN x = gel(e,3), y = gel(e,4);
      return pari_sprintf("inconsistent moduli in %Ps: %Ps != %Ps",
                          gel(e,2), x, y);
    }
  case e_NONE: return NULL;
  case e_NOTFUNC:
    return pari_strdup("not a function in function call");
  case e_OP: case e_TYPE2:
    {
      pari_sp av = avma;
      char *v;
      const char *f, *op = GSTR(gel(e,2));
      const char *what = numerr == e_OP? "inconsistent": "forbidden";
      GEN x = gel(e,3);
      GEN y = gel(e,4);
      switch(*op)
      {
      case '+': f = "addition"; break;
      case '*': f = "multiplication"; break;
      case '/': case '%': case '\\': f = "division"; break;
      case '=': op = "-->"; f = "assignment"; break;
      default:  f = op; op = ","; break;
      }
      v = pari_sprintf("%s %s %s %s %s.", what,f,type_dim(x),op,type_dim(y));
      avma = av; return v;
    }
  case e_COMPONENT:
    {
      const char *f= GSTR(gel(e,2));
      const char *op= GSTR(gel(e,3));
      GEN l = gel(e,4);
      if (!*f)
        return pari_sprintf("non-existent component: index %s %Ps",op,l);
      return pari_sprintf("non-existent component in %s: index %s %Ps",f,op,l);
    }
  case e_DOMAIN:
    {
      const char *f = GSTR(gel(e,2));
      const char *v = GSTR(gel(e,3));
      const char *op= GSTR(gel(e,4));
      GEN l = gel(e,5);
      if (!*op)
        return pari_sprintf("domain error in %s: %s out of range",f,v);
      return pari_sprintf("domain error in %s: %s %s %Ps",f,v,op,l);
    }
  case e_PRIORITY:
    {
      const char *f = GSTR(gel(e,2));
      pari_long vx = gvar(gel(e,3));
      const char *op= GSTR(gel(e,4));
      pari_long v = itos(gel(e,5));
      return pari_sprintf("incorrect priority in %s: variable %Ps %s %Ps",f,
             pol_x(vx), op, pol_x(v));
    }
  case e_OVERFLOW:
    return pari_sprintf("overflow in %Ps.", gel(e,2));
  case e_PREC:
    return pari_sprintf("precision too low in %Ps.", gel(e,2));
  case e_PRIME:
    return pari_sprintf("not a prime number in %Ps: %Ps.",
                        gel(e,2), gel(e,3));
  case e_ROOTS0:
    return pari_sprintf("zero polynomial in %Ps.", gel(e,2));
  case e_SQRTN:
    return pari_sprintf("not an n-th power residue in %Ps: %Ps.",
                        gel(e,2), gel(e,3));
  case e_STACK:
    {
      size_t d = top - bot;
      char *buf = (char *) pari_malloc(512*sizeof(char));
      sprintf(buf, "the PARI stack overflows !\n"
          "  current stack size: %I64u (%.3f Mbytes)\n"
          "  [hint] you can increase GP stack with allocatemem()\n",
          (ulong)d, (double)d/1048576.);
      return buf;
    }
  case e_SYNTAX:
    return pari_strdup(GSTR(gel(e,2)));
  case e_TYPE:
    return pari_sprintf("incorrect type in %Ps (%s).",
                        gel(e,2), type_name(typ(gel(e,3))));
  case e_USER:
    return pari_sprint0("user error: ", gel(e,2), f_RAW);
  case e_VAR:
    {
      GEN x = gel(e,3), y = gel(e,4);
      return pari_sprintf("inconsistent variables in %Ps, %Ps != %Ps.",
                          gel(e,2), pol_x(varn(x)), pol_x(varn(y)));
    }
  }
  return NULL; /*NOT REACHED*/
}

static void
pari_err_display(GEN err)
{
  pari_long numerr=err_get_num(err);
  if (numerr==e_SYNTAX)
  {
    const char *msg = GSTR(gel(err,2));
    const char *s     = (const char *) gmael(err,3,1);
    const char *entry = (const char *) gmael(err,3,2);
    print_errcontext(pariErr, msg, s, entry);
    return;
  }
  else
  {
    char *s = pari_err2str(err);
    err_init_msg(numerr, e_USER);
    pariErr->puts(s);
    if (numerr==e_NOTFUNC)
    {
      GEN fun = gel(err,2);
      if (gequalX(fun))
      {
        entree *ep = varentries[varn(fun)];
        const char *s = ep->name;
        if (cb_pari_whatnow) cb_pari_whatnow(pariErr,s,1);
      }
    }
    pari_free(s);
  }
}

void
pari_err(int numerr, ...)
{
  va_list ap;
  GEN E;

  va_start(ap,numerr);

  if (numerr)
    E = pari_err2GEN(numerr,ap);
  else
  {
    E = va_arg(ap,GEN);
    numerr = err_get_num(E);
  }
  global_err_data = E;
  if (*iferr_env) longjmp(*iferr_env, numerr);
  mt_err_recover(numerr);
  err_init();
  if (numerr != e_SYNTAX) closure_err(0);
  pari_err_display(E);
  out_term_color(pariErr, c_NONE);
  va_end(ap);
  pariErr->flush();
  if (cb_pari_handle_exception &&
      cb_pari_handle_exception(numerr)) return;
  err_recover(numerr);
}

GEN
pari_err_last(void) { return global_err_data; }

const char *
numerr_name(pari_long numerr)
{
  switch ((enum err_list) numerr)
  {
  case e_ALARM:    return "e_ALARM";
  case e_ARCH:     return "e_ARCH";
  case e_BUG:      return "e_BUG";
  case e_COMPONENT: return "e_COMPONENT";
  case e_CONSTPOL: return "e_CONSTPOL";
  case e_COPRIME:  return "e_COPRIME";
  case e_DIM:      return "e_DIM";
  case e_DOMAIN:   return "e_DOMAIN";
  case e_FILE:     return "e_FILE";
  case e_FLAG:     return "e_FLAG";
  case e_IMPL:     return "e_IMPL";
  case e_INV:      return "e_INV";
  case e_IRREDPOL: return "e_IRREDPOL";
  case e_MAXPRIME: return "e_MAXPRIME";
  case e_MEM:      return "e_MEM";
  case e_MISC:     return "e_MISC";
  case e_MODULUS:  return "e_MODULUS";
  case e_NONE:     return "e_NONE";
  case e_NOTFUNC:  return "e_NOTFUNC";
  case e_OP:       return "e_OP";
  case e_OVERFLOW: return "e_OVERFLOW";
  case e_PACKAGE:  return "e_PACKAGE";
  case e_PREC:     return "e_PREC";
  case e_PRIME:    return "e_PRIME";
  case e_PRIORITY: return "e_PRIORITY";
  case e_ROOTS0:   return "e_ROOTS0";
  case e_SQRTN:    return "e_SQRTN";
  case e_STACK:    return "e_STACK";
  case e_SYNTAX:   return "e_SYNTAX";
  case e_TYPE2:    return "e_TYPE2";
  case e_TYPE:     return "e_TYPE";
  case e_USER:     return "e_USER";
  case e_VAR:      return "e_VAR";
  }
  return "invalid error number";
}

pari_long
name_numerr(const char *s)
{
  if (!strcmp(s,"e_ALARM"))    return e_ALARM;
  if (!strcmp(s,"e_ARCH"))     return e_ARCH;
  if (!strcmp(s,"e_BUG"))      return e_BUG;
  if (!strcmp(s,"e_COMPONENT")) return e_COMPONENT;
  if (!strcmp(s,"e_CONSTPOL")) return e_CONSTPOL;
  if (!strcmp(s,"e_COPRIME"))  return e_COPRIME;
  if (!strcmp(s,"e_DIM"))      return e_DIM;
  if (!strcmp(s,"e_DOMAIN"))   return e_DOMAIN;
  if (!strcmp(s,"e_FILE"))     return e_FILE;
  if (!strcmp(s,"e_FLAG"))     return e_FLAG;
  if (!strcmp(s,"e_IMPL"))     return e_IMPL;
  if (!strcmp(s,"e_INV"))      return e_INV;
  if (!strcmp(s,"e_IRREDPOL")) return e_IRREDPOL;
  if (!strcmp(s,"e_MAXPRIME")) return e_MAXPRIME;
  if (!strcmp(s,"e_MEM"))      return e_MEM;
  if (!strcmp(s,"e_MISC"))     return e_MISC;
  if (!strcmp(s,"e_MODULUS"))  return e_MODULUS;
  if (!strcmp(s,"e_NONE"))     return e_NONE;
  if (!strcmp(s,"e_NOTFUNC"))  return e_NOTFUNC;
  if (!strcmp(s,"e_OP"))       return e_OP;
  if (!strcmp(s,"e_OVERFLOW")) return e_OVERFLOW;
  if (!strcmp(s,"e_PACKAGE"))  return e_PACKAGE;
  if (!strcmp(s,"e_PREC"))     return e_PREC;
  if (!strcmp(s,"e_PRIME"))    return e_PRIME;
  if (!strcmp(s,"e_PRIORITY")) return e_PRIORITY;
  if (!strcmp(s,"e_ROOTS0"))   return e_ROOTS0;
  if (!strcmp(s,"e_SQRTN"))    return e_SQRTN;
  if (!strcmp(s,"e_STACK"))    return e_STACK;
  if (!strcmp(s,"e_SYNTAX"))   return e_SYNTAX;
  if (!strcmp(s,"e_TYPE"))     return e_TYPE;
  if (!strcmp(s,"e_TYPE2"))    return e_TYPE2;
  if (!strcmp(s,"e_USER"))     return e_USER;
  if (!strcmp(s,"e_VAR"))      return e_VAR;
  pari_err(e_MISC,"unknown error name");
  return -1; /* NOT REACHED */
}

GEN
errname(GEN err)
{
  if (typ(err)!=t_ERROR) pari_err_TYPE("errname",err);
  return strtoGENstr(numerr_name(err_get_num(err)));
}

/* Try f (trapping error e), recover using r (break_loop, if NULL) */
GEN
trap0(const char *e, GEN r, GEN f)
{
  pari_long numerr = CATCH_ALL;
  GEN x;
  if (!e || !*e) numerr = CATCH_ALL;
  else numerr = name_numerr(e);
  if (!f) {
    pari_warn(warner,"default handlers are no pari_longer supported --> ignored");
    return gnil;
  }
  x = closure_trapgen(f, numerr);
  if (x == (GEN)1LL) x = r? closure_evalgen(r): gnil;
  return x;
}

/*******************************************************************/
/*                                                                */
/*                       CLONING & COPY                            */
/*                  Replicate an existing GEN                      */
/*                                                                 */
/*******************************************************************/
/* lontyp[tx] = 0 (non recursive type) or number of codewords for type tx */
const  pari_long lontyp[] = { 0,0,0,1,1,2,1,2,1,1, 2,2,0,1,1,1,1,1,1,1, 2,0,0,2,2 };

static GEN
list_internal_copy(GEN z, pari_long nmax)
{
  pari_long i, l;
  GEN a;
  if (!z) return NULL;
  l = lg(z);
  a = (GEN)pari_malloc((nmax+1) * sizeof(pari_long));
  for (i = 1; i < l; i++) gel(a,i) = gclone( gel(z,i) );
  a[0] = z[0]; return a;
}

static void
listassign(GEN x, GEN y)
{
  pari_long nmax = list_nmax(x);
  GEN L = list_data(x);
  if (!nmax && L) nmax = lg(L) + 32; /* not malloc'ed yet */
  list_nmax(y) = nmax;
  list_data(y) = list_internal_copy(L, nmax);
}

/* copy list on the PARI stack */
GEN
listcopy(GEN x)
{
  GEN y = listcreate(), L = list_data(x);
  if (L) list_data(y) = gcopy(L);
  return y;
}

GEN
gcopy(GEN x)
{
  pari_long tx = typ(x), lx, i;
  GEN y;
  switch(tx)
  { /* non recursive types */
    case t_INT: return signe(x)? icopy(x): gen_0;
    case t_REAL:
    case t_STR:
    case t_VECSMALL: return leafcopy(x);
    /* one more special case */
    case t_LIST: return listcopy(x);
  }
  y = cgetg_copy(x, &lx);
  if (lontyp[tx] == 1) i = 1; else { y[1] = x[1]; i = 2; }
  for (; i<lx; i++) gel(y,i) = gcopy(gel(x,i));
  return y;
}

/* as gcopy, but truncate to the first lx components if recursive type
 * [ leaves use their own lg ]. No checks. */
GEN
gcopy_lg(GEN x, pari_long lx)
{
  pari_long tx = typ(x), i;
  GEN y;
  switch(tx)
  { /* non recursive types */
    case t_INT: return signe(x)? icopy(x): gen_0;
    case t_REAL:
    case t_STR:
    case t_VECSMALL: return leafcopy(x);
    /* one more special case */
    case t_LIST: return listcopy(x);
  }
  y = cgetg(lx, tx);
  if (lontyp[tx] == 1) i = 1; else { y[1] = x[1]; i = 2; }
  for (; i<lx; i++) gel(y,i) = gcopy(gel(x,i));
  return y;
}

/* cf cgetg_copy: "allocate" (by updating first codeword only) for subsequent
 * copy of x, as if avma = *AVMA */
INLINE GEN
cgetg_copy_avma(GEN x, pari_long *plx, pari_sp *AVMA) {
  GEN z;
  *plx = lg(x);
  z = ((GEN)*AVMA) - *plx;
  z[0] = x[0] & (TYPBITS|LGBITS);
  *AVMA = (pari_sp)z; return z;
}
INLINE GEN
cgetlist_avma(pari_sp *AVMA)
{
  GEN y = ((GEN)*AVMA) - 3;
  y[0] = _evallg(3) | evaltyp(t_LIST);
  *AVMA = (pari_sp)y; return y;
}

/* copy x as if avma = *AVMA, update *AVMA */
GEN
gcopy_avma(GEN x, pari_sp *AVMA)
{
  pari_long i, lx, tx = typ(x);
  GEN y;

  switch(typ(x))
  { /* non recursive types */
    case t_INT:
      *AVMA = (pari_sp)icopy_avma(x, *AVMA);
      return (GEN)*AVMA;
    case t_REAL: case t_STR: case t_VECSMALL:
      *AVMA = (pari_sp)leafcopy_avma(x, *AVMA);
      return (GEN)*AVMA;

    /* one more special case */
    case t_LIST:
      y = cgetlist_avma(AVMA);
      listassign(x, y); return y;

    default:
      y = cgetg_copy_avma(x, &lx, AVMA);
      if (lontyp[tx] == 1) i = 1; else { y[1] = x[1]; i = 2; }
      for (; i<lx; i++) gel(y,i) = gcopy_avma(gel(x,i), AVMA);
  }
  return y;
}

/* [copy_bin/bin_copy:] same as gcopy_avma but use NULL to code an exact 0, and
 * make shallow copies of t_LISTs */
static GEN
gcopy_av0(GEN x, pari_sp *AVMA)
{
  pari_long i, lx, tx = typ(x);
  GEN y;

  switch(tx)
  { /* non recursive types */
    case t_INT:
      if (!signe(x)) return NULL; /* special marker */
      *AVMA = (pari_sp)icopy_avma(x, *AVMA);
      return (GEN)*AVMA;
    case t_REAL: case t_STR: case t_VECSMALL: case t_LIST:
      *AVMA = (pari_sp)leafcopy_avma(x, *AVMA);
      return (GEN)*AVMA;
    default:
      y = cgetg_copy_avma(x, &lx, AVMA);
      if (lontyp[tx] == 1) i = 1; else { y[1] = x[1]; i = 2; }
      for (; i<lx; i++) gel(y,i) = gcopy_av0(gel(x,i), AVMA);
  }
  return y;
}

INLINE GEN
icopy_avma_canon(GEN x, pari_sp AVMA)
{
  pari_long i, lx = lgefint(x);
  GEN y = ((GEN)AVMA) - lx;
  y[0] = evaltyp(t_INT)|evallg(lx); /* kills isclone */
  y[1] = x[1]; x = int_MSW(x);
  for (i=2; i<lx; i++, x = int_precW(x)) y[i] = *x;
  return y;
}

/* [copy_bin_canon/bin_copy_canon:] same as gcopy_av0, but copy integers in
 * canonical (native kernel) form and make a full copy of t_LISTs */
static GEN
gcopy_av0_canon(GEN x, pari_sp *AVMA)
{
  pari_long i, lx, tx = typ(x);
  GEN y;

  switch(tx)
  { /* non recursive types */
    case t_INT:
      if (!signe(x)) return NULL; /* special marker */
      *AVMA = (pari_sp)icopy_avma_canon(x, *AVMA);
      return (GEN)*AVMA;
    case t_REAL: case t_STR: case t_VECSMALL:
      *AVMA = (pari_sp)leafcopy_avma(x, *AVMA);
      return (GEN)*AVMA;

    /* one more special case */
    case t_LIST:
    {
      GEN y = cgetlist_avma(AVMA), z = list_data(x);
      if (z) {
        list_data(y) = gcopy_av0_canon(z, AVMA);
        list_nmax(y) = lg(z)-1;
      } else {
        list_data(y) = NULL;
        list_nmax(y) = 0;
      }
      return y;
    }
    default:
      y = cgetg_copy_avma(x, &lx, AVMA);
      if (lontyp[tx] == 1) i = 1; else { y[1] = x[1]; i = 2; }
      for (; i<lx; i++) gel(y,i) = gcopy_av0_canon(gel(x,i), AVMA);
  }
return y;
}

/* [copy_bin/bin_copy:] size (number of words) required for gcopy_av0(x) */
static pari_long
taille0(GEN x)
{
  pari_long i,n,lx, tx = typ(x);
  switch(tx)
  { /* non recursive types */
    case t_INT: return signe(x)? lgefint(x): 0;
    case t_REAL:
    case t_STR:
    case t_VECSMALL: return lg(x);

    /* one more special case */
    case t_LIST:
    {
      GEN L = list_data(x);
      return L? 3 + taille0(L): 3;
    }
    default:
      n = lx = lg(x);
      for (i=lontyp[tx]; i<lx; i++) n += taille0(gel(x,i));
      return n;
  }
}

/* [copy_bin/bin_copy:] size (number of words) required for gcopy_av0(x) */
static pari_long
taille0_nolist(GEN x)
{
  pari_long i,n,lx, tx = typ(x);
  switch(tx)
  { /* non recursive types */
    case t_INT:
      lx = lgefint(x);
      return lx == 2? 0: lx;
    case t_REAL:
    case t_STR:
    case t_VECSMALL:
    case t_LIST:
      return lg(x);
    default:
      n = lx = lg(x);
      for (i=lontyp[tx]; i<lx; i++) n += taille0_nolist(gel(x,i));
      return n;
  }
}

/* How many words do we need to allocate to copy x ? t_LIST is a special case
 * since list_data() is malloc'ed later, in list_internal_copy() */
static pari_long
words_to_allocate(GEN x)
{
  pari_long i,n,lx, tx = typ(x);
  switch(tx)
  { /* non recursive types */
    case t_INT: return lgefint(x);
    case t_REAL:
    case t_STR:
    case t_VECSMALL: return lg(x);

    case t_LIST: return 3;
    default:
      n = lx = lg(x);
      for (i=lontyp[tx]; i<lx; i++) n += words_to_allocate(gel(x,i));
      return n;
  }
}

pari_long
gsizeword(GEN x)
{
  GEN L;
  if (typ(x) != t_LIST) return words_to_allocate(x);
  /* For t_LIST, return the actual list size, words_to_allocate() is always 3 */
  L = list_data(x);
  return L? 3 + words_to_allocate(L): 3;
}
pari_long
gsizebyte(GEN x) { return gsizeword(x) * sizeof(pari_long); }

/* return a clone of x structured as a gcopy */
GENbin*
copy_bin(GEN x)
{
  pari_long t = taille0_nolist(x);
  GENbin *p = (GENbin*)pari_malloc(sizeof(GENbin) + t*sizeof(pari_long));
  pari_sp AVMA = (pari_sp)(GENbinbase(p) + t);
  p->canon = 0;
  p->len = t;
  p->x   = gcopy_av0(x, &AVMA);
  p->base= (GEN)AVMA; return p;
}

/* same, writing t_INT in canonical native form */
GENbin*
copy_bin_canon(GEN x)
{
  pari_long t = taille0(x);
  GENbin *p = (GENbin*)pari_malloc(sizeof(GENbin) + t*sizeof(pari_long));
  pari_sp AVMA = (pari_sp)(GENbinbase(p) + t);
  p->canon = 1;
  p->len = t;
  p->x   = gcopy_av0_canon(x, &AVMA);
  p->base= (GEN)AVMA; return p;
}

GEN
gclone(GEN x)
{
  pari_long i,lx,tx = typ(x), t = words_to_allocate(x);
  GEN y = newblock(t);
  switch(tx)
  { /* non recursive types */
    case t_INT:
      lx = lgefint(x);
      y[0] = evaltyp(t_INT)|evallg(lx);
      for (i=1; i<lx; i++) y[i] = x[i];
      break;
    case t_REAL:
    case t_STR:
    case t_VECSMALL:
      lx = lg(x);
      for (i=0; i<lx; i++) y[i] = x[i];
      break;

    /* one more special case */
    case t_LIST:
      y[0] = evaltyp(t_LIST)|_evallg(3);
      listassign(x, y);
      break;
    default: {
      pari_sp AVMA = (pari_sp)(y + t);
      lx = lg(x);
      y[0] = x[0];
      if (lontyp[tx] == 1) i = 1; else { y[1] = x[1]; i = 2; }
      for (; i<lx; i++) gel(y,i) = gcopy_avma(gel(x,i), &AVMA);
    }
  }
  setisclone(y); return y;
}

void
shiftaddress(GEN x, pari_long dec)
{
  pari_long i, lx, tx = typ(x);
  if (is_recursive_t(tx) && tx != t_LIST)
  {
    lx = lg(x);
    for (i=lontyp[tx]; i<lx; i++) {
      if (!x[i]) gel(x,i) = gen_0;
      else
      {
        x[i] += dec;
        shiftaddress(gel(x,i), dec);
      }
    }
  }
}

void
shiftaddress_canon(GEN x, pari_long dec)
{
  pari_long i, lx, tx = typ(x);
  switch(tx)
  { /* non recursive types */
    case t_INT: {
      GEN y;
      lx = lgefint(x); if (lx <= 3) return;
      y = x + 2;
      x = int_MSW(x);  if (x == y) return;
      while (x > y) { lswap(*x, *y); x = int_precW(x); y++; }
      break;
    }
    case t_REAL:
    case t_STR:
    case t_VECSMALL:
      break;

    /* one more special case */
    case t_LIST: {
      GEN Lx = list_data(x);
      if (Lx) {
        pari_sp av = avma;
        GEN L = (GEN)((pari_long)Lx+dec);
        shiftaddress_canon(L, dec);
        list_data(x) = list_internal_copy(L, lg(L)); avma = av;
      }
    }
    default:
      lx = lg(x);
      for (i=lontyp[tx]; i<lx; i++) {
        if (!x[i]) gel(x,i) = gen_0;
        else
        {
          x[i] += dec;
          shiftaddress_canon(gel(x,i), dec);
        }
      }
  }
}

/********************************************************************/
/**                                                                **/
/**                INSERT DYNAMIC OBJECT IN STRUCTURE              **/
/**                                                                **/
/********************************************************************/
GEN
obj_init(pari_long d, pari_long n)
{
  GEN S = cgetg(d+2, t_VEC);
  gel(S, d+1) = zerovec(n);
  return S;
}
/* insert O in S [last position] at position K, return it */
GEN
obj_insert(GEN S, pari_long K, GEN O)
{ return obj_insert_shallow(S, K, gclone(O)); }
/* as obj_insert. WITHOUT cloning (for libpari, when creating a *new* obj
 * from an existing one) */
GEN
obj_insert_shallow(GEN S, pari_long K, GEN O)
{
  GEN o, v = gel(S, lg(S)-1);
  if (typ(v) != t_VEC) pari_err_TYPE("obj_insert", S);
  o = gel(v,K);
  gel(v,K) = O; /*SIGINT: before unclone(o)*/
  if (isclone(o)) gunclone(o);
  return gel(v,K);
}

/* Does S [last position] contain data at position K ? Return it, or NULL */
GEN
obj_check(GEN S, pari_long K)
{
  GEN O, v = gel(S, lg(S)-1);
  if (typ(v) != t_VEC || K >= lg(v)) pari_err_TYPE("obj_check", S);
  O = gel(v,K); return isintzero(O)? NULL: O;
}

GEN
obj_checkbuild(GEN S, pari_long tag, GEN (*build)(GEN))
{
  GEN O = obj_check(S, tag);
  if (!O)
  { pari_sp av = avma; O = obj_insert(S, tag, build(S)); avma = av; }
  return O;
}

GEN
obj_checkbuild_prec(GEN S, pari_long tag, GEN (*build)(GEN, pari_long), pari_long prec)
{
  pari_sp av = avma;
  GEN w = obj_check(S, tag);
  if (w)
  {
    pari_long p = gprecision(w);
    if (p >= prec) return gprec_w(w, prec);
  }
  w = obj_insert(S, tag, build(S, prec));
  avma = av; return gcopy(w);
}

GEN
obj_checkbuild_padicprec(GEN S, pari_long tag, GEN (*build)(GEN, pari_long), pari_long prec)
{
  pari_sp av = avma;
  GEN w = obj_check(S, tag);
  if (w)
  {
    pari_long p = padicprec_relative(w);
    if (p >= prec) return gprec_w(w, prec);
  }
  w = obj_insert(S, tag, build(S, prec));
  avma = av; return gcopy(w);
}

/* Reset S [last position], freeing all clones */
void
obj_free(GEN S)
{
  GEN v = gel(S, lg(S)-1);
  pari_long i;
  if (typ(v) != t_VEC) pari_err_TYPE("obj_free", S);
  for (i = 1; i < lg(v); i++)
  {
    GEN o = gel(v,i);
    if (isclone(o)) gunclone(o);
    gel(v,i) = gen_0;
  }
}

/*******************************************************************/
/*                                                                 */
/*                         STACK MANAGEMENT                        */
/*                                                                 */
/*******************************************************************/
INLINE void
dec_gerepile(pari_sp *x, pari_sp av0, pari_sp av, pari_sp tetpil, size_t dec)
{
  if (*x < av && *x >= av0)
  { /* update address if in stack */
    if (*x < tetpil) *x += dec;
    else pari_err_BUG("gerepile, significant pointers lost");
  }
}

void
gerepileallsp(pari_sp av, pari_sp tetpil, int n, ...)
{
  const pari_sp av0 = avma;
  const size_t dec = av-tetpil;
  int i;
  va_list a; va_start(a, n);
  (void)gerepile(av,tetpil,NULL);
  for (i=0; i<n; i++) dec_gerepile((pari_sp*)va_arg(a,GEN*), av0,av,tetpil,dec);
}

/* Takes an array of pointers to GENs, of length n.
 * Cleans up the stack between av and tetpil, updating those GENs. */
void
gerepilemanysp(pari_sp av, pari_sp tetpil, GEN* gptr[], int n)
{
  const pari_sp av0 = avma;
  const size_t dec = av-tetpil;
  int i;
  (void)gerepile(av,tetpil,NULL);
  for (i=0; i<n; i++) dec_gerepile((pari_sp*)gptr[i], av0, av, tetpil, dec);
}

/* Takes an array of GENs (cast to pari_longs), of length n.
 * Cleans up the stack between av and tetpil, updating those GENs. */
void
gerepilecoeffssp(pari_sp av, pari_sp tetpil, pari_long *g, int n)
{
  const pari_sp av0 = avma;
  const size_t dec = av-tetpil;
  int i;
  (void)gerepile(av,tetpil,NULL);
  for (i=0; i<n; i++,g++) dec_gerepile((pari_sp*)g, av0, av, tetpil, dec);
}

static int
dochk_gerepileupto(GEN av, GEN x)
{
  pari_long i,lx,tx;
  if (!isonstack(x)) return 1;
  if (x > av)
  {
    pari_warn(warner,"bad object %Ps",x);
    return 0;
  }
  tx = typ(x);
  if (! is_recursive_t(tx)) return 1;

  lx = lg(x);
  for (i=lontyp[tx]; i<lx; i++)
    if (!dochk_gerepileupto(av, gel(x,i)))
    {
      pari_warn(warner,"bad component %ld in object %Ps",i,x);
      return 0;
    }
  return 1;
}
/* check that x and all its components are out of stack, or have been
 * created after av */
int
chk_gerepileupto(GEN x) { return dochk_gerepileupto(x, x); }

/* print stack between avma & av */
void
dbg_gerepile(pari_sp av)
{
  GEN x = (GEN)avma;
  while (x < (GEN)av)
  {
    const pari_long tx = typ(x), lx = lg(x);
    GEN *a;

    pari_printf(" [%ld] %Ps:", x - (GEN)avma, x);
    if (! is_recursive_t(tx)) { pari_putc('\n'); x += lx; continue; }
    a = (GEN*)x + lontyp[tx]; x += lx;
    for (  ; a < (GEN*)x; a++)
    {
      if (*a == gen_0)
        pari_puts("  gen_0");
      else if (*a == gen_1)
        pari_puts("  gen_1");
      else if (*a == gen_m1)
        pari_puts("  gen_m1");
      else if (*a == gen_2)
        pari_puts("  gen_2");
      else if (*a == gen_m2)
        pari_puts("  gen_m2");
      else if (*a == ghalf)
        pari_puts("  ghalf");
      else if (isclone(*a))
        pari_printf("  %Ps (clone)", *a);
      else
        pari_printf("  %Ps [%ld]", *a, *a - (GEN)avma);
      if (a+1 < (GEN*)x) pari_putc(',');
    }
    pari_printf("\n");
  }
}
void
dbg_gerepileupto(GEN q)
{
  err_printf("%Ps:\n", q);
  dbg_gerepile((pari_sp) (q+lg(q)));
}

GEN
gerepile(pari_sp av, pari_sp tetpil, GEN q)
{
  const size_t dec = av - tetpil;
  const pari_sp av0 = avma;
  GEN x, a;

  if (dec == 0) return q;
  if ((pari_long)dec < 0) pari_err(e_MISC,"lbot>ltop in gerepile");

  /* dec_gerepile(&q, av0, av, tetpil, dec), saving 1 comparison */
  if (q >= (GEN)av0 && q < (GEN)tetpil)
    q = (GEN) (((pari_sp)q) + dec);

  for (x = (GEN)av, a = (GEN)tetpil; a > (GEN)av0; ) *--x = *--a;
  avma = (pari_sp)x;
  while (x < (GEN)av)
  {
    const pari_long tx = typ(x), lx = lg(x);

    if (! is_recursive_t(tx)) { x += lx; continue; }
    a = x + lontyp[tx]; x += lx;
    for (  ; a < x; a++) dec_gerepile((pari_sp*)a, av0, av, tetpil, dec);
  }
  return q;
}

void
fill_stack(void)
{
  GEN x = ((GEN)bot);
  while (x < (GEN)avma) *x++ = 0xfefefefeULL;
}

void
debug_stack(void)
{
  GEN z;
  err_printf("bot=0x%lx\ttop=0x%lx\tavma=0x%lx\n", bot, top, avma);
  for (z = ((GEN)top)-1; z >= (GEN)avma; z--)
    err_printf("%p:\t0x%lx\t%lu\n",z,*z,*z);
}

void
setdebugvar(pari_long n) { DEBUGVAR=n; }

pari_long
getstack(void) { return top-avma; }

/*******************************************************************/
/*                                                                 */
/*                               timer_delay                             */
/*                                                                 */
/*******************************************************************/

#if defined(USE_CLOCK_GETTIME)
#include <time.h>
void
timer_start(pari_timer *T)
{
  struct timespec t;
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID,&t);
  T->us = t.tv_nsec / 1000;
  T->s  = t.tv_sec;
}
#elif defined(USE_GETRUSAGE)
# include <sys/time.h>
# include <sys/resource.h>
void
timer_start(pari_timer *T)
{
  struct rusage r;
  getrusage(RUSAGE_SELF,&r);
  T->us = r.ru_utime.tv_usec;
  T->s  = r.ru_utime.tv_sec;
}
#elif defined(USE_FTIME)

# include <sys/timeb.h>
void
timer_start(pari_timer *T)
{
  struct timeb t;
  ftime(&t);
  T->us = ((pari_long)t.millitm) * 1000;
  T->s  = t.time;
}

#else

static void
_get_time(pari_timer *T, pari_long Ticks, pari_long TickPerSecond)
{
  T->us = (pari_long) ((Ticks % TickPerSecond) * (1000000. / TickPerSecond));
  T->s  = Ticks / TickPerSecond;
}

# ifdef USE_TIMES
#  include <sys/times.h>
#  include <sys/time.h>
#  include <time.h>
void
timer_start(pari_timer *T)
{
# ifdef _SC_CLK_TCK
  pari_long tck = sysconf(_SC_CLK_TCK);
# else
  pari_long tck = CLK_TCK;
# endif
  struct tms t; times(&t);
  _get_time(T, t.tms_utime, tck);
}
# elif defined(WINCE)
void
timer_start(pari_timer *T)
{ _get_time(T, GetTickCount(), 1000); }
# else
#  include <time.h>
#  ifndef CLOCKS_PER_SEC
#   define CLOCKS_PER_SEC 1000000 /* may be false on YOUR system */
#  endif
void
timer_start(pari_timer *T)
{ _get_time(T, clock(), CLOCKS_PER_SEC); }
# endif
#endif

static pari_long
timer_aux(pari_timer *T, pari_timer *U)
{
  pari_long s = T->s, us = T->us; timer_start(U);
  return 1000 * (U->s - s) + (U->us - us + 500) / 1000;
}
/* return delay, reset timer */
pari_long
timer_delay(pari_timer *T) { return timer_aux(T, T); }
/* return delay, don't reset timer */
pari_long
timer_get(pari_timer *T) { pari_timer t; return timer_aux(T, &t); }

static void
timer_vprintf(pari_timer *T, const char *format, va_list args)
{
  out_puts(pariErr, "Time ");
  out_vprintf(pariErr, format,args);
  out_printf(pariErr, ": %ld\n", timer_delay(T));
  pariErr->flush();
}
void
timer_printf(pari_timer *T, const char *format, ...)
{
  va_list args; va_start(args, format);
  timer_vprintf(T, format, args);
  va_end(args);
}

pari_long
timer(void)  { static THREAD pari_timer T; return timer_delay(&T);}
pari_long
gettime(void)  { static THREAD pari_timer T; return timer_delay(&T);}

static THREAD pari_timer timer2_T, abstimer_T;
pari_long
timer2(void) {  return timer_delay(&timer2_T);}
void
msgtimer(const char *format, ...)
{
  va_list args; va_start(args, format);
  timer_vprintf(&timer2_T, format, args);
  va_end(args);
}
pari_long
getabstime(void)  { return timer_get(&abstimer_T);}

/*******************************************************************/
/*                                                                 */
/*                   FUNCTIONS KNOWN TO THE ANALYZER               */
/*                                                                 */
/*******************************************************************/
GEN
pari_version(void)
{
  const ulong mask = (1ULL<<PARI_VERSION_SHIFT) - 1;
  ulong major, minor, patch, n = paricfg_version_code;
  patch = n & mask; n >>= PARI_VERSION_SHIFT;
  minor = n & mask; n >>= PARI_VERSION_SHIFT;
  major = n;
  if (*paricfg_vcsversion) {
    const char *ver = paricfg_vcsversion;
    const char *s = strchr(ver, '-');
    char t[8];
    const pari_long len = s-ver;
    GEN v;
    if (!s || len > 6) pari_err_BUG("pari_version()"); /* paranoia */
    memcpy(t, ver, len); t[len] = 0;
    v = cgetg(6, t_VEC);
    gel(v,1) = utoi(major);
    gel(v,2) = utoi(minor);
    gel(v,3) = utoi(patch);
    gel(v,4) = stoi( atoi(t) );
    gel(v,5) = strtoGENstr(s+1);
    return v;
  } else {
    GEN v = cgetg(4, t_VEC);
    gel(v,1) = utoi(major);
    gel(v,2) = utoi(minor);
    gel(v,3) = utoi(patch);
    return v;
  }
}

/* List of GP functions:
 * generated from the description system.
 * ---------------------
 * Format (struct entree) :
 *   char *name    : name (under GP).
 *   ulong valence : (EpNEW, EpALIAS,EpVAR, EpINSTALL)|EpSTATIC
 *   void *value   : For PREDEFINED FUNCTIONS: C function to call.
 *                   For USER FUNCTIONS: pointer to defining data (block) =
 *                    entree*: NULL, list of entree (arguments), NULL
 *                    char*  : function text
 *   pari_long menu     : which help section do we belong to (See below).
 *   char *code    : argument list (See below).
 *   char *help    : short help text (init to NULL).
 *   void *pvalue  : push_val history.
 *   pari_long arity    : maximum number of arguments.
 *   entree *next  : next entree (init to NULL, used in hashing code).
 * menu:
 * -----
 *  1: Standard monadic or dyadic OPERATORS
 *  2: CONVERSIONS and similar elementary functions
 *  3: TRANSCENDENTAL functions
 *  4: NUMBER THEORETICAL functions
 *  5: Functions related to ELLIPTIC CURVES
 *  6: Functions related to general NUMBER FIELDS
 *  7: POLYNOMIALS and power series
 *  8: Vectors, matrices, LINEAR ALGEBRA and sets
 *  9: SUMS, products, integrals and similar functions
 *  10: GRAPHIC functions
 *  11: PROGRAMMING under GP
 *
 * code: describe function prototype. NULL = use valence instead.
 * -----
 * Arguments:
 *  I  closure whose value is ignored, like in for() loop
 *  E  closure whose value is used, like in sum() loop
 *  J  implicit function of arity 1, like in parsum() loop
 *  G  GEN
 *  L  pari_long
 *  V  lexical variable
 *  C  lexical context
 *  n  variable number
 *  W  GEN, which will be modified in place (for t_LIST)
 *  &  *GEN
 *  f  Fake *long (function requires it, but we don't use the resulting pari_long)
 *  p  real precision (prec for the C library)
 *  P  series precision (precdl for the C library)
 *  r  raw input (treated as a string without quotes).
 *     Quoted args are copied as strings. Stops at first unquoted ')' or ','.
 *     Special chars can be quoted using '\'.  Ex : aa"b\n)"c => "aab\n)c".
 *  s  expanded string. Example: Pi"x"2 yields "3.142x2".
 *     The unquoted components can be of any pari type (converted according to
 *     the current output format)
 *  E* any number of E
 *  s* any number of strings (see s)
 *  M  Mnemonic or a flag (converted to a pari_long); description follows
 *         after \n at the end of the argument description
 *  D  Has a default value. Format is "Dvalue,type," (the ending comma is
 *     mandatory). Ex: D0,L, (arg is pari_long, 0 by default).
 *     Special syntax:
 *       if type = G, &, r, s, I or V:  D[G&rsIV] all send NULL.
 *       if type = n: Dn sends -1.
 *       if type = &: argument must be prefixed by '&'.
 *
 *     The user-given args are read first, then completed by the defaults
 *
 * Return type (first char or immediately after 'x'): GEN by default, otherwise
 *  m Return GEN but is can point to the input (member function).
 *  l Return pari_long
 *  i Return int
 *  v Return void
 *
 * Syntax requirements:
 *  = Separator '=' required.
 ****************************************************************************
 */
#include "init.h"
#include "default.h"
