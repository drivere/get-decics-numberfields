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
#include "anal.h"
#include "parse.h"

/***************************************************************************
 **                                                                       **
 **                           Mnemonic codes parser                       **
 **                                                                       **
 ***************************************************************************/

/* TEMPLATE is assumed to be ";"-separated list of items.  Each item
 * may have one of the following forms: id=value id==value id|value id&~value.
 * Each id consists of alphanum characters, dashes and underscores.
 * IDs are case-sensitive.

 * ARG consists of several IDs separated by punctuation (and optional
 * whitespace).  Each modifies the return value in a "natural" way: an
 * ID from id=value should be the first in the sequence and sets RETVAL to
 * VALUE (and cannot be negated), ID from id|value bit-ORs RETVAL with
 * VALUE (and bit-ANDs RETVAL with ~VALUE if negated), ID from
 * id&~value behaves as if it were noid|value, ID from
 * id==value behaves the same as id=value, but should come alone.

 * For items of the form id|value and id&~value negated forms are
 * allowed: either when arg looks like no[-_]id, or when id looks like
 * this, and arg is not-negated. */

enum { A_ACTION_ASSIGN, A_ACTION_SET, A_ACTION_UNSET };
#define IS_ID(c)        (isalnum((int)c) || ((c) == '_') || ((c) == '-'))

long
eval_mnemonic(GEN str, const char *tmplate)
{
  pari_sp av=avma;
  ulong retval = 0;
  const char *etmplate = NULL;
  const char *arg;

  if (typ(str)==t_INT) return itos(str);
  if (typ(str)!=t_STR) pari_err_TYPE("eval_mnemonic",str);

  arg=GSTR(str);
  etmplate = strchr(tmplate, '\n');
  if (!etmplate)
    etmplate = tmplate + strlen(tmplate);

  while (1)
  {
    long numarg;
    const char *e, *id;
    const char *negated;                /* action found with 'no'-ID */
    int negate;                 /* Arg has 'no' prefix removed */
    ulong l, action = 0, first = 1, singleton = 0;
    char *buf, *inibuf;
    static char b[80];

    while (isspace((int)*arg)) arg++;
    if (!*arg)
      break;
    e = arg;
    while (IS_ID(*e)) e++;
    /* Now the ID is whatever is between arg and e. */
    l = e - arg;
    if (l >= sizeof(b))
      pari_err(e_MISC,"id too long in a stringified flag");
    if (!l)                             /* Garbage after whitespace? */
      pari_err(e_MISC,"a stringified flag does not start with an id");
    strncpy(b, arg, l);
    b[l] = 0;
    arg = e;
    e = inibuf = buf = b;
    while (('0' <= *e) && (*e <= '9'))
      e++;
    if (*e == 0)
      pari_err(e_MISC,"numeric id in a stringified flag");
    negate = 0;
    negated = NULL;
find:
    id = tmplate;
    while ((id = strstr(id, buf)) && id < etmplate)
    {
      if (IS_ID(id[l])) {       /* We do not allow abbreviations yet */
        id += l;                /* False positive */
        continue;
      }
      if ((id >= tmplate + 2) && (IS_ID(id[-1])))
      {
        const char *s = id;

        if ( !negate && s >= tmplate+3
            && ((id[-1] == '_') || (id[-1] == '-')) )
          s--;
        /* Check whether we are preceeded by "no" */
        if ( negate             /* buf initially started with "no" */
            || (s < tmplate+2) || (s[-1] != 'o') || (s[-2] != 'n')
            || (s >= tmplate+3 && IS_ID(s[-3]))) {
          id += l;              /* False positive */
          continue;
        }
        /* Found noID in the template! */
        id += l;
        negated = id;
        continue;               /* Try to find without 'no'. */
      }
      /* Found as is */
      id += l;
      break;
    }
    if ( !id && !negated && !negate
        && (l > 2) && buf[0] == 'n' && buf[1] == 'o' ) {
      /* Try to find the flag without the prefix "no". */
      buf += 2; l -= 2;
      if ((buf[0] == '_') || (buf[0] == '-')) { buf++; l--; }
      negate = 1;
      if (buf[0])
        goto find;
    }
    if (!id && negated) /* Negated and AS_IS forms, prefer AS_IS */
    {
      id = negated;     /* Otherwise, use negated form */
      negate = 1;
    }
    if (!id)
      pari_err(e_MISC,"Unrecognized id '%s' in a stringified flag", inibuf);
    if (singleton && !first)
      pari_err(e_MISC,"Singleton id non-single in a stringified flag");
    if (id[0] == '=') {
      if (negate)
        pari_err(e_MISC,"Cannot negate id=value in a stringified flag");
      if (!first)
        pari_err(e_MISC,"Assign action should be first in a stringified flag");
      action = A_ACTION_ASSIGN;
      id++;
      if (id[0] == '=') {
        singleton = 1;
        id++;
      }
    } else if (id[0] == '^') {
      if (id[1] != '~')
        pari_err(e_MISC, "Unrecognized action in a template");
      id += 2;
      if (negate)
        action = A_ACTION_SET;
      else
        action = A_ACTION_UNSET;
    } else if (id[0] == '|') {
      id++;
      if (negate)
        action = A_ACTION_UNSET;
      else
        action = A_ACTION_SET;
    }

    e = id;

    while ((*e >= '0' && *e <= '9')) e++;
    while (isspace((int)*e))
      e++;
    if (*e && (*e != ';') && (*e != ','))
      pari_err(e_MISC, "Non-numeric argument of an action in a template");
    numarg = atol(id);          /* Now it is safe to get it... */
    switch (action) {
    case A_ACTION_SET:
      retval |= numarg;
      break;
    case A_ACTION_UNSET:
      retval &= ~numarg;
      break;
    case A_ACTION_ASSIGN:
      retval = numarg;
      break;
    default:
      pari_err(e_MISC,"error in parse_option_string");
    }
    first = 0;
    while (isspace((int)*arg))
      arg++;
    if (*arg && !(ispunct((int)*arg) && *arg != '-'))
      pari_err(e_MISC,"Junk after an id in a stringified flag");
    /* Skip punctuation */
    if (*arg)
      arg++;
  }
  avma=av;
  return retval;
}

/*******************************************************************/
/*                                                                 */
/*                  SYNTACTICAL ANALYZER FOR GP                    */
/*                                                                 */
/*******************************************************************/
GEN
readseq(char *t)
{
  pari_sp av = avma;
  return gerepileupto(av, closure_evalres(pari_compile_str(t,0)));
}

/* filtered readseq = remove blanks and comments */
GEN
gp_read_str(const char *s)
{
  char *t = filtre(s, (compatible == OLDALL));
  GEN x = readseq(t);
  pari_free(t); return x;
}

GEN
compile_str(const char *s)
{
  char *t = filtre(s, (compatible == OLDALL));
  GEN x = pari_compile_str(t, 1);
  pari_free(t); return x;
}

static long
check_proto(const char *code)
{
  long arity = 0;
  const char *s = code, *old;
  if (*s == 'l' || *s == 'v' || *s == 'i' || *s == 'm') s++;
  while (*s && *s != '\n') switch (*s++)
  {
    case '&':
    case 'C':
    case 'G':
    case 'I':
    case 'J':
    case 'L':
    case 'M':
    case 'P':
    case 'W':
    case 'f':
    case 'n':
    case 'p':
    case 'r':
    case 'x':
      arity++;
      break;
    case 'E':
    case 's':
      if (*s == '*') s++;
      arity++;
      break;
    case 'D':
      if (*s == 'G' || *s == '&' || *s == 'n' || *s == 'I' || *s == 'E'
                    || *s == 'V' || *s == 'P' || *s == 's' || *s == 'r')
      {
        if (*s != 'V') arity++;
        s++; break;
      }
      old = s; while (*s && *s != ',') s++;
      if (*s != ',') pari_err(e_SYNTAX, "missing comma", old, code);
      break;
    case 'V':
    case '=':
    case ',': break;
    case '\n': break; /* Before the mnemonic */

    case 'm':
    case 'l':
    case 'i':
    case 'v': pari_err(e_SYNTAX, "this code has to come first", s-1, code);
    default: pari_err(e_SYNTAX, "unknown parser code", s-1, code);
  }
  if (arity > 20) pari_err_IMPL("functions with more than 20 parameters");
  return arity;
}

static entree *
installep(const char *name, long len, entree **table)
{
  const long add = 4*sizeof(long);
  entree *ep = (entree *) pari_calloc(sizeof(entree) + add + len+1);
  entree *ep1 = initial_value(ep);
  char *u = (char *) ep1 + add;
  ep->name    = u; strncpy(u, name,len); u[len]=0;
  ep->valence = EpNEW;
  ep->value   = NULL;
  ep->menu    = 0;
  ep->code    = NULL;
  ep->help    = NULL;
  ep->pvalue  = NULL;
  ep->arity   = 0;
  ep->next    = *table;
  return *table = ep;
}

entree *
install(void *f, const char *name, const char *code)
{
  long hash, arity;
  entree *ep = is_entry_intern(name, functions_hash, &hash);

  arity=check_proto(code);
  if (ep && ep->valence != EpNEW)
  {
    if (ep->valence != EpINSTALL)
      pari_err(e_MISC,"[install] identifier '%s' already in use", name);
    pari_warn(warner, "[install] updating '%s' prototype; module not reloaded", name);
    if (ep->code) pari_free((void*)ep->code);
  }
  else
  {
    const char *s = name;
    if (isalpha((int)*s))
      while (is_keyword_char(*++s)) /* empty */;
    if (*s) pari_err(e_SYNTAX,"not a valid identifier", s, name);
    if (!ep) ep = installep(name, strlen(name), functions_hash + hash);
    ep->value=f; ep->valence=EpINSTALL;
  }
  ep->code = pari_strdup(code);
  ep->arity=arity;
  return ep;
}

/* Kill ep, i.e free all memory it references, and reset to initial value */
void
kill0(const char *e)
{
  entree *ep = is_entry(e);
  if (!ep || EpSTATIC(ep)) pari_err(e_MISC,"can't kill that");
  freeep(ep);
  ep->valence = EpNEW;
  ep->value   = NULL;
  ep->pvalue  = NULL;
}

void
addhelp(const char *e, char *s)
{
  entree *ep = fetch_entry(e, strlen(e));
  if (ep->help && !EpSTATIC(ep)) pari_free((void*)ep->help);
  ep->help = pari_strdup(s);
}

GEN
type0(GEN x)
{
  const char *s = type_name(typ(x));
  return strtoGENstr(s);
}

/*******************************************************************/
/*                                                                 */
/*                              PARSER                             */
/*                                                                 */
/*******************************************************************/

#ifdef LONG_IS_64BIT
static const long MAX_DIGITS = 19;
#else
static const long MAX_DIGITS = 9;
#endif

static ulong
number(int *n, const char **s)
{
  ulong m = 0;
  for (*n = 0; *n < MAX_DIGITS && isdigit((int)**s); (*n)++,(*s)++)
    m = 10*m + (**s - '0');
  return m;
}

ulong
u_pow10(int n)
{
  const ulong pw10[] = {
    1UL
    ,10UL
    ,100UL
    ,1000UL
    ,10000UL
    ,100000UL
    ,1000000UL
    ,10000000UL
    ,100000000UL
    ,1000000000UL
#ifdef LONG_IS_64BIT
    ,10000000000UL
    ,100000000000UL
    ,1000000000000UL
    ,10000000000000UL
    ,100000000000000UL
    ,1000000000000000UL
    ,10000000000000000UL
    ,100000000000000000UL
    ,1000000000000000000UL
    ,10000000000000000000UL
#endif
  };
  return pw10[n];
}

static GEN
int_read_more(GEN y, const char **ps)
{
  pari_sp av = avma;
  int i = 0, nb;
  while (isdigit((int)**ps))
  {
    ulong m = number(&nb, ps);
    if (avma != av && ++i > 4) { avma = av; i = 0; } /* HACK gerepile */
    y = addumului(m, u_pow10(nb), y);
  }
  return y;
}

static long
exponent(const char **pts)
{
  const char *s = *pts;
  long n;
  int nb;
  switch(*++s)
  {
    case '-': s++; n = -(long)number(&nb, &s); break;
    case '+': s++; /* Fall through */
    default: n = (long)number(&nb, &s);
  }
  *pts = s; return n;
}

static GEN
real_0_digits(long n) {
  long b = (n > 0)? (long)(n/LOG10_2): (long)-((-n)/LOG10_2 + 1);
  return real_0_bit(b);
}

static GEN
real_read(pari_sp av, const char **s, GEN y, long prec)
{
  long l, n = 0;
  switch(**s)
  {
    default: return y; /* integer */
    case '.':
    {
      const char *old = ++*s;
      if (isalpha((int)**s) || **s=='.')
      {
        if (**s == 'E' || **s == 'e') {
          n = exponent(s);
          if (!signe(y)) { avma = av; return real_0_digits(n); }
          break;
        }
        --*s; return y; /* member */
      }
      y = int_read_more(y, s);
      n = old - *s;
      if (**s != 'E' && **s != 'e')
      {
        if (!signe(y)) { avma = av; return real_0(prec); }
        break;
      }
    }
    /* Fall through */
    case 'E': case 'e':
      n += exponent(s);
      if (!signe(y)) { avma = av; return real_0_digits(n); }
  }
  l = nbits2prec(bit_accuracy(lgefint(y)));
  if (l < prec) l = prec; else prec = l;
  if (!n) return itor(y, prec);
  incrprec(l);
  y = itor(y, l);
  if (n > 0)
    y = mulrr(y, rpowuu(10UL, (ulong)n, l));
  else
    y = divrr(y, rpowuu(10UL, (ulong)-n, l));
  return gerepileuptoleaf(av, rtor(y, prec));
}

static GEN
int_read(const char **s)
{
  int nb;
  GEN y = utoi(number(&nb, s));
  if (nb == MAX_DIGITS) y = int_read_more(y, s);
  return y;
}

GEN
strtoi(const char *s) { return int_read(&s); }

GEN
strtor(const char *s, long prec)
{
  pari_sp av = avma;
  GEN y = int_read(&s);
  y = real_read(av, &s, y, prec);
  if (typ(y) == t_REAL) return y;
  return gerepileuptoleaf(av, itor(y, prec));
}

static void
skipdigits(char **lex) {
  while (isdigit((int)**lex)) ++*lex;
}

static int
skipexponent(char **lex)
{
  char *old=*lex;
  if ((**lex=='e' || **lex=='E'))
  {
    ++*lex;
    if ( **lex=='+' || **lex=='-' ) ++*lex;
    if (!isdigit((int)**lex))
    {
      *lex=old;
      return KINTEGER;
    }
    skipdigits(lex);
    return KREAL;
  }
  return KINTEGER;
}

static int
skipconstante(char **lex)
{
  skipdigits(lex);
  if (**lex=='.')
  {
    char *old = ++*lex;
    if (**lex == '.') { --*lex; return KINTEGER; }
    if (isalpha((int)**lex))
    {
      skipexponent(lex);
      if (*lex == old)
      {
        --*lex; /* member */
        return KINTEGER;
      }
      return KREAL;
    }
    skipdigits(lex);
    skipexponent(lex);
    return KREAL;
  }
  return skipexponent(lex);
}

static void
skipstring(char **lex)
{
  while (**lex)
  {
    while (**lex == '\\') *lex+=2;
    if (**lex == '"')
    {
      if ((*lex)[1] != '"') break;
      *lex += 2; continue;
    }
    (*lex)++;
  }
}

int
pari_lex(union token_value *yylval, struct node_loc *yylloc, char **lex)
{
  (void) yylval;
  yylloc->start=*lex;
  if (!**lex)
  {
    yylloc->end=*lex;
    return 0;
  }
  if (isalpha((int)**lex))
  {
    while (is_keyword_char(**lex)) ++*lex;
    yylloc->end=*lex;
    return KENTRY;
  }
  if (**lex=='"')
  {
    ++*lex;
    skipstring(lex);
    if (!**lex)
      compile_err("run-away string",*lex-1);
    ++*lex;
    yylloc->end=*lex;
    return KSTRING;
  }
  if (**lex == '.')
  {
    int token;
    if ((*lex)[1]== '.')
    {
      *lex+=2; yylloc->end = *lex; return KDOTDOT;
    }
    token=skipconstante(lex);
    if (token==KREAL)
    {
      yylloc->end = *lex;
      return token;
    }
    ++*lex;
    yylloc->end=*lex;
    return '.';
  }
  if (isdigit((int)**lex))
  {
    int token=skipconstante(lex);
    yylloc->end = *lex;
    return token;
  }
  if ((*lex)[1]=='=')
    switch (**lex)
    {
    case '=':
      if ((*lex)[2]=='=')
      { *lex+=3; yylloc->end = *lex; return KID; }
      else
      { *lex+=2; yylloc->end = *lex; return KEQ; }
    case '>':
      *lex+=2; yylloc->end = *lex; return KGE;
    case '<':
      *lex+=2; yylloc->end = *lex; return KLE;
    case '*':
      *lex+=2; yylloc->end = *lex; return KME;
    case '/':
      *lex+=2; yylloc->end = *lex; return KDE;
    case '%':
      if ((*lex)[2]=='=') break;
      *lex+=2; yylloc->end = *lex; return KMODE;
    case '!':
      if ((*lex)[2]=='=') break;
      *lex+=2; yylloc->end = *lex; return KNE;
    case '\\':
      *lex+=2; yylloc->end = *lex; return KEUCE;
    case '+':
      *lex+=2; yylloc->end = *lex; return KPE;
    case '-':
      *lex+=2; yylloc->end = *lex; return KSE;
    }
  if (**lex==')' && (*lex)[1]=='-' && (*lex)[2]=='>')
  {
    *lex+=3; yylloc->end = *lex; return KPARROW;
  }
  if (**lex=='-' && (*lex)[1]=='>')
  {
    *lex+=2; yylloc->end = *lex; return KARROW;
  }
  if (**lex=='<' && (*lex)[1]=='>')
  {
    *lex+=2; yylloc->end = *lex; return KNE;
  }
  if (**lex=='\\' && (*lex)[1]=='/')
    switch((*lex)[2])
    {
    case '=':
      *lex+=3; yylloc->end = *lex; return KDRE;
    default:
      *lex+=2; yylloc->end = *lex; return KDR;
    }
  if ((*lex)[1]==**lex)
    switch (**lex)
    {
    case '&':
      *lex+=2; yylloc->end = *lex; return KAND;
    case '|':
      *lex+=2; yylloc->end = *lex; return KOR;
    case '+':
      *lex+=2; yylloc->end = *lex; return KPP;
    case '-':
      *lex+=2; yylloc->end = *lex; return KSS;
    case '>':
      if ((*lex)[2]=='=') { *lex+=3; yylloc->end = *lex; return KSRE;}
      *lex+=2; yylloc->end = *lex; return KSR;
    case '<':
      if ((*lex)[2]=='=')
      { *lex+=3; yylloc->end = *lex; return KSLE; }
      *lex+=2; yylloc->end = *lex; return KSL;
    }
  yylloc->end = *lex+1;
  return (unsigned char) *(*lex)++;
}

/********************************************************************/
/**                                                                **/
/**                            STRINGS                             **/
/**                                                                **/
/********************************************************************/

/* return the first n0 chars of s as a GEN [s may not be 0-terminated] */
GEN
strntoGENstr(const char *s, long n0)
{
  long n = nchar2nlong(n0+1);
  GEN x = cgetg(n+1, t_STR);
  char *t = GSTR(x);
  strncpy(t, s, n0); t[n0] = 0; return x;
}

GEN
strtoGENstr(const char *s) { return strntoGENstr(s, strlen(s)); }

GEN
chartoGENstr(char c)
{
  GEN x = cgetg(2, t_STR);
  char *t = GSTR(x);
  t[0] = c; t[1] = 0; return x;
}
/********************************************************************/
/**                                                                **/
/**                   HASH TABLE MANIPULATIONS                     **/
/**                                                                **/
/********************************************************************/
/* return hashing value for identifier s */
static ulong
hashvalue(const char *s)
{
  ulong n = 0, c;
  while ( (c = (ulong)*s++) ) n = (n<<1) ^ c;
  return n % functions_tblsz;
}

static ulong
hashvalue_raw(const char *s, long len, ulong n)
{
  long i;
  for(i=0; i<len; i++) { n = (n<<1) ^ *s; s++; }
  return n % functions_tblsz;
}

/* Looking for entry in hashtable. ep1 is the cell's first element */
static entree *
findentry(const char *name, long len, entree *ep1)
{
  entree *ep;
  for (ep = ep1; ep; ep = ep->next)
    if (!strncmp(ep->name, name, len) && !(ep->name)[len]) return ep;
  return NULL; /* not found */
}

entree *
is_entry_intern(const char *s, entree **table, long *pthash)
{
  long hash = hashvalue(s);
  if (pthash) *pthash = hash;
  return findentry(s, strlen(s), table[hash]);
}

entree *
is_entry(const char *s)
{
  return is_entry_intern(s,functions_hash,NULL);
}

entree *
fetch_entry(const char *s, long len)
{
  entree **funhash = functions_hash + hashvalue_raw(s, len, 0);
  entree *ep = findentry(s, len, *funhash);
  if (ep) return ep;
  else return installep(s,len,funhash);
}

/* Assume s point somewhere in the code text, so s[-1]='.' and s[-2]>0
 * So many kludges, so little time */
entree *
fetch_member(const char *s, long len)
{
  entree **funhash = functions_hash+hashvalue_raw(s-1, len+1, '_');
  entree *ep;
  for (ep = *funhash; ep; ep = ep->next)
  {
    if (ep->name[0]!='_' || ep->name[1]!='.') continue;
    if (!strncmp(ep->name+2, s, len) && !(ep->name)[len+2]) break;
  }
  if (ep) return ep;
  ep=installep(s-2,len+2,funhash);
  ((char*)ep->name)[0]='_';
  return ep;
}

/********************************************************************/
/*                                                                  */
/*                Formal variables management                       */
/*                                                                  */
/********************************************************************/
static long max_avail; /* max variable not yet used */
static long nvar; /* first GP free variable */

void pari_var_init(void) {
  nvar = 0; max_avail = MAXVARN;
  (void)fetch_var();
  (void)fetch_named_var("x");
}
long pari_var_next(void) { return nvar; }
long pari_var_next_temp(void) { return max_avail; }
static long
pari_var_pop(long v)
{
  if (v != nvar-1) pari_err(e_MISC,"can't pop user variable %ld", v);
  return --nvar;
}
void
pari_var_create(entree *ep)
{
  GEN p = (GEN)initial_value(ep);
  long v;
  if (*p) return;
  if (nvar == max_avail) pari_err(e_MISC,"no more variables available");
  v = nvar++;
  /* set p = pol_x(v) */
  p[0] = evaltyp(t_POL) | _evallg(4);
  p[1] = evalsigne(1) | evalvarn(v);
  gel(p,2) = gen_0;
  gel(p,3) = gen_1;
  varentries[v] = ep;
}

long
delete_var(void)
{ /* user wants to delete one of his/her/its variables */
  if (max_avail == MAXVARN-1) return 0; /* nothing to delete */
  max_avail++; return max_avail+1;
}
long
fetch_var(void)
{
  if (nvar == max_avail) pari_err(e_MISC,"no more variables available");
  return max_avail--;
}

/* FIXE: obsolete, kept for backward compatibility */
long
manage_var(long n, entree *ep)
{
  switch(n) {
      case manage_var_init: pari_var_init(); return 0;
      case manage_var_next: return pari_var_next();
      case manage_var_max_avail: return pari_var_next_temp();
      case manage_var_pop: return pari_var_pop((long)ep);
      case manage_var_delete: return delete_var();
      case manage_var_create:
        pari_var_create(ep);
        return varn((GEN)initial_value(ep));
  }
  pari_err(e_MISC, "panic");
  return -1; /* not reached */
}

entree *
fetch_named_var(const char *s)
{
  entree **funhash = functions_hash + hashvalue(s);
  entree *ep = findentry(s, strlen(s), *funhash);
  if (!ep) ep = installep(s,strlen(s),funhash);
  else switch (EpVALENCE(ep))
  {
    case EpVAR: return ep;
    case EpNEW: break;
    default: pari_err(e_MISC, "%s already exists with incompatible valence", s);
  }
  pari_var_create(ep);
  ep->valence=EpVAR;
  ep->value=initial_value(ep);
  return ep;
}

long
fetch_user_var(const char *s)
{
  return varn((GEN)initial_value(fetch_named_var(s)) );
}

GEN
fetch_var_value(long vx, GEN t)
{
  entree *ep = varentries[vx];
  long vn;
  if (!ep) return NULL;
  if (!t)  return (GEN) ep->value;
  vn=localvars_find(t,ep);
  if (vn) return get_lex(vn);
  return (GEN) ep->value;
}

void
name_var(long n, const char *s)
{
  entree *ep;
  char *u;

  if (n < pari_var_next())
    pari_err(e_MISC, "renaming a GP variable is forbidden");
  if (n > (long)MAXVARN)
    pari_err_OVERFLOW("variable number");

  ep = (entree*)pari_malloc(sizeof(entree) + strlen(s) + 1);
  u = (char *)initial_value(ep);
  ep->valence = EpVAR;
  ep->name = u; strcpy(u,s);
  ep->value = gen_0; /* in case geval is called */
  if (varentries[n]) pari_free(varentries[n]);
  varentries[n] = ep;
}

GEN
gpolvar(GEN x)
{
  long v;
  if (!x) {
    long k = 1, n = pari_var_next();
    GEN z = cgetg(n+1, t_VEC);
    for (v = 0; v < n; v++)
    {
      entree *ep = varentries[v];
      if (ep && ep->name[0] != '_') gel(z,k++) = (GEN)initial_value(ep);
    }
    if (k <= n) {
      setlg(z,k);
      stackdummy((pari_sp)(z+n), (pari_sp)(z+k));
    }
    return z;
  }
  if (typ(x)==t_PADIC) return gcopy( gel(x,2) );
  v = gvar(x);
  if (v==NO_VARIABLE) return gen_0;
  return pol_x(v);
}

static void
fill_hashtable_single(entree **table, entree *ep)
{
  long n = hashvalue(ep->name);
  EpSETSTATIC(ep);
  ep->next = table[n]; table[n] = ep;
  if (ep->code) ep->arity=check_proto(ep->code);
  ep->pvalue = NULL;
}

void
pari_fill_hashtable(entree **table, entree *ep)
{
  for ( ; ep->name; ep++) fill_hashtable_single(table, ep);
}

void
pari_add_function(entree *ep)
{
  fill_hashtable_single(functions_hash, ep);
}

/********************************************************************/
/**                                                                **/
/**                        SIMPLE GP FUNCTIONS                     **/
/**                                                                **/
/********************************************************************/

#define ALIAS(ep) (entree *) ((GEN)ep->value)[1]

entree *
do_alias(entree *ep)
{
  while (ep->valence == EpALIAS) ep = ALIAS(ep);
  return ep;
}

void
alias0(const char *s, const char *old)
{
  entree *ep, *e;
  GEN x;

  ep = fetch_entry(old,strlen(old));
  e  = fetch_entry(s,strlen(s));
  if (EpVALENCE(e) != EpALIAS && EpVALENCE(e) != EpNEW)
    pari_err(e_MISC,"can't replace an existing symbol by an alias");
  freeep(e);
  x = newblock(2); x[0] = evaltyp(t_STR)|_evallg(2); /* for getheap */
  gel(x,1) = (GEN)ep;
  e->value=x; e->valence=EpALIAS;
}

GEN
ifpari(GEN g, GEN a/*closure*/, GEN b/*closure*/)
{
  if (gequal0(g)) /* false */
    return b?closure_evalgen(b):gnil;
  else /* true */
    return a?closure_evalgen(a):gnil;
}

void
ifpari_void(GEN g, GEN a/*closure*/, GEN b/*closure*/)
{
  if (gequal0(g)) /* false */
  {
    if(b) closure_evalvoid(b);
  }
  else /* true */
  {
    if(a) closure_evalvoid(a);
  }
}

GEN
ifpari_multi(GEN g, GEN a/*closure*/)
{
  long i, nb = lg(a)-1;
  if (!gequal0(g)) /* false */
    return closure_evalgen(gel(a,1));
  for(i=2;i<nb;i+=2)
  {
    GEN g = closure_evalgen(gel(a,i));
    if (!g) return g;
    if (!gequal0(g))
      return closure_evalgen(gel(a,i+1));
  }
  return i<=nb? closure_evalgen(gel(a,i)): gnil;
}

GEN
andpari(GEN a, GEN b/*closure*/)
{
  GEN g;
  if (gequal0(a))
    return gen_0;
  g=closure_evalgen(b);
  if (!g) return g;
  return gequal0(g)?gen_0:gen_1;
}

GEN
orpari(GEN a, GEN b/*closure*/)
{
  GEN g;
  if (!gequal0(a))
    return gen_1;
  g=closure_evalgen(b);
  if (!g) return g;
  return gequal0(g)?gen_0:gen_1;
}

GEN gmule(GEN *x, GEN y)
{
  *x=gmul(*x,y);
  return *x;
}

GEN gdive(GEN *x, GEN y)
{
  *x=gdiv(*x,y);
  return *x;
}

GEN gdivente(GEN *x, GEN y)
{
  *x=gdivent(*x,y);
  return *x;
}

GEN gdivrounde(GEN *x, GEN y)
{
  *x=gdivround(*x,y);
  return *x;
}

GEN gmode(GEN *x, GEN y)
{
  *x=gmod(*x,y);
  return *x;
}

GEN gshiftle(GEN *x, long n)
{
  *x=gshift(*x,n);
  return *x;
}

GEN gshiftre(GEN *x, long n)
{
  *x=gshift(*x,-n);
  return *x;
}

GEN gadde(GEN *x, GEN y)
{
  *x=gadd(*x,y);
  return *x;
}

GEN gadd1e(GEN *x)
{
  *x=typ(*x)==t_INT?addis(*x,1):gaddgs(*x,1);
  return *x;
}

GEN gsube(GEN *x, GEN y)
{
  *x=gsub(*x,y);
  return *x;
}

GEN gsub1e(GEN *x)
{
  *x=typ(*x)==t_INT?subis(*x,1):gsubgs(*x,1);
  return *x;
}

GEN gshift_right(GEN x, long n) { return gshift(x,-n); }

/********************************************************************/
/**                                                                **/
/**            PRINT USER FUNCTION AND MEMBER FUNCTION             **/
/**                                                                **/
/********************************************************************/
static int
cmp_epname(void *E, GEN e, GEN f)
{
  (void)E;
  return strcmp(((entree*)e)->name, ((entree*)f)->name);
}

void
print_all_user_fun(int member)
{
  pari_sp av = avma;
  long iL = 0, lL = 1024;
  GEN L = cgetg(lL+1, t_VECSMALL);
  entree *ep;
  int i;
  for (i = 0; i < functions_tblsz; i++)
    for (ep = functions_hash[i]; ep; ep = ep->next)
    {
      const char *f;
      int is_member;
      if (EpVALENCE(ep) != EpVAR || typ((GEN)ep->value)!=t_CLOSURE) continue;
      f = ep->name;
      is_member = (f[0] == '_' && f[1] == '.');
      if (member != is_member) continue;

      if (iL >= lL)
      {
        GEN oL = L;
        long j;
        lL *= 2; L = cgetg(lL+1, t_VECSMALL);
        for (j = 1; j <= iL; j++) gel(L,j) = gel(oL,j);
      }
      L[++iL] = (long)ep;
    }
  if (iL)
  {
    setlg(L, iL+1);
    L = gen_sort(L, NULL, &cmp_epname);
    for (i = 1; i <= iL; i++)
    {
      ep = (entree*)L[i];
      pari_printf("%s =\n  %Ps\n\n", ep->name, ep->value);
    }
  }
  avma = av;
}
