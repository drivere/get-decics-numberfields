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

GEN
iferrpari(GEN a, GEN b, GEN c)
{
  GEN res;
  struct pari_evalstate state;
  evalstate_save(&state);
  pari_CATCH(CATCH_ALL)
  {
    GEN E;
    if (!b&&!c) return gnil;
    E = evalstate_restore_err(&state);
    if (c)
    {
      push_lex(E,c);
      res = closure_evalgen(c);
      pop_lex(1);
      if (gequal0(res))
        pari_err(0, E);
    }
    if (!b) return gnil;
    push_lex(E,b);
    res = closure_evalgen(b);
    pop_lex(1);
    return res;
  } pari_TRY {
    res = closure_evalgen(a);
  } pari_ENDCATCH;
  return res;
}

/********************************************************************/
/**                                                                **/
/**                        ITERATIONS                              **/
/**                                                                **/
/********************************************************************/

static void
forparii(GEN a, GEN b, GEN code)
{
  pari_sp av, av0 = avma;
  GEN aa;
  if (gcmp(b,a) < 0) return;
  b = gfloor(b);
  aa = a = setloop(a);
  av=avma;
  push_lex(a,code);
  while (gcmp(a,b) <= 0)
  {
    closure_evalvoid(code); if (loop_break()) break;
    a = get_lex(-1);
    if (a == aa)
    {
      a = incloop(a);
      if (a != aa) { set_lex(-1,a); aa = a; }
    }
    else
    { /* 'code' modified a ! Be careful (and slow) from now on */
      a = gaddgs(a,1);
      if (gc_needed(av,1))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"forparii");
        a = gerepileupto(av,a);
      }
      set_lex(-1,a);
    }
  }
  pop_lex(1);  avma = av0;
}

void
forpari(GEN a, GEN b, GEN code)
{
  pari_sp ltop=avma, av;
  if (typ(a) == t_INT) { forparii(a,b,code); return; }
  b = gcopy(b); /* Kludge to work-around the a+(a=2) bug */
  av=avma;
  push_lex(a,code);
  while (gcmp(a,b) <= 0)
  {
    closure_evalvoid(code); if (loop_break()) break;
    a = get_lex(-1); a = gaddgs(a,1);
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"forpari");
      a = gerepileupto(av,a);
    }
    set_lex(-1, a);
  }
  pop_lex(1); avma = ltop;
}

void
whilepari(GEN a, GEN b)
{
  pari_sp av = avma;
  for(;;)
  {
    GEN res = closure_evalnobrk(a);
    if (gequal0(res)) break;
    avma = av;
    closure_evalvoid(b); if (loop_break()) break;
  }
  avma = av;
}

void
untilpari(GEN a, GEN b)
{
  pari_sp av = avma;
  for(;;)
  {
    GEN res;
    closure_evalvoid(b); if (loop_break()) break;
    res = closure_evalnobrk(a);
    if (!gequal0(res)) break;
    avma = av;
  }
  avma = av;
}

static int negcmp(GEN x, GEN y) { return gcmp(y,x); }

void
forstep(GEN a, GEN b, GEN s, GEN code)
{
  long ss, i;
  pari_sp av, av0 = avma;
  GEN v = NULL;
  int (*cmp)(GEN,GEN);

  b = gcopy(b); av=avma;
  push_lex(a,code);
  if (is_vec_t(typ(s)))
  {
    v = s; s = gen_0;
    for (i=lg(v)-1; i; i--) s = gadd(s,gel(v,i));
  }
  ss = gsigne(s);
  if (!ss) pari_err_DOMAIN("forstep","step","=",gen_0,s);
  cmp = (ss > 0)? &gcmp: &negcmp;
  i = 0;
  while (cmp(a,b) <= 0)
  {
    closure_evalvoid(code); if (loop_break()) break;
    if (v)
    {
      if (++i >= lg(v)) i = 1;
      s = gel(v,i);
    }
    a = get_lex(-1); a = gadd(a,s);

    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"forstep");
      a = gerepileupto(av,a);
    }
    set_lex(-1,a);
  }
  pop_lex(1); avma = av0;
}

/* return good chunk size for sieve, 16 | chunk + 2 */
static ulong
optimize_chunk(ulong a, ulong b)
{
  /* TODO: Optimize size (surely < 512k to stay in L1 cache, but not so large */
  /* as to force recalculating too often). */
  /* Guesstimate: greater of sqrt(n) * lg(n) or 1M */
  ulong chunk = maxuu(0x100000, usqrt(b) * expu(b));
  ulong tmp = (b - a) / chunk + 1;

  if (tmp == 1)
    chunk = b - a + 16;
  else
    chunk = (b - a) / tmp + 15;
  /* Don't take up more than 2/3 of the stack */
  chunk = minuu(chunk, avma - stack_lim(avma, 2));
  /* ensure 16 | chunk + 2 */
  return (((chunk + 2)>>4)<<4) - 2;
}
static void
sieve_init(forprime_t *T, ulong a, ulong b)
{
  T->sieveb = b;
  T->chunk = optimize_chunk(a, b);
  T->sieve = (unsigned char*)stack_malloc(((T->chunk+2) >> 4) + 1);
  T->cache[0] = 0;
  /* >> 1 [only odds] + 3 [convert from bits to bytes] */
  T->a = a;
  T->end = minuu(a + T->chunk, b);
  T->pos = T->maxpos = 0;
}

static void
u_forprime_set_prime_table(forprime_t *T, ulong a)
{
  T->strategy = 1;
  if (a < 3)
  {
    T->p = 0;
    T->d = diffptr;
  }
  else
    T->p = init_primepointer_lt(a, &T->d);
}

/* Set p so that p + q the smallest integer = c (mod q) and > original p.
 * Assume 0 < c < q. Set p = 0 on overflow */
static void
arith_set(forprime_t *T)
{
  ulong r = T->p % T->q; /* 0 <= r <= min(p, q-1) */
  pari_sp av = avma;
  GEN d = adduu(T->p - r, T->c);
  if (T->c > r) d = subiu(d, T->q);
  /* d = c mod q,  d = c > r? p-r+c-q: p-r+c, so that
   *  d <= p  and  d+q = c>r? p-r+c  : p-r+c+q > p */
  T->p = itou_or_0(d); avma = av; /* d = 0 is impossible */
}

/* run through primes in arithmetic progression = c (mod q).
 * Assume (c,q)=1, 0 <= c < q */
int
u_forprime_arith_init(forprime_t *T, ulong a, ulong b, ulong c, ulong q)
{
  ulong maxp, maxp2;
  if (a > b || b < 2)
  {
    T->strategy = 1; /* paranoia */
    T->p = 0; /* empty */
    T->b = 0; /* empty */
    T->d = diffptr;
    return 0;
  }
  maxp = maxprime();
  if (q != 1 && c != 2 && odd(q)) {
    /* only allow *odd* primes. If c = 2, then p = 2 must be included :-( */
    if (!odd(c)) c += q;
    q <<= 1;
  }
  T->q = q;
  T->c = c;
  T->strategy = 0; /* unknown */
  T->sieve = NULL; /* unused for now */
  T->b = b;
  if (maxp >= b) { /* [a,b] \subset prime table */
    u_forprime_set_prime_table(T, a);
    return 1;
  }
  /* b > maxp */
  if (a >= maxp)
  {
    if (T->q == 1)
      T->p = a - 1;
    else
      arith_set(T);
  }
  else
    u_forprime_set_prime_table(T, a);

  maxp2 = (maxp & HIGHMASK)? 0 : maxp*maxp;
  /* FIXME: should sieve as well if q != 1, adapt sieve code */
  if (q != 1 || (maxp2 && maxp2 <= a)
             || T->b - maxuu(a,maxp) < maxp / expu(b))
  { if (!T->strategy) T->strategy = 3; }
  else
  { /* worth sieving */
#ifdef LONG_IS_64BIT
    const ulong UPRIME_MAX = 18446744073709551557UL;
#else
    const ulong UPRIME_MAX = 4294967291UL;
#endif
    ulong sieveb;
    if (b > UPRIME_MAX) b = UPRIME_MAX;
    sieveb = b;
    if (maxp2 && maxp2 < b) sieveb = maxp2;
    if (!T->strategy) T->strategy = 2;
    if (!odd(sieveb)) sieveb--;
    sieve_init(T, maxuu(maxp+2, a), sieveb);
  }
  return 1;
}

/* will run through primes in [a,b] */
int
u_forprime_init(forprime_t *T, ulong a, ulong b)
{ return u_forprime_arith_init(T, a,b, 0,1); }
/* now only run through primes <= c; assume c <= b above */
void
u_forprime_restrict(forprime_t *T, ulong c) { T->b = c; }

/* b = NULL: loop forever */
int
forprime_init(forprime_t *T, GEN a, GEN b)
{
  long lb;
  a = gceil(a); if (typ(a) != t_INT) pari_err_TYPE("forprime_init",a);
  if (signe(a) <= 0) a = gen_1;
  if (b)
  {
    b = gfloor(b);
    if (typ(b) != t_INT) pari_err_TYPE("forprime_init",b);
    if (signe(b) < 0 || cmpii(a,b) > 0)
    {
      T->strategy = 4; /* paranoia */
      T->bb = gen_0;
      T->pp = gen_0;
      return 0;
    }
    lb = lgefint(b);
  }
  else
    lb = lgefint(a) + 4;
  T->bb = b;
  T->pp = cgeti(lb);
  /* a, b are positive integers, a <= b */
  if (lgefint(a) == 3) /* lb == 3 implies b != NULL */
    return u_forprime_init(T, uel(a,2), lb == 3? uel(b,2): ULONG_MAX);
  T->strategy = 4;
  affii(subiu(a,1), T->pp);
  return 1;
}

/* assume a <= b <= maxprime()^2, a,b odd, sieve[n] corresponds to
 *   a+16*n, a+16*n+2, ..., a+16*n+14 (bits 0 to 7)
 * maxpos = index of last sieve cell. */
static void
sieve_block(ulong a, ulong b, ulong maxpos, unsigned char* sieve)
{
  ulong p = 2, lim = usqrt(b), sz = (b-a) >> 1;
  byteptr d = diffptr+1;
  (void)memset(sieve, 0, maxpos+1);
  for (;;)
  { /* p is odd */
    ulong k, r;
    NEXT_PRIME_VIADIFF(p, d); /* starts at p = 3 */
    if (p > lim) break;

    /* solve a + 2k = 0 (mod p) */
    r = a % p;
    if (r == 0)
      k = 0;
    else
    {
      k = p - r;
      if (odd(k)) k += p;
      k >>= 1;
    }
    /* m = a + 2k is the smallest odd m >= a, p | m */
    /* position n (corresponds to a+2n) is sieve[n>>3], bit n&7 */
    while (k <= sz) { sieve[k>>3] |= 1 << (k&7); k += p; /* 2k += 2p */ }
  }
}

/* T->cache is a 0-terminated list of primes, return the first one and
 * remove it from list. Most of the time the list contains a single prime */
static ulong
shift_cache(forprime_t *T)
{
  long i;
  T->p = T->cache[0];
  for (i = 1;; i++)  /* remove one prime from cache */
    if (! (T->cache[i-1] = T->cache[i]) ) break;
  return T->p;
}

ulong
u_forprime_next(forprime_t *T)
{
  if (T->strategy == 1)
  {
    for(;;)
    {
      if (!*(T->d))
      {
        T->strategy = T->sieve? 2: 3;
        if (T->q != 1) { arith_set(T); if (!T->p) return 0; }
        /* T->p possibly not a prime if q != 1 */
        break;
      }
      else
      {
        NEXT_PRIME_VIADIFF(T->p, T->d);
        if (T->p > T->b) return 0;
        if (T->q == 1 || T->p % T->q == T->c) return T->p;
      }
    }
  }
  if (T->strategy == 2)
  {
    ulong n;
    if (T->cache[0]) return shift_cache(T);
NEXT_CHUNK:
    for (n = T->pos; n < T->maxpos; n++)
      if (T->sieve[n] != 0xFF)
      {
        unsigned char mask = T->sieve[n];
        ulong p = T->a + (n<<4);
        long i = 0;
        T->pos = n;
        if (!(mask &  1)) T->cache[i++] = p;
        if (!(mask &  2)) T->cache[i++] = p+2;
        if (!(mask &  4)) T->cache[i++] = p+4;
        if (!(mask &  8)) T->cache[i++] = p+6;
        if (!(mask & 16)) T->cache[i++] = p+8;
        if (!(mask & 32)) T->cache[i++] = p+10;
        if (!(mask & 64)) T->cache[i++] = p+12;
        if (!(mask &128)) T->cache[i++] = p+14;
        T->cache[i] = 0;
        T->pos = n+1;
        return shift_cache(T);
      }
    /* n = T->maxpos, last cell: check p <= b */
    if (T->maxpos && n == T->maxpos && T->sieve[n] != 0xFF)
    {
      unsigned char mask = T->sieve[n];
      ulong p = T->a + (n<<4);
      long i = 0;
      T->pos = n;
      if (!(mask &  1) && p <= T->sieveb) T->cache[i++] = p;
      if (!(mask &  2) && p <= T->sieveb-2) T->cache[i++] = p+2;
      if (!(mask &  4) && p <= T->sieveb-4) T->cache[i++] = p+4;
      if (!(mask &  8) && p <= T->sieveb-6) T->cache[i++] = p+6;
      if (!(mask & 16) && p <= T->sieveb-8) T->cache[i++] = p+8;
      if (!(mask & 32) && p <= T->sieveb-10) T->cache[i++] = p+10;
      if (!(mask & 64) && p <= T->sieveb-12) T->cache[i++] = p+12;
      if (!(mask &128) && p <= T->sieveb-14) T->cache[i++] = p+14;
      if (i)
      {
        T->cache[i] = 0;
        T->pos = n+1;
        return shift_cache(T);
      }
    }

    if (T->end >= T->sieveb) /* done */
      T->strategy = 3;
    else
    { /* initialize next chunk */
      if (T->maxpos == 0)
        T->a |= 1; /* first time; ensure odd */
      else
        T->a = (T->end + 2) | 1;
      T->end = T->a + T->chunk; /* may overflow */
      if (T->end < T->a || T->end > T->sieveb) T->end = T->sieveb;
      /* end and a are odd; sieve[k] contains the a + 8*2k + (0,2,...,14).
       * The largest k is (end-a) >> 4 */
      T->pos = 0;
      T->maxpos = (T->end - T->a) >> 4;
      sieve_block(T->a, T->end, T->maxpos, T->sieve);
      goto NEXT_CHUNK;
    }
  }
  if (T->strategy == 3)
  {
    if (T->q == 1)
      T->p = unextprime(T->p + 1);
    else
    {
      do {
        T->p += T->q;
        if (T->p < T->q) return 0; /* overflow */
      } while (!uisprime(T->p));
    }
    if (!T->p) /* overflow ulong, switch to GEN */
      T->strategy = 4;
    else
    {
      if (T->p > T->b) return 0;
      return T->p;
    }
  }
  return 0; /* overflow */
}

GEN
forprime_next(forprime_t *T)
{
  pari_sp av;
  GEN p;
  if (T->strategy <= 3)
  {
    ulong q = u_forprime_next(T);
    if (q) { affui(q, T->pp); return T->pp; }
    /* failure */
    if (T->strategy <= 3) return NULL; /* we're done */
    /* overflow ulong, switch to GEN */
    affui(ULONG_MAX, T->pp); /* initialize */
  }
  av = avma;
  p = nextprime(addiu(T->pp, 1));
  if (T->bb && absi_cmp(p, T->bb) > 0) { avma = av; return NULL; }
  affii(p, T->pp); avma = av; return T->pp;
}

void
forprime(GEN a, GEN b, GEN code)
{
  pari_sp av = avma;
  forprime_t T;

  if (!forprime_init(&T, a,b)) { avma = av; return; }

  push_lex(T.pp,code);
  while(forprime_next(&T))
  {
    closure_evalvoid(code); if (loop_break()) break;
    /* p changed in 'code', complain */
    if (get_lex(-1) != T.pp)
      pari_err(e_MISC,"prime index read-only: was changed to %Ps", get_lex(-1));
  }
  pop_lex(1); avma = av;
}

int
forcomposite_init(forcomposite_t *C, GEN a, GEN b)
{
  pari_sp av = avma;
  a = gceil(a); if (typ(a)!=t_INT) pari_err_TYPE("forcomposite",a);
  if (b) {
    b = gfloor(b);if (typ(b)!=t_INT) pari_err_TYPE("forcomposite",b);
  }
  if (signe(a) < 0) pari_err_DOMAIN("forcomposite", "a", "<", gen_0, a);
  if (cmpiu(a, 4) < 0) a = utoipos(4);
  C->first = 1;
  if (!forprime_init(&C->T, a,b))
  {
    C->n = gen_1; /* in case caller forgets to check the return value */
    C->b = gen_0;
    avma = av; return 0;
  }
  C->n = setloop(a);
  C->b = b;
  C->p = NULL; return 1;
}

GEN
forcomposite_next(forcomposite_t *C)
{
  if (C->first) /* first call ever */
  {
    C->first = 0;
    C->p = forprime_next(&C->T);
  }
  else
    C->n = incloop(C->n);
  if (C->p)
  {
    if (cmpii(C->n, C->p) < 0) return C->n;
    C->n = incloop(C->n);
    /* n = p+1 */
    C->p = forprime_next(&C->T); /* nextprime(p) > n */
    if (C->p) return C->n;
  }
  if (!C->b || cmpii(C->n, C->b) <= 0) return C->n;
  return NULL;
}

void
forcomposite(GEN a, GEN b, GEN code)
{
  pari_sp av = avma;
  forcomposite_t T;
  GEN n;
  if (!forcomposite_init(&T,a,b)) return;
  push_lex(T.n,code);
  while((n = forcomposite_next(&T)))
  {
    closure_evalvoid(code); if (loop_break()) break;
    /* n changed in 'code', complain */
    if (get_lex(-1) != n)
      pari_err(e_MISC,"index read-only: was changed to %Ps", get_lex(-1));
  }
  pop_lex(1); avma = av;
}

void
fordiv(GEN a, GEN code)
{
  long i, l;
  pari_sp av2, av = avma;
  GEN t = divisors(a);

  push_lex(gen_0,code); l=lg(t); av2 = avma;
  for (i=1; i<l; i++)
  {
    set_lex(-1,gel(t,i));
    closure_evalvoid(code); if (loop_break()) break;
    avma = av2;
  }
  pop_lex(1); avma=av;
}

/* Embedded for loops:
 *   fl = 0: execute ch (a), where a = (ai) runs through all n-uplets in
 *     [m1,M1] x ... x [mn,Mn]
 *   fl = 1: impose a1 <= ... <= an
 *   fl = 2:        a1 <  ... <  an
 */
/* increment and return d->a [over integers]*/
static GEN
_next_i(forvec_t *d)
{
  long i = d->n;
  if (d->first) { d->first = 0; return (GEN)d->a; }
  for (;;) {
    if (cmpii(d->a[i], d->M[i]) < 0) {
      d->a[i] = incloop(d->a[i]);
      return (GEN)d->a;
    }
    d->a[i] = resetloop(d->a[i], d->m[i]);
    if (--i <= 0) return NULL;
  }
}
/* increment and return d->a [generic]*/
static GEN
_next(forvec_t *d)
{
  long i = d->n;
  if (d->first) { d->first = 0; return (GEN)d->a; }
  for (;;) {
    d->a[i] = gaddgs(d->a[i], 1);
    if (gcmp(d->a[i], d->M[i]) <= 0) return (GEN)d->a;
    d->a[i] = d->m[i];
    if (--i <= 0) return NULL;
  }
}

/* non-decreasing order [over integers] */
static GEN
_next_le_i(forvec_t *d)
{
  long i = d->n;
  if (d->first) { d->first = 0; return (GEN)d->a; }
  for (;;) {
    if (cmpii(d->a[i], d->M[i]) < 0)
    {
      d->a[i] = incloop(d->a[i]);
      /* m[i] < a[i] <= M[i] <= M[i+1] */
      while (i < d->n)
      {
        GEN t;
        i++;
        if (cmpii(d->a[i-1], d->a[i]) <= 0) continue;
        /* a[i] < a[i-1] <= M[i-1] <= M[i] */
        t = d->a[i-1]; if (cmpii(t, d->m[i]) < 0) t = d->m[i];
        d->a[i] = resetloop(d->a[i], t);/*a[i]:=max(a[i-1],m[i])*/
      }
      return (GEN)d->a;
    }
    d->a[i] = resetloop(d->a[i], d->m[i]);
    if (--i <= 0) return NULL;
  }
}
/* non-decreasing order [generic] */
static GEN
_next_le(forvec_t *d)
{
  long i = d->n;
  if (d->first) { d->first = 0; return (GEN)d->a; }
  for (;;) {
    d->a[i] = gaddgs(d->a[i], 1);
    if (gcmp(d->a[i], d->M[i]) <= 0)
    {
      while (i < d->n)
      {
        GEN c;
        i++;
        if (gcmp(d->a[i-1], d->a[i]) <= 0) continue;
        /* M[i] >= M[i-1] >= a[i-1] > a[i] */
        c = gceil(gsub(d->a[i-1], d->a[i]));
        d->a[i] = gadd(d->a[i], c);
        /* a[i-1] <= a[i] < M[i-1] + 1 => a[i] < M[i]+1 => a[i] <= M[i] */
      }
      return (GEN)d->a;
    }
    d->a[i] = d->m[i];
    if (--i <= 0) return NULL;
  }
}
/* strictly increasing order [over integers] */
static GEN
_next_lt_i(forvec_t *d)
{
  long i = d->n;
  if (d->first) { d->first = 0; return (GEN)d->a; }
  for (;;) {
    if (cmpii(d->a[i], d->M[i]) < 0)
    {
      d->a[i] = incloop(d->a[i]);
      /* m[i] < a[i] <= M[i] < M[i+1] */
      while (i < d->n)
      {
        pari_sp av;
        GEN t;
        i++;
        if (cmpii(d->a[i-1], d->a[i]) < 0) continue;
        av = avma;
        /* M[i] > M[i-1] >= a[i-1] */
        t = addis(d->a[i-1],1); if (cmpii(t, d->m[i]) < 0) t = d->m[i];
        d->a[i] = resetloop(d->a[i], t);/*a[i]:=max(a[i-1]+1,m[i]) <= M[i]*/
        avma = av;
      }
      return (GEN)d->a;
    }
    d->a[i] = resetloop(d->a[i], d->m[i]);
    if (--i <= 0) return NULL;
  }
}
/* strictly increasing order [generic] */
static GEN
_next_lt(forvec_t *d)
{
  long i = d->n;
  if (d->first) { d->first = 0; return (GEN)d->a; }
  for (;;) {
    d->a[i] = gaddgs(d->a[i], 1);
    if (gcmp(d->a[i], d->M[i]) <= 0)
    {
      while (i < d->n)
      {
        GEN c;
        i++;
        if (gcmp(d->a[i-1], d->a[i]) < 0) continue;
        /* M[i] > M[i-1] >= a[i-1] >= a[i] */
        c = addis(gfloor(gsub(d->a[i-1], d->a[i])), 1); /* > a[i-1] - a[i] */
        d->a[i] = gadd(d->a[i], c);
        /* a[i-1] < a[i] <= M[i-1] + 1 => a[i] < M[i]+1 => a[i] <= M[i] */
      }
      return (GEN)d->a;
    }
    d->a[i] = d->m[i];
    if (--i <= 0) return NULL;
  }
}
/* for forvec(v=[],) */
static GEN
_next_void(forvec_t *d)
{
  if (d->first) { d->first = 0; return (GEN)d->a; }
  return NULL;
}

/* Initialize minima (m) and maxima (M); guarantee M[i] - m[i] integer and
 *   if flag = 1: m[i-1] <= m[i] <= M[i] <= M[i+1]
 *   if flag = 2: m[i-1] <  m[i] <= M[i] <  M[i+1],
 * for all i */
int
forvec_init(forvec_t *d, GEN x, long flag)
{
  long i, tx = typ(x), l = lg(x), t = t_INT;
  if (!is_vec_t(tx)) pari_err_TYPE("forvec [not a vector]", x);
  d->first = 1;
  d->n = l - 1;
  d->a = (GEN*)cgetg(l,tx);
  d->m = (GEN*)cgetg(l,tx);
  d->M = (GEN*)cgetg(l,tx);
  if (l == 1) { d->next = &_next_void; return 1; }
  for (i = 1; i < l; i++)
  {
    GEN a, e = gel(x,i), m = gel(e,1), M = gel(e,2);
    tx = typ(e);
    if (! is_vec_t(tx) || lg(e)!=3)
      pari_err_TYPE("forvec [expected vector not of type [min,MAX]]",e);
    if (typ(m) != t_INT) t = t_REAL;
    if (i > 1) switch(flag)
    {
      case 1: /* a >= m[i-1] - m */
        a = gceil(gsub(d->m[i-1], m));
        if (typ(a) != t_INT) pari_err_TYPE("forvec",a);
        if (signe(a) > 0) m = gadd(m, a); else m = gcopy(m);
        break;
      case 2: /* a > m[i-1] - m */
        a = gfloor(gsub(d->m[i-1], m));
        if (typ(a) != t_INT) pari_err_TYPE("forvec",a);
        a = addis(a, 1);
        if (signe(a) > 0) m = gadd(m, a); else m = gcopy(m);
        break;
      default: m = gcopy(m);
        break;
    }
    M = gadd(m, gfloor(gsub(M,m))); /* ensure M-m is an integer */
    if (gcmp(m,M) > 0) { d->a = NULL; d->next = &_next; return 0; }
    d->m[i] = m;
    d->M[i] = M;
  }
  if (flag == 1) for (i = l-2; i >= 1; i--)
  {
    GEN M = d->M[i], a = gfloor(gsub(d->M[i+1], M));
    if (typ(a) != t_INT) pari_err_TYPE("forvec",a);
    /* M[i]+a <= M[i+1] */
    if (signe(a) < 0) d->M[i] = gadd(M, a);
  }
  else if (flag == 2) for (i = l-2; i >= 1; i--)
  {
    GEN M = d->M[i], a = gceil(gsub(d->M[i+1], M));
    if (typ(a) != t_INT) pari_err_TYPE("forvec",a);
    a = subiu(a, 1);
    /* M[i]+a < M[i+1] */
    if (signe(a) < 0) d->M[i] = gadd(M, a);
  }
  if (t == t_INT) {
    for (i = 1; i < l; i++) {
      d->a[i] = setloop(d->m[i]);
      if (typ(d->M[i]) != t_INT) d->M[i] = gfloor(d->M[i]);
    }
  } else {
    for (i = 1; i < l; i++) d->a[i] = d->m[i];
  }
  switch(flag)
  {
    case 0: d->next = t==t_INT? &_next_i:    &_next; break;
    case 1: d->next = t==t_INT? &_next_le_i: &_next_le; break;
    case 2: d->next = t==t_INT? &_next_lt_i: &_next_lt; break;
    default: pari_err_FLAG("forvec");
  }
  return 1;
}
GEN
forvec_next(forvec_t *d) { return d->next(d); }

void
forvec(GEN x, GEN code, long flag)
{
  pari_sp av = avma;
  forvec_t T;
  GEN v;
  if (!forvec_init(&T, x, flag)) { avma = av; return; }
  push_lex((GEN)T.a, code);
  while ((v = forvec_next(&T)))
  {
    closure_evalvoid(code);
    if (loop_break()) break;
  }
  pop_lex(1); avma = av;
}

/********************************************************************/
/**                                                                **/
/**                              SUMS                              **/
/**                                                                **/
/********************************************************************/

GEN
somme(GEN a, GEN b, GEN code, GEN x)
{
  pari_sp av, av0 = avma;
  GEN p1;

  if (typ(a) != t_INT) pari_err_TYPE("sum",a);
  if (!x) x = gen_0;
  if (gcmp(b,a) < 0) return gcopy(x);

  b = gfloor(b);
  a = setloop(a);
  av=avma;
  push_lex(a,code);
  for(;;)
  {
    p1 = closure_evalnobrk(code);
    x=gadd(x,p1); if (cmpii(a,b) >= 0) break;
    a = incloop(a);
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"sum");
      x = gerepileupto(av,x);
    }
    set_lex(-1,a);
  }
  pop_lex(1); return gerepileupto(av0,x);
}

GEN
suminf(void *E, GEN (*eval)(void *, GEN), GEN a, long prec)
{
  long fl, G;
  pari_sp av0 = avma, av;
  GEN p1,x = real_1(prec);

  if (typ(a) != t_INT) pari_err_TYPE("suminf",a);
  a = setloop(a);
  av = avma;
  fl=0; G = prec2nbits(prec) + 5;
  for(;;)
  {
    p1 = eval(E, a); x = gadd(x,p1); a = incloop(a);
    if (gequal0(p1) || gexpo(p1) <= gexpo(x)-G)
      { if (++fl==3) break; }
    else
      fl=0;
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"suminf");
      x = gerepileupto(av,x);
    }
  }
  return gerepileupto(av0, gaddgs(x,-1));
}
GEN
suminf0(GEN a, GEN code, long prec)
{ EXPR_WRAP(code, suminf(EXPR_ARG, a, prec)); }

GEN
sumdivexpr(GEN num, GEN code)
{
  pari_sp av = avma;
  GEN y = gen_0, t = divisors(num);
  long i, l = lg(t);

  push_lex(gen_0, code);
  for (i=1; i<l; i++)
  {
    set_lex(-1,gel(t,i));
    y = gadd(y, closure_evalnobrk(code));
  }
  pop_lex(1); return gerepileupto(av,y);
}
GEN
sumdivmultexpr(GEN num, GEN code)
{
  pari_sp av = avma;
  GEN y = gen_1, P,E;
  int isint = divisors_init(num, &P,&E);
  long i, l = lg(P);

  if (l == 1) { avma = av; return gen_1; }
  push_lex(gen_0, code);
  for (i=1; i<l; i++)
  {
    GEN p = gel(P,i), q = p, z = gen_1;
    long j, e = E[i];
    for (j = 1; j <= e; j++, q = isint?mulii(q, p): gmul(q,p))
    {
      set_lex(-1, q);
      z = gadd(z, closure_evalnobrk(code));
      if (j == e) break;
    }
    y = gmul(y, z);
  }
  pop_lex(1); return gerepileupto(av,y);
}

/********************************************************************/
/**                                                                **/
/**                           PRODUCTS                             **/
/**                                                                **/
/********************************************************************/

GEN
produit(GEN a, GEN b, GEN code, GEN x)
{
  pari_sp av, av0 = avma;
  GEN p1;

  if (typ(a) != t_INT) pari_err_TYPE("prod",a);
  if (!x) x = gen_1;
  if (gcmp(b,a) < 0) return gcopy(x);

  b = gfloor(b);
  a = setloop(a);
  av=avma;
  push_lex(a,code);
  for(;;)
  {
    p1 = closure_evalnobrk(code);
    x = gmul(x,p1); if (cmpii(a,b) >= 0) break;
    a = incloop(a);
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"prod");
      x = gerepileupto(av,x);
    }
    set_lex(-1,a);
  }
  pop_lex(1); return gerepileupto(av0,x);
}

GEN
prodinf(void *E, GEN (*eval)(void *, GEN), GEN a, long prec)
{
  pari_sp av0 = avma, av;
  long fl,G;
  GEN p1,x = real_1(prec);

  if (typ(a) != t_INT) pari_err_TYPE("prodinf",a);
  a = setloop(a);
  av = avma;
  fl=0; G = -prec2nbits(prec)-5;
  for(;;)
  {
    p1 = eval(E, a); if (gequal0(p1)) { x = p1; break; }
    x = gmul(x,p1); a = incloop(a);
    p1 = gsubgs(p1, 1);
    if (gequal0(p1) || gexpo(p1) <= G) { if (++fl==3) break; } else fl=0;
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"prodinf");
      x = gerepileupto(av,x);
    }
  }
  return gerepilecopy(av0,x);
}
GEN
prodinf1(void *E, GEN (*eval)(void *, GEN), GEN a, long prec)
{
  pari_sp av0 = avma, av;
  long fl,G;
  GEN p1,p2,x = real_1(prec);

  if (typ(a) != t_INT) pari_err_TYPE("prodinf1",a);
  a = setloop(a);
  av = avma;
  fl=0; G = -prec2nbits(prec)-5;
  for(;;)
  {
    p2 = eval(E, a); p1 = gaddgs(p2,1);
    if (gequal0(p1)) { x = p1; break; }
    x = gmul(x,p1); a = incloop(a);
    if (gequal0(p2) || gexpo(p2) <= G) { if (++fl==3) break; } else fl=0;
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"prodinf1");
      x = gerepileupto(av,x);
    }
  }
  return gerepilecopy(av0,x);
}
GEN
prodinf0(GEN a, GEN code, long flag, long prec)
{
  switch(flag)
  {
    case 0: EXPR_WRAP(code, prodinf (EXPR_ARG, a, prec));
    case 1: EXPR_WRAP(code, prodinf1(EXPR_ARG, a, prec));
  }
  pari_err_FLAG("prodinf");
  return NULL; /* not reached */
}

GEN
prodeuler(void *E, GEN (*eval)(void *, GEN), GEN a, GEN b, long prec)
{
  pari_sp av, av0 = avma;
  GEN x = real_1(prec), prime;
  forprime_t T;

  av = avma;
  if (!forprime_init(&T, a,b)) { avma = av; return x; }

  av = avma;
  while ( (prime = forprime_next(&T)) )
  {
    x = gmul(x, eval(E, prime));
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"prodeuler");
      x = gerepilecopy(av, x);
    }
  }
  return gerepilecopy(av0,x);
}
GEN
prodeuler0(GEN a, GEN b, GEN code, long prec)
{ EXPR_WRAP(code, prodeuler(EXPR_ARG, a, b, prec)); }

static void
err_direuler(GEN x)
{ pari_err_DOMAIN("direuler","constant term","!=", gen_1,x); }

GEN
direuler(void *E, GEN (*eval)(void *, GEN), GEN a, GEN b, GEN c)
{
  ulong i, k, n;
  pari_sp av0 = avma, av;
  long j, tx, lx;
  GEN x, y, s, polnum, polden, prime;
  forprime_t T;

  if (typ(b) != t_INT)
  {
    b = gfloor(b);
    if (typ(b) != t_INT) pari_err_TYPE("direuler",b);
  }
  if (typ(a) != t_INT)
  {
    a = gceil(a);
    if (typ(a) != t_INT) pari_err_TYPE("direuler",a);
  }
  if (c)
  {
    if (typ(c) != t_INT)
    {
      c = gfloor(c);
      if (typ(c) != t_INT) pari_err_TYPE("direuler", c);
    }
    if (signe(c) <= 0) { avma = av0; return cgetg(1,t_VEC); }
    if (cmpii(c, b) < 0) b = c;
  }
  if (lgefint(b) > 3) pari_err_OVERFLOW("direuler");
  if (!forprime_init(&T, a,b)) { avma = av0; return mkvec(gen_1); }
  n = itou(b);
  y = cgetg(n+1,t_VEC); av = avma;
  x = zerovec(n); gel(x,1) = gen_1;
  while ( (prime = forprime_next(&T)) )
  {
    ulong p = prime[2];
    s = eval(E, prime);
    polnum = numer(s);
    polden = denom(s);
    tx = typ(polnum);
    if (is_scalar_t(tx))
    {
      if (!gequal1(polnum))
      {
        if (!gequalm1(polnum)) err_direuler(polnum);
        polden = gneg(polden);
      }
    }
    else
    {
      ulong k1, q, qlim;
      if (tx != t_POL) pari_err_TYPE("direuler",polnum);
      lx = degpol(polnum);
      if (lx < 0) err_direuler(polnum);
      c = gel(polnum,2);
      if (!gequal1(c))
      {
        if (!gequalm1(c)) err_direuler(polnum);
        polnum = gneg(polnum);
        polden = gneg(polden);
      }
      for (i=1; i<=n; i++) gel(y,i) = gel(x,i);
      q = p; qlim = n/p;
      for (j = 1; q<=n && j<=lx; j++)
      {
        c = gel(polnum,j+2);
        if (!gequal0(c))
          for (k=1,k1=q; k1<=n; k1+=q,k++)
            gel(x,k1) = gadd(gel(x,k1), gmul(c,gel(y,k)));
        if (q > qlim) break;
        q *= p;
      }
    }
    tx = typ(polden);
    if (is_scalar_t(tx))
    {
      if (!gequal1(polden))
        pari_err_DOMAIN("direuler","constant term", "!=", gen_1,polden);
    }
    else
    {
      if (tx != t_POL) pari_err_TYPE("direuler",polden);
      c = gel(polden,2);
      if (!gequal1(c))
        pari_err_DOMAIN("direuler","constant term", "!=", gen_1,polden);
      lx = degpol(polden);
      for (i=p; i<=n; i+=p)
      {
        s = gen_0; k = i;
        for (j = 1; !(k%p) && j<=lx; j++)
        {
          c = gel(polden,j+2); k /= p;
          if (!gequal0(c)) s = gadd(s, gmul(c,gel(x,k)));
        }
        gel(x,i) = gsub(gel(x,i),s);
      }
    }
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"direuler");
      x = gerepilecopy(av, x);
    }
  }
  return gerepilecopy(av0,x);
}
GEN
direuler0(GEN a, GEN b, GEN code, GEN c)
{ EXPR_WRAP(code, direuler(EXPR_ARG, a, b, c)); }

/********************************************************************/
/**                                                                **/
/**                       VECTORS & MATRICES                       **/
/**                                                                **/
/********************************************************************/

INLINE GEN
copyupto(GEN z, GEN t)
{
  if (is_universal_constant(z) || (z>(GEN)pari_mainstack->bot && z<=t))
    return z;
  else
    return gcopy(z);
}

GEN
vecexpr0(GEN vec, GEN code, GEN pred)
{
  switch(typ(vec))
  {
    case t_LIST:
    {
      if (list_typ(vec)==t_LIST_MAP)
        vec = mapdomain_shallow(vec);
      else
        vec = list_data(vec);
      if (!vec) return cgetg(1, t_VEC);
      break;
    }
    case t_VEC: case t_COL: case t_MAT: break;
    default: pari_err_TYPE("[_|_<-_,_]",vec);
  }
  if (pred && code)
    EXPR_WRAP(code,vecselapply((void*)pred,&gp_evalbool,EXPR_ARGUPTO,vec))
  else if (code)
    EXPR_WRAP(code,vecapply(EXPR_ARGUPTO,vec))
  else
    EXPR_WRAP(pred,vecselect(EXPR_ARGBOOL,vec))
}

GEN
vecexpr1(GEN vec, GEN code, GEN pred)
{
  GEN v = vecexpr0(vec, code, pred);
  return lg(v) == 1? v: shallowconcat1(v);
}

GEN
vecteur(GEN nmax, GEN code)
{
  GEN y,p1;
  long i,m;
  GEN c=utoipos(1);

  m = gtos(nmax);
  if (m < 0)  pari_err_DOMAIN("vector", "dimension", "<", gen_0, stoi(m));
  if (!code) return zerovec(m);
  y = cgetg(m+1,t_VEC); push_lex(c, code);
  for (i=1; i<=m; i++)
  {
    c[2] = i; p1 = closure_evalnobrk(code);
    gel(y,i) = copyupto(p1, y);
    set_lex(-1,c);
  }
  pop_lex(1); return y;
}

GEN
vecteursmall(GEN nmax, GEN code)
{
  GEN y;
  long i,m;
  GEN c=utoipos(1);

  m = gtos(nmax);
  if (m < 0)  pari_err_DOMAIN("vectorsmall", "dimension", "<", gen_0, stoi(m));
  if (!code) return zero_zv(m);
  y = cgetg(m+1,t_VECSMALL); push_lex(c,code);
  for (i=1; i<=m; i++)
  {
    c[2] = i;
    y[i] = gtos(closure_evalnobrk(code));
    set_lex(-1,c);
  }
  pop_lex(1); return y;
}

GEN
vvecteur(GEN nmax, GEN n)
{
  GEN y = vecteur(nmax,n);
  settyp(y,t_COL); return y;
}

GEN
matrice(GEN nlig, GEN ncol, GEN code)
{
  GEN y, z, p1;
  long i, j, m, n;
  GEN c1 = utoipos(1), c2 = utoipos(1);

  m = gtos(ncol);
  n = gtos(nlig);
  if (m < 0)  pari_err_DOMAIN("matrix", "nbcols", "<", gen_0, stoi(m));
  if (n < 0)  pari_err_DOMAIN("matrix", "nbrows", "<", gen_0, stoi(n));
  if (!m) return cgetg(1,t_MAT);
  if (!code || !n) return zeromatcopy(n, m);
  push_lex(c1,code);
  push_lex(c2,NULL); y = cgetg(m+1,t_MAT);
  for (i=1; i<=m; i++)
  {
    c2[2] = i; z = cgetg(n+1,t_COL); gel(y,i) = z;
    for (j=1; j<=n; j++)
    {
      c1[2] = j; p1 = closure_evalnobrk(code);
      gel(z,j) = copyupto(p1, y);
      set_lex(-2,c1);
      set_lex(-1,c2);
    }
  }
  pop_lex(2); return y;
}

/********************************************************************/
/**                                                                **/
/**                         SUMMING SERIES                         **/
/**                                                                **/
/********************************************************************/
/* h = (2+2x)g'- g; g has t_INT coeffs */
static GEN
delt(GEN g, long n)
{
  GEN h = cgetg(n+3,t_POL);
  long k;
  h[1] = g[1];
  gel(h,2) = gel(g,2);
  for (k=1; k<n; k++)
    gel(h,k+2) = addii(mului(k+k+1,gel(g,k+2)), mului(k<<1,gel(g,k+1)));
  gel(h,n+2) = mului(n<<1, gel(g,n+1)); return h;
}

#ifdef _MSC_VER /* Bill Daly: work around a MSVC bug */
#pragma optimize("g",off)
#endif
/* P = polzagier(n,m)(-X), unnormalized (P(0) != 1) */
static GEN
polzag1(long n, long m)
{
  const long d = n - m, d2 = d<<1, r = (m+1)>>1, D = (d+1)>>1;
  long i, k;
  pari_sp av = avma;
  GEN g, T;

  if (d <= 0 || m < 0) return pol_0(0);
  g = cgetg(d+2, t_POL);
  g[1] = evalsigne(1)|evalvarn(0);
  T = cgetg(d+1,t_VEC);
  /* T[k+1] = binomial(2d,2k+1), 0 <= k < d */
  gel(T,1) = utoipos(d2);
  for (k = 1; k < D; k++)
  {
    long k2 = k<<1;
    gel(T,k+1) = diviiexact(mulii(gel(T,k), muluu(d2-k2+1, d2-k2)),
                            muluu(k2,k2+1));
  }
  for (; k < d; k++) gel(T,k+1) = gel(T,d-k);
  gel(g,2) = gel(T,d); /* binomial(2d, 2(d-1)+1) */
  for (i = 1; i < d; i++)
  {
    pari_sp av2 = avma;
    GEN s, t = gel(T,d-i); /* binomial(2d, 2(d-1-i)+1) */
    s = t;
    for (k = d-i; k < d; k++)
    {
      long k2 = k<<1;
      t = diviiexact(mulii(t, muluu(d2-k2+1, d-k)), muluu(k2+1,k-(d-i)+1));
      s = addii(s, t);
    }
    /* g_i = sum_{d-1-i <= k < d}, binomial(2*d, 2*k+1)*binomial(k,d-1-i) */
    gel(g,i+2) = gerepileuptoint(av2, s);
  }
  /* sum_{0 <= i < d} g_i x^i * (x+x^2)^r */
  g = RgX_mulXn(gmul(g, gpowgs(deg1pol(gen_1,gen_1,0),r)), r);
  if (!odd(m)) g = delt(g, n);
  for (i=1; i<=r; i++)
  {
    g = delt(ZX_deriv(g), n);
    if (gc_needed(av,4))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"polzag, i = %ld/%ld", i,r);
      g = gerepilecopy(av, g);
    }
  }
  return g;
}
GEN
polzag(long n, long m)
{
  pari_sp av = avma;
  GEN g = ZX_unscale(polzag1(n,m), gen_m1);
  return gerepileupto(av, RgX_Rg_div(g,gel(g,2)));
}

GEN
sumalt(void *E, GEN (*eval)(void *, GEN), GEN a, long prec)
{
  ulong k, N;
  pari_sp av = avma, av2;
  GEN s, az, c, d;

  if (typ(a) != t_INT) pari_err_TYPE("sumalt",a);
  N = (ulong)(0.39322*(prec2nbits(prec) + 7)); /*0.39322 > 1/log_2(3+sqrt(8))*/
  d = powru(addsr(3, sqrtr(stor(8,prec))), N);
  d = shiftr(addrr(d, invr(d)),-1);
  a = setloop(a);
  az = gen_m1; c = d;
  s = gen_0;
  av2 = avma;
  for (k=0; ; k++) /* k < N */
  {
    c = addir(az,c); s = gadd(s, gmul(c, eval(E, a)));
    if (k==N-1) break;
    az = diviuuexact(muluui((N-k)<<1,N+k,az), k+1, (k<<1)+1);
    a = incloop(a); /* in place! */
    if (gc_needed(av,4))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"sumalt, k = %ld/%ld", k,N-1);
      gerepileall(av2, 3, &az,&c,&s);
    }
  }
  return gerepileupto(av, gdiv(s,d));
}

GEN
sumalt2(void *E, GEN (*eval)(void *, GEN), GEN a, long prec)
{
  long k, N;
  pari_sp av = avma, av2;
  GEN s, dn, pol;

  if (typ(a) != t_INT) pari_err_TYPE("sumalt",a);
  N = (long)(0.307073*(prec2nbits(prec) + 5)); /*0.307073 > 1/log_2(\beta_B)*/
  pol = ZX_div_by_X_1(polzag1(N,N>>1), &dn);
  a = setloop(a);
  N = degpol(pol);
  s = gen_0;
  av2 = avma;
  for (k=0; k<=N; k++)
  {
    GEN t = itor(gel(pol,k+2), prec+EXTRAPRECWORD);
    s = gadd(s, gmul(t, eval(E, a)));
    if (k == N) break;
    a = incloop(a); /* in place! */
    if (gc_needed(av,4))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"sumalt2, k = %ld/%ld", k,N-1);
      s = gerepileupto(av2, s);
    }
  }
  return gerepileupto(av, gdiv(s,dn));
}

GEN
sumalt0(GEN a, GEN code, long flag, long prec)
{
  switch(flag)
  {
    case 0: EXPR_WRAP(code, sumalt (EXPR_ARG,a,prec));
    case 1: EXPR_WRAP(code, sumalt2(EXPR_ARG,a,prec));
    default: pari_err_FLAG("sumalt");
  }
  return NULL; /* not reached */
}

/* For k > 0, set S[k*2^i] <- g(k*2^i), k*2^i <= N = #S.
 * Only needed with k odd (but also works for g even). */
static void
binsum(GEN S, ulong k, void *E, GEN (*f)(void *, GEN), GEN a,
        long G, long prec)
{
  long e, i, N = lg(S)-1, l = expu(N / k); /* k 2^l <= N < k 2^(l+1) */
  pari_sp av;
  GEN r, t = gen_0;

  gel(S, k << l) = cgetr(prec); av = avma;
  G -= l;
  r = utoipos(k<<l);
  for(e=0;;e++) /* compute g(k 2^l) with absolute error ~ 2^(G-l) */
  {
    GEN u = gtofp(f(E, addii(a,r)), prec);
    if (typ(u) != t_REAL) pari_err_TYPE("sumpos",u);
    if (!signe(u)) break;
    if (!e)
      t = u;
    else {
      shiftr_inplace(u, e);
      t = addrr(t,u);
      if (expo(u) < G) break;
    }
    r = shifti(r,1);
  }
  gel(S, k << l) = t = gerepileuptoleaf(av, t);
  /* g(j) = 2g(2j) + f(a+j) for all j > 0 */
  for(i = l-1; i >= 0; i--)
  { /* t ~ g(2 * k*2^i) with error ~ 2^(G-i-1) */
    GEN u;
    av = avma; u = gtofp(f(E, addiu(a, k << i)), prec);
    if (typ(u) != t_REAL) pari_err_TYPE("sumpos",u);
    t = addrr(gtofp(u,prec), shiftr(t,1)); /* ~ g(k*2^i) */
    gel(S, k << i) = t = gerepileuptoleaf(av, t);
  }
}
/* For k > 0, let g(k) := \sum_{e >= 0} 2^e f(a + k*2^e).
 * Return [g(k), 1 <= k <= N] */
static GEN
sumpos_init(void *E, GEN (*f)(void *, GEN), GEN a, long N, long prec)
{
  GEN S = cgetg(N+1,t_VEC);
  long k, G = -prec2nbits(prec) - 5;
  for (k=1; k<=N; k+=2) binsum(S,k, E,f, a,G,prec);
  return S;
}

GEN
sumpos(void *E, GEN (*eval)(void *, GEN), GEN a, long prec)
{
  ulong k, N;
  pari_sp av = avma;
  GEN s, az, c, d, S;

  if (typ(a) != t_INT) pari_err_TYPE("sumpos",a);
  a = subiu(a,1);
  N = (ulong)(0.4*(prec2nbits(prec) + 7));
  d = powru(addsr(3, sqrtr(stor(8,prec))), N);
  d = shiftr(addrr(d, invr(d)),-1);
  az = gen_m1; c = d;

  if (odd(N)) N++; /* extra precision for free */
  S = sumpos_init(E, eval, a, N, prec);
  s = gen_0;
  for (k=0; k<N; k++)
  {
    GEN t;
    c = addir(az,c);
    t = mulrr(gel(S,k+1), c);
    s = odd(k)? mpsub(s, t): mpadd(s, t);
    if (k == N-1) break;
    az = diviuuexact(muluui((N-k)<<1,N+k,az), k+1, (k<<1)+1);
  }
  return gerepileupto(av, gdiv(s,d));
}

GEN
sumpos2(void *E, GEN (*eval)(void *, GEN), GEN a, long prec)
{
  ulong k, N;
  pari_sp av = avma;
  GEN s, pol, dn, S;

  if (typ(a) != t_INT) pari_err_TYPE("sumpos2",a);
  a = subiu(a,1);
  N = (ulong)(0.31*(prec2nbits(prec) + 5));

  if (odd(N)) N++; /* extra precision for free */
  S = sumpos_init(E, eval, a, N, prec);
  pol = ZX_div_by_X_1(polzag1(N,N>>1), &dn);
  s = gen_0;
  for (k=0; k<N; k++)
  {
    GEN t = mulri(gel(S,k+1), gel(pol,k+2));
    s = odd(k)? mpsub(s,t): mpadd(s,t);
  }
  return gerepileupto(av, gdiv(s,dn));
}

GEN
sumpos0(GEN a, GEN code, long flag, long prec)
{
  switch(flag)
  {
    case 0: EXPR_WRAP(code, sumpos (EXPR_ARG,a,prec));
    case 1: EXPR_WRAP(code, sumpos2(EXPR_ARG,a,prec));
    default: pari_err_FLAG("sumpos");
  }
  return NULL; /* not reached */
}

/********************************************************************/
/**                                                                **/
/**            SEARCH FOR REAL ZEROS of an expression              **/
/**                                                                **/
/********************************************************************/
/* Brent's method, [a,b] bracketing interval */
GEN
zbrent(void *E, GEN (*eval)(void *, GEN), GEN a, GEN b, long prec)
{
  long sig, iter, itmax;
  pari_sp av = avma;
  GEN c, d, e, tol, fa, fb, fc;

  a = gtofp(a,prec);
  b = gtofp(b,prec); sig = cmprr(b,a);
  if (!sig) return gerepileupto(av, a);
  if (sig < 0) { c=a; a=b; b=c; } else c = b;

  fa = eval(E, a);
  fb = eval(E, b);
  if (gsigne(fa)*gsigne(fb) > 0)
    pari_err_DOMAIN("solve", "f(a)f(b)", ">", gen_0, mkvec2(fa,fb));
  itmax = prec2nbits(prec) * 2 + 1;
  tol = real2n(5-prec2nbits(prec), LOWDEFAULTPREC);
  fc = fb;
  e = d = NULL; /* gcc -Wall */
  for (iter=1; iter<=itmax; iter++)
  {
    GEN xm, tol1;
    if (gsigne(fb)*gsigne(fc) > 0)
    {
      c = a; fc = fa; e = d = subrr(b,a);
    }
    if (gcmp(gabs(fc,0),gabs(fb,0)) < 0)
    {
      a = b; b = c; c = a; fa = fb; fb = fc; fc = fa;
    }
    tol1 = absr_cmp(tol, b) > 0? sqrr(tol): mulrr(tol, absr(b));
    xm = shiftr(subrr(c,b),-1);
    if (absr_cmp(xm,tol1) <= 0 || gequal0(fb)) break; /* SUCCESS */

    if (absr_cmp(e,tol1) >= 0 && gcmp(gabs(fa,0),gabs(fb,0)) > 0)
    { /* attempt interpolation */
      GEN min1, min2, p, q, s = gdiv(fb,fa);
      if (cmprr(a,c)==0)
      {
        p = gmul2n(gmul(xm,s),1);
        q = gsubsg(1,s);
      }
      else
      {
        GEN r = gdiv(fb,fc);
        q = gdiv(fa,fc);
        p = gmul2n(gmul(gsub(q,r),gmul(xm,q)),1);
        p = gmul(s, gsub(p, gmul(gsub(b,a),gsubgs(r,1))));
        q = gmul(gmul(gsubgs(q,1),gsubgs(r,1)),gsubgs(s,1));
      }
      if (gsigne(p) > 0) q = gneg_i(q); else p = gneg_i(p);
      min1 = gsub(gmulsg(3,gmul(xm,q)), gabs(gmul(q,tol1),0));
      min2 = gabs(gmul(e,q),0);
      if (gcmp(gmul2n(p,1), gmin(min1,min2)) < 0)
        { e = d; d = gdiv(p,q); } /* interpolation OK */
      else
        { d = xm; e = d; } /* failed, use bisection */
    }
    else { d = xm; e = d; } /* bound decreasing too slowly, use bisection */
    a = b; fa = fb;
    if (gcmp(gabs(d,0),tol1) > 0) b = gadd(b,d);
    else if (gsigne(xm) > 0)      b = addrr(b,tol1);
    else                          b = subrr(b,tol1);
    fb = eval(E, b);
  }
  if (iter > itmax) pari_err_IMPL("solve recovery [too many iterations]");
  return gerepileuptoleaf(av, rcopy(b));
}

GEN
zbrent0(GEN a, GEN b, GEN code, long prec)
{ EXPR_WRAP(code, zbrent(EXPR_ARG, a,b, prec)); }

/* x = solve_start(&D, a, b, prec)
 * while (x) {
 *   y = ...(x);
 *   x = solve_next(&D, y);
 * }
 * return D.res; */

/********************************************************************/
/**                     Numerical derivation                       **/
/********************************************************************/

struct deriv_data
{
  GEN code;
  GEN args;
};

static GEN deriv_eval(void *E, GEN x, long prec)
{
 struct deriv_data *data=(struct deriv_data *)E;
 gel(data->args,1)=x;
 return closure_callgenvecprec(data->code, data->args, prec);
}

/* Rationale: (f(2^-e) - f(-2^-e) + O(2^-pr)) / (2 * 2^-e) = f'(0) + O(2^-2e)
 * since 2nd derivatives cancel.
 *   prec(LHS) = pr - e
 *   prec(RHS) = 2e, equal when  pr = 3e = 3/2 fpr (fpr = required final prec)
 *
 * For f'(x), x far from 0: prec(LHS) = pr - e - expo(x)
 * --> pr = 3/2 fpr + expo(x) */
GEN
derivnum(void *E, GEN (*eval)(void *, GEN, long), GEN x, long prec)
{
  GEN eps,a,b, y;
  long pr, l, e, ex, newprec;
  pari_sp av = avma;
  long p = precision(x);
  long fpr = p ? prec2nbits(p): prec2nbits(prec);
  ex = gexpo(x);
  if (ex < 0) ex = 0; /* near 0 */
  pr = (long)ceil(fpr * 1.5 + ex);
  l = nbits2prec(pr);
  newprec = nbits2prec(pr + ex + BITS_IN_LONG);
  switch(typ(x))
  {
    case t_REAL:
    case t_COMPLEX:
      x = gprec_w(x, newprec);
  }

  e = fpr/2; /* 1/2 required prec (in sig. bits) */
  eps = real2n(-e, l);
  a = eval(E, gsub(x, eps), newprec);
  b = eval(E, gadd(x, eps), newprec);
  y = gmul2n(gsub(b,a), e-1);
  return gerepileupto(av, gprec_w(y, nbits2prec(fpr)));
}

GEN
derivfun(void *E, GEN (*eval)(void *, GEN, long), GEN x, long prec)
{
  pari_sp av = avma;
  long vx;
  switch(typ(x))
  {
  case t_REAL: case t_INT: case t_FRAC: case t_COMPLEX:
    return derivnum(E,eval, x, prec);
  case t_POL:
    x = RgX_to_ser(x, precdl+2+1); /* +1 because deriv reduce the precision by 1 */
  case t_SER: /* FALL THROUGH */
    vx = varn(x);
    return gerepileupto(av, gdiv(deriv(eval(E, x, prec),vx), deriv(x,vx)));
  default: pari_err_TYPE("formal derivation",x);
    return NULL; /*NOT REACHED*/
  }
}

GEN
derivnum0(GEN a, GEN code, long prec)
{
  EXPR_WRAP(code, derivfun (EXPR_ARGPREC,a,prec));
}

GEN
derivfun0(GEN code, GEN args, long prec)
{
  struct deriv_data E;
  E.code=code; E.args=args;
  return derivfun((void*)&E, deriv_eval, gel(args,1), prec);
}

/********************************************************************/
/**                   Numerical extrapolation                      **/
/********************************************************************/

static double
extgetmf(long muli)
{
  double mulfact[] = {0.5,0.5,0.48,0.43,0.41,0.39,0.38,0.37,0.36,0.36,0.35};
  if (muli > 100) return 0.35*LOG10_2;
  return mulfact[muli/10]*LOG10_2;
}

/* [u(n*muli), u <= N], muli = 1 unless f!=NULL */
static GEN
get_u(void *E, GEN (*f)(void *, GEN, long), long N, long muli, long prec)
{
  long n;
  GEN u;
  if (f)
  {
    u = cgetg(N+1, t_VEC);
    for (n = 1; n <= N; n++) gel(u,n) = f(E, stoi(muli*n), prec);
  }
  else
  {
    u = (GEN)E;
    n = lg(u)-1;
    if (n < N) pari_err_COMPONENT("limitnum","<",stoi(N), stoi(n));
    u = vecslice(u, 1, N);
  }
  for (n = 1; n <= N; n++)
  {
    GEN un = gel(u,n);
    if (is_rational_t(typ(un))) gel(u,n) = gtofp(un, prec);
  }
  return u;
}

struct limit
{
  long prec0; /* target accuracy */
  long prec; /* working accuracy */
  long N; /* number of terms */
  GEN u; /* sequence to extrapolate */
  GEN na; /* [n^alpha, n <= N] */
  GEN nma; /* [n^-alpha, n <= N] or NULL (alpha = 1) */
  GEN coef; /* or NULL (alpha != 1) */
};

static void
limit_init(struct limit *L, void *E, GEN (*f)(void*,GEN,long),
           long muli, GEN alpha, long prec)
{
  long bitprec = prec2nbits(prec), N;
  GEN na;
  long n;

  if (muli <= 0) muli = 20;
  if (!f) muli = 1;
  L->N = N = (long)ceil(extgetmf(muli)*bitprec);
  L->prec = nbits2prec((long)ceil(1.25*bitprec) + 32);
  L->prec0 = prec;
  L->u = get_u(E, f, N, muli, L->prec);
  if (alpha && gcmp1(alpha)) alpha = NULL;
  L->na = na  = cgetg(N+1, t_VEC);
  for (n = 1; n <= N; n++)
  {
    GEN c = utoipos(n*muli);
    if (alpha) c = gpow(c, alpha, L->prec);
    gel(na,n) = c;
  }
  if (alpha)
  {
    GEN nma, malpha = gneg(alpha);
    L->coef = NULL;
    L->nma= nma = cgetg(N+1, t_VEC);
    for (n = 1; n <= N; n++)
    {
      GEN c = gpow(utoipos(n),malpha,L->prec);
      if (typ(c) != t_REAL) c = gtofp(c, L->prec);
      gel(nma, n) = c;
    }
  }
  else
  {
    GEN coef, C = vecbinome(N);
    L->coef = coef = cgetg(N+1, t_VEC);
    L->nma = NULL;
    for (n = 1; n <= N; n++)
    {
      GEN c = mulii(gel(C,n+1), powuu(n, N));
      if (odd(N-n)) togglesign_safe(&c);
      gel(coef, n) = c;
    }
  }
}

/* Zagier/Lagrange extrapolation */
static GEN
limitnum_i(struct limit *L)
{
  pari_sp av = avma;
  GEN S;
  if (L->nma)
    S = polint(L->nma, L->u,gen_0,NULL);
  else
    S = gdiv(RgV_dotproduct(L->u,L->coef), mpfact(L->N));
  return gerepilecopy(av, gprec_w(S, L->prec0));
}
GEN
limitnum(void *E, GEN (*f)(void *, GEN, long), long muli, GEN alpha, long prec)
{
  struct limit L;
  limit_init(&L, E,f, muli, alpha, prec);
  return limitnum_i(&L);
}
GEN
limitnum0(GEN u, long muli, GEN alpha, long prec)
{
  void *E = (void*)u;
  GEN (*f)(void*,GEN,long) = NULL;
  switch(typ(u))
  {
    case t_COL:
    case t_VEC: break;
    case t_CLOSURE: f = gp_callprec; break;
    default: pari_err_TYPE("limitnum", u);
  }
  return limitnum(E,f, muli,alpha, prec);
}

GEN
asympnum(void *E, GEN (*f)(void *, GEN, long), long muli, GEN alpha, long prec)
{
  const long MAX = 100;
  pari_sp av = avma;
  GEN u, vres = vectrunc_init(MAX);
  long i;
  struct limit L;
  limit_init(&L, E,f, muli, alpha, prec);
  u = L.u;
  for(i = 1; i <= MAX; i++)
  {
    GEN a, s, v, p, q;
    long n;
    s = limitnum_i(&L);
    /* NOT bestappr: lindep will "properly" ignore the lower bits */
    v = lindep(mkvec2(gen_1, s));
    p = negi(gel(v,1));
    q = gel(v,2);
    if (!signe(q)) break;
    a = gdiv(p,q);
    s = gsub(s, a);
    /* |s|q^2 > eps */
    if (!gcmp0(s) && gexpo(s) + 2*expi(q) > -17) break;
    vectrunc_append(vres, a);
    for (n = 1; n <= L.N; n++) gel(u,n) = gmul(gsub(gel(u,n), a), gel(L.na,n));
  }
  return gerepilecopy(av, vres);
}
GEN
asympnum0(GEN u, long muli, GEN alpha, long prec)
{
  void *E = (void*)u;
  GEN (*f)(void*,GEN,long) = NULL;
  switch(typ(u))
  {
    case t_COL:
    case t_VEC: break;
    case t_CLOSURE: f = gp_callprec; break;
    default: pari_err_TYPE("asympnum", u);
  }
  return asympnum(E,f, muli,alpha, prec);
}
