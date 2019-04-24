/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */
/********************************************************************/
/*                                                                  */
/*                      PSEUDO-RANDOM INTEGERS                      */
/*                                                                  */
/********************************************************************/
#include "pari.h"
#include "paripriv.h"
/********************************************************************/
/*                    XORGEN (Richard P. Brent)                     */
/*          http://wwwmaths.anu.edu.au/~brent/random.html           */
/*        (initial adaptation to PARI/GP by Randall Rathbun)        */
/********************************************************************/
/* Adapted from xorgens.c version 3.04, Richard P. Brent, 20060628 (GPL).
 * 32-bit or 64-bit integer random number generator with period at
 * least 2**4096-1. It is assumed that "ulong" is a 32-bit or 64-bit integer */
static THREAD ulong xorgen_w;
static THREAD int xorgen_i;

#ifdef LONG_IS_64BIT /* weyl = odd approximation to 2^BIL*(sqrt(5)-1)/2. */
  static const ulong weyl = 0x61c8864680b583ebUL;
  static const int ws = 27, r = 64,  s = 53, a = 33, b = 26, c = 27, d = 29;
  static THREAD ulong state[64]; /* size r */
#else
  static const ulong weyl = 0x61c88647UL;
  static const int ws = 16, r = 128, s = 95, a = 17, b = 12, c = 13, d = 15;
  static THREAD ulong state[128]; /* size r */
#endif

static void
init_xor4096i(ulong seed)
{
  ulong t, v = seed;  /* v must be nonzero */
  int k;

  for (k = BITS_IN_LONG; k > 0; k--) {/* Avoid correlations for close seeds */
    v ^= v<<10; v ^= v>>15;      /* Recurrence has period 2**BIL -1 */
    v ^= v<<4;  v ^= v>>13;
  }
  for (xorgen_w = v, k = 0; k < r; k++) { /* Initialise circular array */
    v ^= v<<10; v ^= v>>15;
    v ^= v<<4;  v ^= v>>13;
    state[k] = v + (xorgen_w+=weyl);
  }
  for (xorgen_i = r-1, k = 4*r; k > 0; k--) { /* Discard first 4*r results */
    t = state[xorgen_i = (xorgen_i+1)&(r-1)]; t ^= t<<a;  t ^= t>>b;
    v = state[(xorgen_i+(r-s))&(r-1)];        v ^= v<<c;  v ^= v>>d;
    state[xorgen_i] = t^v;
  }
}

void pari_init_rand(void) { init_xor4096i(1); }

/* One random number uniformly distributed in [0..2**BIL) is returned, where
 * BIL = 8*sizeof(ulong) = 32 or 64. */
ulong
pari_rand(void)
{
  ulong t, v;

  t = state[xorgen_i = (xorgen_i+1)&(r-1)];
  v = state[(xorgen_i+(r-s))&(r-1)];   /* Index is (xorgen_i-s) mod r */
  t ^= t<<a;  t ^= t>>b;               /* (I + L^a)(I + R^b) */
  v ^= v<<c;  v ^= v>>d;               /* (I + L^c)(I + R^d) */
  state[xorgen_i] = (v ^= t);          /* Update circular array */
  xorgen_w += weyl;                    /* Update Weyl generator */
  return v + (xorgen_w ^ (xorgen_w>>ws));
}

void
setrand(GEN seed) {
  switch (typ(seed))
  {
    case t_VECSMALL:
    {
      GEN xd = seed+1;
      long i;
      if (lg(seed) != r+2 + 1) break;
      for (i = 0; i < r; i++) state[i] = xd[i];
      xorgen_i = xd[i++];
      xorgen_w = xd[i++];
      return;
    }
    case t_INT: if (signe(seed) > 0) { init_xor4096i( itou(seed) ); return; }
  }
  pari_err_TYPE("setrand",seed);
}
GEN
getrand(void) {
  GEN x, xd;
  long i;
  if (xorgen_i < 0) init_xor4096i(1);

  x = cgetg(r+2 + 1, t_VECSMALL); xd = x+1;
  for (i = 0; i < r; i++) xd[i] = state[i];
  xd[i++] = xorgen_i;
  xd[i++] = xorgen_w;
  return x;
}

/********************************************************************/
/*                                                                  */
/*                         GENERIC ROUTINES                         */
/*                                                                  */
/********************************************************************/

/* assume n > 0 */
ulong
random_Fl(ulong n)
{
  ulong d;
  int shift;

  if (n == 1) return 0;

  shift = bfffo(n); /* 2^(BIL-shift) > n >= 2^(BIL-shift-1)*/
  /* if N a power of 2, increment shift. No reject */
  if ((n << shift) == HIGHBIT) return pari_rand() >> (shift+1);
  for (;;) {
    d = pari_rand() >> shift; /* d < 2^(BIL-shift) uniformly distributed */
    /* reject strategy: proba success = n 2^(shift-BIL), in [1/2, 1[ */
    if (d < n) return d;
  }
}

/* assume N > 0, see random_Fl() for algorithm */
GEN
randomi(GEN N)
{
  long lx = lgefint(N);
  GEN d, NMSW;
  pari_sp av;
  int shift;

  if (lx == 3) return utoi( random_Fl(N[2]) );

  NMSW = int_MSW(N); shift = bfffo(*NMSW);
  if (((ulong)*NMSW << shift) == HIGHBIT)
  { /* if N a power of 2, increment shift */
    for (d = int_LSW(N); !*d; d = int_nextW(d)) /* empty */;
    if (d == NMSW && ++shift == BITS_IN_LONG) { shift = 0; lx--; }
  }
  for (av = avma;; avma = av) {
    GEN x = cgetipos(lx), xMSW = int_MSW(x);
    for (d = int_LSW(x); d != xMSW; d = int_nextW(d)) *d = pari_rand();
    *d = pari_rand() >> shift;
    x = int_normalize(x, 0);
    if (absi_cmp(x, N) < 0) return x;
  }
}

GEN
randomr(long prec)
{
  pari_sp av;
  long b;
  GEN x, y;
  if (prec <= 2) return real_0_bit(0);
  x = cgetr(prec); av = avma;
  b = prec2nbits(prec);
  y = randomi(int2n(b));
  if (!signe(y)) return real_0_bit(b);
  affir(y, x); shiftr_inplace(x, - b);
  avma = av; return x;
}

static GEN
polrandom(GEN N) /* assume N!=0 */
{
  long i, d = lg(N);
  GEN z = leading_term(N);
  GEN y = cgetg(d,t_POL);
  y[1] = evalsigne(1) | evalvarn(varn(N));
  for (i=2; i<d; i++) gel(y,i) = genrand(z);
  return normalizepol_lg(y,d);
}

GEN
genrand(GEN N)
{
  GEN z;
  if (!N) return utoi( random_bits(31) );
  switch(typ(N))
  {
    case t_INT:
      if (signe(N)<=0) pari_err_DOMAIN("random","N","<=",gen_0,gen_0);
      return randomi(N);
    case t_REAL:
      return randomr(realprec(N));
    case t_INTMOD:
      z = cgetg(3, t_INTMOD);
      gel(z,1) = icopy(gel(N,1));
      gel(z,2) = randomi(gel(N,1)); return z;
    case t_FFELT:
      return ffrandom(N);
    case t_POL:
      if (signe(N)==0) return pol_0(varn(N));
      return polrandom(N);
    case t_VEC:
      if (lg(N) == 3)
      {
        pari_sp av = avma;
        GEN a = gel(N,1), b = gel(N,2), d;
        if (typ(a) != t_INT) a = gceil(a);
        if (typ(b) != t_INT) b = gfloor(b);
        if (typ(a) != t_INT || typ(b) != t_INT) pari_err_TYPE("random", N);
        d = subii(b,a);
        if (signe(d) < 0) pari_err_TYPE("random([a,b]) (a > b)", N);
        return gerepileuptoint(av, addii(a, randomi(addis(d,1))));
      }
      return ellrandom(N);
    default:
      pari_err_TYPE("genrand",N);
      return NULL;/*not reached*/
  }
}
