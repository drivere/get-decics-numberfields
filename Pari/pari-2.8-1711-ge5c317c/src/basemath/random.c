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

#ifdef LONG_IS_64BIT
  typedef ulong u64;
  static THREAD ulong state[64];
  #define u64state(i)      ((u64)state[(i)])
  #define u64stateset(i,x) state[(i)] = (ulong) (x);
#else
  typedef unsigned long long u64;
  static THREAD ulong state[128];
  #define u64state(i)      _32to64(state[2*(i)],state[2*(i)+1])
  #define u64stateset(i,x) _64to32(x,state+2*(i),state+2*(i)+1)
static u64
_32to64(ulong a, ulong b) { u64 v = a; return (v<<32)|b; }
static void
_64to32(u64 v, ulong *a, ulong *b) { *a = v>>32; *b = v&0xFFFFFFFF; }
#endif
static THREAD u64 xorgen_w;
static THREAD int xorgen_i;
/* weyl = odd approximation to 2^64*(sqrt(5)-1)/2. */
static const u64 weyl = (((u64)0x61c88646U)<<32)|((u64)0x80b583ebU);

static u64
block(void)
{
  const int r = 64;
  const int a = 33, b = 26, c = 27, d = 29, s = 53;
  u64 t, v, w;
  xorgen_i = (xorgen_i+1)&(r-1);
  t = u64state(xorgen_i);
  v = u64state((xorgen_i+(r-s))&(r-1));   /* index is (i-s) mod r */
  t ^= t<<a; t ^= t>>b;                   /* (I + L^a)(I + R^b) */
  v ^= v<<c; v ^= v>>d;                   /* (I + L^c)(I + R^d) */
  w = t^v;
  u64stateset(xorgen_i, w);               /* update circular array */
  return w;
}

static void
init_xor4096i(ulong seed)
{
  const int r = 64;
  u64 v = seed; /* v must be nonzero */
  int k;

  for (k = r; k > 0; k--) {/* avoid correlations for close seeds */
    v ^= v<<10; v ^= v>>15; /* recurrence has period 2**64-1 */
    v ^= v<<4;  v ^= v>>13;
  }
  for (xorgen_w = v, k = 0; k < r; k++) { /* initialise circular array */
    v ^= v<<10; v ^= v>>15;
    v ^= v<<4;  v ^= v>>13;
    u64stateset(k, v + (xorgen_w+=weyl));
  }
  /* discard first 4*r results */
  for (xorgen_i = r-1, k = 4*r; k > 0; k--) (void)block();
}

void pari_init_rand(void) { init_xor4096i(1); }

static u64
rand64(void)
{
  u64 v = block();
  xorgen_w += weyl; /* update Weyl generator */
  return v + (xorgen_w ^ (xorgen_w>>27));
}

/* One random number uniformly distributed in [0..2**BIL) is returned, where
 * BIL = 8*sizeof(ulong) = 32 or 64. */
ulong
pari_rand(void) { return rand64(); }

void
setrand(GEN x)
{
  const int r2 = numberof(state);
  ulong useed;
  long i;
  GEN xp;
  if (typ(x)!=t_INT)
    pari_err_TYPE("setrand",x);
  if (signe(x) <= 0) return;
  useed = itou_or_0(x);
  if (useed > 0) { init_xor4096i(useed); return; }
  if (lgefint(x)!=2+r2+2+(r2==128))
    pari_err_TYPE("setrand",x);
  xp = int_LSW(x);
  for (i = 0; i < r2; i++) { state[i] = *xp; xp = int_nextW(xp); }
#ifdef LONG_IS_64BIT
  xorgen_w = *xp; xp = int_nextW(xp);
#else
  xorgen_w = _32to64(*xp, *int_nextW(xp)); xp = int_nextW(int_nextW(xp));
#endif
  xorgen_i =  (*xp) & 63;
}

GEN
getrand(void)
{
  const int r2 = numberof(state);
  GEN x;
  ulong *xp;
  long i;
  if (xorgen_i < 0) init_xor4096i(1);

  x = cgetipos(2+r2+2+(r2==128)); xp = (ulong *) int_LSW(x);
  for (i = 0; i < r2; i++) { *xp = state[i]; xp = int_nextW(xp); }
#ifdef LONG_IS_64BIT
  *xp = xorgen_w; xp = int_nextW(xp);
#else
  _64to32(xorgen_w, xp, int_nextW(xp)); xp = int_nextW(int_nextW(xp));
#endif
  *xp = xorgen_i? xorgen_i: 64; return x;
}

/* assume 0 <= k <= BITS_IN_LONG. Return uniform random 0 <= x < (1<<k) */
long
random_bits(long k) { return rand64() >> (64-k); }

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
#ifdef LONG_IS_64BIT
  int SHIFT = 0;
#else
  int SHIFT = 32;
#endif

  if (n == 1) return 0;

  shift = bfffo(n); /* 2^(BIL-shift) > n >= 2^(BIL-shift-1)*/
  /* if N a power of 2, increment shift. No reject */
  if ((n << shift) == HIGHBIT) return rand64() >> (SHIFT+shift+1);
  for (;;) {
    d = rand64() >> (SHIFT+shift); /* d < 2^(64-shift) uniformly distributed */
    /* reject strategy: proba success = n 2^(shift-64), in [1/2, 1[ */
    if (d < n) return d;
  }
}

/* assume N > 0, see random_Fl() for algorithm. Make sure that 32-bit and
 * 64-bit architectures produce the same integers (consuming random bits
 * by packets of 64) */
GEN
randomi(GEN N)
{
  long lx = lgefint(N);
  GEN x, d;
  int shift;

  if (lx == 3) return utoi( random_Fl(N[2]) );

  shift = bfffo(*int_MSW(N));
  /* if N a power of 2, increment shift */
  if (Z_ispow2(N) && ++shift == BITS_IN_LONG) { shift = 0; lx--; }
  x = cgetipos(lx);
  for (;;) {
    GEN y, MSW = int_MSW(x), STOP = MSW;
#ifdef LONG_IS_64BIT
    for (d = int_LSW(x); d != STOP; d = int_nextW(d)) *d = rand64();
    *d = rand64() >> shift;
#else
    if (!odd(lx)) STOP = int_precW(STOP);
    /* STOP points to where MSW would in 64-bit */
    for (d = int_LSW(x); d != STOP; d = int_nextW(d))
    {
      ulong a, b; _64to32(rand64(), &a,&b);
      *d = b; d = int_nextW(d);
      *d = a;
    }
    {
      ulong a, b; _64to32(rand64() >> shift, &a,&b);
      if (d == MSW) /* 32 bits needed */
        *d = a;
      else
      { /* 64 bits needed */
        *d = b; d = int_nextW(d);
        *d = a;
      }
    }
#endif
    y = int_normalize(x, 0);
    if (absi_cmp(y, N) < 0) return y;
  }
}

GEN
random_F2x(long d, long vs)
{
  long i, l = nbits2lg(d+1), n = l-1;
  GEN y = cgetg(l,t_VECSMALL); y[1] = vs;
#ifdef LONG_IS_64BIT
  for (i=2; i<=n; i++) y[i] = rand64();
#else
  for (i=2; i<=n; i++)
  {
    u64 v = rand64();
    y[i] = v & 0xFFFFFFFFUL;
    i++;
    if (i > n) break;
    y[i] = v>>32;
    i++;
    if (i > n) { v = rand64(); break; }
  }
#endif
  y[n] &= (1UL<<remsBIL(d))-1UL;
  return F2x_renormalize(y,l);
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
