/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*********************************************************************/
/**                                                                 **/
/**                     ARITHMETIC FUNCTIONS                        **/
/**                        (second part)                            **/
/**                                                                 **/
/*********************************************************************/
#include "pari.h"
#include "paripriv.h"

static ulong _maxprime = 0;
static ulong diffptrlen;

/* Building/Rebuilding the diffptr table. The actual work is done by the
 * following two subroutines;  the user entry point is the function
 * initprimes() below.  initprimes1() is the old algorithm, called when
 * maxnum (size) is moderate. Must be called after pari_init_stack() )*/
static void
initprimes1(ulong size, long *lenp, ulong *lastp, byteptr p1)
{
  pari_sp av = avma;
  long k;
  byteptr q, r, s, p = (byteptr)stack_calloc(size+2), fin = p + size;

  for (r=q=p,k=1; r<=fin; )
  {
    do { r+=k; k+=2; r+=k; } while (*++q);
    for (s=r; s<=fin; s+=k) *s = 1;
  }
  r = p1; *r++ = 2; *r++ = 1; /* 2 and 3 */
  for (s=q=p+1; ; s=q)
  {
    do q++; while (*q);
    if (q > fin) break;
    *r++ = (unsigned char) ((q-s) << 1);
  }
  *r++ = 0;
  *lenp = r - p1;
  *lastp = ((s - p) << 1) + 1;
  avma = av;
}

/*  Timing in ms (Athlon/850; reports 512K of secondary cache; looks
    like there is 64K of quickier cache too).

      arena|    30m     100m    300m    1000m    2000m  <-- primelimit
      =================================================
      16K       1.1053  1.1407  1.2589  1.4368   1.6086
      24K       1.0000  1.0625  1.1320  1.2443   1.3095
      32K       1.0000  1.0469  1.0761  1.1336   1.1776
      48K       1.0000  1.0000  1.0254  1.0445   1.0546
      50K       1.0000  1.0000  1.0152  1.0345   1.0464
      52K       1.0000  1.0000  1.0203  1.0273   1.0362
      54K       1.0000  1.0000  1.0812  1.0216   1.0281
      56K       1.0526  1.0000  1.0051  1.0144   1.0205
      58K       1.0000  1.0000  1.0000  1.0086   1.0123
      60K       0.9473  0.9844  1.0051  1.0014   1.0055
      62K       1.0000  0.9844  0.9949  0.9971   0.9993
      64K       1.0000  1.0000  1.0000  1.0000   1.0000
      66K       1.2632  1.2187  1.2183  1.2055   1.1953
      68K       1.4211  1.4844  1.4721  1.4425   1.4188
      70K       1.7368  1.7188  1.7107  1.6767   1.6421
      72K       1.9474  1.9531  1.9594  1.9023   1.8573
      74K       2.2105  2.1875  2.1827  2.1207   2.0650
      76K       2.4211  2.4219  2.4010  2.3305   2.2644
      78K       2.5789  2.6250  2.6091  2.5330   2.4571
      80K       2.8421  2.8125  2.8223  2.7213   2.6380
      84K       3.1053  3.1875  3.1776  3.0819   2.9802
      88K       3.5263  3.5312  3.5228  3.4124   3.2992
      92K       3.7895  3.8438  3.8375  3.7213   3.5971
      96K       4.0000  4.1093  4.1218  3.9986   3.9659
      112K      4.3684  4.5781  4.5787  4.4583   4.6115
      128K      4.7368  4.8750  4.9188  4.8075   4.8997
      192K      5.5263  5.7188  5.8020  5.6911   5.7064
      256K      6.0000  6.2187  6.3045  6.1954   6.1033
      384K      6.7368  6.9531  7.0405  6.9181   6.7912
      512K      7.3158  7.5156  7.6294  7.5000   7.4654
      768K      9.1579  9.4531  9.6395  9.5014   9.1075
      1024K    10.368  10.7497 10.9999 10.878   10.8201
      1536K    12.579  13.3124 13.7660 13.747   13.4739
      2048K    13.737  14.4839 15.0509 15.151   15.1282
      3076K    14.789  15.5780 16.2993 16.513   16.3365

    Now the same number relative to the model

    (1 + 0.36*sqrt(primelimit)/arena) * (arena <= 64 ? 1.05 : (arena-64)**0.38)

     [SLOW2_IN_ROOTS = 0.36, ALPHA = 0.38]

      arena|    30m     100m    300m    1000m    2000m  <-- primelimit
      =================================================
        16K    1.014    0.9835  0.9942  0.9889  1.004
        24K    0.9526   0.9758  0.9861  0.9942  0.981
        32K    0.971    0.9939  0.9884  0.9849  0.9806
        48K    0.9902   0.9825  0.996   0.9945  0.9885
        50K    0.9917   0.9853  0.9906  0.9926  0.9907
        52K    0.9932   0.9878  0.9999  0.9928  0.9903
        54K    0.9945   0.9902  1.064   0.9939  0.9913
        56K    1.048    0.9924  0.9925  0.993   0.9921
        58K    0.9969   0.9945  0.9909  0.9932  0.9918
        60K    0.9455   0.9809  0.9992  0.9915  0.9923
        62K    0.9991   0.9827  0.9921  0.9924  0.9929
        64K    1        1       1       1       1
        66K    1.02     0.9849  0.9857  0.9772  0.9704
        68K    0.8827   0.9232  0.9176  0.9025  0.8903
        70K    0.9255   0.9177  0.9162  0.9029  0.8881
        72K    0.9309   0.936   0.9429  0.9219  0.9052
        74K    0.9715   0.9644  0.967   0.9477  0.9292
        76K    0.9935   0.9975  0.9946  0.9751  0.9552
        78K    0.9987   1.021   1.021   1.003   0.9819
        80K    1.047    1.041   1.052   1.027   1.006
        84K    1.052    1.086   1.092   1.075   1.053
        88K    1.116    1.125   1.133   1.117   1.096
        92K    1.132    1.156   1.167   1.155   1.134
        96K    1.137    1.177   1.195   1.185   1.196
       112K    1.067    1.13    1.148   1.15    1.217
       128K    1.04     1.083   1.113   1.124   1.178
       192K    0.9368   0.985   1.025   1.051   1.095
       256K    0.8741   0.9224  0.9619  0.995   1.024
       384K    0.8103   0.8533  0.8917  0.9282  0.9568
       512K    0.7753   0.8135  0.8537  0.892   0.935
       768K    0.8184   0.8638  0.9121  0.9586  0.9705
      1024K    0.8241   0.8741  0.927   0.979   1.03
      1536K    0.8505   0.9212  0.9882  1.056   1.096
      2048K    0.8294   0.8954  0.9655  1.041   1.102

*/

#ifndef SLOW2_IN_ROOTS
  /* SLOW2_IN_ROOTS below 3: some slowdown starts to be noticable
   * when things fit into the cache on Sparc.
   * The choice of 2.6 gives a slowdown of 1-2% on UltraSparcII,
   * but makes calculations for "maximum" of 436273009
   * fit into 256K cache (still common for some architectures).
   *
   * One may change it when small caches become uncommon, but the gain
   * is not going to be very noticable... */
#  ifdef i386           /* gcc defines this? */
#    define SLOW2_IN_ROOTS      0.36
#  else
#    define SLOW2_IN_ROOTS      2.6
#  endif
#endif
#ifndef CACHE_ARENA
#  ifdef i386           /* gcc defines this? */
   /* Due to smaller SLOW2_IN_ROOTS, smaller arena is OK; fit L1 cache */
#    define CACHE_ARENA (63 * 1024UL) /* No slowdown even with 64K L1 cache */
#  else
#    define CACHE_ARENA (200 * 1024UL) /* No slowdown even with 256K L2 cache */
#  endif
#endif

#define CACHE_ALPHA     (0.38)          /* Cache performance model parameter */
#define CACHE_CUTOFF    (0.018)         /* Cache performance not smooth here */

static double slow2_in_roots = SLOW2_IN_ROOTS;

typedef struct {
    ulong arena;
    double power;
    double cutoff;
} cache_model_t;

static cache_model_t cache_model = { CACHE_ARENA, CACHE_ALPHA, CACHE_CUTOFF };

/* Assume that some calculation requires a chunk of memory to be
   accessed often in more or less random fashion (as in sieving).
   Assume that the calculation can be done in steps by subdividing the
   chunk into smaller subchunks (arenas) and treating them
   separately.  Assume that the overhead of subdivision is equivalent
   to the number of arenas.

   Find an optimal size of the arena taking into account the overhead
   of subdivision, and the overhead of arena not fitting into the
   cache.  Assume that arenas of size slow2_in_roots slows down the
   calculation 2x (comparing to very big arenas; when cache hits do
   not matter).  Since cache performance varies wildly with
   architecture, load, and wheather (especially with cache coloring
   enabled), use an idealized cache model based on benchmarks above.

   Assume that an independent region of FIXED_TO_CACHE bytes is accessed
   very often concurrently with the arena access.
 */
static ulong
good_arena_size(ulong slow2_size, ulong total, ulong fixed_to_cache,
                cache_model_t *cache_model)
{
  ulong asize, cache_arena = cache_model->arena;
  double Xmin, Xmax, A, B, C1, C2, D, V;
  double alpha = cache_model->power, cut_off = cache_model->cutoff;

  /* Estimated relative slowdown,
     with overhead = max((fixed_to_cache+arena)/cache_arena - 1, 0):

     1 + slow2_size/arena due to initialization overhead;

     max(1, 4.63 * overhead^0.38 ) due to footprint > cache size.

     [The latter is hard to substantiate theoretically, but this
     function describes benchmarks pretty close; it does not hurt that
     one can minimize it explicitly too ;-).  The switch between
     different choices of max() happens when overhead=0.018.]

     Thus the problem is minimizing (1 + slow2_size/arena)*overhead**0.29.
     This boils down to F=((X+A)/(X+B))X^alpha, X=overhead,
     B = (1 - fixed_to_cache/cache_arena), A = B +
     slow2_size/cache_arena, alpha = 0.38, and X>=0.018, X>-B.

     We need to find the rightmost root of (X+A)*(X+B) - alpha(A-B)X to the
     right of 0.018 (if such exists and is below Xmax).  Then we manually
     check the remaining region [0, 0.018].

     Since we cannot trust the purely-experimental cache-hit slowdown
     function, as a sanity check always prefer fitting into the
     cache (or "almost fitting") if F-law predicts that the larger
     value of the arena provides less than 10% speedup.

   */

  /* The simplest case: we fit into cache */
  if (total + fixed_to_cache <= cache_arena)
      return total;
  /* The simple case: fitting into cache doesn't slow us down more than 10% */
  if (cache_arena - fixed_to_cache > 10 * slow2_size) {
      asize = cache_arena - fixed_to_cache;
      if (asize > total) asize = total; /* Automatically false... */
      return asize;
  }
  /* Slowdown of not fitting into cache is significant.  Try to optimize.
     Do not be afraid to spend some time on optimization - in trivial
     cases we do not reach this point; any gain we get should
     compensate the time spent on optimization.  */

  B = (1 - ((double)fixed_to_cache)/cache_arena);
  A = B + ((double)slow2_size)/cache_arena;
  C2 = A*B;
  C1 = (A + B - 1/alpha*(A - B))/2;
  D = C1*C1 - C2;
  if (D > 0)
      V = cut_off*cut_off + 2*C1*cut_off + C2; /* Value at CUT_OFF */
  else
      V = 0;                            /* Peacify the warning */
  Xmin = cut_off;
  Xmax = ((double)total - fixed_to_cache)/cache_arena; /* Two candidates */

  if ( D <= 0 || (V >= 0 && C1 + cut_off >= 0) ) /* slowdown increasing */
      Xmax = cut_off;                   /* Only one candidate */
  else if (V >= 0 &&                    /* slowdown concave down */
           ((Xmax + C1) <= 0 || (Xmax*Xmax + 2*C1*Xmax + C2) <= 0))
      /* DO NOTHING */;                 /* Keep both candidates */
  else if (V <= 0 && (Xmax*Xmax + 2*C1*Xmax + C2) <= 0) /* slowdown decreasing */
      Xmin = cut_off;                   /* Only one candidate */
  else /* Now we know: 2 roots, the largest is in CUT_OFF..Xmax */
      Xmax = sqrt(D) - C1;
  if (Xmax != Xmin) {   /* Xmin == CUT_OFF; Check which one is better */
      double v1 = (cut_off + A)/(cut_off + B);
      double v2 = 2.33 * (Xmax + A)/(Xmax + B) * pow(Xmax, alpha);

      if (1.1 * v2 >= v1) /* Prefer fitting into the cache if slowdown < 10% */
          V = v1;
      else {
          Xmin = Xmax;
          V = v2;
      }
  } else if (B > 0)                     /* We need V */
      V = 2.33 * (Xmin + A)/(Xmin + B) * pow(Xmin, alpha);
  if (B > 0 && 1.1 * V > A/B)  /* Now Xmin is the minumum.  Compare with 0 */
      Xmin = 0;

  asize = (ulong)((1 + Xmin)*cache_arena - fixed_to_cache);
  if (asize > total) asize = total;     /* May happen due to approximations */
  return asize;
}

/* Use as in
    install(set_optimize,lLDG)          \\ Through some M too?
    set_optimize(2,1) \\ disable dependence on limit
    \\ 1: how much cache usable, 2: slowdown of setup, 3: alpha, 4: cutoff
    \\ 2,3,4 are in units of 0.001

    { time_primes_arena(ar,limit) =     \\ ar = arena size in K
        set_optimize(1,floor(ar*1024));
        default(primelimit, 200 000);   \\ 100000 results in *larger* malloc()!
        gettime;
        default(primelimit, floor(limit));
        if(ar >= 1, ar=floor(ar));
        print("arena "ar"K => "gettime"ms");
    }
*/
long
set_optimize(long what, GEN g)
{
  long ret = 0;

  switch (what) {
  case 1:
    ret = (long)cache_model.arena;
    break;
  case 2:
    ret = (long)(slow2_in_roots * 1000);
    break;
  case 3:
    ret = (long)(cache_model.power * 1000);
    break;
  case 4:
    ret = (long)(cache_model.cutoff * 1000);
    break;
  default:
    pari_err_BUG("set_optimize");
    break;
  }
  if (g != NULL) {
    ulong val = itou(g);

    switch (what) {
    case 1: cache_model.arena = val; break;
    case 2: slow2_in_roots     = (double)val / 1000.; break;
    case 3: cache_model.power  = (double)val / 1000.; break;
    case 4: cache_model.cutoff = (double)val / 1000.; break;
    }
  }
  return ret;
}

/* s is odd; prime differences (starting from 5-3=2) start at known_primes[2],
  terminated by a 0 byte. Checks n odd numbers starting at 'start', setting
  bytes starting at data to 0 (composite) or 1 (prime) */
static void
sieve_chunk(byteptr known_primes, ulong s, byteptr data, ulong n)
{
  ulong p, cnt = n-1, start = s, delta = 1;
  byteptr q;

  memset(data, 0, n);
  start >>= 1;  /* (start - 1)/2 */
  start += n; /* Corresponds to the end */
  /* data corresponds to start, q runs over primediffs */
  for (q = known_primes + 1, p = 3; delta; delta = *++q, p += delta)
  { /* first odd number >= start > p and divisible by p
       = last odd number <= start + 2p - 2 and 0 (mod p)
       = p + last number <= start + p - 2 and 0 (mod 2p)
       = p + start+p-2 - (start+p-2) % 2p
       = start + 2(p - 1 - ((start-1)/2 + (p-1)/2) % p). */
    long off = cnt - ((start+(p>>1)) % p);
    while (off >= 0) { data[off] = 1; off -= p; }
  }
}

/* assume maxnum <= 436273289 < 2^29 */
static void
initprimes0(ulong maxnum, long *lenp, ulong *lastp, byteptr p1)
{
  pari_sp av = avma, bot = pari_mainstack->bot;
  long alloced, psize;
  byteptr q, end, p, end1, plast, curdiff;
  ulong last, remains, curlow, rootnum, asize;
  ulong prime_above;
  byteptr p_prime_above;

  maxnum |= 1; /* make it odd. */
  /* base case */
  if (maxnum < 1ul<<17) { initprimes1(maxnum>>1, lenp, lastp, p1); return; }

  /* Checked to be enough up to 40e6, attained at 155893 */
  rootnum = usqrt(maxnum) | 1;
  initprimes1(rootnum>>1, &psize, &last, p1);
  end1 = p1 + psize - 1;
  remains = (maxnum - last) >> 1; /* number of odd numbers to check */

  /* we access primes array of psize too; but we access it consecutively,
   * thus we do not include it in fixed_to_cache */
  asize = good_arena_size((ulong)(rootnum * slow2_in_roots), remains+1, 0,
                          &cache_model) - 1;
  /* enough room on the stack ? */
  alloced = (((byteptr)avma) <= ((byteptr)bot) + asize);
  if (alloced)
    p = (byteptr)pari_malloc(asize+1);
  else
    p = (byteptr)stack_malloc(asize+1);
  end = p + asize; /* the 0 sentinel goes at end. */
  curlow = last + 2; /* First candidate: know primes up to last (odd). */
  curdiff = end1;

  /* During each iteration p..end-1 represents a range of odd
     numbers.  plast is a pointer which represents the last prime seen,
     it may point before p..end-1. */
  plast = p - 1;
  p_prime_above = p1 + 2;
  prime_above = 3;
  while (remains)
  { /* cycle over arenas; performance not crucial */
    unsigned char was_delta;
    if (asize > remains) { asize = remains; end = p + asize; }
    /* Fake the upper limit appropriate for the given arena */
    while (prime_above*prime_above <= curlow + (asize << 1) && *p_prime_above)
      prime_above += *p_prime_above++;
    was_delta = *p_prime_above;
    *p_prime_above = 0; /* sentinel for sieve_chunk */
    sieve_chunk(p1, curlow, p, asize);
    *p_prime_above = was_delta; /* restore */

    p[asize] = 0; /* sentinel */
    for (q = p; ; plast = q++)
    { /* q runs over addresses corresponding to primes */
      while (*q) q++; /* use sentinel at end */
      if (q >= end) break;
      *curdiff++ = (unsigned char)(q-plast) << 1; /* < 255 for q < 436273291 */
    }
    plast -= asize;
    remains -= asize;
    curlow += (asize<<1);
  }
  last = curlow - ((p - plast) << 1);
  *curdiff++ = 0; /* sentinel */
  *lenp = curdiff - p1;
  *lastp = last;
  if (alloced) pari_free(p); else avma = av;
}

ulong
maxprime(void) { return diffptr ? _maxprime : 0; }

void
maxprime_check(ulong c) { if (_maxprime < c) pari_err_MAXPRIME(c); }

/* We ensure 65302 <= maxnum <= 436273289: the LHS ensures modular function
 * have enough fast primes to work, the RHS ensures that p_{n+1} - p_n < 255
 * (N.B. RHS would be incorrect since initprimes0 would make it odd, thereby
 * increasing it by 1) */
byteptr
initprimes(ulong maxnum, long *lenp, ulong *lastp)
{
  byteptr t;
  if (maxnum < 65537)
    maxnum = 65537;
  else if (maxnum > 436273289)
    maxnum = 436273289;
  t = (byteptr)pari_malloc((size_t) (1.09 * maxnum/log((double)maxnum)) + 146);
  initprimes0(maxnum, lenp, lastp, t);
  return (byteptr)pari_realloc(t, *lenp);
}

void
initprimetable(ulong maxnum)
{
  long len;
  ulong last;
  byteptr p = initprimes(maxnum, &len, &last), old = diffptr;
  diffptrlen = minss(diffptrlen, len);
  _maxprime  = minss(_maxprime,last); /*Protect against ^C*/
  diffptr = p; diffptrlen = len; _maxprime = last;
  if (old) free(old);
}

/* all init_primepointer_xx routines set *ptr to the corresponding place
 * in prime table */
/* smallest p >= a */
ulong
init_primepointer_geq(ulong a, byteptr *pd)
{
  ulong n, p;
  prime_table_next_p(a, pd, &p, &n);
  return p;
}
/* largest p < a */
ulong
init_primepointer_lt(ulong a, byteptr *pd)
{
  ulong n, p;
  prime_table_next_p(a, pd, &p, &n);
  PREC_PRIME_VIADIFF(p, *pd);
  return p;
}
/* largest p <= a */
ulong
init_primepointer_leq(ulong a, byteptr *pd)
{
  ulong n, p;
  prime_table_next_p(a, pd, &p, &n);
  if (p != a) PREC_PRIME_VIADIFF(p, *pd);
  return p;
}
/* smallest p > a */
ulong
init_primepointer_gt(ulong a, byteptr *pd)
{
  ulong n, p;
  prime_table_next_p(a, pd, &p, &n);
  if (p == a) NEXT_PRIME_VIADIFF(p, *pd);
  return p;
}

GEN
boundfact(GEN n, ulong lim)
{
  switch(typ(n))
  {
    case t_INT: return Z_factor_limit(n,lim);
    case t_FRAC: {
      pari_sp av = avma;
      GEN a = Z_factor_limit(gel(n,1),lim);
      GEN b = Z_factor_limit(gel(n,2),lim);
      gel(b,2) = ZC_neg(gel(b,2));
      return gerepilecopy(av, merge_factor_i(a,b));
    }
  }
  pari_err_TYPE("boundfact",n);
  return NULL; /* not reached */
}

/* NOT memory clean */
GEN
Z_smoothen(GEN N, GEN L, GEN *pP, GEN *pe)
{
  long i, j, l = lg(L);
  GEN e = new_chunk(l), P = new_chunk(l);
  for (i = j = 1; i < l; i++)
  {
    ulong p = uel(L,i);
    long v = Z_lvalrem(N, p, &N);
    if (v) { P[j] = p; e[j] = v; j++; if (is_pm1(N)) { N = NULL; break; } }
  }
  P[0] = evaltyp(t_VECSMALL) | evallg(j); *pP = P;
  e[0] = evaltyp(t_VECSMALL) | evallg(j); *pe = e; return N;
}
/***********************************************************************/
/**                                                                   **/
/**                    SIMPLE FACTORISATIONS                          **/
/**                                                                   **/
/***********************************************************************/
/* Factor n and output [p,e,c] where
 * p, e and c are vecsmall with n = prod{p[i]^e[i]} and c[i] = p[i]^e[i] */
GEN
factoru_pow(ulong n)
{
  GEN f = cgetg(4,t_VEC);
  pari_sp av = avma;
  GEN F, P, E, p, e, c;
  long i, l;
  /* enough room to store <= 15 * [p,e,p^e] (OK if n < 2^64) */
  (void)new_chunk((15 + 1)*3);
  F = factoru(n);
  P = gel(F,1);
  E = gel(F,2); l = lg(P);
  avma = av;
  gel(f,1) = p = cgetg(l,t_VECSMALL);
  gel(f,2) = e = cgetg(l,t_VECSMALL);
  gel(f,3) = c = cgetg(l,t_VECSMALL);
  for(i = 1; i < l; i++)
  {
    p[i] = P[i];
    e[i] = E[i];
    c[i] = upowuu(p[i], e[i]);
  }
  return f;
}

static GEN
factorlim(GEN n, ulong lim)
{ return lim? Z_factor_limit(n, lim): Z_factor(n); }
/* factor p^n - 1, assuming p prime. If lim != 0, limit factorization to
 * primes <= lim */
GEN
factor_pn_1_limit(GEN p, long n, ulong lim)
{
  pari_sp av = avma;
  GEN A = factorlim(subiu(p,1), lim), d = divisorsu(n);
  long i, pp = itos_or_0(p);
  for(i=2; i<lg(d); i++)
  {
    GEN B;
    if (pp && d[i]%pp==0 && (
       ((pp&3)==1 && (d[i]&1)) ||
       ((pp&3)==3 && (d[i]&3)==2) ||
       (pp==2 && (d[i]&7)==4)))
    {
      GEN f=factor_Aurifeuille_prime(p,d[i]);
      B = factorlim(f, lim);
      A = merge_factor(A, B, (void*)&cmpii, cmp_nodata);
      B = factorlim(diviiexact(polcyclo_eval(d[i],p), f), lim);
    }
    else
      B = factorlim(polcyclo_eval(d[i],p), lim);
    A = merge_factor(A, B, (void*)&cmpii, cmp_nodata);
  }
  return gerepilecopy(av, A);
}
GEN
factor_pn_1(GEN p, ulong n)
{ return factor_pn_1_limit(p, n, 0); }

#if 0
static GEN
to_mat(GEN p, long e) {
  GEN B = cgetg(3, t_MAT);
  gel(B,1) = mkcol(p);
  gel(B,2) = mkcol(utoipos(e)); return B;
}
/* factor phi(n) */
GEN
factor_eulerphi(GEN n)
{
  pari_sp av = avma;
  GEN B = NULL, A, P, E, AP, AE;
  long i, l, v = vali(n);

  l = lg(n);
  /* result requires less than this: at most expi(n) primes */
  (void)new_chunk(bit_accuracy(l) * (l /*p*/ + 3 /*e*/ + 2 /*vectors*/) + 3+2);
  if (v) { n = shifti(n, -v); v--; }
  A = Z_factor(n); P = gel(A,1); E = gel(A,2); l = lg(P);
  for(i = 1; i < l; i++)
  {
    GEN p = gel(P,i), q = subis(p,1), fa;
    long e = itos(gel(E,i)), w;

    w = vali(q); v += w; q = shifti(q,-w);
    if (! is_pm1(q))
    {
      fa = Z_factor(q);
      B = B? merge_factor(B, fa, (void*)&cmpii, cmp_nodata): fa;
    }
    if (e > 1) {
      if (B) {
        gel(B,1) = shallowconcat(gel(B,1), p);
        gel(B,2) = shallowconcat(gel(B,2), utoipos(e-1));
      } else
        B = to_mat(p, e-1);
    }
  }
  avma = av;
  if (!B) return v? to_mat(gen_2, v): trivial_fact();
  A = cgetg(3, t_MAT);
  P = gel(B,1); E = gel(B,2); l = lg(P);
  AP = cgetg(l+1, t_COL); gel(A,1) = AP; AP++;
  AE = cgetg(l+1, t_COL); gel(A,2) = AE; AE++;
  /* prepend "2^v" */
  gel(AP,0) = gen_2;
  gel(AE,0) = utoipos(v);
  for (i = 1; i < l; i++)
  {
    gel(AP,i) = icopy(gel(P,i));
    gel(AE,i) = icopy(gel(E,i));
  }
  return A;
}
#endif

/***********************************************************************/
/**                                                                   **/
/**         CHECK FACTORIZATION FOR ARITHMETIC FUNCTIONS              **/
/**                                                                   **/
/***********************************************************************/
static int
RgV_is_ZVpos(GEN v)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(v,i);
    if (typ(c) != t_INT || signe(c) <= 0) return 0;
  }
  return 1;
}
/* check whether v is a ZV with non-0 entries */
static int
RgV_is_ZVnon0(GEN v)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(v,i);
    if (typ(c) != t_INT || !signe(c)) return 0;
  }
  return 1;
}
/* check whether v is a ZV with non-zero entries OR exactly [0] */
static int
RgV_is_ZV0(GEN v)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(v,i);
    long s;
    if (typ(c) != t_INT) return 0;
    s = signe(c);
    if (!s) return (l == 2);
  }
  return 1;
}

static int
is_Z_factor_i(GEN f)
{ return typ(f) == t_MAT && lg(f) == 3 && RgV_is_ZVpos(gel(f,2)); }
int
is_Z_factorpos(GEN f)
{ return is_Z_factor_i(f) && RgV_is_ZVpos(gel(f,1)); }
int
is_Z_factor(GEN f)
{ return is_Z_factor_i(f) && RgV_is_ZV0(gel(f,1)); }
/* as is_Z_factorpos, also allow factor(0) */
int
is_Z_factornon0(GEN f)
{ return is_Z_factor_i(f) && RgV_is_ZVnon0(gel(f,1)); }
GEN
clean_Z_factor(GEN f)
{
  GEN P = gel(f,1);
  long n = lg(P)-1;
  if (n && equalim1(gel(P,1)))
    return mkmat2(vecslice(P,2,n), vecslice(gel(f,2),2,n));
  return f;
}
GEN
fuse_Z_factor(GEN f, GEN B)
{
  GEN P = gel(f,1), E = gel(f,2), P2,E2;
  long i, l = lg(P);
  if (l == 1) return f;
  for (i = 1; i < l; i++)
    if (absi_cmp(gel(P,i), B) > 0) break;
  if (i == l) return f;
  /* tail / initial segment */
  P2 = vecslice(P, i, l-1); P = vecslice(P, 1, i-1);
  E2 = vecslice(E, i, l-1); E = vecslice(E, 1, i-1);
  P = shallowconcat(P, mkvec(factorback2(P2,E2)));
  E = shallowconcat(E, mkvec(gen_1));
  return mkmat2(P, E);
}

/* n associated to a factorization of a positive integer: either N (t_INT)
 * a factorization matrix faN, or a t_VEC: [N, faN] */
GEN
check_arith_pos(GEN n, const char *f) {
  switch(typ(n))
  {
    case t_INT:
      if (signe(n) <= 0 ) pari_err_DOMAIN(f, "argument", "<=", gen_0, gen_0);
      return NULL;
    case t_VEC:
      if (lg(n) != 3 || typ(gel(n,1)) != t_INT) break;
      n = gel(n,2); /* fall through */
    case t_MAT:
      if (!is_Z_factorpos(n)) break;
      return n;
  }
  pari_err_TYPE(f,n);
  return NULL;
}
/* n associated to a factorization of a non-0 integer */
GEN
check_arith_non0(GEN n, const char *f) {
  switch(typ(n))
  {
    case t_INT:
      if (!signe(n)) pari_err_DOMAIN(f, "argument", "=", gen_0, gen_0);
      return NULL;
    case t_VEC:
      if (lg(n) != 3 || typ(gel(n,1)) != t_INT) break;
      n = gel(n,2); /* fall through */
    case t_MAT:
      if (!is_Z_factornon0(n)) break;
      return n;
  }
  pari_err_TYPE(f,n);
  return NULL;
}
/* n associated to a factorization of an integer */
GEN
check_arith_all(GEN n, const char *f) {
  switch(typ(n))
  {
    case t_INT:
      return NULL;
    case t_VEC:
      if (lg(n) != 3 || typ(gel(n,1)) != t_INT) break;
      n = gel(n,2); /* fall through */
    case t_MAT:
      if (!is_Z_factor(n)) break;
      return n;
  }
  pari_err_TYPE(f,n);
  return NULL;
}

/***********************************************************************/
/**                                                                   **/
/**                MISCELLANEOUS ARITHMETIC FUNCTIONS                 **/
/**                (ultimately depend on Z_factor())                  **/
/**                                                                   **/
/***********************************************************************/
/* set P,E from F. Check whether F is an integer and kill "factor" -1 */
static void
set_fact_check(GEN F, GEN *pP, GEN *pE, int *isint)
{
  GEN E, P;
  if (lg(F) != 3) pari_err_TYPE("divisors",F);
  P = gel(F,1);
  E = gel(F,2);
  RgV_check_ZV(E, "divisors");
  *isint = RgV_is_ZV(P);
  if (*isint)
  {
    long i, l = lg(P);
    /* skip -1 */
    if (l>1 && signe(gel(P,1)) < 0) { E++; P = vecslice(P,2,--l); }
    /* test for 0 */
    for (i = 1; i < l; i++)
      if (!signe(gel(P,i)) && signe(gel(E,i)))
        pari_err_DOMAIN("divisors", "argument", "=", gen_0, F);
  }
  *pP = P;
  *pE = E;
}
static void
set_fact(GEN F, GEN *pP, GEN *pE) { *pP = gel(F,1); *pE = gel(F,2); }

int
divisors_init(GEN n, GEN *pP, GEN *pE)
{
  long i,l;
  GEN E, P, e;
  int isint;

  switch(typ(n))
  {
    case t_INT:
      if (!signe(n)) pari_err_DOMAIN("divisors", "argument", "=", gen_0, gen_0);
      set_fact(absi_factor(n), &P,&E);
      isint = 1; break;
    case t_VEC:
      if (lg(n) != 3 || typ(gel(n,2)) !=t_MAT) pari_err_TYPE("divisors",n);
      set_fact_check(gel(n,2), &P,&E, &isint);
      break;
    case t_MAT:
      set_fact_check(n, &P,&E, &isint);
      break;
    default:
      set_fact(factor(n), &P,&E);
      isint = 0; break;
  }
  l = lg(P);
  e = cgetg(l, t_VECSMALL);
  for (i=1; i<l; i++)
  {
    e[i] = itos(gel(E,i));
    if (e[i] < 0) pari_err_TYPE("divisors [denominator]",n);
  }
  *pP = P; *pE = e; return isint;
}

GEN
divisors(GEN n)
{
  pari_sp av = avma;
  long i, j, l;
  ulong ndiv;
  GEN *d, *t, *t1, *t2, *t3, P, E, e;
  int isint = divisors_init(n, &P, &E);

  l = lg(E); e = cgetg(l, t_VECSMALL);
  for (i=1; i<l; i++) e[i] = E[i]+1;
  ndiv = itou_or_0( zv_prod_Z(e) );
  if (!ndiv || ndiv & ~LGBITS) pari_err_OVERFLOW("divisors");
  d = t = (GEN*) cgetg(ndiv+1,t_VEC);
  *++d = gen_1;
  if (isint)
  {
    for (i=1; i<l; i++)
      for (t1=t,j=E[i]; j; j--,t1=t2)
        for (t2=d, t3=t1; t3<t2; ) *++d = mulii(*++t3, gel(P,i));
    e = ZV_sort((GEN)t);
  } else {
    for (i=1; i<l; i++)
      for (t1=t,j=E[i]; j; j--,t1=t2)
        for (t2=d, t3=t1; t3<t2; ) *++d = gmul(*++t3, gel(P,i));
    e = (GEN)t;
  }
  return gerepileupto(av, e);
}

GEN
divisorsu(ulong n)
{
  pari_sp av = avma;
  long i, j, l;
  ulong nbdiv;
  GEN d, t, t1, t2, t3, P, e, fa = factoru(n);

  P = gel(fa,1); l = lg(P);
  e = gel(fa,2);
  nbdiv = 1;
  for (i=1; i<l; i++) nbdiv *= 1+e[i];
  d = t = cgetg(nbdiv+1,t_VECSMALL);
  *++d = 1;
  for (i=1; i<l; i++)
    for (t1=t,j=e[i]; j; j--,t1=t2)
      for (t2=d, t3=t1; t3<t2; ) *(++d) = *(++t3) * P[i];
  vecsmall_sort(t);
  return gerepileupto(av, t);
}

static GEN
corefa(GEN fa)
{
  GEN P = gel(fa,1), E = gel(fa,2), c = gen_1;
  long i;
  for (i=1; i<lg(P); i++)
    if (mod2(gel(E,i))) c = mulii(c,gel(P,i));
  return c;
}
static GEN
core2fa(GEN fa)
{
  GEN P = gel(fa,1), E = gel(fa,2), c = gen_1, f = gen_1;
  long i;
  for (i=1; i<lg(P); i++)
  {
    long e = itos(gel(E,i));
    if (e & 1)  c = mulii(c, gel(P,i));
    if (e != 1) f = mulii(f, powiu(gel(P,i), e >> 1));
  }
  return mkvec2(c,f);
}
GEN
corepartial(GEN n, long all)
{
  pari_sp av = avma;
  if (typ(n) != t_INT) pari_err_TYPE("corepartial",n);
  return gerepileuptoint(av, corefa(Z_factor_limit(n,all)));
}
GEN
core2partial(GEN n, long all)
{
  pari_sp av = avma;
  if (typ(n) != t_INT) pari_err_TYPE("core2partial",n);
  return gerepilecopy(av, core2fa(Z_factor_limit(n,all)));
}
static GEN
core2_i(GEN n)
{
  GEN f = core(n);
  if (!signe(f)) return mkvec2(gen_0, gen_1);
  switch(typ(n))
  {
    case t_VEC: n = gel(n,1); break;
    case t_MAT: n = factorback(n); break;
  }
  return mkvec2(f, sqrtint(diviiexact(n, f)));
}
GEN
core2(GEN n) { pari_sp av = avma; return gerepilecopy(av, core2_i(n)); }

GEN
core0(GEN n,long flag) { return flag? core2(n): core(n); }

static long
_mod4(GEN c) {
  long r, s = signe(c);
  if (!s) return 0;
  r = mod4(c); if (s < 0) r = 4-r;
  return r;
}

long
corediscs(long D, ulong *f)
{
  /* D = f^2 dK */
  long dK = D>=0 ? (long) coreu(D) : -(long) coreu(-(ulong) D);
  ulong dKmod4 = ((ulong)dK)&3UL;
  if (dKmod4 == 2 || dKmod4 == 3)
    dK *= 4;
  if (f) *f = usqrt((ulong)(D/dK));
  return D;
}

GEN
coredisc(GEN n)
{
  pari_sp av = avma;
  GEN c = core(n);
  if (_mod4(c)<=1) return c; /* c = 0 or 1 mod 4 */
  return gerepileuptoint(av, shifti(c,2));
}

GEN
coredisc2(GEN n)
{
  pari_sp av = avma;
  GEN y = core2_i(n);
  GEN c = gel(y,1), f = gel(y,2);
  if (_mod4(c)<=1) return gerepilecopy(av, y);
  y = cgetg(3,t_VEC);
  gel(y,1) = shifti(c,2);
  gel(y,2) = gmul2n(f,-1); return gerepileupto(av, y);
}

GEN
coredisc0(GEN n,long flag) { return flag? coredisc2(n): coredisc(n); }

long
omega(GEN n)
{
  pari_sp av = avma;
  GEN F, P;
  if ((F = check_arith_non0(n,"omega"))) {
    long n;
    P = gel(F,1); n = lg(P)-1;
    if (n && equalim1(gel(P,1))) n--;
    return n;
  }
  else if (lgefint(n) == 3)
  {
    if (n[2] == 1) return 0;
    F = factoru(n[2]);
  }
  else
    F = absi_factor(n);
  P = gel(F,1); avma = av; return lg(P)-1;
}

long
bigomega(GEN n)
{
  pari_sp av = avma;
  GEN F, E;
  if ((F = check_arith_non0(n,"bigomega")))
  {
    GEN P = gel(F,1);
    long n = lg(P)-1;
    E = gel(F,2);
    if (n && equalim1(gel(P,1))) E = vecslice(E,2,n);
    E = ZV_to_zv(E);
  }
  else if (lgefint(n) == 3)
  {
    if (n[2] == 1) return 0;
    F = factoru(n[2]);
    E = gel(F,2);
  }
  else
    E = ZV_to_zv(gel(absi_factor(n), 2));
  avma = av; return zv_sum(E);
}

/* assume f = factoru(n), possibly with 0 exponents. Return phi(n) */
ulong
eulerphiu_fact(GEN f)
{
  GEN P = gel(f,1), E = gel(f,2);
  long i, m = 1, l = lg(P);
  for (i = 1; i < l; i++)
  {
    ulong p = P[i], e = E[i];
    if (!e) continue;
    if (p == 2)
    { if (e > 1) m <<= e-1; }
    else
    {
      m *= (p-1);
      if (e > 1) m *= upowuu(p, e-1);
    }
  }
  return m;
}
ulong
eulerphiu(ulong n)
{
  pari_sp av = avma;
  GEN F;
  if (!n) return 2;
  F = factoru(n);
  avma = av; return eulerphiu_fact(F);
}
GEN
eulerphi(GEN n)
{
  pari_sp av = avma;
  GEN Q, F, P, E;
  long i, l;

  if ((F = check_arith_all(n,"eulerphi")))
  {
    F = clean_Z_factor(F);
    n = (typ(n) == t_VEC)? gel(n,1): factorback(F);
    if (lgefint(n) == 3)
    {
      ulong e;
      F = mkmat2(ZV_to_nv(gel(F,1)), ZV_to_nv(gel(F,2)));
      e = eulerphiu_fact(F);
      avma = av; return utoipos(e);
    }
  }
  else if (lgefint(n) == 3) return utoipos(eulerphiu(uel(n,2)));
  else
    F = absi_factor(n);
  if (!signe(n)) return gen_2;
  P = gel(F,1);
  E = gel(F,2); l = lg(P);
  Q = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN p = gel(P,i), q;
    ulong v = itou(gel(E,i));
    q = subiu(p,1);
    if (v != 1) q = mulii(q, v == 2? p: powiu(p, v-1));
    gel(Q,i) = q;
  }
  return gerepileuptoint(av, ZV_prod(Q));
}

static GEN
numdiv_aux(GEN F)
{
  GEN x, E = gel(F,2);
  long i, l = lg(E);
  x = cgetg(l, t_VECSMALL);
  for (i=1; i<l; i++) x[i] = itou(gel(E,i))+1;
  return x;
}
GEN
numdiv(GEN n)
{
  pari_sp av = avma;
  GEN F, E;
  long i, l;
  if ((F = check_arith_non0(n,"numdiv")))
  {
    F = clean_Z_factor(F);
    E = numdiv_aux(F);
  }
  else if (lgefint(n) == 3)
  {
    if (n[2] == 1) return gen_1;
    F = factoru(n[2]);
    E = gel(F,2); l = lg(E);
    for (i=1; i<l; i++) E[i]++;
  }
  else
    E = numdiv_aux(absi_factor(n));
  return gerepileuptoint(av, zv_prod_Z(E));
}

/* 1 + p + ... + p^v, p != 2^BIL - 1 */
static GEN
u_euler_sumdiv(ulong p, long v)
{
  GEN u = utoipos(1 + p); /* can't overflow */
  for (; v > 1; v--) u = addsi(1, mului(p, u));
  return u;
}
/* 1 + q + ... + q^v */
static GEN
euler_sumdiv(GEN q, long v)
{
  GEN u = addui(1, q);
  for (; v > 1; v--) u = addui(1, mulii(q, u));
  return u;
}
static GEN
u_euler_sumdivk(ulong p, long v, long k) { return euler_sumdiv(powuu(p,k), v); }
static GEN
euler_sumdivk(GEN p, long v, long k) { return euler_sumdiv(powiu(p,k), v); }

static GEN
sumdiv_aux(GEN F)
{
  GEN x, P = gel(F,1), E = gel(F,2);
  long i, l = lg(P);
  x = cgetg(l, t_VEC);
  for (i=1; i<l; i++) gel(x,i) = euler_sumdiv(gel(P,i), itou(gel(E,i)));
  return x;
}
GEN
sumdiv(GEN n)
{
  pari_sp av = avma;
  GEN F, P, E;
  long i, l;

  if ((F = check_arith_non0(n,"sumdiv")))
  {
    F = clean_Z_factor(F);
    P = sumdiv_aux(F);
  }
  else if (lgefint(n) == 3)
  {
    if (n[2] == 1) return gen_1;
    F = factoru(n[2]);
    P = gel(F,1);
    E = gel(F,2); l = lg(P);
    for (i=1; i<l; i++) gel(P,i) = u_euler_sumdiv(P[i], E[i]);
  }
  else
    P = sumdiv_aux(absi_factor(n));
  return gerepileuptoint(av, ZV_prod(P));
}

static GEN
sumdivk_aux(GEN F, long k)
{
  GEN x, P = gel(F,1), E = gel(F,2);
  long i, l = lg(P);
  x = cgetg(l, t_VEC);
  for (i=1; i<l; i++) gel(x,i) = euler_sumdivk(gel(P,i), gel(E,i)[2], k);
  return x;
}
GEN
sumdivk(GEN n, long k)
{
  pari_sp av = avma;
  GEN E, F, P;
  long i, l, k1;

  if (!k) return numdiv(n);
  if (k == 1) return sumdiv(n);
  if (k ==-1) return gerepileupto(av, gdiv(sumdiv(n), n));
  k1 = k;
  if (k < 0)  k = -k;
  if ((F = check_arith_non0(n,"sumdivk")))
  {
    F = clean_Z_factor(F);
    P = sumdivk_aux(F,k);
  }
  else if (lgefint(n) == 3)
  {
    if (n[2] == 1) return gen_1;
    F = factoru(n[2]);
    P = gel(F,1);
    E = gel(F,2); l = lg(P);
    for (i=1; i<l; i++) gel(P,i) = u_euler_sumdivk(P[i], E[i], k);
  }
  else
    P = sumdivk_aux(absi_factor(n), k);
  P = ZV_prod(P);
  if (k1 > 0) return gerepileuptoint(av, P);
  return gerepileupto(av, gdiv(P, powiu(n,k)));
}

/* K t_VECSMALL of k >= 0 */
GEN
usumdivkvec(ulong n, GEN K)
{
  pari_sp av = avma;
  GEN F = factoru(n), P = gel(F,1), E = gel(F,2), Z, S;
  long i,j, l = lg(P), lK = lg(K);
  Z = cgetg(l, t_VEC);
  S = cgetg(lK, t_VEC);
  for (j=1; j<lK; j++)
  {
    long k = K[j];
    for (i=1; i<l; i++) gel(Z,i) = u_euler_sumdivk(P[i], E[i], k);
    gel(S,j) = ZV_prod(Z);
  }
  return gerepilecopy(av, S);
}

long
uissquarefree_fact(GEN f)
{
  GEN E = gel(f,2);
  long i, l = lg(E);
  for (i = 1; i < l; i++)
    if (E[i] > 1) return 0;
  return 1;
}
long
uissquarefree(ulong n)
{
  if (!n) return 0;
  return moebiusu(n)? 1: 0;
}
long
Z_issquarefree(GEN n)
{
  switch(lgefint(n))
  {
    case 2: return 0;
    case 3: return uissquarefree(n[2]);
  }
  return moebius(n)? 1: 0;
}
long
issquarefree(GEN x)
{
  pari_sp av;
  GEN d;
  switch(typ(x))
  {
    case t_INT: return Z_issquarefree(x);
    case t_POL:
      if (!signe(x)) return 0;
      av = avma; d = RgX_gcd(x, RgX_deriv(x));
      avma = av; return (lg(d) == 3);
    default: pari_err_TYPE("issquarefree",x);
      return 0; /* not reached */
  }
}

/*********************************************************************/
/**                                                                 **/
/**                    DIGITS / SUM OF DIGITS                       **/
/**                                                                 **/
/*********************************************************************/

/* set v[i] = 1 iff B^i is needed in the digits_dac algorithm */
static void
set_vexp(GEN v, long l)
{
  long m;
  if (v[l]) return;
  v[l] = 1; m = l>>1;
  set_vexp(v, m);
  set_vexp(v, l-m);
}

/* return all needed B^i for DAC algorithm, for lz digits */
static GEN
get_vB(GEN T, long lz, void *E, struct bb_ring *r)
{
  GEN vB, vexp = const_vecsmall(lz, 0);
  long i, l = (lz+1) >> 1;
  vexp[1] = 1;
  vexp[2] = 1;
  set_vexp(vexp, lz);
  vB = zerovec(lz); /* unneeded entries remain = 0 */
  gel(vB, 1) = T;
  for (i = 2; i <= l; i++)
    if (vexp[i])
    {
      long j = i >> 1;
      GEN B2j = r->sqr(E, gel(vB,j));
      gel(vB,i) = odd(i)? r->mul(E, B2j, T): B2j;
    }
  return vB;
}

static void
gen_digits_dac(GEN x, GEN vB, long l, GEN *z,
               void *E, GEN div(void *E, GEN a, GEN b, GEN *r))
{
  GEN q, r;
  long m = l>>1;
  if (l==1) { *z=x; return; }
  q = div(E, x, gel(vB,m), &r);
  gen_digits_dac(r, vB, m, z, E, div);
  gen_digits_dac(q, vB, l-m, z+m, E, div);
}

static GEN
gen_fromdigits_dac(GEN x, GEN vB, long i, long l, void *E,
                   GEN add(void *E, GEN a, GEN b),
                   GEN mul(void *E, GEN a, GEN b))
{
  GEN a, b;
  long m = l>>1;
  if (l==1) return gel(x,i);
  a = gen_fromdigits_dac(x, vB, i, m, E, add, mul);
  b = gen_fromdigits_dac(x, vB, i+m, l-m, E, add, mul);
  return add(E, a, mul(E, b, gel(vB, m)));
}

static GEN
gen_digits_i(GEN x, GEN B, long n, void *E, struct bb_ring *r,
                          GEN (*div)(void *E, GEN x, GEN y, GEN *r))
{
  GEN z, vB;
  if (n==1) retmkvec(gcopy(x));
  vB = get_vB(B, n, E, r);
  z = cgetg(n+1, t_VEC);
  gen_digits_dac(x, vB, n, (GEN*)(z+1), E, div);
  return z;
}

GEN
gen_digits(GEN x, GEN B, long n, void *E, struct bb_ring *r,
                          GEN (*div)(void *E, GEN x, GEN y, GEN *r))
{
  pari_sp av = avma;
  return gerepilecopy(av, gen_digits_i(x, B, n, E, r, div));
}

GEN
gen_fromdigits(GEN x, GEN B, void *E, struct bb_ring *r)
{
  pari_sp av = avma;
  long n = lg(x)-1;
  GEN vB = get_vB(B, n, E, r);
  GEN z = gen_fromdigits_dac(x, vB, 1, n, E, r->add, r->mul);
  return gerepilecopy(av, z);
}

static GEN
_addii(void *data /* ignored */, GEN x, GEN y)
{ (void)data; return addii(x,y); }
static GEN
_sqri(void *data /* ignored */, GEN x) { (void)data; return sqri(x); }
static GEN
_mulii(void *data /* ignored */, GEN x, GEN y)
 { (void)data; return mulii(x,y); }
static GEN
_dvmdii(void *data /* ignored */, GEN x, GEN y, GEN *r)
 { (void)data; return dvmdii(x,y,r); }

static struct bb_ring Z_ring = { _addii, _mulii, _sqri };

static GEN
check_basis(GEN B)
{
  if (!B) return utoipos(10);
  if (typ(B)!=t_INT) pari_err_TYPE("digits",B);
  if (cmpis(B,2)<0) pari_err_DOMAIN("digits","B","<",gen_2,B);
  return B;
}

/* x has l digits in base B, write them to z[0..l-1], vB[i] = B^i */
static void
digits_dacsmall(GEN x, GEN vB, long l, ulong* z)
{
  pari_sp av = avma;
  GEN q,r;
  long m;
  if (l==1) { *z=itou(x); return; }
  m=l>>1;
  q = dvmdii(x, gel(vB,m), &r);
  digits_dacsmall(q,vB,l-m,z);
  digits_dacsmall(r,vB,m,z+l-m);
  avma = av;
}

GEN
digits(GEN x, GEN B)
{
  pari_sp av=avma;
  long lz;
  GEN z, vB;
  if (typ(x)!=t_INT) pari_err_TYPE("digits",x);
  B = check_basis(B);
  if (!signe(x))       {avma = av; return cgetg(1,t_VEC); }
  if (absi_cmp(x,B)<0) {avma = av; retmkvec(absi(x)); }
  if (Z_ispow2(B))
  {
    long k = expi(B);
    if (k == 1) return binaire(x);
    if (k < BITS_IN_LONG)
    {
      (void)new_chunk(4*(expi(x) + 2)); /* HACK */
      z = binary_2k_zv(x, k);
      avma = av; return Flv_to_ZV(z);
    }
    else
    {
      avma = av; return binary_2k(x, k);
    }
  }
  if (signe(x) < 0) x = absi(x);
  lz = logint(x,B,NULL);
  if (lgefint(B)>3)
  {
    z = gerepileupto(av, gen_digits_i(x, B, lz, NULL, &Z_ring, _dvmdii));
    vecreverse_inplace(z);
    return z;
  }
  else
  {
    vB = get_vB(B, lz, NULL, &Z_ring);
    (void)new_chunk(3*lz); /* HACK */
    z = zero_zv(lz);
    digits_dacsmall(x,vB,lz,(ulong*)(z+1));
    avma = av; return vecsmall_to_vec(z);
  }
}

GEN
fromdigits(GEN x, GEN B)
{
  pari_sp av = avma;
  if (typ(x)!=t_VEC || !RgV_is_ZV(x)) pari_err_TYPE("fromdigits",x);
  B = check_basis(B);
  if (lg(x)==1) { avma = av; return gen_0; }
  x = vecreverse(x);
  return gerepileupto(av, gen_fromdigits(x, B, NULL, &Z_ring));
}

static ulong DS[] ={
  0,1,2,3,4,5,6,7,8,9,1,2,3,4,5,6,7,8,9,10,2,3,4,5,6,7,8,9,10,11,3,4,5,6,7,8,
  9,10,11,12,4,5,6,7,8,9,10,11,12,13,5,6,7,8,9,10,11,12,13,14,6,7,8,9,10,11,
  12,13,14,15,7,8,9,10,11,12,13,14,15,16,8,9,10,11,12,13,14,15,16,17,9,10,11,
  12,13,14,15,16,17,18,1,2,3,4,5,6,7,8,9,10,2,3,4,5,6,7,8,9,10,11,3,4,5,6,7,8,
  9,10,11,12,4,5,6,7,8,9,10,11,12,13,5,6,7,8,9,10,11,12,13,14,6,7,8,9,10,11,
  12,13,14,15,7,8,9,10,11,12,13,14,15,16,8,9,10,11,12,13,14,15,16,17,9,10,11,
  12,13,14,15,16,17,18,10,11,12,13,14,15,16,17,18,19,2,3,4,5,6,7,8,9,10,11,3,
  4,5,6,7,8,9,10,11,12,4,5,6,7,8,9,10,11,12,13,5,6,7,8,9,10,11,12,13,14,6,7,8,
  9,10,11,12,13,14,15,7,8,9,10,11,12,13,14,15,16,8,9,10,11,12,13,14,15,16,17,
  9,10,11,12,13,14,15,16,17,18,10,11,12,13,14,15,16,17,18,19,11,12,13,14,15,
  16,17,18,19,20,3,4,5,6,7,8,9,10,11,12,4,5,6,7,8,9,10,11,12,13,5,6,7,8,9,10,
  11,12,13,14,6,7,8,9,10,11,12,13,14,15,7,8,9,10,11,12,13,14,15,16,8,9,10,11,
  12,13,14,15,16,17,9,10,11,12,13,14,15,16,17,18,10,11,12,13,14,15,16,17,18,
  19,11,12,13,14,15,16,17,18,19,20,12,13,14,15,16,17,18,19,20,21,4,5,6,7,8,9,
  10,11,12,13,5,6,7,8,9,10,11,12,13,14,6,7,8,9,10,11,12,13,14,15,7,8,9,10,11,
  12,13,14,15,16,8,9,10,11,12,13,14,15,16,17,9,10,11,12,13,14,15,16,17,18,10,
  11,12,13,14,15,16,17,18,19,11,12,13,14,15,16,17,18,19,20,12,13,14,15,16,17,
  18,19,20,21,13,14,15,16,17,18,19,20,21,22,5,6,7,8,9,10,11,12,13,14,6,7,8,9,
  10,11,12,13,14,15,7,8,9,10,11,12,13,14,15,16,8,9,10,11,12,13,14,15,16,17,9,
  10,11,12,13,14,15,16,17,18,10,11,12,13,14,15,16,17,18,19,11,12,13,14,15,16,
  17,18,19,20,12,13,14,15,16,17,18,19,20,21,13,14,15,16,17,18,19,20,21,22,14,
  15,16,17,18,19,20,21,22,23,6,7,8,9,10,11,12,13,14,15,7,8,9,10,11,12,13,14,
  15,16,8,9,10,11,12,13,14,15,16,17,9,10,11,12,13,14,15,16,17,18,10,11,12,13,
  14,15,16,17,18,19,11,12,13,14,15,16,17,18,19,20,12,13,14,15,16,17,18,19,20,
  21,13,14,15,16,17,18,19,20,21,22,14,15,16,17,18,19,20,21,22,23,15,16,17,18,
  19,20,21,22,23,24,7,8,9,10,11,12,13,14,15,16,8,9,10,11,12,13,14,15,16,17,9,
  10,11,12,13,14,15,16,17,18,10,11,12,13,14,15,16,17,18,19,11,12,13,14,15,16,
  17,18,19,20,12,13,14,15,16,17,18,19,20,21,13,14,15,16,17,18,19,20,21,22,14,
  15,16,17,18,19,20,21,22,23,15,16,17,18,19,20,21,22,23,24,16,17,18,19,20,21,
  22,23,24,25,8,9,10,11,12,13,14,15,16,17,9,10,11,12,13,14,15,16,17,18,10,11,
  12,13,14,15,16,17,18,19,11,12,13,14,15,16,17,18,19,20,12,13,14,15,16,17,18,
  19,20,21,13,14,15,16,17,18,19,20,21,22,14,15,16,17,18,19,20,21,22,23,15,16,
  17,18,19,20,21,22,23,24,16,17,18,19,20,21,22,23,24,25,17,18,19,20,21,22,23,
  24,25,26,9,10,11,12,13,14,15,16,17,18,10,11,12,13,14,15,16,17,18,19,11,12,
  13,14,15,16,17,18,19,20,12,13,14,15,16,17,18,19,20,21,13,14,15,16,17,18,19,
  20,21,22,14,15,16,17,18,19,20,21,22,23,15,16,17,18,19,20,21,22,23,24,16,17,
  18,19,20,21,22,23,24,25,17,18,19,20,21,22,23,24,25,26,18,19,20,21,22,23,24,
  25,26,27
};

ulong
sumdigitsu(ulong n)
{
  ulong s = 0;
  while (n) { s += DS[n % 1000]; n /= 1000; }
  return s;
}

/* res=array of 9-digits integers, return \sum_{0 <= i < l} sumdigits(res[i]) */
static ulong
sumdigits_block(ulong *res, long l)
{
  long s = sumdigitsu(*--res);
  while (--l > 0) s += sumdigitsu(*--res);
  return s;
}

GEN
sumdigits(GEN n)
{
  pari_sp av = avma;
  ulong s, *res;
  long l;

  if (typ(n) != t_INT) pari_err_TYPE("sumdigits", n);
  l = lgefint(n);
  switch(l)
  {
    case 2: return gen_0;
    case 3: return utoipos(sumdigitsu(n[2]));
  }
  res = convi(n, &l);
  if ((ulong)l < ULONG_MAX / 81)
  {
    s = sumdigits_block(res, l);
    avma = av; return utoipos(s);
  }
  else /* Huge. Overflows ulong */
  {
    const long L = (long)(ULONG_MAX / 81);
    GEN S = gen_0;
    while (l > L)
    {
      S = addiu(S, sumdigits_block(res, L));
      res += L; l -= L;
    }
    if (l)
      S = addiu(S, sumdigits_block(res, l));
    return gerepileuptoint(av, S);
  }
}

GEN
sumdigits0(GEN x, GEN B)
{
  pari_sp av = avma;
  GEN z;
  long lz;

  if (!B) return sumdigits(x);
  if (typ(x) != t_INT) pari_err_TYPE("sumdigits", x);
  B = check_basis(B);
  if (Z_ispow2(B))
  {
    long k = expi(B);
    if (k == 1) { avma = av; return utoi(hammingweight(x)); }
    if (k < BITS_IN_LONG)
    {
      GEN z = binary_2k_zv(x, k);
      if (lg(z)-1 > 1<<(BITS_IN_LONG-k)) /* may overflow */
        return gerepileuptoint(av, ZV_sum(Flv_to_ZV(z)));
      avma = av; return utoi(zv_sum(z));
    }
    return gerepileuptoint(av, ZV_sum(binary_2k(x, k)));
  }
  if (!signe(x))       { avma = av; return gen_0; }
  if (absi_cmp(x,B)<0) { avma = av; return absi(x); }
  if (equaliu(B,10))   { avma = av; return sumdigits(x); }
  lz = logint(x,B,NULL);
  z = gen_digits_i(x, B, lz, NULL, &Z_ring, _dvmdii);
  return gerepileuptoint(av, ZV_sum(z));
}
