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
/*********************************************************************/
/**                                                                 **/
/**               PSEUDO PRIMALITY (MILLER-RABIN)                   **/
/**                                                                 **/
/*********************************************************************/
typedef struct {
  ulong n, sqrt1, sqrt2, t1, t;
  long r1;
} Fl_MR_Jaeschke_t;

typedef struct {
  GEN n, sqrt1, sqrt2, t1, t;
  long r1;
} MR_Jaeschke_t;

static void
init_MR_Jaeschke(MR_Jaeschke_t *S, GEN n)
{
  if (signe(n) < 0) n = absi(n);
  S->n = n;
  S->t = addsi(-1,n);
  S->r1 = vali(S->t);
  S->t1 = shifti(S->t, -S->r1);
  S->sqrt1 = cgeti(lg(n)); S->sqrt1[1] = evalsigne(0)|evallgefint(2);
  S->sqrt2 = cgeti(lg(n)); S->sqrt2[1] = evalsigne(0)|evallgefint(2);
}
static void
Fl_init_MR_Jaeschke(Fl_MR_Jaeschke_t *S, ulong n)
{
  S->n = n;
  S->t = n-1;
  S->r1 = vals(S->t);
  S->t1 = S->t >> S->r1;
  S->sqrt1 = 0;
  S->sqrt2 = 0;
}

/* c = sqrt(-1) seen in bad_for_base. End-matching: compare or remember
 * If ends do mismatch, then we have factored n, and this information
 * should somehow be made available to the factoring machinery. But so
 * exceedingly rare... besides we use BSPW now. */
static int
MR_Jaeschke_ok(MR_Jaeschke_t *S, GEN c)
{
  if (signe(S->sqrt1))
  { /* saw one earlier: compare */
    if (!equalii(c, S->sqrt1) && !equalii(c, S->sqrt2))
    { /* too many sqrt(-1)s mod n */
      if (DEBUGLEVEL) {
        GEN z = gcdii(addii(c, S->sqrt1), S->n);
        pari_warn(warner,"found factor\n\t%Ps\ncurrently lost to the factoring machinery", z);
      }
      return 1;
    }
  } else { /* remember */
    affii(c, S->sqrt1);
    affii(subii(S->n, c), S->sqrt2);
  }
  return 0;
}
static int
Fl_MR_Jaeschke_ok(Fl_MR_Jaeschke_t *S, ulong c)
{
  if (S->sqrt1)
  { /* saw one earlier: compare */
    if (c != S->sqrt1 && c != S->sqrt2) return 1;
  } else { /* remember */
    S->sqrt1 = c;
    S->sqrt2 = S->n - c;
  }
  return 0;
}

/* is n strong pseudo-prime for base a ? 'End matching' (check for square
 * roots of -1) added by GN */
static int
bad_for_base(MR_Jaeschke_t *S, GEN a)
{
  pari_sp av = avma;
  long r;
  GEN c2, c = Fp_pow(a, S->t1, S->n);

  if (is_pm1(c) || equalii(S->t, c)) return 0;

  /* go fishing for -1, not for 1 (saves one squaring) */
  for (r = S->r1 - 1; r; r--) /* r1 - 1 squarings */
  {
    c2 = c; c = remii(sqri(c), S->n);
    if (equalii(S->t, c)) return MR_Jaeschke_ok(S, c2);
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"Rabin-Miller");
      c = gerepileuptoint(av, c);
    }
  }
  return 1;
}
static int
Fl_bad_for_base(Fl_MR_Jaeschke_t *S, ulong a)
{
  long r;
  ulong c2, c = Fl_powu(a, S->t1, S->n);

  if (c == 1 || c == S->t) return 0;

  /* go fishing for -1, not for 1 (saves one squaring) */
  for (r = S->r1 - 1; r; r--) /* r1 - 1 squarings */
  {
    c2 = c; c = Fl_sqr(c, S->n);
    if (c == S->t) return Fl_MR_Jaeschke_ok(S, c2);
  }
  return 1;
}

/* Miller-Rabin test for k random bases */
long
millerrabin(GEN n, long k)
{
  pari_sp av2, av = avma;
  ulong r;
  long i;
  MR_Jaeschke_t S;

  if (typ(n) != t_INT) pari_err_TYPE("millerrabin",n);
  if (signe(n)<=0) return 0;
  /* If |n| <= 3, check if n = +- 1 */
  if (lgefint(n)==3 && uel(n,2)<=3) return uel(n,2) != 1;

  if (!mod2(n)) return 0;
  init_MR_Jaeschke(&S, n); av2 = avma;
  for (i=1; i<=k; i++)
  {
    do r = umodui(pari_rand(), n); while (!r);
    if (DEBUGLEVEL > 4) err_printf("Miller-Rabin: testing base %ld\n", r);
    if (bad_for_base(&S, utoipos(r))) { avma = av; return 0; }
    avma = av2;
  }
  avma = av; return 1;
}

GEN
gispseudoprime(GEN x, long flag)
{ return flag? map_proto_lGL(millerrabin, x, flag): map_proto_lG(BPSW_psp,x); }

long
ispseudoprime(GEN x, long flag)
{ return flag? millerrabin(x, flag): BPSW_psp(x); }

/* As above for k bases taken in pr (i.e not random). We must have |n|>2 and
 * 1<=k<=11 (not checked) or k in {16,17} to select some special sets of bases.
 *
 * From Jaeschke, 'On strong pseudoprimes to several bases', Math.Comp. 61
 * (1993), 915--926  (see also http://www.utm.edu/research/primes/prove2.html),
 * we have:
 *
 * k == 4  (bases 2,3,5,7)  detects all composites
 *    n <     118 670 087 467 == 172243 * 688969  with the single exception of
 *    n ==      3 215 031 751 == 151 * 751 * 28351,
 *
 * k == 5  (bases 2,3,5,7,11)  detects all composites
 *    n <   2 152 302 898 747 == 6763 * 10627 * 29947,
 *
 * k == 6  (bases 2,3,...,13)  detects all composites
 *    n <   3 474 749 660 383 == 1303 * 16927 * 157543,
 *
 * k == 7  (bases 2,3,...,17)  detects all composites
 *    n < 341 550 071 728 321 == 10670053 * 32010157,
 * Even this limiting value is caught by an end mismatch between bases 5 and 17
 *
 * Moreover, the four bases chosen at
 *
 * k == 16  (2,13,23,1662803)  detects all composites up
 * to at least 10^12, and the combination at
 *
 * k == 17  (31,73)  detects most odd composites without prime factors > 100
 * in the range  n < 2^36  (with less than 250 exceptions, indeed with fewer
 * than 1400 exceptions up to 2^42). --GN */
int
Fl_MR_Jaeschke(ulong n, long k)
{
  const ulong pr[] =
    { 0, 2,3,5,7,11,13,17,19,23,29, 31,73, 2,13,23,1662803UL, };
  const ulong *p;
  ulong r;
  long i;
  Fl_MR_Jaeschke_t S;

  if (!(n & 1)) return 0;
  if (k == 16)
  { /* use smaller (faster) bases if possible */
    p = (n < 3215031751UL)? pr: pr+13;
    k = 4;
  }
  else if (k == 17)
  {
    p = (n < 1373653UL)? pr: pr+11;
    k = 2;
  }
  else p = pr; /* 2,3,5,... */
  Fl_init_MR_Jaeschke(&S, n);
  for (i=1; i<=k; i++)
  {
    r = p[i] % n; if (!r) break;
    if (Fl_bad_for_base(&S, r)) return 0;
  }
  return 1;
}

int
MR_Jaeschke(GEN n, long k)
{
  pari_sp av2, av = avma;
  const ulong pr[] =
    { 0, 2,3,5,7,11,13,17,19,23,29, 31,73, 2,13,23,1662803UL, };
  const ulong *p;
  long i;
  MR_Jaeschke_t S;

  if (lgefint(n) == 3) return Fl_MR_Jaeschke(uel(n,2), k);

  if (!mod2(n)) return 0;
  if      (k == 16) { p = pr+13; k = 4; } /* 2,13,23,1662803 */
  else if (k == 17) { p = pr+11; k = 2; } /* 31,73 */
  else p = pr; /* 2,3,5,... */
  init_MR_Jaeschke(&S, n); av2 = avma;
  for (i=1; i<=k; i++)
  {
    if (bad_for_base(&S, utoipos(p[i]))) { avma = av; return 0; }
    avma = av2;
  }
  avma = av; return 1;
}

/*********************************************************************/
/**                                                                 **/
/**                      PSEUDO PRIMALITY (LUCAS)                   **/
/**                                                                 **/
/*********************************************************************/
/* compute n-th term of Lucas sequence modulo N.
 * v_{k+2} = P v_{k+1} - v_k, v_0 = 2, v_1 = P.
 * Assume n > 0 */
static GEN
LucasMod(GEN n, ulong P, GEN N)
{
  pari_sp av = avma;
  GEN nd = int_MSW(n);
  long i, m = *nd, j = 1+bfffo((ulong)m);
  GEN v = utoipos(P), v1 = utoipos(P*P - 2);

  m <<= j; j = BITS_IN_LONG - j;
  for (i=lgefint(n)-2;;) /* cf. leftright_pow */
  {
    for (; j; m<<=1,j--)
    { /* v = v_k, v1 = v_{k+1} */
      if (m < 0)
      { /* set v = v_{2k+1}, v1 = v_{2k+2} */
        v = subis(mulii(v,v1), (long)P);
        v1= subis(sqri(v1), 2);
      }
      else
      {/* set v = v_{2k}, v1 = v_{2k+1} */
        v1= subis(mulii(v,v1), (long)P);
        v = subis(sqri(v), 2);
      }
      v = modii(v, N);
      v1= modii(v1,N);
      if (gc_needed(av,1))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"LucasMod");
        gerepileall(av, 2, &v,&v1);
      }
    }
    if (--i == 0) return v;
    j = BITS_IN_LONG;
    nd=int_precW(nd);
    m = *nd;
  }
}
/* compute n-th term of Lucas sequence modulo N.
 * v_{k+2} = P v_{k+1} - v_k, v_0 = 2, v_1 = P.
 * Assume n > 0 */
static ulong
u_LucasMod(ulong n, ulong P, ulong N)
{
  long j = 1 + bfffo(n);
  ulong v = P, v1 = P*P - 2, mP = N - P, m2 = N - 2, m = n << j;

  j = BITS_IN_LONG - j;
  for (; j; m<<=1,j--)
  { /* v = v_k, v1 = v_{k+1} */
    if (((long)m) < 0)
    { /* set v = v_{2k+1}, v1 = v_{2k+2} */
      v = Fl_add(Fl_mul(v,v1,N), mP, N);
      v1= Fl_add(Fl_mul(v1,v1,N),m2, N);
    }
    else
    {/* set v = v_{2k}, v1 = v_{2k+1} */
      v1= Fl_add(Fl_mul(v,v1,N),mP, N);
      v = Fl_add(Fl_mul(v,v,N), m2, N);
    }
  }
  return v;
}

int
uislucaspsp(ulong n)
{
  long i, v;
  ulong b, z, m2, m = n + 1;

  for (b=3, i=0;; b+=2, i++)
  {
    ulong c = b*b - 4; /* = 1 mod 4 */
    if (krouu(n % c, c) < 0) break;
    if (i == 64 && uissquareall(n, &c)) return 0; /* oo loop if N = m^2 */
  }
  if (!m) return 0; /* neither 2^32-1 nor 2^64-1 are Lucas-pp */
  v = vals(m); m >>= v;
  z = u_LucasMod(m, b, n);
  if (z == 2) return 1;
  m2 = n - 2;
  if (z == m2) return 1;
  for (i=1; i<v; i++)
  {
    if (!z) return 1;
    z = Fl_add(Fl_mul(z,z, n), m2, n);
    if (z == 2) return 0;
  }
  return 0;
}
/* check that N not a square first (taken care of here, but inefficient)
 * assume N > 3 */
static int
IsLucasPsP(GEN N)
{
  pari_sp av = avma;
  GEN N_2, m, z;
  long i, v;
  ulong b;

  for (b=3, i=0;; b+=2, i++)
  {
    ulong c = b*b - 4; /* = 1 mod 4 */
    if (i == 64 && Z_issquare(N)) return 0; /* avoid oo loop if N = m^2 */
    if (krouu(umodiu(N,c), c) < 0) break;
  }
  m = addis(N,1); v = vali(m); m = shifti(m,-v);
  z = LucasMod(m, b, N);
  if (equaliu(z, 2)) return 1;
  N_2 = subis(N,2);
  if (equalii(z, N_2)) return 1;
  for (i=1; i<v; i++)
  {
    if (!signe(z)) return 1;
    z = modii(subis(sqri(z), 2), N);
    if (equaliu(z, 2)) return 0;
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"IsLucasPsP");
      z = gerepileupto(av, z);
    }
  }
  return 0;
}

/* assume u odd, u > 1 */
static int
iu_coprime(GEN N, ulong u)
{
  const ulong n = umodiu(N, u);
  return (n == 1 || gcduodd(n, u) == 1);
}
/* assume u odd, u > 1 */
static int
uu_coprime(ulong n, ulong u)
{
  return gcduodd(n, u) == 1;
}

/* composite strong 2-pseudoprime < 1016801 whose prime divisors are > 101 */
static int
is_2_prp_101(ulong n)
{
  switch(n) {
  case 42799:
  case 49141:
  case 88357:
  case 90751:
  case 104653:
  case 130561:
  case 196093:
  case 220729:
  case 253241:
  case 256999:
  case 271951:
  case 280601:
  case 357761:
  case 390937:
  case 458989:
  case 486737:
  case 489997:
  case 514447:
  case 580337:
  case 741751:
  case 838861:
  case 873181:
  case 877099:
  case 916327:
  case 976873:
  case 983401: return 1;
  } return 0;
}

static int
u_2_prp(ulong n)
{
  Fl_MR_Jaeschke_t S;
  Fl_init_MR_Jaeschke(&S, n);
  return Fl_bad_for_base(&S, 2) == 0;
}
static int
uBPSW_psp(ulong n) { return (u_2_prp(n) && uislucaspsp(n)); }

int
uisprime(ulong n)
{
  if (n < 103)
    switch(n)
    {
      case 2:
      case 3:
      case 5:
      case 7:
      case 11:
      case 13:
      case 17:
      case 19:
      case 23:
      case 29:
      case 31:
      case 37:
      case 41:
      case 43:
      case 47:
      case 53:
      case 59:
      case 61:
      case 67:
      case 71:
      case 73:
      case 79:
      case 83:
      case 89:
      case 97:
      case 101: return 1;
      default: return 0;
    }
  if (!odd(n)) return 0;
#ifdef LONG_IS_64BIT
  /* 16294579238595022365 = 3*5*7*11*13*17*19*23*29*31*37*41*43*47*53
   *  7145393598349078859 = 59*61*67*71*73*79*83*89*97*101 */
  if (!uu_coprime(n, 16294579238595022365UL) ||
      !uu_coprime(n,  7145393598349078859UL)) return 0;
#else
  /* 4127218095 = 3*5*7*11*13*17*19*23*37
   * 3948078067 = 29*31*41*43*47*53
   * 4269855901 = 59*83*89*97*101
   * 1673450759 = 61*67*71*73*79 */
  if (!uu_coprime(n, 4127218095UL) ||
      !uu_coprime(n, 3948078067UL) ||
      !uu_coprime(n, 1673450759UL) ||
      !uu_coprime(n, 4269855901UL)) return 0;
#endif
  if (n < 10427) return 1;
  if (n < 1016801) return !is_2_prp_101(n) && u_2_prp(n);
  return uBPSW_psp(n);
}

/* assume no prime divisor <= 101 */
int
uisprime_101(ulong n)
{
  if (n < 10427) return 1;
  if (n < 1016801) return !is_2_prp_101(n) && u_2_prp(n);
  return uBPSW_psp(n);
}

/* assume no prime divisor <= 661 */
int
uisprime_661(ulong n) { return uBPSW_psp(n); }

long
BPSW_psp(GEN N)
{
  pari_sp av;
  MR_Jaeschke_t S;
  int k;

  if (typ(N) != t_INT) pari_err_TYPE("BPSW_psp",N);
  if (signe(N) <= 0) return 0;
  if (lgefint(N) == 3) return uisprime(uel(N,2));
  if (!mod2(N)) return 0;
#ifdef LONG_IS_64BIT
  /* 16294579238595022365 = 3*5*7*11*13*17*19*23*29*31*37*41*43*47*53
   *  7145393598349078859 = 59*61*67*71*73*79*83*89*97*101 */
  if (!iu_coprime(N, 16294579238595022365UL) ||
      !iu_coprime(N,  7145393598349078859UL)) return 0;
#else
  /* 4127218095 = 3*5*7*11*13*17*19*23*37
   * 3948078067 = 29*31*41*43*47*53
   * 4269855901 = 59*83*89*97*101
   * 1673450759 = 61*67*71*73*79 */
  if (!iu_coprime(N, 4127218095UL) ||
      !iu_coprime(N, 3948078067UL) ||
      !iu_coprime(N, 1673450759UL) ||
      !iu_coprime(N, 4269855901UL)) return 0;
#endif
  /* no prime divisor < 103 */
  av = avma;
  init_MR_Jaeschke(&S, N);
  k = (!bad_for_base(&S, gen_2) && IsLucasPsP(N));
  avma = av; return k;
}

/* can we write n = x^k ? Assume N has no prime divisor <= 2^14.
 * Not memory clean */
long
isanypower_nosmalldiv(GEN N, GEN *px)
{
  GEN x = N, y;
  ulong mask = 7;
  long ex, k = 1;
  forprime_t T;
  while (Z_issquareall(x, &y)) { k <<= 1; x = y; }
  while ( (ex = is_357_power(x, &y, &mask)) ) { k *= ex; x = y; }
  (void)u_forprime_init(&T, 11, ULONG_MAX);
  /* stop when x^(1/k) < 2^14 */
  while ( (ex = is_pth_power(x, &y, &T, 15)) ) { k *= ex; x = y; }
  *px = x; return k;
}

/* no prime divisor <= 2^14 (> 661) */
long
BPSW_psp_nosmalldiv(GEN N)
{
  pari_sp av;
  MR_Jaeschke_t S;
  long l = lgefint(N);
  int k;

  if (l == 3) return uisprime_661(uel(N,2));
  av = avma;
  /* N large: test for pure power, rarely succeeds, but requires < 1% of
   * compositeness test times */
  if (bit_accuracy(l) > 512 && isanypower_nosmalldiv(N, &N) != 1)
  {
    avma = av; return 0;
  }
  init_MR_Jaeschke(&S, N);
  k = (!bad_for_base(&S, gen_2) && IsLucasPsP(N));
  avma = av; return k;
}

/***********************************************************************/
/**                                                                   **/
/**                       Pocklington-Lehmer                          **/
/**                        P-1 primality test                         **/
/**                                                                   **/
/***********************************************************************/
/* Assume x BPSW pseudoprime. Check whether it's small enough to be certified
 * prime (< 2^64). Reference for strong 2-pseudoprimes:
 *   http://www.cecm.sfu.ca/Pseudoprimes/index-2-to-64.html */
static int
BPSW_isprime_small(GEN x)
{
  long l = lgefint(x);
#ifdef LONG_IS_64BIT
  return (l == 3);
#else
  return (l <= 4);
#endif
}

/* Brillhart, Lehmer, Selfridge test (Crandall & Pomerance, Th 4.1.5)
 * N^(1/3) <= f fully factored, f | N-1. If pl831(p) is true for
 * any prime divisor p of f, then any divisor of N is 1 mod f.
 * In that case return 1 iff N is prime */
static int
BLS_test(GEN N, GEN f)
{
  GEN c1, c2, r, q;
  q = dvmdii(N, f, &r);
  if (!is_pm1(r)) return 0;
  c2 = dvmdii(q, f, &c1);
  /* N = 1 + f c1 + f^2 c2, 0 <= c_i < f; check whether it is of the form
   * (1 + f a)(1 + fb) */
  return ! Z_issquare(subii(sqri(c1), shifti(c2,2)));
}

/*assume N>1, p^e || N-1. Find a witness a(p) such that
 * a^(N-1) = 1 (mod N)
 * a^(N-1)/p - 1 invertible mod N.
 * Proves that any divisor of N is 1 mod p^e */
static ulong
pl831(GEN N, GEN p)
{
  pari_sp ltop = avma, av;
  ulong a;
  GEN Nmunp = diviiexact(addis(N,-1), p);
  av = avma;
  for(a = 2;; a++, avma = av)
  {
    GEN b = Fp_pow(utoipos(a), Nmunp, N);
    GEN c = Fp_pow(b,p,N), g = gcdii(addis(b,-1), N);
    if (!is_pm1(c)) return 0;
    if (is_pm1(g)) { avma=ltop; return a; }
    if (!equalii(g,N)) return 0;
  }
}
/* Assume x BPSW pseudoprime. Return NULL if not prime, and a primality
 * certificate otherwise */
static GEN isprimePL(GEN N);
static GEN
check_prime(GEN p)
{
  if (BPSW_isprime_small(p)) return gen_1;
  if (expi(p) <= 250) return isprimePL(p);
  return isprimeAPRCL(p)? gen_2: NULL;
}
/* initialize Selfridge / Pocklington-Lehmer test, return 0
 * if proven composite */
static int
selfridge_init(GEN N, GEN *pF, GEN *pf)
{
  GEN cbrtN = sqrtnint(N, 3);
  GEN N_1 = addis(N,-1);
  GEN F = Z_factor_until(N_1, sqri(cbrtN));
  GEN f = factorback(F); /* factored part of N-1, f^3 > N */
  *pF = gel(F,1);
  *pf = f;
  /* smooth or N^(1/2)-smooth (Pocklington) or N^(1/3)-smooth (BLS) */
  return equalii(f, N_1) || cmpii(sqri(f), N) > 0 || BLS_test(N,f);
}
/* Assume N is a strong BPSW pseudoprime, Pocklington-Lehmer primality proof.
 *
 * return gen_0 (non-prime), gen_1 (small prime), matrix (large prime)
 *
 * The matrix has 3 columns, [a,b,c] with
 * a[i] prime factor of N-1,
 * b[i] witness for a[i] as in pl831
 * c[i] isprimePL(a[i]) */
static GEN
isprimePL(GEN N)
{
  pari_sp ltop = avma;
  long i, l;
  int eps;
  GEN P, W, R, F, f;

  if (typ(N) != t_INT) pari_err_TYPE("isprimePL",N);
  eps = cmpis(N,2);
  if (eps <= 0) return eps? gen_0: gen_1;
  /* N > 2 */
  if (!selfridge_init(N, &F, &f)) { avma = ltop; return gen_0; }
  if (DEBUGLEVEL>3)
  {
    err_printf("Pocklington-Lehmer: proving primality of N = %Ps\n", N);
    err_printf("Pocklington-Lehmer: N-1 factored up to %Ps! (%.3Ps%%)\n", f, divri(itor(f,LOWDEFAULTPREC), N));
    err_printf("Pocklington-Lehmer: N-1 smooth enough! Computing certificate\n");
  }
  l = lg(F);
  P = cgetg(l,t_COL);
  W = cgetg(l,t_COL);
  R = cgetg(l,t_COL);
  for(i=1; i<l; i++)
  {
    GEN p = gel(F,i);
    ulong witness = pl831(N,p);

    if (!witness) { avma = ltop; return gen_0; }
    gel(P,i) = p;
    gel(W,i) = utoipos(witness);
    gel(R,i) = check_prime(p);
    if (!gel(R,i))
    { /* composite in prime factorisation ! */
      err_printf("Not a prime: %Ps", p);
      pari_err_BUG("isprimePL [false prime number]");
    }
  }
  return gerepilecopy(ltop, mkmat3(P,W,R));
}

/* F is a vector whose n first entries are primes. For each of them,
 * find a PL witness */
static long
isprimeSelfridge(GEN N, GEN F, long n)
{
  long i;
  for(i = 1; i <= n; i++)
    if (! pl831(N, gel(F,i))) return 0;
  return 1;
}

/* BPSW_psp(N) && !BPSW_isprime_small(N). Prove N prime  */
static long
BPSW_isprime_big(GEN N)
{
  ulong B = minuu(1UL<<19, maxprime());
  GEN E, p, U, F, N_1 = subiu(N,1);
  GEN fa = Z_factor_limit(N_1, B), P = gel(fa,1);
  long n = lg(P)-1;

  p = gel(P,n);
  /* fully factored */
  if (cmpiu(p,B) <= 0 ||
      (BPSW_psp_nosmalldiv(p)
      && (BPSW_isprime_small(N) || BPSW_isprime_big(p))))
    return isprimeSelfridge(N,P, n);

  E = gel(fa,2);
  U = powii(p, gel(E,n)); /* unfactored part of N-1 */
  /* n >= 2, since 2 and p divide  N-1 */
  if (n == 2)
    F = powii(gel(P,1), gel(E,1));
  else
    F = diviiexact(N_1,  U);

  /* N-1 = F U, F factored, U possibly composite */
  if (cmpii(F, U) >= 0) /* 1/2-smooth */
    return isprimeSelfridge(N,P, n-1);
  if (cmpii(sqri(F), U) >= 0) /* 1/3-smooth */
    return BLS_test(N, F) && isprimeSelfridge(N,P, n-1);
  return isprimeAPRCL(N);
}

/* assume N a BPSW pseudoprime, in particular, it is odd > 2 */
long
BPSW_isprime(GEN N)
{
  pari_sp av;
  long res;
  if (BPSW_isprime_small(N)) return 1;
  av = avma; res = BPSW_isprime_big(N);
  avma = av; return res;
}

GEN
gisprime(GEN x, long flag)
{
  switch (flag)
  {
    case 0: return map_proto_lG(isprime,x);
    case 1: return map_proto_G(isprimePL,x);
    case 2: return map_proto_lG(isprimeAPRCL,x);
  }
  pari_err_FLAG("gisprime");
  return NULL;
}

long
isprime(GEN x) { return BPSW_psp(x) && BPSW_isprime(x); }

/***********************************************************************/
/**                                                                   **/
/**                          PRIME NUMBERS                            **/
/**                                                                   **/
/***********************************************************************/

static struct {
  ulong p;
  long n;
} prime_table[] = {
  {           0,          0},
  {        7919,       1000},
  {       17389,       2000},
  {       27449,       3000},
  {       37813,       4000},
  {       48611,       5000},
  {       59359,       6000},
  {       70657,       7000},
  {       81799,       8000},
  {       93179,       9000},
  {      104729,      10000},
  {      224737,      20000},
  {      350377,      30000},
  {      479909,      40000},
  {      611953,      50000},
  {      746773,      60000},
  {      882377,      70000},
  {     1020379,      80000},
  {     1159523,      90000},
  {     1299709,     100000},
  {     2750159,     200000},
  {     7368787,     500000},
  {    15485863,    1000000},
  {    32452843,    2000000},
  {    86028121,    5000000},
  {   179424673,   10000000},
  {   373587883,   20000000},
  {   982451653,   50000000},
  {  2038074743,  100000000},
  {  4000000483UL,189961831},
  {  4222234741UL,200000000},
#if BITS_IN_LONG == 64
  { 11037271757,  500000000},
  { 22801763489, 1000000000},
  { 47055833459, 2000000000},
  {122430513841, 5000000000},
  {200000000507, 8007105083},
#endif
};
static const int prime_table_len = numberof(prime_table);

/* find prime closest to n in prime_table. */
static long
prime_table_closest_p(ulong n)
{
  long i;
  for (i = 1; i < prime_table_len; i++)
  {
    ulong p = prime_table[i].p;
    if (p > n)
    {
      ulong u = n - prime_table[i-1].p;
      if (p - n > u) i--;
      break;
    }
  }
  if (i == prime_table_len) i = prime_table_len - 1;
  return i;
}

/* return the n-th successor of prime p > 2 */
static GEN
prime_successor(ulong p, ulong n)
{
  forprime_t S;
  ulong i;
  forprime_init(&S, utoipos(p+1), NULL);
  for (i = 1; i < n; i++) (void)forprime_next(&S);
  return forprime_next(&S);
}
/* find the N-th prime */
static GEN
prime_table_find_n(ulong N)
{
  byteptr d;
  ulong n, p, maxp = maxprime();
  long i;
  for (i = 1; i < prime_table_len; i++)
  {
    n = prime_table[i].n;
    if (n > N)
    {
      ulong u = N - prime_table[i-1].n;
      if (n - N > u) i--;
      break;
    }
  }
  if (i == prime_table_len) i = prime_table_len - 1;
  p = prime_table[i].p;
  n = prime_table[i].n;
  if (n > N && p > maxp)
  {
    i--;
    p = prime_table[i].p;
    n = prime_table[i].n;
  }
  /* if beyond prime table, then n <= N */
  d = diffptr + n;
  if (n > N)
  {
    n -= N;
    do { n--; PREC_PRIME_VIADIFF(p,d); } while (n) ;
  }
  else if (n < N)
  {
    n = N-n;
    if (p > maxp) return prime_successor(p, n);
    do {
      if (!*d) return prime_successor(p, n);
      n--; NEXT_PRIME_VIADIFF(p,d);
    } while (n) ;
  }
  return utoipos(p);
}

ulong
uprime(long N)
{
  pari_sp av = avma;
  GEN p;
  if (N <= 0) pari_err_DOMAIN("prime", "n", "<=",gen_0, stoi(N));
  p = prime_table_find_n(N);
  if (lgefint(p) != 3) pari_err_OVERFLOW("uprime");
  avma = av; return p[2];
}
GEN
prime(long N)
{
  pari_sp av = avma;
  GEN p;
  if (N <= 0) pari_err_DOMAIN("prime", "n", "<=",gen_0, stoi(N));
  new_chunk(4); /*HACK*/
  p = prime_table_find_n(N);
  avma = av; return icopy(p);
}

/* random b-bit prime */
GEN
randomprime(GEN N)
{
  pari_sp av = avma, av2;
  GEN a, b, d;
  if (!N)
    for(;;)
    {
      ulong p = random_bits(31);
      if (uisprime(p)) return utoipos(p);
    }
  switch(typ(N))
  {
    case t_INT:
      a = gen_2;
      b = subiu(N,1); /* between 2 and N-1 */
      d = subiu(N,2);
      if (signe(d) <= 0)
        pari_err_DOMAIN("randomprime","N", "<=", gen_2, N);
      break;
    case t_VEC:
      if (lg(N) != 3) pari_err_TYPE("randomprime",N);
      a = gel(N,1);
      b = gel(N,2);
      if (gcmp(b, a) < 0)
        pari_err_DOMAIN("randomprime","b-a", "<", gen_0, mkvec2(a,b));
      if (typ(a) != t_INT)
      {
        a = gceil(a);
        if (typ(a) != t_INT) pari_err_TYPE("randomprime",a);
      }
      if (typ(b) != t_INT)
      {
        b = gfloor(b);
        if (typ(b) != t_INT) pari_err_TYPE("randomprime",b);
      }
      if (cmpis(a, 2) < 0)
      {
        a = gen_2;
        d = subiu(b,1);
      }
      else
        d = addiu(subii(b,a), 1);
      if (signe(d) <= 0)
        pari_err_DOMAIN("randomprime","floor(b) - max(ceil(a),2)", "<",
                        gen_0, mkvec2(a,b));
      break;
    default:
      pari_err_TYPE("randomprime", N);
      return NULL; /*notreached*/
  }
  av2 = avma;
  for (;;)
  {
    GEN p = addii(a, randomi(d));
    if (BPSW_psp(p)) return gerepileuptoint(av, p);
    avma = av2;
  }
}

/* set *pp = nextprime(a) = p
 *     *pd so that NEXT_PRIME_VIADIFF(d, p) = nextprime(p+1)
 *     *pn so that p = the n-th prime
 * error if nextprime(a) is out of primetable bounds */
void
prime_table_next_p(ulong a, byteptr *pd, ulong *pp, ulong *pn)
{
  byteptr d;
  ulong p, n, maxp = maxprime();
  long i = prime_table_closest_p(a);
  p = prime_table[i].p;
  if (p > a && p > maxp)
  {
    i--;
    p = prime_table[i].p;
  }
  /* if beyond prime table, then p <= a */
  n = prime_table[i].n;
  d = diffptr + n;
  if (p < a)
  {
    if (a > maxp) pari_err_MAXPRIME(a);
    do { n++; NEXT_PRIME_VIADIFF(p,d); } while (p < a);
  }
  else if (p != a)
  {
    do { n--; PREC_PRIME_VIADIFF(p,d); } while (p > a) ;
    if (p < a) { NEXT_PRIME_VIADIFF(p,d); n++; }
  }
  *pn = n;
  *pp = p;
  *pd = d;
}

ulong
uprimepi(ulong a)
{
  ulong p, n, maxp = maxprime();
  if (a <= maxp)
  {
    byteptr d;
    prime_table_next_p(a, &d, &p, &n);
    return p == a? n: n-1;
  }
  else
  {
    long i = prime_table_closest_p(a);
    forprime_t S;
    p = prime_table[i].p;
    if (p > a)
    {
      i--;
      p = prime_table[i].p;
    }
    /* p = largest prime in table <= a */
    n = prime_table[i].n;
    (void)u_forprime_init(&S, p+1, a);
    for (; p; n++) p = u_forprime_next(&S);
    return n-1;
  }
}

GEN
primepi(GEN x)
{
  pari_sp av = avma;
  GEN pp, nn, N = typ(x) == t_INT? x: gfloor(x);
  forprime_t S;
  ulong n, p;
  long i, l;
  if (typ(N) != t_INT) pari_err_TYPE("primepi",N);
  if (signe(N) <= 0) return gen_0;
  avma = av; l = lgefint(N);
  if (l == 3) return utoi(uprimepi(N[2]));
  i = prime_table_len-1;
  p = prime_table[i].p;
  n = prime_table[i].n;
  (void)forprime_init(&S, utoipos(p+1), N);
  nn = setloop(utoipos(n));
  pp = gen_0;
  for (; pp; incloop(nn)) pp = forprime_next(&S);
  return gerepileuptoint(av, subiu(nn,1));
}

/* pi(x) < x/log x * (1 + 1/log x + 2.51/log^2 x)), x>=355991 [ Dusart ]
 * pi(x) < x/(log x - 1.1), x >= 60184 [ Dusart ]
 * ? \p9
 * ? M = 0; for(x = 4, 60184, M = max(M, log(x) - x/primepi(x))); M
 * %1 = 1.11196252 */
double
primepi_upper_bound(double x)
{
  if (x >= 355991)
  {
    double L = 1/log(x);
    return x * L * (1 + L + 2.51*L*L);
  }
  if (x >= 60184) return x / (log(x) - 1.1);
  if (x < 5) return 2; /* don't bother */
  return x / (log(x) - 1.111963);
}
/* pi(x) > x/log x (1 + 1/log x), x >= 599 [ Dusart ]
 * pi(x) > x / (log x + 2), x >= 55 [ Rosser ] */
double
primepi_lower_bound(double x)
{
  if (x >= 599)
  {
    double L = 1/log(x);
    return x * L * (1 + L);
  }
  if (x < 55) return 0; /* don't bother */
  return x / (log(x) + 2.);
}
GEN
gprimepi_upper_bound(GEN x)
{
  pari_sp av = avma;
  double L;
  if (typ(x) != t_INT) x = gfloor(x);
  if (expi(x) <= 1022)
  {
    avma = av;
    return dbltor(primepi_upper_bound(gtodouble(x)));
  }
  x = itor(x, LOWDEFAULTPREC);
  L = 1 / rtodbl(logr_abs(x));
  x = mulrr(x, dbltor(L * (1 + L + 2.51*L*L)));
  return gerepileuptoleaf(av, x);
}
GEN
gprimepi_lower_bound(GEN x)
{
  pari_sp av = avma;
  double L;
  if (typ(x) != t_INT) x = gfloor(x);
  if (cmpiu(x, 55) <= 0) return gen_0;
  if (expi(x) <= 1022)
  {
    avma = av;
    return dbltor(primepi_lower_bound(gtodouble(x)));
  }
  x = itor(x, LOWDEFAULTPREC);
  L = 1 / rtodbl(logr_abs(x));
  x = mulrr(x, dbltor(L * (1 + L)));
  return gerepileuptoleaf(av, x);
}

GEN
primes(long n)
{
  forprime_t S;
  long i;
  GEN y;
  if (n <= 0) return cgetg(1, t_VEC);
  y = cgetg(n+1, t_VEC);
  (void)new_chunk(3*n); /*HACK*/
  u_forprime_init(&S, 2, ULONG_MAX);
  avma = (pari_sp)y;
  for (i = 1; i <= n; i++) gel(y, i) = utoipos( u_forprime_next(&S) );
  return y;
}
GEN
primes_zv(long n)
{
  forprime_t S;
  long i;
  GEN y;
  if (n <= 0) return cgetg(1, t_VECSMALL);
  y = cgetg(n+1,t_VECSMALL);
  u_forprime_init(&S, 2, ULONG_MAX);
  for (i = 1; i <= n; i++) y[i] =  u_forprime_next(&S);
  avma = (pari_sp)y; return y;
}
GEN
primes0(GEN N)
{
  switch(typ(N))
  {
    case t_INT: return primes(itos(N));
    case t_VEC:
      if (lg(N) == 3) return primes_interval(gel(N,1),gel(N,2));
  }
  pari_err_TYPE("primes", N);
  return NULL;
}

GEN
primes_interval(GEN a, GEN b)
{
  pari_sp av = avma;
  forprime_t S;
  long i, n;
  GEN y, d, p;
  if (typ(a) != t_INT)
  {
    a = gceil(a);
    if (typ(a) != t_INT) pari_err_TYPE("primes_interval",a);
  }
  if (typ(b) != t_INT)
  {
    b = gfloor(b);
    if (typ(b) != t_INT) pari_err_TYPE("primes_interval",b);
  }
  if (signe(a) < 0) a = gen_2;
  d = subii(b, a);
  if (signe(d) < 0 || signe(b) <= 0) { avma = av; return cgetg(1, t_VEC); }
  if (lgefint(b) == 3)
  {
    avma = av;
    y = primes_interval_zv(itou(a), itou(b));
    n = lg(y); settyp(y, t_VEC);
    for (i = 1; i < n; i++) gel(y,i) = utoipos(y[i]);
    return y;
  }
  /* at most d+1 primes in [a,b]. If d large, try better bound to lower
   * memory use */
  if (cmpiu(d,100000) > 0)
  {
    GEN D = gsub(gprimepi_upper_bound(b), gprimepi_lower_bound(a));
    D = ceil_safe(D);
    if (cmpii(D, d) < 0) d = D;
  }
  n = itos(d)+1;
  forprime_init(&S, a, b);
  y = cgetg(n+1, t_VEC); i = 1;
  while ((p = forprime_next(&S))) gel(y, i++) = icopy(p);
  setlg(y, i); return gerepileupto(av, y);
}

/* a <= b, at most d primes in [a,b]. Return them */
static GEN
primes_interval_i(ulong a, ulong b, ulong d)
{
  ulong p, i = 1, n = d + 1;
  forprime_t S;
  GEN y = cgetg(n+1, t_VECSMALL);
  pari_sp av = avma;
  u_forprime_init(&S, a, b);
  while ((p = u_forprime_next(&S))) y[i++] = p;
  avma = av; setlg(y, i); stackdummy((pari_sp)(y + i), (pari_sp)(y + n+1));
  return y;
}
GEN
primes_interval_zv(ulong a, ulong b)
{
  ulong d;
  if (!a) return primes_upto_zv(b);
  if (b < a) return cgetg(1, t_VECSMALL);
  d = b - a;
  if (d > 100000UL)
  {
    ulong D = (ulong)ceil(primepi_upper_bound(b)-primepi_lower_bound(a));
    if (D < d) d = D;
  }
  return primes_interval_i(a, b, d);
}
GEN
primes_upto_zv(ulong b)
{
  ulong d;
  if (b < 2) return cgetg(1, t_VECSMALL);
  d = (b > 100000UL)? (ulong)primepi_upper_bound(b): b;
  return primes_interval_i(2, b, d);
}

/***********************************************************************/
/**                                                                   **/
/**                       PRIVATE PRIME TABLE                         **/
/**                                                                   **/
/***********************************************************************/
/* delete dummy NULL entries */
static void
cleanprimetab(GEN T)
{
  long i,j, l = lg(T);
  for (i = j = 1; i < l; i++)
    if (T[i]) T[j++] = T[i];
  setlg(T,j);
}
/* remove p from T */
static void
rmprime(GEN T, GEN p)
{
  long i;
  if (typ(p) != t_INT) pari_err_TYPE("removeprimes",p);
  i = ZV_search(T, p);
  if (!i)
    pari_err_DOMAIN("removeprime","prime","not in",
                    strtoGENstr("primetable"), p);
  gunclone(gel(T,i)); gel(T,i) = NULL;
  cleanprimetab(T);
}

/*stolen from ZV_union_shallow() : clone entries from y */
static GEN
addp_union(GEN x, GEN y)
{
  long i, j, k, lx = lg(x), ly = lg(y);
  GEN z = cgetg(lx + ly - 1, t_VEC);
  i = j = k = 1;
  while (i<lx && j<ly)
  {
    int s = cmpii(gel(x,i), gel(y,j));
    if (s < 0)
      gel(z,k++) = gel(x,i++);
    else if (s > 0)
      gel(z,k++) = gclone(gel(y,j++));
    else {
      gel(z,k++) = gel(x,i++);
      j++;
    }
  }
  while (i<lx) gel(z,k++) = gel(x,i++);
  while (j<ly) gel(z,k++) = gclone(gel(y,j++));
  setlg(z, k); return z;
}

/* p is NULL, or a single element or a row vector with "primes" to add to
 * prime table. */
static GEN
addp(GEN *T, GEN p)
{
  pari_sp av = avma;
  long i, l;
  GEN v;

  if (!p || lg(p) == 1) return *T;
  if (!is_vec_t(typ(p))) p = mkvec(p);

  RgV_check_ZV(p, "addprimes");
  v = gen_indexsort_uniq(p, (void*)&cmpii, &cmp_nodata);
  p = vecpermute(p, v);
  if (cmpiu(gel(p,1), 2) < 0) pari_err_DOMAIN("addprimes", "p", "<", gen_2,p);
  p = addp_union(*T, p);
  l = lg(p);
  if (l != lg(*T))
  {
    GEN old = *T, t = cgetalloc(t_VEC, l);
    for (i = 1; i < l; i++) gel(t,i) = gel(p,i);
    *T = t; free(old);
  }
  avma = av; return *T;
}
GEN
addprimes(GEN p) { return addp(&primetab, p); }

static GEN
rmprimes(GEN T, GEN prime)
{
  long i,tx;

  if (!prime) return T;
  tx = typ(prime);
  if (is_vec_t(tx))
  {
    if (prime == T)
    {
      for (i=1; i < lg(prime); i++) gunclone(gel(prime,i));
      setlg(prime, 1);
    }
    else
    {
      for (i=1; i < lg(prime); i++) rmprime(T, gel(prime,i));
    }
    return T;
  }
  rmprime(T, prime); return T;
}
GEN
removeprimes(GEN prime) { return rmprimes(primetab, prime); }
