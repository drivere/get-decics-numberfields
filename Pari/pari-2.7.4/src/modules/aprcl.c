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
/*                    THE APRCL PRIMALITY TEST                     */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

typedef struct Red {
/* global data */
  GEN N; /* prime we are certifying */
  GEN N2; /* floor(N/2) */
/* globa data for flexible window */
  long k, lv;
  ulong mask;
/* reduction data */
  long n;
  GEN C; /* polcyclo(n) */
  GEN (*red)(GEN x, struct Red*);
} Red;

typedef struct Cache { /* data associated to p^k */
  GEN aall, tall;
  GEN cyc;
  GEN E;
  GEN eta;
  GEN matvite, matinvvite;
  GEN avite, pkvite;
  ulong ctsgt; /* DEBUG */
} Cache;

static GEN
makepoldeg1(GEN c, GEN d)
{
  GEN z;
  if (signe(c)) {
    z = cgetg(4,t_POL); z[1] = evalsigne(1);
    gel(z,2) = d; gel(z,3) = c;
  } else if (signe(d)) {
    z = cgetg(3,t_POL); z[1] = evalsigne(1);
    gel(z,2) = d;
  } else {
    z = cgetg(2,t_POL); z[1] = evalsigne(0);
  }
  return z;
}

/* T mod polcyclo(p), assume deg(T) < 2p */
static GEN
red_cyclop(GEN T, long p)
{
  long i, d;
  GEN y, z;

  d = degpol(T) - p; /* < p */
  if (d <= -2) return T;

  /* reduce mod (x^p - 1) */
  y = ZX_mod_Xnm1(T, p);
  z = y+2;

  /* reduce mod x^(p-1) + ... + 1 */
  d = p-1;
  if (degpol(y) == d)
    for (i=0; i<d; i++) gel(z,i) = subii(gel(z,i), gel(z,d));
  return normalizepol_lg(y, d+2);
}

/* x t_VECSMALL, as red_cyclo2n_ip */
static GEN
u_red_cyclo2n_ip(GEN x, long n)
{
  long i, pow2 = 1L<<(n-1);
  GEN z;

  for (i = lg(x)-1; i>pow2; i--) x[i-pow2] -= x[i];
  for (; i>0; i--)
    if (x[i]) break;
  i += 2;
  z = cgetg(i, t_POL); z[1] = evalsigne(1);
  for (i--; i>=2; i--) gel(z,i) = stoi(x[i-1]);
  return z;
}
/* x t_POL, n > 0. Return x mod polcyclo(2^n) = (x^(2^(n-1)) + 1). IN PLACE */
static GEN
red_cyclo2n_ip(GEN x, long n)
{
  long i, pow2 = 1L<<(n-1);
  for (i = lg(x)-1; i>pow2+1; i--)
    if (signe(gel(x,i))) gel(x,i-pow2) = subii(gel(x,i-pow2), gel(x,i));
  return normalizepol_lg(x, i+1);
}
static GEN
red_cyclo2n(GEN x, long n) { return red_cyclo2n_ip(leafcopy(x), n); }

/* x a non-zero VECSMALL */
static GEN
smallpolrev(GEN x)
{
  long i,j, lx = lg(x);
  GEN y;

  while (lx-- && x[lx]==0) /* empty */;
  i = lx+2; y = cgetg(i,t_POL);
  y[1] = evalsigne(1);
  for (j=2; j<i; j++) gel(y,j) = stoi(x[j-1]);
  return y;
}

/* x polynomial in t_VECSMALL form, T t_POL return x mod T */
static GEN
u_red(GEN x, GEN T) {
  return RgX_rem(smallpolrev(x), T);
}

/* special case R->C = polcyclo(2^n) */
static GEN
_red_cyclo2n(GEN x, Red *R) {
  return centermod_i(red_cyclo2n(x, R->n), R->N, R->N2);
}
/* special case R->C = polcyclo(p) */
static GEN
_red_cyclop(GEN x, Red *R) {
  return centermod_i(red_cyclop(x, R->n), R->N, R->N2);
}
static GEN
_red(GEN x, Red *R) {
  return centermod_i(grem(x, R->C), R->N, R->N2);
}
static GEN
_redsimple(GEN x, Red *R) { return centermodii(x, R->N, R->N2); }

static GEN
sqrmod(GEN x, Red *R) {
  return R->red(gsqr(x), R);
}

static GEN
sqrconst(GEN pol, Red *R)
{
  GEN z = cgetg(3,t_POL);
  gel(z,2) = centermodii(sqri(gel(pol,2)), R->N, R->N2);
  z[1] = pol[1]; return z;
}

/* pol^2 mod (x^2+x+1, N) */
static GEN
sqrmod3(GEN pol, Red *R)
{
  GEN a,b,bma,A,B;
  long lv = lg(pol);

  if (lv==2) return pol;
  if (lv==3) return sqrconst(pol, R);
  a = gel(pol,3);
  b = gel(pol,2); bma = subii(b,a);
  A = centermodii(mulii(a,addii(b,bma)), R->N, R->N2);
  B = centermodii(mulii(bma,addii(a,b)), R->N, R->N2);
  return makepoldeg1(A,B);
}

/* pol^2 mod (x^2+1,N) */
static GEN
sqrmod4(GEN pol, Red *R)
{
  GEN a,b,A,B;
  long lv = lg(pol);

  if (lv==2) return pol;
  if (lv==3) return sqrconst(pol, R);
  a = gel(pol,3);
  b = gel(pol,2);
  A = centermodii(mulii(a, shifti(b,1)), R->N, R->N2);
  B = centermodii(mulii(subii(b,a),addii(b,a)), R->N, R->N2);
  return makepoldeg1(A,B);
}

/* pol^2 mod (polcyclo(5),N) */
static GEN
sqrmod5(GEN pol, Red *R)
{
  GEN c2,b,c,d,A,B,C,D;
  long lv = lg(pol);

  if (lv==2) return pol;
  if (lv==3) return sqrconst(pol, R);
  c = gel(pol,3); c2 = shifti(c,1);
  d = gel(pol,2);
  if (lv==4)
  {
    A = sqri(d);
    B = mulii(c2, d);
    C = sqri(c);
    A = centermodii(A, R->N, R->N2);
    B = centermodii(B, R->N, R->N2);
    C = centermodii(C, R->N, R->N2); return mkpoln(3,A,B,C);
  }
  b = gel(pol,4);
  if (lv==5)
  {
    A = mulii(b, subii(c2,b));
    B = addii(sqri(c), mulii(b, subii(shifti(d,1),b)));
    C = subii(mulii(c2,d), sqri(b));
    D = mulii(subii(d,b), addii(d,b));
  }
  else
  { /* lv == 6 */
    GEN a = gel(pol,5), a2 = shifti(a,1);
    /* 2a(d - c) + b(2c - b) */
    A = addii(mulii(a2, subii(d,c)), mulii(b, subii(c2,b)));
    /* c(c - 2a) + b(2d - b) */
    B = addii(mulii(c, subii(c,a2)), mulii(b, subii(shifti(d,1),b)));
    /* (a-b)(a+b) + 2c(d - a) */
    C = addii(mulii(subii(a,b),addii(a,b)), mulii(c2,subii(d,a)));
    /* 2a(b - c) + (d-b)(d+b) */
    D = addii(mulii(a2, subii(b,c)), mulii(subii(d,b), addii(d,b)));
  }
  A = centermodii(A, R->N, R->N2);
  B = centermodii(B, R->N, R->N2);
  C = centermodii(C, R->N, R->N2);
  D = centermodii(D, R->N, R->N2); return mkpoln(4,A,B,C,D);
}

static GEN
_mul(GEN x, GEN y, Red *R) { return R->red(gmul(x,y), R); }

/* jac^floor(N/pk) mod (N, polcyclo(pk)), flexible window */
static GEN
_powpolmod(Cache *C, GEN jac, Red *R, GEN (*_sqr)(GEN, Red *))
{
  const GEN taba = C->aall;
  const GEN tabt = C->tall;
  const long efin = lg(taba)-1, lv = R->lv;
  GEN L, res = jac, pol2 = _sqr(res, R);
  long f;
  pari_sp av0 = avma, av, lim;

  L = cgetg(lv+1, t_VEC); gel(L,1) = res;
  for (f=2; f<=lv; f++) gel(L,f) = _mul(gel(L,f-1), pol2, R);
  av = avma; lim = stack_lim(av, 1);
  for (f = efin; f >= 1; f--)
  {
    GEN t = gel(L, taba[f]);
    long tf = tabt[f];
    res = (f==efin)? t: _mul(t, res, R);
    while (tf--) {
      res = _sqr(res, R);
      if (low_stack(lim, stack_lim(av,1))) {
        res = gerepilecopy(av, res);
        if(DEBUGMEM>1) pari_warn(warnmem,"powpolmod: f = %ld",f);
      }
    }
  }
  return gerepilecopy(av0, res);
}

static GEN
_powpolmodsimple(Cache *C, Red *R, GEN jac)
{
  pari_sp av = avma;
  GEN w = mulmat_pol(C->matvite, jac);
  long j, ph = lg(w);

  R->red = &_redsimple;
  for (j=1; j<ph; j++)
    gel(w,j) = _powpolmod(C, centermodii(gel(w,j), R->N, R->N2), R, &sqrmod);
  w = centermod_i( gmul(C->matinvvite, w), R->N, R->N2 );
  w = gerepileupto(av, w);
  return RgV_to_RgX(w, 0);
}

static GEN
powpolmod(Cache *C, Red *R, long p, long k, GEN jac)
{
  GEN (*_sqr)(GEN, Red *);

  if (DEBUGLEVEL>2) C->ctsgt++;
  if (C->matvite) return _powpolmodsimple(C, R, jac);
  if (p == 2) /* p = 2 */
  {
    if (k == 2) _sqr = &sqrmod4;
    else        _sqr = &sqrmod;
    R->n = k;
    R->red = &_red_cyclo2n;
  } else if (k == 1)
  {
    if      (p == 3) _sqr = &sqrmod3;
    else if (p == 5) _sqr = &sqrmod5;
    else             _sqr = &sqrmod;
    R->n = p;
    R->red = &_red_cyclop;
  } else {
    R->red = &_red; _sqr = &sqrmod;
  }
  return _powpolmod(C, jac, R, _sqr);
}

/* Return e(t) = \prod_{p-1 | t} p^{1+v_p(t)}}
 * faet contains the odd prime divisors of e(t) */
static GEN
compute_e(ulong t, GEN *faet)
{
  GEN L, P, D = divisorsu(t);
  long l = lg(D);
  ulong k;

  P = vecsmalltrunc_init(l);
  L = vecsmalltrunc_init(l);
  for (k=l-1; k>1; k--) /* k != 1: avoid d = 1 */
  {
    ulong d = D[k];
    if (uisprime(++d))
    { /* we want q = 1 (mod p) prime, not too large */
      if (d > 50000000) return gen_0;
      vecsmalltrunc_append(P, d);
      vecsmalltrunc_append(L, upowuu(d, 1 + u_lval(t,d)));
    }
  }
  if (faet) *faet = P;
  return shifti(zv_prod_Z(L), 2 + u_lval(t,2));
}

/* Table obtained by the following script:

install(compute_e, "LD&"); \\ remove 'static' first

table(first = 6, step = 6, MAXT = 8648640)=
{
  emax = 0;
  forstep(t = first, MAXT, step,
    e = compute_e(t);
    if (e > 1.9*emax, emax = e;
      printf("  if (C < %5.5g) return %8d;\n", 2*log(e)/log(2)*0.9999, t)
    );
  );
}

Previous values can be recovered using the following table:

T=[6,12,24,48,36,60,120,180,240,504,360,420,720,840,1440,1260,1680,2520,3360,5040,13860,10080,16380,21840,18480,27720,32760,36960,55440,65520,98280,110880,131040,166320,196560,262080,277200,360360,480480,332640,554400,720720,665280,831600,1113840,1441440,1663200,2227680,2162160,2827440,3326400,3603600,6126120,4324320,6683040,7207200,11138400,8648640];
f(t) = 2*log(compute_e(t))/log(2);
for (i=1,#T, t=T[i]; printf("  if (C < %5.5g) return %8d;\n", f(t),t));

*/

/* assume C < 3514.6 */
static ulong
compute_t_small(double C)
{
  if (C < 17.953) return        6;
  if (C < 31.996) return       12;
  if (C < 33.996) return       24;
  if (C < 54.079) return       36;
  if (C < 65.325) return       60;
  if (C < 68.457) return       72;
  if (C < 70.783) return      108;
  if (C < 78.039) return      120;
  if (C < 102.41) return      180;
  if (C < 127.50) return      360;
  if (C < 136.68) return      420;
  if (C < 153.43) return      540;
  if (C < 165.66) return      840;
  if (C < 169.17) return     1008;
  if (C < 178.52) return     1080;
  if (C < 192.68) return     1200;
  if (C < 206.34) return     1260;
  if (C < 211.94) return     1620;
  if (C < 222.09) return     1680;
  if (C < 225.11) return     2016;
  if (C < 244.19) return     2160;
  if (C < 270.29) return     2520;
  if (C < 279.50) return     3360;
  if (C < 293.62) return     3780;
  if (C < 346.68) return     5040;
  if (C < 348.70) return     6480;
  if (C < 383.34) return     7560;
  if (C < 396.68) return     8400;
  if (C < 426.04) return    10080;
  if (C < 458.34) return    12600;
  if (C < 527.16) return    15120;
  if (C < 595.38) return    25200;
  if (C < 636.29) return    30240;
  if (C < 672.53) return    42840;
  if (C < 684.90) return    45360;
  if (C < 708.78) return    55440;
  if (C < 771.30) return    60480;
  if (C < 775.86) return    75600;
  if (C < 859.62) return    85680;
  if (C < 893.16) return   100800;
  if (C < 912.27) return   110880;
  if (C < 966.13) return   128520;
  if (C < 1009.1) return   131040;
  if (C < 1041.9) return   166320;
  if (C < 1124.9) return   196560;
  if (C < 1251.0) return   257040;
  if (C < 1375.0) return   332640;
  if (C < 1431.0) return   393120;
  if (C < 1483.3) return   514080;
  if (C < 1546.3) return   655200;
  if (C < 1585.8) return   665280;
  if (C < 1661.3) return   786240;
  if (C < 1667.5) return   831600;
  if (C < 1676.9) return   917280;
  if (C < 1728.0) return   982800;
  if (C < 1747.4) return  1081080;
  if (C < 1773.6) return  1179360;
  if (C < 1810.6) return  1285200;
  if (C < 1924.5) return  1310400;
  if (C < 2001.1) return  1441440;
  if (C < 2096.3) return  1663200;
  if (C < 2165.8) return  1965600;
  if (C < 2321.6) return  2162160;
  if (C < 2368.2) return  2751840;
  if (C < 2377.2) return  2827440;
  if (C < 2514.7) return  3326400;
  if (C < 2588.5) return  3341520;
  if (C < 2636.6) return  3603600;
  if (C < 2667.2) return  3931200;
  if (C < 3028.6) return  4324320;
  if (C < 3045.5) return  5654880;
  if (C < 3080.5) return  6652800;
  if (C < 3121.6) return  6683040;
  if (C < 3283.1) return  7207200;
  return  8648640;
}

/* return t such that e(t) > sqrt(N), set *faet = odd prime divisors of e(t) */
static ulong
compute_t(GEN N, GEN *e, GEN *faet)
{
  /* 2^e b <= N < 2^e (b+1), where b >= 2^52. Approximating log_2 N by
   * log2(gtodouble(N)) ~ e+log2(b), the error is less than log(1+1/b) < 1e-15*/
  double C = dbllog2(N) + 1e-6; /* > log_2 N */
  ulong t;
  GEN B;
  /* Return "smallest" t such that f(t) >= C, which implies e(t) > sqrt(N) */
  /* For N < 2^3515 ~ 10^1058 */
  if (C < 3514.6)
  {
    t = compute_t_small(C);
    *e = compute_e(t, faet);
    return t;
  }
  B = sqrti(N);
  for (t = 8648640+840;; t+=840)
  {
    pari_sp av = avma;
    *e = compute_e(t, faet);
    if (cmpii(*e, B) > 0) break;
    avma = av;
  }
  return t;
}

/* T[i] = discrete log of i in (Z/q)^*, q odd prime
 * To save on memory, compute half the table: T[q-x] = T[x] + (q-1)/2 */
static GEN
computetabdl(ulong q)
{
  ulong g, a, i, qs2 = q>>1; /* (q-1)/2 */
  GEN T = cgetg(qs2+2,t_VECSMALL);

  g = pgener_Fl(q); a = 1;
  for (i=1; i < qs2; i++) /* g^((q-1)/2) = -1 */
  {
    a = Fl_mul(g,a,q);
    if (a > qs2) T[q-a] = i+qs2; else T[a] = i;
  }
  T[qs2+1] = T[qs2] + qs2;
  T[1] = 0; return T;
}

/* Return T: T[x] = dl of x(1-x) */
static GEN
compute_g(ulong q)
{
  const ulong qs2 = q>>1; /* (q-1)/2 */
  ulong x, a;
  GEN T = computetabdl(q); /* updated in place to save on memory */
  a = 0; /* dl[1] */
  for (x=2; x<=qs2+1; x++)
  { /* a = dl(x) */
    ulong b = T[x]; /* = dl(x) */
    T[x] = b + a + qs2; /* dl(x) + dl(x-1) + dl(-1) */
    a = b;
  }
  return T;
}

/* p odd prime */
static GEN
get_jac(Cache *C, ulong q, long pk, GEN tabg)
{
  ulong x, qs2 = q>>1; /* (q-1)/2 */
  GEN vpk = zero_zv(pk);

  for (x=2; x<=qs2; x++) vpk[ tabg[x]%pk + 1 ] += 2;
  vpk[ tabg[x]%pk + 1 ]++; /* x = (q+1)/2 */
  return u_red(vpk, C->cyc);
}

/* p = 2 */
static GEN
get_jac2(GEN N, ulong q, long k, GEN *j2q, GEN *j3q)
{
  GEN jpq, vpk, T = computetabdl(q);
  ulong x, pk, i, qs2;

  /* could store T[x+1] + T[x] + qs2 (cf compute_g).
   * Recompute instead, saving half the memory. */
  pk = 1UL << k;;
  vpk = zero_zv(pk);

  qs2 = q>>1; /* (q-1)/2 */

  for (x=2; x<=qs2; x++) vpk[ (T[x]+T[x-1]+qs2)%pk + 1 ] += 2;
  vpk[ (T[x]+T[x-1]+qs2)%pk + 1 ]++;
  jpq = u_red_cyclo2n_ip(vpk, k);

  if (k == 2) return jpq;

  if (mod8(N) >= 5)
  {
    GEN v8 = cgetg(9,t_VECSMALL);
    for (x=1; x<=8; x++) v8[x] = 0;
    for (x=2; x<=qs2; x++) v8[ ((3*T[x]+T[x-1]+qs2)&7) + 1 ]++;
    for (   ; x<=q-1; x++) v8[ ((3*T[q-x]+T[q-x+1]-3*qs2)&7) + 1 ]++;
    *j2q = RgX_inflate(ZX_sqr(u_red_cyclo2n_ip(v8,3)), pk>>3);
    *j2q = red_cyclo2n_ip(*j2q, k);
  }
  for (i=1; i<=pk; i++) vpk[i] = 0;
  for (x=2; x<=qs2; x++) vpk[ (2*T[x]+T[x-1]+qs2)%pk + 1 ]++;
  for (   ; x<=q-1; x++) vpk[ (2*T[q-x]+T[q-x+1]-2*qs2)%pk + 1 ]++;
  *j3q = ZX_mul(jpq, u_red_cyclo2n_ip(vpk,k));
  *j3q = red_cyclo2n_ip(*j3q, k);
  return jpq;
}

/* N = 1 mod p^k, return an elt of order p^k in (Z/N)^* */
static GEN
finda(Cache *Cp, GEN N, long pk, long p)
{
  GEN a, pv;
  if (Cp && Cp->avite) {
    a  = Cp->avite;
    pv = Cp->pkvite;
  }
  else
  {
    GEN ph, b, q;
    ulong u = 2;
    long v = Z_lvalrem(addis(N,-1), p, &q);
    ph = powuu(p, v-1); pv = muliu(ph, p); /* N - 1 = p^v q */
    if (p > 2)
    {
      for (;;u++)
      {
        a = Fp_pow(utoipos(u), q, N);
        b = Fp_pow(a, ph, N);
        if (!gequal1(b)) break;
      }
    }
    else
    {
      while (krosi(u,N) >= 0) u++;
      a = Fp_pow(utoipos(u), q, N);
      b = Fp_pow(a, ph, N);
    }
    /* checking b^p = 1 mod N done economically in caller */
    b = gcdii(addis(b,-1), N);
    if (!gequal1(b)) return NULL;

    if (Cp) {
      Cp->avite  = a; /* a has order p^v */
      Cp->pkvite = pv;
    }
  }
  return Fp_pow(a, divis(pv, pk), N);
}

/* return 0: N not a prime, 1: no problem so far */
static long
filltabs(Cache *C, Cache *Cp, Red *R, long p, long pk, long ltab)
{
  pari_sp av;
  long i, j;
  long e;
  GEN tabt, taba, m;

  C->cyc = polcyclo(pk,0);

  if (p > 2)
  {
    long LE = pk - pk/p + 1;
    GEN E = cgetg(LE, t_VECSMALL), eta = cgetg(pk+1,t_VEC);
    for (i=1,j=0; i<pk; i++)
      if (i%p) E[++j] = i;
    C->E = E;

    for (i=1; i<=pk; i++)
    {
      GEN z = FpX_rem(monomial(gen_1, i-1, 0), C->cyc, R->N);
      gel(eta,i) = FpX_center(z, R->N, R->N2);
    }
    C->eta = eta;
  }
  else if (pk >= 8)
  {
    long LE = (pk>>2) + 1;
    GEN E = cgetg(LE, t_VECSMALL);
    for (i=1,j=0; i<pk; i++)
      if ((i%8)==1 || (i%8)==3) E[++j] = i;
    C->E = E;
  }

  if (pk > 2 && umodiu(R->N,pk) == 1)
  {
    GEN vpa, p1, p2, p3, a2 = NULL, a = finda(Cp, R->N, pk, p);
    long jj, ph;

    if (!a) return 0;
    ph = pk - pk/p;
    vpa = cgetg(ph+1,t_COL); gel(vpa,1) = a;
    if (pk > p) a2 = centermodii(sqri(a), R->N, R->N2);
    jj = 1;
    for (i=2; i<pk; i++) /* vpa = { a^i, (i,p) = 1 } */
      if (i%p) {
        GEN z = mulii((i%p==1) ? a2 : a, gel(vpa,jj));
        gel(vpa,++jj) = centermodii(z , R->N, R->N2);
      }
    if (!gequal1( centermodii( mulii(a, gel(vpa,ph)), R->N, R->N2) )) return 0;
    p1 = cgetg(ph+1,t_MAT);
    p2 = cgetg(ph+1,t_COL); gel(p1,1) = p2;
    for (i=1; i<=ph; i++) gel(p2,i) = gen_1;
    j = 2; gel(p1,j) = vpa; p3 = vpa;
    for (j++; j <= ph; j++)
    {
      p2 = cgetg(ph+1,t_COL); gel(p1,j) = p2;
      for (i=1; i<=ph; i++)
        gel(p2,i) = centermodii(mulii(gel(vpa,i),gel(p3,i)), R->N, R->N2);
      p3 = p2;
    }
    C->matvite = p1;
    C->matinvvite = FpM_inv(p1, R->N);
  }

  tabt = cgetg(ltab+1, t_VECSMALL);
  taba = cgetg(ltab+1, t_VECSMALL);
  av = avma; m = divis(R->N, pk);
  for (e=1; e<=ltab && signe(m); e++)
  {
    long s = vali(m); m = shifti(m,-s);
    tabt[e] = e==1? s: s + R->k;
    taba[e] = signe(m)? ((mod2BIL(m) & R->mask)+1)>>1: 0;
    m = shifti(m, -R->k);
  }
  setlg(taba, e); C->aall = taba;
  setlg(tabt, e); C->tall = tabt;
  avma = av; return 1;
}

static Cache *
alloc_cache(void)
{
  Cache *C = (Cache*)stack_malloc(sizeof(Cache));
  C->matvite = NULL;
  C->avite   = NULL;
  C->ctsgt = 0; return C;
}

static Cache **
calcglobs(Red *R, ulong t, long *plpC, long *pltab, GEN *pP)
{
  GEN fat, P, E, PE;
  long lv, i, k, b;
  Cache **pC;

  b = expi(R->N)+1;
  k = 3; while (((k+1)*(k+2) << (k-1)) < b) k++;
  *pltab = (b/k)+2;
  R->k  = k;
  R->lv = 1L << (k-1);
  R->mask = (1UL << k) - 1;

  fat = factoru_pow(t);
  P = gel(fat,1);
  E = gel(fat,2);
  PE= gel(fat,3);
  *plpC = lv = vecsmall_max(PE); /* max(p^e, p^e | t) */
  pC = (Cache**)stack_malloc((lv+1)*sizeof(Cache*));
  pC[1] = alloc_cache(); /* to be used as temp in step5() */
  for (i = 2; i <= lv; i++) pC[i] = NULL;
  for (i=1; i<lg(P); i++)
  {
    long pk, p = P[i], e = E[i];
    pk = p;
    for (k=1; k<=e; k++, pk*=p)
    {
      pC[pk] = alloc_cache();
      if (!filltabs(pC[pk], pC[p], R, p,pk, *pltab)) return NULL;
    }
  }
  *pP = P; return pC;
}

/* sig_a^{-1}(z) for z in Q(zeta_pk) and sig_a: zeta -> zeta^a. Assume
 * a reduced mod pk := p^k*/
static GEN
aut(long pk, GEN z, long a)
{
  GEN v;
  long b, i, dz = degpol(z);
  if (a == 1 || dz < 0) return z;
  v = cgetg(pk+2,t_POL);
  v[1] = evalvarn(0);
  b = 0;
  gel(v,2) = gel(z,2); /* i = 0 */
  for (i = 1; i < pk; i++)
  {
    b += a; if (b > pk) b -= pk; /* b = (a*i) % pk */
    gel(v,i+2) = b > dz? gen_0: gel(z,b+2);
  }
  return normalizepol_lg(v, pk+2);
}

/* z^v for v in Z[G], represented by couples [sig_x^{-1},x] */
static GEN
autvec_TH(long pk, GEN z, GEN v, GEN C)
{
  long i, lv = lg(v);
  GEN s = pol_1(varn(C));
  for (i=1; i<lv; i++)
  {
    long y = v[i];
    if (y) s = RgXQ_mul(s, RgXQ_powu(aut(pk,z, y), y, C), C);
  }
  return s;
}

static GEN
autvec_AL(long pk, GEN z, GEN v, Red *R)
{
  const long r = umodiu(R->N, pk);
  GEN s = pol_1(varn(R->C));
  long i, lv = lg(v);
  for (i=1; i<lv; i++)
  {
    long y = (r*v[i]) / pk;
    if (y) s = RgXQ_mul(s, RgXQ_powu(aut(pk,z, v[i]), y, R->C), R->C);
  }
  return s;
}

/* 0 <= i < pk, such that x^i = z mod polcyclo(pk),  -1 if no such i exist */
static long
look_eta(GEN eta, long pk, GEN z)
{
  long i;
  for (i=1; i<=pk; i++)
    if (ZX_equal(z, gel(eta,i))) return i-1;
  return -1;
}
/* same pk = 2^k */
static long
look_eta2(long k, GEN z)
{
  long d, s;
  if (typ(z) != t_POL) d = 0; /* t_INT */
  else
  {
    if (!RgX_is_monomial(z)) return -1;
    d = degpol(z);
    z = gel(z,d+2); /* leading term */
  }
  s = signe(z);
  if (!s || !is_pm1(z)) return -1;
  return (s > 0)? d: d + (1L<<(k-1));
}

static long
step4a(Cache *C, Red *R, ulong q, long p, long k, GEN tabg)
{
  const long pk = upowuu(p,k);
  long ind;
  GEN jpq, s1, s2, s3;

  if (!tabg) tabg = compute_g(q);
  jpq = get_jac(C, q, pk, tabg);
  s1 = autvec_TH(pk, jpq, C->E, C->cyc);
  s2 = powpolmod(C,R, p,k, s1);
  s3 = autvec_AL(pk, jpq, C->E, R);
  s3 = _red(gmul(s3,s2), R);

  ind = look_eta(C->eta, pk, s3);
  if (ind < 0) return -1;
  return (ind%p) != 0;
}

/* x == -1 mod N ? */
static long
is_m1(GEN x, GEN N)
{
  return equalii(addis(x,1), N);
}

/* p=2, k>=3 */
static long
step4b(Cache *C, Red *R, ulong q, long k)
{
  const long pk = 1L << k;
  long ind;
  GEN s1, s2, s3, j2q = NULL, j3q = NULL;

  (void)get_jac2(R->N,q,k, &j2q,&j3q);

  s1 = autvec_TH(pk, j3q, C->E, C->cyc);
  s2 = powpolmod(C,R, 2,k, s1);
  s3 = autvec_AL(pk, j3q, C->E, R);
  s3 = _red(gmul(s3,s2), R);
  if (j2q) s3 = _red(gmul(j2q, s3), R);

  ind = look_eta2(k, s3);
  if (ind < 0) return -1;
  if ((ind&1)==0) return 0;
  if (DEBUGLEVEL>2) C->ctsgt++;
  s3 = Fp_pow(utoipos(q), R->N2, R->N);
  return is_m1(s3, R->N);
}

/* p=2, k=2 */
static long
step4c(Cache *C, Red *R, ulong q)
{
  long ind;
  GEN s0,s1,s3, jpq = get_jac2(R->N,q,2, NULL,NULL);

  s0 = sqrmod4(jpq, R);
  s1 = gmulsg(q,s0);
  s3 = powpolmod(C,R, 2,2, s1);
  if (mod4(R->N) == 3) s3 = _red(gmul(s0,s3), R);

  ind = look_eta2(2, s3);
  if (ind < 0) return -1;
  if ((ind&1)==0) return 0;
  if (DEBUGLEVEL>2) C->ctsgt++;
  s3 = Fp_pow(utoipos(q), R->N2, R->N);
  return is_m1(s3, R->N);
}

/* p=2, k=1 */
static long
step4d(Cache *C, Red *R, ulong q)
{
  GEN s1 = Fp_pow(utoipos(q), R->N2, R->N);
  if (DEBUGLEVEL>2) C->ctsgt++;
  if (is_pm1(s1)) return 0;
  if (is_m1(s1, R->N)) return (mod4(R->N) == 1);
  return -1;
}

static GEN
_res(long a, long b) { return b? mkvec2s(a, b): mkvecs(a); }

/* return 1 [OK so far] or <= 0 [not a prime] */
static GEN
step5(Cache **pC, Red *R, long p, GEN et, ulong ltab, long lpC)
{
  pari_sp av;
  ulong q;
  long pk, k, fl = -1;
  Cache *C, *Cp;
  forprime_t T;

  (void)u_forprime_arith_init(&T, 3, ULONG_MAX, 1,p);
  while( (q = u_forprime_next(&T)) )
  { /* q = 1 (mod p) */
    if (umodiu(et,q) == 0) continue;
    if (umodiu(R->N,q) == 0) return _res(1,p);
    k = u_lval(q-1, p);
    pk = upowuu(p,k);
    if (pk <= lpC && pC[pk]) {
      C = pC[pk];
      Cp = pC[p];
    } else {
      C = pC[1];
      Cp = NULL;
      C->matvite = NULL; /* re-init */
    }

    av = avma;
    if (!filltabs(C, Cp, R, p, pk, ltab)) return _res(1,0);
    R->C = C->cyc;
    if (p >= 3)      fl = step4a(C,R, q,p,k, NULL);
    else if (k >= 3) fl = step4b(C,R, q,k);
    else if (k == 2) fl = step4c(C,R, q);
    else             fl = step4d(C,R, q);
    if (fl == -1) return _res(q,p);
    if (fl == 1) return NULL; /*OK*/
    avma = av;
  }
  pari_err_BUG("aprcl test fails! This is highly improbable");
  return NULL;
}

static GEN
step6(GEN N, ulong t, GEN et)
{
  GEN r, N1 = remii(N, et);
  ulong i;
  pari_sp av = avma;

  r = gen_1;
  for (i=1; i<t; i++)
  {
    r = remii(mulii(r,N1), et);
    if (equali1(r)) break;
    if (!signe(remii(N,r)) && !equalii(r,N)) return mkvec2(r, gen_0);
    if ((i & 0x1f) == 0) r = gerepileuptoint(av, r);
  }
  return gen_1;
}

static GEN
aprcl(GEN N)
{
  GEN et, fat, flaglp, faet = NULL; /*-Wall*/
  long i, j, l, ltab, lfat, lpC;
  ulong t;
  Red R;
  Cache **pC;

  if (typ(N) != t_INT) pari_err_TYPE("aprcl",N);
  if (cmpis(N,12) <= 0)
    switch(itos(N))
    {
      case 2: case 3: case 5: case 7: case 11: return gen_1;
      default: return _res(0,0);
    }
  if (Z_issquare(N)) return _res(0,0);
  t = compute_t(N, &et, &faet);
  if (DEBUGLEVEL) err_printf("Starting APRCL with t = %ld\n",t);
  if (cmpii(sqri(et),N) < 0) pari_err_BUG("aprcl: e(t) too small");
  if (!equali1(gcdii(N,mului(t,et)))) return _res(1,0);

  R.N = N;
  R.N2= shifti(N, -1);
  pC = calcglobs(&R, t, &lpC, &ltab, &fat);
  if (!pC) return _res(1,0);
  lfat = lg(fat);
  flaglp = cgetg(lfat, t_VECSMALL);
  flaglp[1] = 0;
  for (i=2; i<lfat; i++)
  {
    ulong p = fat[i];
    flaglp[i] = equaliu(Fp_powu(N, p-1, sqru(p)), 1);
  }
  vecsmall_sort(faet);

  l = lg(faet);
  if (DEBUGLEVEL>2) err_printf("Step4: %ld q-values\n", l-1);
  for (i=l-1; i>0; i--) /* decreasing order: slowest first */
  {
    pari_sp av1 = avma;
    ulong q = faet[i];
    GEN faq = factoru_pow(q-1), tabg = compute_g(q);
    GEN P = gel(faq,1), E = gel(faq,2), PE = gel(faq,3);
    long lfaq = lg(P);
    pari_sp av2 = avma;
    if (DEBUGLEVEL>2) err_printf("testing Jacobi sums for q = %ld...",q);
    for (j=1; j<lfaq; j++, avma = av2)
    {
      long p = P[j], e = E[j], pe = PE[j], fl;
      Cache *C = pC[pe];
      R.C = C->cyc;
      if (p >= 3)      fl = step4a(C,&R, q,p,e, tabg);
      else if (e >= 3) fl = step4b(C,&R, q,e);
      else if (e == 2) fl = step4c(C,&R, q);
      else             fl = step4d(C,&R, q);
      if (fl == -1) return _res(q,p);
      if (fl == 1) flaglp[ zv_search(fat, p) ] = 0;
    }
    if (DEBUGLEVEL>2) err_printf("OK\n");
    avma = av1;
  }
  if (DEBUGLEVEL>2) err_printf("Step5: testing conditions lp\n");
  for (i=2; i<lfat; i++) /*skip fat[1] = 2*/
  {
    pari_sp av = avma;
    long p = fat[i];
    GEN r;
    if (flaglp[i] && (r = step5(pC, &R, p, et, ltab, lpC))) return r;
    avma = av;
  }
  if (DEBUGLEVEL>2)
  {
    ulong sc = pC[1]->ctsgt;
    err_printf("Individual Fermat powerings:\n");
    for (i=2; i<lpC; i++)
      if (pC[i]) {
        err_printf("  %-3ld: %3ld\n", i, pC[i]->ctsgt);
        sc += pC[i]->ctsgt;
      }
    err_printf("Number of Fermat powerings = %lu\n",sc);
    err_printf("Step6: testing potential divisors\n");
  }
  return step6(N, t, et);
}

long
isprimeAPRCL(GEN N)
{
  pari_sp av = avma;
  GEN res = aprcl(N);
  avma = av; return (typ(res) == t_INT);
}
