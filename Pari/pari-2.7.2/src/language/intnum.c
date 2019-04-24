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
/********************************************************************/
/**                                                                **/
/**                NUMERICAL INTEGRATION (Romberg)                 **/
/**                                                                **/
/********************************************************************/
typedef struct {
  void *E;
  GEN (*f)(void *E, GEN);
} invfun;

/* 1/x^2 f(1/x) */
static GEN
_invf(void *E, GEN x)
{
  invfun *S = (invfun*)E;
  GEN y = ginv(x);
  return gmul(S->f(S->E, y), gsqr(y));
}

static GEN
interp(GEN h, GEN s, long j, long lim, long KLOC)
{
  pari_sp av = avma;
  long e1,e2;
  GEN dss, ss = polint_i(h+j-KLOC,s+j-KLOC,gen_0,KLOC+1,&dss);

  e1 = gexpo(ss);
  e2 = gexpo(dss);
  if (e1-e2 <= lim && (j <= 10 || e1 >= -lim)) { avma = av; return NULL; }
  if (typ(ss) == t_COMPLEX && gequal0(gel(ss,2))) ss = gel(ss,1);
  return ss;
}

static GEN
qrom3(void *E, GEN (*eval)(void *, GEN), GEN a, GEN b, long prec)
{
  const long JMAX = 25, KLOC = 4;
  GEN ss,s,h,p1,p2,qlint,del,x,sum;
  long j, j1, it, sig;

  a = gtofp(a,prec);
  b = gtofp(b,prec);
  qlint = subrr(b,a); sig = signe(qlint);
  if (!sig)  return gen_0;
  if (sig < 0) { setabssign(qlint); swap(a,b); }

  s = new_chunk(JMAX+KLOC-1);
  h = new_chunk(JMAX+KLOC-1);
  gel(h,0) = real_1(prec);

  p1 = eval(E, a); if (p1 == a) p1 = rcopy(p1);
  p2 = eval(E, b);
  gel(s,0) = gmul2n(gmul(qlint,gadd(p1,p2)),-1);
  for (it=1,j=1; j<JMAX; j++, it<<=1) /* it = 2^(j-1) */
  {
    pari_sp av, av2;
    gel(h,j) = real2n(-2*j, prec); /* 2^(-2j) */
    av = avma; del = divru(qlint,it);
    x = addrr(a, shiftr(del,-1));
    av2 = avma;
    for (sum = gen_0, j1 = 1; j1 <= it; j1++, x = addrr(x,del))
    {
      sum = gadd(sum, eval(E, x));
      if ((j1 & 0x1ff) == 0) gerepileall(av2, 2, &sum,&x);
    }
    sum = gmul(sum,del);
    gel(s,j) = gerepileupto(av, gmul2n(gadd(gel(s,j-1), sum), -1));
    if (DEBUGLEVEL>3) err_printf("qrom3: iteration %ld: %Ps\n", j,s[j]);

    if (j >= KLOC && (ss = interp(h, s, j, prec2nbits(prec)-j-6, KLOC)))
      return gmulsg(sig,ss);
  }
  return NULL;
}

static GEN
qrom2(void *E, GEN (*eval)(void *, GEN), GEN a, GEN b, long prec)
{
  const long JMAX = 16, KLOC = 4;
  GEN ss,s,h,p1,qlint,del,ddel,x,sum;
  long j, j1, it, sig;

  a = gtofp(a, prec);
  b = gtofp(b, prec);
  qlint = subrr(b,a); sig = signe(qlint);
  if (!sig)  return gen_0;
  if (sig < 0) { setabssign(qlint); swap(a,b); }

  s = new_chunk(JMAX+KLOC-1);
  h = new_chunk(JMAX+KLOC-1);
  gel(h,0) = real_1(prec);

  p1 = shiftr(addrr(a,b),-1);
  gel(s,0) = gmul(qlint, eval(E, p1));
  for (it=1, j=1; j<JMAX; j++, it*=3) /* it = 3^(j-1) */
  {
    pari_sp av, av2;
    gel(h,j) = divru(gel(h,j-1), 9); /* 3^(-2j) */
    av = avma; del = divru(qlint,3*it); ddel = shiftr(del,1);
    x = addrr(a, shiftr(del,-1));
    av2 = avma;
    for (sum = gen_0, j1 = 1; j1 <= it; j1++)
    {
      sum = gadd(sum, eval(E, x)); x = addrr(x,ddel);
      sum = gadd(sum, eval(E, x)); x = addrr(x,del);
      if ((j1 & 0x1ff) == 0) gerepileall(av2, 2, &sum,&x);
    }
    sum = gmul(sum,del); p1 = gdivgs(gel(s,j-1),3);
    gel(s,j) = gerepileupto(av, gadd(p1,sum));
    if (DEBUGLEVEL>3) err_printf("qrom2: iteration %ld: %Ps\n", j,s[j]);

    if (j >= KLOC && (ss = interp(h, s, j, prec2nbits(prec)-(3*j/2)-6, KLOC)))
      return gmulsg(sig, ss);
  }
  return NULL;
}

/* integrate after change of variables x --> 1/x */
static GEN
qromi(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, long prec)
{
  GEN A = ginv(b), B = ginv(a);
  invfun S;
  S.f = eval;
  S.E = E; return qrom2(&S, &_invf, A, B, prec);
}

/* a < b, assume b "small" (< 100 say) */
static GEN
rom_bsmall(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, long prec)
{
  if (gcmpgs(a,-100) >= 0) return qrom2(E,eval,a,b,prec);
  if (b == gen_1 || gcmpgs(b, -1) >= 0) /* a < -100, b >= -1 */
    return gadd(qromi(E,eval,a,gen_m1,prec), /* split at -1 */
                qrom2(E,eval,gen_m1,b,prec));
  /* a < -100, b < -1 */
  return qromi(E,eval,a,b,prec);
}

static GEN
rombint(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, long prec)
{
  long l = gcmp(b,a);
  GEN z;

  if (!l) return gen_0;
  if (l < 0) swap(a,b);
  if (gcmpgs(b,100) >= 0)
  {
    if (gcmpgs(a,1) >= 0)
      z = qromi(E,eval,a,b,prec);
    else /* split at 1 */
      z = gadd(rom_bsmall(E,eval,a,gen_1,prec), qromi(E,eval,gen_1,b,prec));
  }
  else
    z = rom_bsmall(E,eval,a,b,prec);
  if (l < 0) z = gneg(z);
  return z;
}

/********************************************************************/
/**                                                                **/
/**                DOUBLE EXPONENTIAL INTEGRATION                  **/
/**                                                                **/
/********************************************************************/

/* The init functions have the following purposes:
* 1) They fill the value tabx0 = phi(0) and arrays of abcissas
*   tabxp[] = phi(k/2^m) (positive x) and also of tabxm[] = phi(-k/2^m)
*   (negative x) unless the phi function is odd, in which case this is useless.
* 2) They fill the corresponding arrays of weights tabw0 = phi'(0) and
*   tabwp[] = phi'(k/2^m) (and possibly also of tabwm[] = phi'(-k/2^m)).
* 3) They set eps to the desired accuracy (depending on the GP default).
* 4) They compute nt which says that the weights tabwp[k] and tabwm[k] are
*   negligible with respect to eps if k > nt. In particular the tabxx[] arrays
*   are indexed from 1 to nt+1. */

typedef struct _intdata {
  long m;    /* integration step h = 1/2^m */
  long eps;  /* bit accuracy of current precision */
  GEN tabx0; /* abcissa phi(0) for t = 0 */
  GEN tabw0; /* weight phi'(0) for t = 0 */
  GEN tabxp; /* table of abcissas phi(kh) for k > 0 */
  GEN tabwp; /* table of weights phi'(kh) for k > 0 */
  GEN tabxm; /* table of abcissas phi(kh) for k < 0 */
  GEN tabwm; /* table of weights phi'(kh) for k < 0 */
} intdata;

#define TABm(v)  gel(v,1)
#define TABx0(v) gel(v,2)
#define TABw0(v) gel(v,3)
#define TABxp(v) gel(v,4)
#define TABwp(v) gel(v,5)
#define TABxm(v) gel(v,6)
#define TABwm(v) gel(v,7)

static int
isinR(GEN z)
{
  long tz = typ(z);
  return (tz == t_INT || tz == t_REAL || tz == t_FRAC);
}

static int
isinC(GEN z)
{
  return (typ(z) == t_COMPLEX)? isinR(gel(z,1)) && isinR(gel(z,2)):
                                isinR(z);
}

static int
checktabsimp(GEN tab)
{
  long L, LN, LW;
  if (!tab || typ(tab) != t_VEC) return 0;
  if (lg(tab) != 8) return 0;
  if (typ(TABm(tab))!= t_INT) return 0;
  if (typ(TABxp(tab)) != t_VEC) return 0;
  if (typ(TABwp(tab)) != t_VEC) return 0;
  if (typ(TABxm(tab)) != t_VEC) return 0;
  if (typ(TABwm(tab)) != t_VEC) return 0;
  L = lg(TABxp(tab)); if (lg(TABwp(tab)) != L) return 0;
  LN = lg(TABxm(tab)); if (LN != 1 && LN != L) return 0;
  LW = lg(TABwm(tab)); if (LW != 1 && LW != L) return 0;
  return 1;
}

static int
checktabdoub(GEN tab)
{
  long L;
  if (typ(tab) != t_VEC) return 0;
  if (lg(tab) != 8) return 0;
  if (typ(TABm(tab)) != t_INT) return 0;
  L = lg(TABxp(tab));
  if (lg(TABwp(tab)) != L) return 0;
  if (lg(TABxm(tab)) != L) return 0;
  if (lg(TABwm(tab)) != L) return 0;
  return 1;
}

static int
checktab(GEN tab)
{
  if (typ(tab) != t_VEC) return 0;
  if (lg(tab) != 3) return checktabsimp(tab);
  return checktabsimp(gel(tab,1))
      && checktabsimp(gel(tab,2));
}

static long
findmforinit(long m, long prec)
{
  long p, r;

  if (m <= 0)
  {
    p = (long)prec2nbits_mul(prec, 0.3);
    m = 2; r = 4;
    while (r < p) { m++; r <<= 1; }
  }
  return m;
}

long
intnumstep(long prec) { return findmforinit(0, prec); }

static void
intinit_start(intdata *D, long m0, long flext, long prec)
{
  long m = findmforinit(m0, prec), lim = 20L<<m;
  if (flext > 0) lim = lim << (2*flext);
  D->m = m;
  D->eps = prec2nbits(prec);
  D->tabxp = cgetg(lim+1, t_VEC);
  D->tabwp = cgetg(lim+1, t_VEC);
  D->tabxm = cgetg(lim+1, t_VEC);
  D->tabwm = cgetg(lim+1, t_VEC);
}

static GEN
intinit_end(intdata *D, long pnt, long mnt)
{
  GEN v = cgetg(8, t_VEC);
  if (pnt < 0) pari_err_DOMAIN("intnuminit","table length","<",gen_0,stoi(pnt));
  gel(v,1) = stoi(D->m);
  TABx0(v) = D->tabx0;
  TABw0(v) = D->tabw0;
  TABxp(v) = D->tabxp; setlg(D->tabxp, pnt+1);
  TABwp(v) = D->tabwp; setlg(D->tabwp, pnt+1);
  TABxm(v) = D->tabxm; setlg(D->tabxm, mnt+1);
  TABwm(v) = D->tabwm; setlg(D->tabwm, mnt+1); return v;
}

static const long EXTRAPREC =
#ifdef LONG_IS_64BIT
  1;
#else
  2;
#endif

/* divide by 2 in place */
static GEN
divr2_ip(GEN x) { shiftr_inplace(x, -1); return x; }

/* phi(t)=tanh((3/2)sinh(t)) : from -1 to 1, hence also from a to b compact
 * interval. */
static GEN
inittanhsinh(long m, long prec)
{
  pari_sp av, ltop = avma;
  GEN h, et, ct, st, ext, ex, xp, wp;
  long k, nt = -1, lim;
  intdata D; intinit_start(&D, m, 0, prec);

  lim = lg(D.tabxp) - 1;
  D.tabx0 = real_0(prec);
  D.tabw0 = divr2_ip(stor(3, prec));
  h = real2n(-D.m, prec);
  et = ex = mpexp(h);
  for (k = 1; k <= lim; k++)
  {
    gel(D.tabxp,k) = cgetr(prec+EXTRAPREC);
    gel(D.tabwp,k) = cgetr(prec+EXTRAPREC); av = avma;
    ct = divr2_ip(addrr(et, invr(et)));
    st = subrr(et, ct);
    ext = invr( addrs(mpexp(mulur(3, st)), 1) );
    shiftr_inplace(ext, 1);
    xp = subsr(1, ext);
    wp = divr2_ip(mulur(3, mulrr(ct, mulrr(ext, addsr(1, xp)))));
    if (expo(wp) < -D.eps) { nt = k-1; break; }
    affrr(xp, gel(D.tabxp,k));
    affrr(wp, gel(D.tabwp,k)); et = gerepileuptoleaf(av, mulrr(et, ex));
  }
  return gerepilecopy(ltop, intinit_end(&D, nt, 0));
}

/* phi(t)=sinh(sinh(t)) : from -\infty to \infty, slowly decreasing, at least
 * as 1/x^2. */
static GEN
initsinhsinh(long m, long prec)
{
  pari_sp av, ltop = avma;
  GEN h, et, ct, st, ext, exu, ex, xp, wp;
  long k, nt = -1, lim;
  intdata D; intinit_start(&D, m, 0, prec);

  lim = lg(D.tabxp) - 1;
  D.tabx0 = real_0(prec);
  D.tabw0 = real_1(prec);
  h = real2n(-D.m, prec);
  et = ex = mpexp(h);
  for (k = 1; k <= lim; k++)
  {
    gel(D.tabxp,k) = cgetr(prec+EXTRAPREC);
    gel(D.tabwp,k) = cgetr(prec+EXTRAPREC); av = avma;
    ct = divr2_ip(addrr(et, invr(et)));
    st = subrr(et, ct);
    ext = mpexp(st);
    exu = invr(ext);
    xp = divr2_ip(subrr(ext, exu));
    wp = divr2_ip(mulrr(ct, addrr(ext, exu)));
    if (expo(wp) - 2*expo(xp) < -D.eps) { nt = k-1; break; }
    affrr(xp, gel(D.tabxp,k));
    affrr(wp, gel(D.tabwp,k)); et = gerepileuptoleaf(av, mulrr(et, ex));
  }
  return gerepilecopy(ltop, intinit_end(&D, nt, 0));
}

/* phi(t)=2sinh(t) : from -\infty to \infty, exponentially decreasing as
 * exp(-x). */
static GEN
initsinh(long m, long prec)
{
  pari_sp av, ltop = avma;
  GEN h, et, ex, eti, xp, wp;
  long k, nt = -1, lim;
  intdata D; intinit_start(&D, m, 0, prec);

  lim = lg(D.tabxp) - 1;
  D.tabx0 = real_0(prec);
  D.tabw0 = real2n(1, prec);
  h = real2n(-D.m, prec);
  et = ex = mpexp(h);
  for (k = 1; k <= lim; k++)
  {
    gel(D.tabxp,k) = cgetr(prec+EXTRAPREC);
    gel(D.tabwp,k) = cgetr(prec+EXTRAPREC); av = avma;
    eti = invr(et);
    xp = subrr(et, eti);
    wp = addrr(et, eti);
    if (cmprs(xp, (long)(LOG2*(expo(wp)+D.eps) + 1)) > 0) { nt = k-1; break; }
    affrr(xp, gel(D.tabxp,k));
    affrr(wp, gel(D.tabwp,k)); et = gerepileuptoleaf(av, mulrr(et, ex));
  }
  return gerepilecopy(ltop, intinit_end(&D, nt, 0));
}

/* phi(t)=exp(2sinh(t)) : from 0 to \infty, slowly decreasing at least as
 * 1/x^2. */
static GEN
initexpsinh(long m, long prec)
{
  pari_sp ltop = avma;
  GEN h, et, eti, ex, xp;
  long k, nt = -1, lim;
  intdata D; intinit_start(&D, m, 0, prec);

  lim = lg(D.tabxp) - 1;
  D.tabx0 = real_1(prec);
  D.tabw0 = real2n(1, prec);
  h = real2n(-D.m, prec);
  ex = mpexp(h);
  et = real_1(prec);
  for (k = 1; k <= lim; k++)
  {
    GEN t;
    et = mulrr(et, ex);
    eti = invr(et); t = addrr(et, eti);
    xp = mpexp(subrr(et, eti));
    gel(D.tabxp,k) = xp;
    gel(D.tabwp,k) = mulrr(xp, t);
    gel(D.tabxm,k) = invr(xp);
    gel(D.tabwm,k) = mulrr(gel(D.tabxm,k), t);
    if (expo(gel(D.tabxm,k)) < -D.eps) { nt = k-1; break; }
  }
  return gerepilecopy(ltop, intinit_end(&D, nt, nt));
}

/* phi(t)=exp(t-exp(-t)) : from 0 to \infty, exponentially decreasing. */
static GEN
initexpexp(long m, long prec)
{
  pari_sp av, ltop = avma;
  GEN kh, h, et, eti, ex, xp, xm, wp, wm;
  long k, nt = -1, lim;
  intdata D; intinit_start(&D, m, 0, prec);

  lim = lg(D.tabxp) - 1;
  D.tabx0 = mpexp(real_m1(prec));
  D.tabw0 = gmul2n(D.tabx0, 1);
  h = real2n(-D.m, prec);
  et = ex = mpexp(negr(h));
  for (k = 1; k <= lim; k++)
  {
    gel(D.tabxp,k) = cgetr(prec+EXTRAPREC);
    gel(D.tabwp,k) = cgetr(prec+EXTRAPREC);
    gel(D.tabxm,k) = cgetr(prec+EXTRAPREC);
    gel(D.tabwm,k) = cgetr(prec+EXTRAPREC); av = avma;
    eti = invr(et); kh = mulur(k,h);
    xp = mpexp(subrr(kh, et));
    xm = mpexp(negr(addrr(kh, eti)));
    wp = mulrr(xp, addsr(1, et));
    wm = mulrr(xm, addsr(1, eti));
    if (expo(xm) < -D.eps && cmprs(xp, (long)(LOG2*(expo(wp)+D.eps) + 1)) > 0) { nt = k-1; break; }
    affrr(xp, gel(D.tabxp,k));
    affrr(wp, gel(D.tabwp,k));
    affrr(xm, gel(D.tabxm,k));
    affrr(wm, gel(D.tabwm,k)); et = gerepileuptoleaf(av, mulrr(et, ex));
  }
  return gerepilecopy(ltop, intinit_end(&D, nt, nt));
}

/* phi(t)=(Pi/h)t/(1-exp(-sinh(t))) : from 0 to \infty, sine oscillation. */
static GEN
initnumsine(long m, long prec)
{
  pari_sp av, ltop = avma;
  GEN h, et, eti, ex, st, ct, extp, extm, extp1, extm1, extp2, extm2, kpi, kct;
  GEN xp, xm, wp, wm, pi = mppi(prec);
  long k, nt = -1, lim;
  intdata D; intinit_start(&D, m, 0, prec);

  lim = lg(D.tabxp) - 1;
  D.tabx0 = gmul2n(pi, D.m);
  D.tabw0 = gmul2n(pi, D.m - 1);
  h = real2n(-D.m, prec);
  et = ex = mpexp(h);
  for (k = 1; k <= lim; k++)
  {
    gel(D.tabxp,k) = cgetr(prec+EXTRAPREC);
    gel(D.tabwp,k) = cgetr(prec+EXTRAPREC);
    gel(D.tabxm,k) = cgetr(prec+EXTRAPREC);
    gel(D.tabwm,k) = cgetr(prec+EXTRAPREC); av = avma;
    eti = invr(et); /* exp(-kh) */
    ct = divr2_ip(addrr(et, eti));
    st = divr2_ip(subrr(et, eti));
    extp = mpexp(st);  extp1 = subsr(1, extp); extp2 = invr(extp1);
    extm = invr(extp); extm1 = subsr(1, extm); extm2 = invr(extm1);
    kpi = mulur(k, pi);
    kct = mulur(k, ct);
    shiftr_inplace(extm1, D.m);
    shiftr_inplace(extp1, D.m);
    xp = mulrr(kpi, extm2);
    wp = mulrr(subrr(extm1, mulrr(kct, extm)), mulrr(pi, sqrr(extm2)));
    xm = mulrr(negr(kpi), extp2);
    wm = mulrr(addrr(extp1, mulrr(kct, extp)), mulrr(pi, sqrr(extp2)));
    if (expo(wm) < -D.eps && expo(extm) + D.m + expu(10 * k) < -D.eps) { nt = k-1; break; }
    affrr(xp, gel(D.tabxp,k));
    affrr(wp, gel(D.tabwp,k));
    affrr(xm, gel(D.tabxm,k));
    affrr(wm, gel(D.tabwm,k)); et = gerepileuptoleaf(av, mulrr(et, ex));
  }
  return gerepilecopy(ltop, intinit_end(&D, nt, nt));
}

static GEN
suminit_start(GEN sig)
{
  GEN sig2;

  if (typ(sig) == t_VEC)
  {
    if (lg(sig) != 3) pari_err_TYPE("sumnum",sig);
    sig2 = gel(sig,2);
    sig  = gel(sig,1);
    if (!isinR(sig2)) pari_err_TYPE("sumnum",sig2);
    if (gsigne(sig2) > 0) sig2 = mulcxmI(sig2);
  }
  else sig2 = gen_0;
  if (!isinR(sig)) pari_err_TYPE("sumnum",sig);
  return mkvec2(mkvec(gen_1), sig2);
}

/* phi(t) depending on sig[2] as in intnum, with weights phi'(t)tanh(Pi*phi(t))
 * (sgn >= 0) or phi'(t)/cosh(Pi*phi(t)) (otherwise), for use in sumnumall.
 * integrations are done from 0 to +infty (flii is set to 0), except if slowly
   decreasing, from -infty to +infty (flii is set to 1). */
GEN
sumnuminit(GEN sig, long m, long sgn, long prec)
{
  pari_sp ltop = avma;
  GEN b, t, tab, tabxp, tabwp, tabxm, tabwm, pi = mppi(prec);
  long L, k, eps, flii;

  b = suminit_start(sig);
  flii = gequal0(gel(b,2));
  if (flii)
    tab = intnuminit(mkvec(gen_m1), mkvec(gen_1), m, prec);
  else
    tab = intnuminit(gen_0, b, m, prec);
  eps = prec2nbits(prec);
  t = gmul(pi, TABx0(tab));
  if (sgn < 0) TABw0(tab) = gdiv(TABw0(tab), gcosh(t, prec));
  else         TABw0(tab) = gmul(TABw0(tab), gtanh(t, prec));
  tabxp = TABxp(tab); L = lg(tabxp);
  tabwp = TABwp(tab);
  tabxm = TABxm(tab);
  tabwm = TABwm(tab);
  for (k = 1; k < L; k++)
  {
    if (cmprs(gel(tabxp,k), eps) < 0)
    {
      t = mulrr(pi, gel(tabxp,k));
      gel(tabwp,k) = (sgn < 0)? divrr(gel(tabwp,k), gcosh(t, prec))
                              : mulrr(gel(tabwp,k), gtanh(t, prec));
    }
    else
      if (sgn < 0) gel(tabwp,k) = real_0_bit(-eps);
    if (!flii)
    {
      t = mulrr(pi, gel(tabxm,k));
      gel(tabwm,k) = (sgn < 0)? divrr(gel(tabwm,k), gcosh(t, prec))
                              : mulrr(gel(tabwm,k), gtanh(t, prec));
    }
  }
  return gerepilecopy(ltop, tab);
}

/* End of initialization functions. These functions can be executed once
 * and for all for a given accuracy, type of integral ([a,b], [a,\infty[ or
 * ]-\infty,a], ]-\infty,\infty[) and of integrand in the noncompact case
 * (slowly decreasing, exponentially decreasing, oscillating with a fixed
 * oscillating factor such as sin(x)). */

/* In the following integration functions the parameters are as follows:
* 1) The parameter denoted by m is the most crucial and difficult to
* determine in advance: h = 1/2^m is the integration step size. Usually
* m = floor(log(D)/log(2)), where D is the number of decimal digits of accuracy
* is plenty for very regulat functions, for instance m = 6 for 100D, and m = 9
* for 1000D, but values of m 1 or 2 less are often sufficient, while for
* singular functions, 1 or 2 more may be necessary. The best test is to take 2
* or 3 consecutive values of m and look. Note that the number of function
* evaluations, hence the time doubles when m increases by 1. */

/* All inner functions such as intn, etc... must be called with a
 * valid 'tab' table. The wrapper intnum provides a higher level interface */

/* compute $\int_a^b f(t)dt$ with [a,b] compact and f nonsingular. */
static GEN
intn(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, GEN tab)
{
  GEN tabx0, tabw0, tabxp, tabwp;
  GEN bpa, bma, bmb, S, SP, SM;
  long m, k, L, i;
  pari_sp ltop = avma, av;

  if (!checktabsimp(tab)) pari_err_TYPE("intnum",tab);
  if (!isinC(a)) pari_err_TYPE("intnum",a);
  if (!isinC(b)) pari_err_TYPE("intnum",b);
  m = itos(TABm(tab));
  tabx0 = TABx0(tab); tabw0 = TABw0(tab);
  tabxp = TABxp(tab); tabwp = TABwp(tab); L = lg(tabxp);
  bpa = gmul2n(gadd(b, a), -1); /* (b+a)/2 */
  bma = gsub(bpa, a); /* (b-a)/2 */
  bmb = gmul(bma, tabx0); /* (b-a)/2 phi(0) */
  av = avma;
  /* phi'(0) f( (b+a)/2 + (b-a)/2 * phi(0) ) */
  S = gmul(tabw0, eval(E, gadd(bpa, bmb)));
  for (k = 1; k <= m; k++)
  {
    long pas = 1L<<(m-k);
    for (i = pas; i < L; i += pas)
      if (i & pas || k == 1)
      {
        bmb = gmul(bma, gel(tabxp,i));
        SP = eval(E, gsub(bpa, bmb));
        SM = eval(E, gadd(bpa, bmb));
        S = gadd(S, gmul(gel(tabwp,i), gadd(SP, SM)));
        if ((i & 0x7f) == 1) S = gerepileupto(av, S);
      }
  }
  return gerepileupto(ltop, gmul(S, gmul2n(bma, -m)));
}

/* compute $\int_{a[1]}^{b} f(t)dt$ with [a,b] compact, possible
 *  singularity with exponent a[2] at lower extremity, b regular.
 *  Use tanh(sinh(t)). */
static GEN
intnsing(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, GEN tab, long prec)
{
  GEN tabx0, tabw0, tabxp, tabwp, ea, ba, bm, bp, S, tra, SP, SM;
  long m, k, L, i;
  pari_sp ltop = avma, av;

  if (!checktabsimp(tab)) pari_err_TYPE("intnum",tab);
  m = itos(TABm(tab));
  tabx0 = TABx0(tab); tabw0 = TABw0(tab);
  tabxp = TABxp(tab); tabwp = TABwp(tab); L = lg(tabxp);
  tra = gel(a,1);
  ea = ginv(gaddsg(1, gel(a,2)));
  ba = gdiv(gsub(b, tra), gpow(gen_2, ea, prec));
  av = avma;
  S = gmul(gmul(tabw0, ba), eval(E, gadd(gmul(ba, gaddsg(1, tabx0)), tra)));
  for (k = 1; k <= m; k++)
  {
    long pas = 1L<<(m-k);
    for (i = pas; i < L; i += pas)
      if (i & pas || k == 1) /* i = odd multiple of pas = 2^(m-k) */
      {
        GEN p = addsr(1, gel(tabxp,i));
        GEN m = subsr(1, gel(tabxp,i));
        bp = gmul(ba, gpow(p, ea, prec));
        bm = gmul(ba, gpow(m, ea, prec));
        SP = gmul(gdiv(bp, p), eval(E, gadd(bp, tra)));
        SM = gmul(gdiv(bm, m), eval(E, gadd(bm, tra)));
        S = gadd(S, gmul(gel(tabwp,i), gadd(SP, SM)));
        if ((i & 0x7f) == 1) S = gerepileupto(av, S);
      }
  }
  return gerepileupto(ltop, gmul(gmul2n(S, -m), ea));
}

/* compute  $\int_a^\infty f(t)dt$ if $si=1$ or $\int_{-\infty}^a f(t)dt$
   if $si=-1$. Use exp(2sinh(t)) for slowly decreasing functions,
   exp(1+t-exp(-t)) for exponentially decreasing functions, and
   (pi/h)t/(1-exp(-sinh(t))) for oscillating functions. */

static GEN
intninfpm(void *E, GEN (*eval)(void*, GEN), GEN a, long si, GEN tab)
{
  GEN tabx0, tabw0, tabxp, tabwp, tabxm, tabwm;
  GEN S, SP, SM;
  long m, L, k, h = 0, pas, i;
  pari_sp ltop = avma, av;

  if (!checktabdoub(tab)) pari_err_TYPE("intnum",tab);
  m = itos(TABm(tab));
  tabx0 = TABx0(tab); tabw0 = TABw0(tab);
  tabxp = TABxp(tab); tabwp = TABwp(tab); L = lg(tabxp);
  tabxm = TABxm(tab); tabwm = TABwm(tab);
  if (si < 0) { tabxp = gneg(tabxp); tabxm = gneg(tabxm); }
  av = avma;
  S = gmul(tabw0, eval(E, gadd(a, gmulsg(si, tabx0))));
  for (k = 1; k <= m; k++)
  {
    h++; pas = 1L<<(m-k);
    for (i = pas; i < L; i += pas)
      if (i & pas || k == 1)
      {
        SP = eval(E, gadd(a, gel(tabxp,i)));
        SM = eval(E, gadd(a, gel(tabxm,i)));
        S = gadd(S, gadd(gmul(gel(tabwp,i), SP), gmul(gel(tabwm,i), SM)));
        if ((i & 0x7f) == 1) S = gerepileupto(av, S);
      }
  }
  return gerepileupto(ltop, gmul2n(S, -h));
}

/* compute  $\int_{-\infty}^\infty f(t)dt$
 * use sinh(sinh(t)) for slowly decreasing functions and sinh(t) for
 * exponentially decreasing functions.
 * HACK: in case TABwm(tab) contains something, assume function to be integrated
 * satisfies f(-x) = conj(f(x)).
 * Usually flag < 0, but flag > 0 is used in sumnumall. */
static GEN
intninfinfintern(void *E, GEN (*eval)(void*, GEN), GEN tab, long flag)
{
  GEN tabx0, tabw0, tabxp, tabwp, tabwm;
  GEN S, SP, SM;
  long m, L, k, i, spf;
  pari_sp ltop = avma;

  if (!checktabsimp(tab)) pari_err_TYPE("intnum",tab);
  m = itos(TABm(tab));
  tabx0 = TABx0(tab); tabw0 = TABw0(tab);
  tabxp = TABxp(tab); tabwp = TABwp(tab); L = lg(tabxp);
  tabwm = TABwm(tab);
  spf = (lg(tabwm) == lg(tabwp));
  S = flag > 0 ? gen_0 : gmul(tabw0, eval(E, tabx0));
  if (spf) S = gmul2n(real_i(S), -1);
  for (k = 1; k <= m; k++)
  {
    long pas = 1L<<(m-k);
    for (i = pas; i < L; i += pas)
      if (i & pas || k == 1)
      {
        SP = eval(E, gel(tabxp,i));
        if (spf) S = gadd(S, real_i(gmul(gel(tabwp,i), SP)));
        else
        {
          SM = eval(E, negr(gel(tabxp,i)));
          if (flag > 0) SM = gneg(SM);
          S = gadd(S, gmul(gel(tabwp,i), gadd(SP, SM)));
        }
        if ((i & 0x7f) == 1) S = gerepileupto(ltop, S);
      }
  }
  if (spf) m--;
  return gerepileupto(ltop, gmul2n(S, -m));
}

static GEN
intninfinf(void *E, GEN (*eval)(void*, GEN), GEN tab)
{
  return intninfinfintern(E, eval, tab, -1);
}

/* general num integration routine int_a^b f(t)dt, where a and b are as follows:
 (1) a scalar : the scalar, no singularity worse than logarithmic at a.
 (2) [a, e] : the scalar a, singularity exponent -1 < e <= 0.
 (3) [1], [-1] : +\infty, -\infty, slowly decreasing function.
 (4) [[+-1], a], a nonnegative real : +-\infty, function behaving like
      exp(-a|t|) at +-\infty.
 (5) [[+-1], e], e < -1 : +-\infty, function behaving like t^e
      at +-\infty.
 (5) [[+-1], a*I], a real : +-\infty, function behaving like cos(at) if a>0
     and like sin(at) if a < 0 at +-\infty.
*/

/* FIXME: The numbers below can be changed, but NOT the ordering */
enum {
  f_REG    = 0, /* regular function */
  f_SING   = 1, /* algebraic singularity */
  f_YSLOW  = 2, /* +\infty, slowly decreasing */
  f_YVSLO  = 3, /* +\infty, very slowly decreasing */
  f_YFAST  = 4, /* +\infty, exponentially decreasing */
  f_YOSCS  = 5, /* +\infty, sine oscillating */
  f_YOSCC  = 6  /* +\infty, cosine oscillating */
};
/* is c finite */
static int
is_fin_f(long c) { return c == f_REG || c == f_SING; }
/* oscillating case: valid for +oo (c > 0) or -oo (c < 0) */
static int
is_osc_f(long c) { c = labs(c); return c == f_YOSCS || c == f_YOSCC; }

static GEN
f_getycplx(GEN a, long prec)
{
  long s;
  GEN tmp, a2R, a2I;

  if (lg(a) == 2 || gequal0(gel(a,2))) return gen_1;
  a2R = real_i(gel(a,2));
  a2I = imag_i(gel(a,2));
  s = gsigne(a2I); if (s < 0) a2I = gneg(a2I);
  tmp = s ? ginv(a2I) : ginv(a2R);
  if (gprecision(tmp) < prec) tmp = gprec_w(tmp, prec);
  return tmp;
}

static void
err_code(GEN a, const char *name)
{
  char *s = stack_sprintf("intnum [incorrect %s]", name);
  pari_err_TYPE(s, a);
}

/* a = [[+/-1], alpha]*/
static long
code_aux(GEN a, const char *name)
{
  GEN re, im, alpha = gel(a,2);
  long s;
  if (!isinC(alpha)) err_code(a, name);
  re = real_i(alpha);
  im = imag_i(alpha);
  s = gsigne(im);
  if (s)
  {
    if(!gequal0(re))
      pari_warn(warner,"real(z)*imag(z)!=0 in endpoint code, real(z) ignored");
    return s > 0 ? f_YOSCC : f_YOSCS;
  }
  if (gequal0(re) || gcmpgs(re, -2)<=0) return f_YSLOW;
  if (gsigne(re) > 0) return f_YFAST;
  if (gcmpgs(re, -1) >= 0) err_code(a, name);
  return f_YVSLO;
}

static long
transcode(GEN a, const char *name)
{
  GEN a1, a2;
  if (typ(a) != t_VEC) return f_REG;
  switch(lg(a))
  {
    case 2: return gsigne(gel(a,1)) > 0 ? f_YSLOW : -f_YSLOW;
    case 3: a1 = gel(a,1); a2 = gel(a,2); break;
    default: err_code(a,name);
  }
  a1 = gel(a,1);
  a2 = gel(a,2);
  if (typ(a1) != t_VEC)
  {
    if (!isinC(a1) || !isinR(a2) || gcmpgs(a2, -1) <= 0) err_code(a,name);
    return gsigne(a2) < 0 ? f_SING : f_REG;
  }
  if (lg(a1) != 2) err_code(a,name);
  return gsigne(gel(a1,1)) * code_aux(a, name);
}

/* computes the necessary tabs, knowing a, b and m */
static GEN
homtab(GEN tab, GEN k)
{
  GEN z;
  if (gequal0(k) || gequal(k, gen_1)) return tab;
  if (gsigne(k) < 0) k = gneg(k);
  z = cgetg(8, t_VEC);
  TABm(z)  = icopy(TABm(tab));
  TABx0(z) = gmul(TABx0(tab), k);
  TABw0(z) = gmul(TABw0(tab), k);
  TABxp(z) = gmul(TABxp(tab), k);
  TABwp(z) = gmul(TABwp(tab), k);
  TABxm(z) = gmul(TABxm(tab), k);
  TABwm(z) = gmul(TABwm(tab), k); return z;
}

static GEN
expvec(GEN v, GEN ea, long prec)
{
  long lv = lg(v), i;
  GEN z = cgetg(lv, t_VEC);
  for (i = 1; i < lv; i++) gel(z,i) = gpow(gel(v,i),ea,prec);
  return z;
}

static GEN
expscalpr(GEN vnew, GEN xold, GEN wold, GEN ea)
{
  pari_sp av = avma;
  return gerepileupto(av, gdiv(gmul(gmul(vnew, wold), ea), xold));
}
static GEN
expvecpr(GEN vnew, GEN xold, GEN wold, GEN ea)
{
  long lv = lg(vnew), i;
  GEN z = cgetg(lv, t_VEC);
  for (i = 1; i < lv; i++)
    gel(z,i) = expscalpr(gel(vnew,i), gel(xold,i), gel(wold,i), ea);
  return z;
}

/* here k < -1 */
static GEN
exptab(GEN tab, GEN k, long prec)
{
  GEN v, ea;

  if (gcmpgs(k, -2) <= 0) return tab;
  ea = ginv(gsubsg(-1, k));
  v = cgetg(8, t_VEC);
  TABm(v) = icopy(TABm(tab));
  TABx0(v) = gpow(TABx0(tab), ea, prec);
  TABw0(v) = expscalpr(TABx0(v), TABx0(tab), TABw0(tab), ea);
  TABxp(v) = expvec(TABxp(tab), ea, prec);
  TABwp(v) = expvecpr(TABxp(v), TABxp(tab), TABwp(tab), ea);
  TABxm(v) = expvec(TABxm(tab), ea, prec);
  TABwm(v) = expvecpr(TABxm(v), TABxm(tab), TABwm(tab), ea);
  return v;
}

GEN
intnuminit(GEN a, GEN b, long m, long prec)
{
  long codea, codeb, l;
  GEN T, U, km, kma, kmb, tmp;

  if (m > 30) pari_err_OVERFLOW("intnuminit [m]");
  l = prec+EXTRAPREC;
  codea = transcode(a, "a");
  codeb = transcode(b, "b");
  if (is_fin_f(codea) && is_fin_f(codeb)) return inittanhsinh(m, l);
  if (labs(codea) > labs(codeb)) { swap(a, b); lswap(codea, codeb); }
  if (codea == f_REG)
  {
    km = f_getycplx(b, l);
    switch(labs(codeb))
    {
      case f_YSLOW: return initexpsinh(m, l);
      case f_YVSLO: return exptab(initexpsinh(m, l), gel(b,2), prec);
      case f_YFAST: return homtab(initexpexp(m, l), km);
      case f_YOSCS:
        if (typ(a) == t_VEC || gequal0(a)) return homtab(initnumsine(m, l), km);
            /* fall through */
      case f_YOSCC:
        T = cgetg(3, t_VEC);
        gel(T,1) = inittanhsinh(m, l);
        gel(T,2) = homtab(initnumsine(m, l), km);
        return T;
    }
  }
  if (codea == f_SING)
  {
    km = f_getycplx(b, l);
    T = cgetg(3, t_VEC);
    gel(T,1) = inittanhsinh(m, l);
    switch(labs(codeb))
    {
      case f_YSLOW: gel(T,2) = initexpsinh(m, l); break;
      case f_YVSLO: gel(T,2) = exptab(initexpsinh(m, l), gel(b,2), prec); break;
      case f_YFAST: gel(T,2) = homtab(initexpexp(m, l), km); break;
      case f_YOSCS: case f_YOSCC:
        gel(T,2) = homtab(initnumsine(m, l), km); break;
    }
    return T;
  }
  if (codea * codeb > 0) return gen_0;
  kma = f_getycplx(a, l);
  kmb = f_getycplx(b, l);
  codea = labs(codea);
  codeb = labs(codeb);
  if (codea == f_YSLOW && codeb == f_YSLOW) return initsinhsinh(m, l);
  if (codea == f_YFAST && codeb == f_YFAST && gequal(kma, kmb))
    return homtab(initsinh(m, l), kmb);
  T = cgetg(3, t_VEC);
  switch (codea)
  {
    case f_YSLOW: gel(T,1) = initexpsinh(m, l);
      switch (codeb)
      {
        case f_YVSLO: gel(T,2) = exptab(gel(T,1), gel(b,2), prec); return T;
        case f_YFAST: gel(T,2) = homtab(initexpexp(m, l), kmb); return T;
        case f_YOSCS: case f_YOSCC:
          gel(T,2) = homtab(initnumsine(m, l), kmb); return T;
      }
    case f_YVSLO:
      tmp = initexpsinh(m, l);
      gel(T,1) = exptab(tmp, gel(a,2), prec);
      switch (codeb)
      {
        case f_YVSLO: gel(T,2) = exptab(tmp, gel(b,2), prec); return T;
        case f_YFAST: gel(T,2) = homtab(initexpexp(m, l), kmb); return T;
        case f_YOSCS:
        case f_YOSCC: gel(T,2) = homtab(initnumsine(m, l), kmb); return T;
      }
    case f_YFAST:
      tmp = initexpexp(m, l);
      gel(T,1) = homtab(tmp, kma);
      switch (codeb)
      {
        case f_YFAST: gel(T,2) = homtab(tmp, kmb); return T;
        case f_YOSCS:
        case f_YOSCC: gel(T,2) = homtab(initnumsine(m, l), kmb); return T;
      }
    case f_YOSCS: case f_YOSCC: tmp = initnumsine(m, l);
      gel(T,1) = homtab(tmp, kma);
      if (codea == f_YOSCC && codeb == f_YOSCC && !gequal(kma, kmb))
      {
        U = cgetg(3, t_VEC);
        gel(U,1) = inittanhsinh(m, l);
        gel(U,2) = homtab(tmp, kmb);
        gel(T,2) = U;
      }
      else gel(T,2) = homtab(tmp, kmb);
      return T;
  }
  return gen_0; /* not reached */
}

GEN
intnuminit0(GEN a, GEN b, GEN tab, long prec)
{
  long m;
  if (!tab) m = 0;
  else if (typ(tab) != t_INT)
  {
    if (!checktab(tab)) pari_err_TYPE("intnuminit0",tab);
    return tab;
  }
  else
    m = itos(tab);
  return intnuminit(a, b, m, prec);
}
GEN
sumnuminit0(GEN a, GEN tab, long sgn, long prec)
{
  long m;
  if (!tab) m = 0;
  else if (typ(tab) != t_INT)
  {
    if (!checktab(tab)) pari_err_TYPE("sumnuminit0",tab);
    return tab;
  }
  else
    m = itos(tab);
  return sumnuminit(a, m, sgn, prec);
}

/* User-defined change of variable phi(t) = f(t), where t goes from -oo to +oo,
 * and a and b are as in intnuminit. If [a,b] compact, assume phi(t) odd. */
static int
condfin(long code, GEN xw, long eps, long m, long k)
{
  GEN x, w;
  eps -= 8; /* for safety. Lose 8 bits, but took 1 whole word extra. */
  x = gel(xw,1);
  w = gel(xw,2);
  switch(labs(code))
  {
    case f_REG: case f_SING:
      return gexpo(w) < -eps;
    case f_YSLOW: case f_YVSLO:
      return gexpo(w) - 2*gexpo(x) < -eps;
    case f_YFAST:
      return cmprs(x, (long)(LOG2 * (gexpo(w) + eps) + 1)) > 0;
    case f_YOSCS: case f_YOSCC:
      return gexpo(x) + m + expu(10 * k) < - eps;
    default: return 0;
  }
}

/* eps = 2^(-k). Return f'(a) ~ (f(a+eps) - f(a-eps)) / 2eps*/
static GEN
myderiv_num(void *E, GEN (*eval)(void*, GEN), GEN a, GEN eps, long k, long prec)
{
  GEN d = gmul2n(gsub(eval(E, gadd(a,eps)), eval(E, gsub(a,eps))), k-1);
  return gprec_w(d, prec);
}
/* zp = z to a higher accuracy (enough to evaluate numerical derivative) */
static GEN
ffprime(void *E, GEN (*eval)(void*, GEN), GEN z, GEN zp, GEN eps, long h, long precl)
{
  GEN f = eval(E, z), fp = myderiv_num(E, eval, zp, eps, h, precl);
  return mkvec2(f, fp);
}
/* v = [f(z), f'(z)]. Return h := z/(1-f(z)), h + h^2 zf'(z) */
static GEN
ffmodify(GEN v, GEN z)
{
  GEN f = gel(v,1), fp = gel(v,2), h = ginv(gsubsg(1, f));
  return mkvec2(gmul(z, h), gadd(h, gmul(gsqr(h), gmul(z,fp))));
}
GEN
intnuminitgen(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, long m,
              long flext, long prec)
{
  enum {
    f_COMP, /* [a,b] */
    f_SEMI, /* [a,+-oo[, no oscillation */
    f_OSC1, /* [a,+-oo[, oscillation */
    f_INF , /* ]-oo,+oo[, no oscillation */
    f_OSC2  /* ]-oo,+oo[, oscillation */
  };
  pari_sp ltop = avma;
  GEN hnpr, eps, v;
  long k, h, newprec, lim, precl = prec+EXTRAPREC;
  long flag, codea = transcode(a, "a"), codeb = transcode(b, "b");
  int NOT_OSC, NOT_ODD;
  intdata D; intinit_start(&D, m, flext, precl);

  flag = f_SEMI;
  if (is_osc_f(codea) || is_osc_f(codeb)) flag = f_OSC1;
  if (is_fin_f(codea) && is_fin_f(codeb)) flag = f_COMP;
  else if (!is_fin_f(codea) && !is_fin_f(codeb))
  {
    if (codea * codeb > 0) return gen_0;
    if (codea != -codeb)
      pari_err_TYPE("intnuminitgen [infinities of different types]",
                    mkvec2(a,b));
    flag = (flag == f_SEMI) ? f_INF : f_OSC2;
  }
  NOT_OSC = (flag == f_COMP || flag == f_SEMI || flag == f_INF);
  NOT_ODD = (flag == f_SEMI || flag == f_OSC1);

  newprec = (3*precl - 1)>>1;
  h = prec2nbits(precl)/2;
  eps = real2n(-h, newprec);

  if (NOT_OSC || !gequal1(eval(E, gen_0)))
  {
    GEN a0 = real_0(precl), a0n = real_0(newprec), xw, xwmod;
    xw = ffprime(E, eval, a0, a0n, eps, h, precl);
    xwmod = NOT_OSC? xw: ffmodify(xw, a0);
    D.tabx0 = gel(xwmod,1);
    D.tabw0 = gel(xwmod,2);
  }
  else
  {
    GEN xw = gdiv(pol_x(0), gsubsg(1, eval(E, gadd(pol_x(0), zeroser(0, 4)))));
    D.tabx0 = gprec_w(polcoeff0(xw, 0, 0), precl);
    D.tabw0 = gprec_w(polcoeff0(xw, 1, 0), precl);
  }
  /* precl <= newprec */
  hnpr = real2n(-D.m, newprec);
  lim = lg(D.tabxp) - 1;
  for (k = 1; k <= lim; k++)
  {
    GEN akn = mulur(k, hnpr), ak = rtor(akn, precl), xw, xwmod;
    int finb;
    xw = ffprime(E, eval, ak, akn, eps, h, precl);
    xwmod = NOT_OSC? xw: ffmodify(xw, ak);
    gel(D.tabxp,k) = gel(xwmod,1);
    gel(D.tabwp,k) = gel(xwmod,2);
    finb = condfin(codeb, is_osc_f(codeb)? xw: xwmod, D.eps, D.m, k);
    if (NOT_ODD)
    {
      ak = negr(ak); akn = negr(akn);
      xw = ffprime(E, eval, ak, akn, eps, h, precl);
      xwmod = NOT_OSC? xw: ffmodify(xw, ak);
      gel(D.tabxm,k) = gel(xwmod,1);
      gel(D.tabwm,k) = gel(xwmod,2);
      if (finb && condfin(codea, is_osc_f(codeb)? xw: xwmod, D.eps, D.m, k))
        break;
    }
    else if (finb) break;
  }
  v = intinit_end(&D, k-1, NOT_ODD? k-1: 0);
  if (!NOT_OSC)
  {
    GEN C = Pi2n(D.m, precl);
    TABx0(v) = gmul(TABx0(v), C);
    TABw0(v) = gmul(TABw0(v), C);
    TABxp(v) = RgV_Rg_mul(TABxp(v), C);
    TABwp(v) = RgV_Rg_mul(TABwp(v), C);
    TABxm(v) = RgV_Rg_mul(TABxm(v), C);
    TABwm(v) = RgV_Rg_mul(TABwm(v), C);
  }
  return gerepilecopy(ltop, v);
}

/* Assigns the values of the function weighted by w[k] at quadrature points x[k]
 * [replacing the weights]. Return the index of the last non-zero coeff */
static long
weight(void *E, GEN (*eval)(void *, GEN), GEN x, GEN w)
{
  long k, l = lg(x);
  for (k = 1; k < l; k++) gel(w,k) = gmul(gel(w,k), eval(E, gel(x,k)));
  k--; while (k >= 1) if (!gequal0(gel(w,k--))) break;
  return k;
}
/* compute the necessary tabs, weights multiplied by f(t).
 * If flag set, assumes that f(-t) = conj(f(t)). */
static GEN
intfuncinitintern(void *E, GEN (*eval)(void*, GEN), GEN tab, long flag)
{
  GEN tabxp = TABxp(tab), tabwp = TABwp(tab);
  GEN tabxm = TABxm(tab), tabwm = TABwm(tab);
  long L = weight(E, eval, tabxp, tabwp), L0 = lg(tabxp);

  TABw0(tab) = gmul(TABw0(tab), eval(E, TABx0(tab)));
  if (lg(tabxm) > 1) (void)weight(E, eval, tabxm, tabwm);
  else
  {
    tabxm = gneg(tabxp);
    if (flag) tabwm = gconj(tabwp);
    else
    {
      long L2;
      tabwm = leafcopy(tabwp);
      L2 = weight(E, eval, tabxm, tabwm);
      if (L > L2) L = L2;
    }
    TABxm(tab) = tabxm;
    TABwm(tab) = tabwm;
  }
  if (L < L0)
  { /* catch up functions whose growth at oo was not adequately described */
    setlg(tabxp, L+1);
    setlg(tabwp, L+1);
    if (lg(tabxm) > 1) { setlg(tabxm, L+1); setlg(tabwm, L+1); }
  }
  return tab;
}

GEN
intfuncinit(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, long m, long flag, long prec)
{
  pari_sp ltop = avma;
  GEN T, tab = intnuminit(a, b, m, prec);

  if (lg(tab) != 3) T = intfuncinitintern(E, eval, tab, flag);
  else
  {
    T = cgetg(3, t_VEC);
    gel(T,1) = intfuncinitintern(E, eval, gel(tab,1), flag);
    gel(T,2) = intfuncinitintern(E, eval, gel(tab,2), flag);
  }
  return gerepilecopy(ltop, T);
}

static GEN
intnum_i(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, GEN tab, long prec)
{
  GEN tmp, S = gen_0, res1, res2, tm, pi2, pi2p, pis2, pis2p, kma, kmb;
  GEN SP, SN;
  long tmpi, sgns = 1, codea = transcode(a, "a"), codeb = transcode(b, "b");

  if (codea == f_REG && typ(a) == t_VEC) a = gel(a,1);
  if (codeb == f_REG && typ(b) == t_VEC) b = gel(b,1);
  if (codea == f_REG && codeb == f_REG) return intn(E, eval, a, b, tab);
  if (labs(codea) > labs(codeb)) { swap(a, b); lswap(codea, codeb); sgns = -1; }
  /* now labs(codea) <= labs(codeb) */
  if (codeb == f_SING)
  {
    if (codea == f_REG)
      S = intnsing(E, eval, b, a, tab, prec), sgns = -sgns;
    else
    {
      tmp = gmul2n(gadd(gel(a,1), gel(b,1)), -1);
      res1 = intnsing(E, eval, a, tmp, tab, prec);
      res2 = intnsing(E, eval, b, tmp, tab, prec);
      S = gsub(res1, res2);
    }
    return (sgns < 0) ? gneg(S) : S;
  }
  /* now b is infinite */
  tmpi = codeb > 0 ? 1 : -1;
  if (codea == f_REG && labs(codeb) != f_YOSCC
      && (labs(codeb) != f_YOSCS || gequal0(a)))
  {
    S = intninfpm(E, eval, a, tmpi, tab);
    return sgns*tmpi < 0 ? gneg(S) : S;
  }
  pi2 = Pi2n(1, prec); pis2 = Pi2n(-1, prec);
  if (is_fin_f(codea))
  { /* either codea == f_SING  or codea == f_REG and codeb = f_YOSCC
     * or (codeb == f_YOSCS and !gequal0(a)) */
    pi2p = gmul(pi2, f_getycplx(b, prec));
    pis2p = gmul2n(pi2p, -2);
    tm = real_i(codea == f_SING ? gel(a,1) : a);
    if (labs(codeb) == f_YOSCC) tm = gadd(tm, pis2p);
    tm = gdiv(tm, pi2p);
    if (tmpi > 0)
      tm = addsi(1, gceil(tm));
    else
      tm = subis(gfloor(tm), 1);
    tm = gmul(pi2p, tm);
    if (labs(codeb) == f_YOSCC) tm = gsub(tm, pis2p);
    res1 = codea==f_SING? intnsing(E, eval, a,  tm,  gel(tab,1), prec)
                        : intn    (E, eval, a,  tm,  gel(tab,1));
    res2 = intninfpm(E, eval, tm, tmpi,gel(tab,2));
    if (tmpi < 0) res2 = gneg(res2);
    res1 = gadd(res1, res2);
    return sgns < 0 ? gneg(res1) : res1;
  }
  /* now a and b are infinite */
  if (codea * codeb > 0)
  {
    pari_warn(warner, "integral from infty to infty or from -infty to -infty");
    return gen_0;
  }
  if (codea > 0) { lswap(codea, codeb); swap(a, b); sgns = -sgns; }
  /* now codea < 0 < codeb */
  codea = -codea;
  kma = f_getycplx(a, prec);
  kmb = f_getycplx(b, prec);
  if ((codea == f_YSLOW && codeb == f_YSLOW)
   || (codea == f_YFAST && codeb == f_YFAST && gequal(kma, kmb)))
    S = intninfinf(E, eval, tab);
  else
  {
    GEN coupea = (codea == f_YOSCC)? gmul(pis2, kma): gen_0;
    GEN coupeb = (codeb == f_YOSCC)? gmul(pis2, kmb): gen_0;
    GEN coupe = codea == f_YOSCC ? coupea : coupeb;
    SN = intninfpm(E, eval, coupe, -1, gel(tab,1));
    if (codea != f_YOSCC)
      SP = intninfpm(E, eval, coupeb, 1, gel(tab,2));
    else
    {
      if (codeb != f_YOSCC) pari_err_BUG("code error in intnum");
      if (gequal(kma, kmb))
        SP = intninfpm(E, eval, coupeb, 1, gel(tab,2));
      else
      {
        tab = gel(tab,2);
        SP = intninfpm(E, eval, coupeb, 1, gel(tab,2));
        SP = gadd(SP, intn(E, eval, coupea, coupeb, gel(tab,1)));
      }
    }
    S = gadd(SN, SP);
  }
  if (sgns < 0) S = gneg(S);
  return S;
}

GEN
intnum(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, GEN tab, long prec)
{
  pari_sp ltop = avma;
  long l = prec+EXTRAPREC;
  GEN S;

  tab = intnuminit0(a, b, tab, prec);
  S = intnum_i(E, eval, gprec_w(a, l), gprec_w(b, l), tab, l);
  return gerepilecopy(ltop, gprec_wtrunc(S, prec));
}

typedef struct auxint_s {
  GEN a, R, pi;
  GEN (*f)(void*, GEN);
  GEN (*w)(GEN, long);
  long prec;
  void *E;
} auxint_t;

static GEN
auxcirc(void *E, GEN t)
{
  auxint_t *D = (auxint_t*) E;
  GEN s, c, z;
  mpsincos(mulrr(t, D->pi), &s, &c); z = mkcomplex(c,s);
  return gmul(z, D->f(D->E, gadd(D->a, gmul(D->R, z))));
}

GEN
intcirc(void *E, GEN (*eval)(void*, GEN), GEN a, GEN R, GEN tab, long prec)
{
  auxint_t D;
  GEN z;

  D.a = a;
  D.R = R;
  D.pi = mppi(prec);
  D.f = eval;
  D.E = E;
  z = intnum(&D, &auxcirc, real_m1(prec), real_1(prec), tab, prec);
  return gmul2n(gmul(R, z), -1);
}

static GEN
gettmpP(GEN x) { return mkvec2(mkvec(gen_1), x); }

static GEN
gettmpN(GEN tmpP) { return mkvec2(gneg(gel(tmpP,1)), gel(tmpP,2)); }

/* w(Rt) f(a+it) */
static GEN
auxinv(void *E, GEN t)
{
  auxint_t *D = (auxint_t*) E;
  GEN tmp = D->w(gmul(D->R, t), D->prec);
  return gmul(tmp, D->f(D->E, gadd(D->a, mulcxI(t))));
}
static GEN
intinvintern(void *E, GEN (*eval)(void*, GEN), GEN sig, GEN x, GEN tab, long prec)
{
  auxint_t D;
  GEN z, zR, zI, tmpP, tmpN;

  if (lg(sig) != 3 || !isinR(gel(sig,1)) || !isinR(gel(sig,2)))
    pari_err_TYPE("integral transform",sig);
  if (gsigne(gel(sig,2)) < 0)
    pari_err_OVERFLOW("integral transform [exponential increase]");
  D.a = gel(sig,1);
  D.prec = prec;
  D.f = eval;
  D.E = E;
  if (gequal0(gel(sig,2)))
  {
    D.R = x;
    tmpP = gettmpP(mulcxI(gabs(x, prec)));
    tmpN = gettmpN(tmpP);
    tab = intnuminit0(tmpN, tmpP, tab, prec);
    D.w = gcos;
    zR = intnum_i(&D, &auxinv, tmpN, tmpP, tab, prec);
    gel(tmpP,2) = gneg(gel(tmpP,2));
    D.w = gsin;
    zI = intnum_i(&D, &auxinv, gettmpN(tmpP), tmpP, tab, prec);
    z = gadd(zR, mulcxI(zI));
  }
  else
  {
    D.R = mulcxI(x);
    tmpP = gettmpP(gel(sig,2));
    D.w = gexp;
    z = intnum(&D, &auxinv, gettmpN(tmpP), tmpP, tab, prec);
  }
  return gdiv(gmul(gexp(gmul(gel(sig,1), x), prec), z), Pi2n(1, prec));
}

/* If sig = [sigR, e]: if e = 0, slowly decreasing, if e > 0, exponentially
 * decreasing like exp(-e*t). If sig is real, identical to [sig, 1]. */
GEN
intmellininv(void *E, GEN (*eval)(void*, GEN), GEN sig, GEN x, GEN tab, long prec)
{
  if (typ(sig) != t_VEC) sig = mkvec2(sig, gen_1);
  return intinvintern(E, eval, sig, gneg(glog(x, prec)), tab, prec);
}

/* If sig = [sigR, e]: if e = 0, slowly decreasing, if e > 0, exponentially
 * decreasing like exp(-e*t). If sig is real, identical to [sig, 0]. */
GEN
intlaplaceinv(void *E, GEN (*eval)(void*, GEN), GEN sig, GEN x, GEN tab, long prec)
{
  if (typ(sig) != t_VEC) sig = mkvec2(sig, gen_0);
  return intinvintern(E, eval, sig, x, tab, prec);
}

/* assume tab computed with additional weights f(sig + I*T) */
typedef struct auxmel_s {
  GEN L;
  long prec;
} auxmel_t;

static GEN
auxmelshort(void *E, GEN t)
{
  auxmel_t *D = (auxmel_t*) E;
  return gexp(gmul(D->L, t), D->prec);
}

GEN
intmellininvshort(GEN sig, GEN x, GEN tab, long prec)
{
  auxmel_t D;
  GEN z, tmpP, LX = gneg(glog(x, prec));

  if (typ(sig) != t_VEC) sig = mkvec2(sig, gen_1);
  if (lg(sig) != 3 || !isinR(gel(sig,1)) || !isinR(gel(sig,2)))
    pari_err_TYPE("intmellininvshort",sig);
  if (gsigne(gel(sig,2)) <= 0)
    pari_err_OVERFLOW("intinvmellinshort [need exponential decrease]");
  D.L = mulcxI(LX);
  D.prec = prec;
  tmpP = gettmpP(gel(sig,2));
  z = intnum_i(&D, &auxmelshort, gettmpN(tmpP), tmpP, tab, prec);
  return gdiv(gmul(gexp(gmul(gel(sig,1), LX), prec), z), Pi2n(1, prec));
}

/* a as in intnum. flag = 0 for sin, flag = 1 for cos. */
static GEN
mytra(GEN a, GEN x, long flag, const char *name)
{
  GEN b, xa;
  long s, codea = transcode(a, name);

  switch (labs(codea))
  {
    case f_REG: case f_SING: case f_YFAST: return a;
    case f_YSLOW: case f_YVSLO:
      xa = real_i(x); s = gsigne(xa);
      if (!s) pari_err_DOMAIN("Fourier transform","Re(x)","=",gen_0,x);
      if (s < 0) xa = gneg(xa);
      b = cgetg(3, t_VEC);
      gel(b,1) = mkvec( codea > 0 ? gen_1 : gen_m1 );
      gel(b,2) = (flag? mulcxI(xa): mulcxmI(xa));
      return b;
    case f_YOSCS: case f_YOSCC:
      pari_err_IMPL("Fourier transform of oscillating functions");
  }
  return NULL;
}

/* w(ta) f(t) */
static GEN
auxfour(void *E, GEN t)
{
  auxint_t *D = (auxint_t*) E;
  return gmul(D->w(gmul(t, D->a), D->prec), D->f(D->E, t));
}

GEN
intfouriersin(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, GEN x, GEN tab, long prec)
{
  auxint_t D;
  GEN tmp;

  if (gequal0(x)) return gcopy(x);
  tmp = gmul(x, Pi2n(1, prec));
  D.a = tmp;
  D.R = NULL;
  D.prec = prec;
  D.f = eval;
  D.E = E;
  a = mytra(a,tmp,0,"a");
  b = mytra(b,tmp,0,"b");
  D.w = gsin;
  return intnum(&D, &auxfour, a, b, tab, prec);
}

GEN
intfouriercos(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, GEN x, GEN tab, long prec)
{
  auxint_t D;
  GEN tmp;

  if (gequal0(x)) return intnum(E, eval, a, b, tab, prec);
  tmp = gmul(x, Pi2n(1, prec));
  D.a = tmp;
  D.R = NULL;
  D.prec = prec;
  D.f = eval;
  D.E = E;
  a = mytra(a,tmp,1,"a");
  b = mytra(b,tmp,1,"b");
  D.w = gcos;
  return intnum(&D, &auxfour, a, b, tab, prec);
}

GEN
intfourierexp(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, GEN x, GEN tab,
              long prec)
{
  pari_sp ltop = avma;
  GEN R = intfouriercos(E, eval, a, b, x, tab, prec);
  GEN I = intfouriersin(E, eval, a, b, x, tab, prec);
  return gerepileupto(ltop, gadd(R, mulcxmI(I)));
}

GEN
intnumromb(void *E, GEN (*eval)(void *, GEN), GEN a, GEN b, long flag, long prec)
{
  pari_sp av = avma;
  GEN z;
  switch(flag)
  {
    case 0: z = qrom3  (E, eval, a, b, prec); break;
    case 1: z = rombint(E, eval, a, b, prec); break;
    case 2: z = qromi  (E, eval, a, b, prec); break;
    case 3: z = qrom2  (E, eval, a, b, prec); break;
    default: pari_err_FLAG("intnumromb"); return NULL; /* not reached */
  }
  if (!z) pari_err_IMPL("intnumromb recovery [too many iterations]");
  return gerepileupto(av, z);
}

GEN
intnumromb0(GEN a, GEN b, GEN code, long flag, long prec)
{ EXPR_WRAP(code, intnumromb(EXPR_ARG, a, b, flag, prec)); }
GEN
intnum0(GEN a, GEN b, GEN code, GEN tab, long prec)
{ EXPR_WRAP(code, intnum(EXPR_ARG, a, b, tab, prec)); }
GEN
intcirc0(GEN a, GEN R, GEN code, GEN tab, long prec)
{ EXPR_WRAP(code, intcirc(EXPR_ARG, a, R, tab, prec)); }
GEN
intmellininv0(GEN sig, GEN x, GEN code, GEN tab, long prec)
{ EXPR_WRAP(code, intmellininv(EXPR_ARG, sig, x, tab, prec)); }
GEN
intlaplaceinv0(GEN sig, GEN x, GEN code, GEN tab, long prec)
{ EXPR_WRAP(code, intlaplaceinv(EXPR_ARG, sig, x, tab, prec)); }
GEN
intfourcos0(GEN a, GEN b, GEN x, GEN code, GEN tab, long prec)
{ EXPR_WRAP(code, intfouriercos(EXPR_ARG, a, b, x, tab, prec)); }
GEN
intfoursin0(GEN a, GEN b, GEN x, GEN code, GEN tab, long prec)
{ EXPR_WRAP(code, intfouriersin(EXPR_ARG, a, b, x, tab, prec)); }
GEN
intfourexp0(GEN a, GEN b, GEN x, GEN code, GEN tab, long prec)
{ EXPR_WRAP(code, intfourierexp(EXPR_ARG, a, b, x, tab, prec)); }

GEN
intnuminitgen0(GEN a, GEN b, GEN code, long m, long flag, long prec)
{ EXPR_WRAP(code, intnuminitgen(EXPR_ARG, a, b, m, flag, prec)); }

/* m and flag reversed on purpose */
GEN
intfuncinit0(GEN a, GEN b, GEN code, long flag, long m, long prec)
{ EXPR_WRAP(code, intfuncinit(EXPR_ARG, a, b, m, flag? 1: 0, prec)); }

#if 0
/* Two variable integration */

typedef struct auxf_s {
  GEN x;
  GEN (*f)(void *, GEN, GEN);
  void *E;
} auxf_t;

typedef struct indi_s {
  GEN (*c)(void*, GEN);
  GEN (*d)(void*, GEN);
  GEN (*f)(void *, GEN, GEN);
  void *Ec;
  void *Ed;
  void *Ef;
  GEN tabintern;
  long prec;
} indi_t;

static GEN
auxf(GEN y, void *E)
{
  auxf_t *D = (auxf_t*) E;
  return D->f(D->E, D->x, y);
}

static GEN
intnumdoubintern(GEN x, void *E)
{
  indi_t *D = (indi_t*) E;
  GEN c = D->c(x, D->Ec), d = D->d(x, D->Ed);
  auxf_t A;

  A.x = x;
  A.f = D->f;
  A.E = D->Ef;
  return intnum(&A, &auxf, c, d, D->tabintern, D->prec);
}

GEN
intnumdoub(void *Ef, GEN (*evalf)(void *, GEN, GEN), void *Ec, GEN (*evalc)(void*, GEN), void *Ed, GEN (*evald)(void*, GEN), GEN a, GEN b, GEN tabext, GEN tabint, long prec)
{
  indi_t E;

  E.c = evalc;
  E.d = evald;
  E.f = evalf;
  E.Ec = Ec;
  E.Ed = Ed;
  E.Ef = Ef;
  E.prec = prec;
  if (typ(tabint) == t_INT)
  {
    GEN C = evalc(a, Ec), D = evald(a, Ed);
    if (typ(C) != t_VEC && typ(D) != t_VEC) { C = gen_0; D = gen_1; }
    E.tabintern = intnuminit0(C, D, tabint, prec);
  }
  else E.tabintern = tabint;
  return intnum(&E, &intnumdoubintern, a, b, tabext, prec);
}

GEN
intnumdoub0(GEN a, GEN b, int nc, int nd, int nf, GEN tabext, GEN tabint, long prec)
{
  GEN z;
  push_lex(NULL);
  push_lex(NULL);
  z = intnumdoub(chf, &gp_eval2, chc, &gp_eval, chd, &gp_eval, a, b, tabext, tabint, prec);
  pop_lex(1); pop_lex(1); return z;
}
#endif

/* Numerical summation routine assuming f holomorphic for Re(s) >= sig.
 * Computes sum_{n>=a} f(n)  if sgn >= 0,
 *          sum_{n>=a} (-1)^n f(n) otherwise,  where a is real.
 * Variant of Abel-Plana. */

static GEN
auxsum(void *E, GEN t)
{
  auxint_t *D = (auxint_t*) E;
  GEN z = mkcomplex(D->a, t);
  return D->f(D->E, z);
}
/* assume that conj(f(z)) = f(conj(z)) */
static GEN
auxsumintern1(void *E, GEN t, long sgn)
{
  auxint_t *D = (auxint_t*) E;
  GEN z = mkcomplex(D->a, t), u = D->f(D->E, z);
  return sgn > 0 ? imag_i(u): real_i(u);
}
/* no assumption */
static GEN
auxsumintern(void *E, GEN t, long sgn)
{
  auxint_t *D = (auxint_t*) E;
  GEN u,v, z = mkcomplex(D->a, t);
  u = D->f(D->E, z); gel(z,2) = gneg(t);
  v = D->f(D->E, z); return sgn > 0 ? gsub(u, v) : gadd(u, v);
}
static GEN
auxsum0(void *E, GEN t) { return auxsumintern(E, t, 1); }
static GEN
auxsum1(void *E, GEN t) { return auxsumintern1(E, t, 1); }
static GEN
auxsumalt0(void *E, GEN t) { return auxsumintern(E, t, -1); }
static GEN
auxsumalt1(void *E, GEN t) { return auxsumintern1(E, t, -1); }

static GEN
sumnumall(void *E, GEN (*eval)(void*, GEN), GEN a, GEN sig, GEN tab, long flag, long sgn, long prec)
{
  GEN SI, S, nsig, b, signew;
  long si = 1, flii;
  pari_sp ltop = avma;
  auxint_t D;

  b = suminit_start(sig);
  flii = gequal0(gel(b,2));
  if (!is_scalar_t(typ(a))) pari_err_TYPE("sumnum",a);
  tab = sumnuminit0(sig, tab, sgn, prec);

  signew = (typ(sig) == t_VEC) ? gel(sig,1) : sig;
  a = gceil(a); nsig = gmax(subis(a, 1), gceil(gsub(signew, ghalf)));
  if (sgn < 0) {
    if (mpodd(nsig)) nsig = addsi(1, nsig);
    si = mpodd(a) ? -1 : 1;
  }
  SI = real_0(prec);
  while (cmpii(a, nsig) <= 0)
  {
    SI = (si < 0) ? gsub(SI, eval(E, a)) : gadd(SI, eval(E, a));
    a = addsi(1, a); if (sgn < 0) si = -si;
  }
  D.a = gadd(nsig, ghalf);
  D.R = gen_0;
  D.f = eval;
  D.E = E;
  D.prec = prec;
  if (!flii)
    S = intnum_i(&D, sgn > 0? (flag ? &auxsum1 : &auxsum0)
                            : (flag ? &auxsumalt1 : &auxsumalt0),
                      gen_0, b, tab, prec);
  else
  {
    if (flag)
    {
      GEN emp = leafcopy(tab); TABwm(emp) = TABwp(emp);
      S = gmul2n(intninfinf(&D, sgn > 0? &auxsum1: &auxsumalt1, emp),-1);
    }
    else
      S = intninfinfintern(&D, &auxsum, tab, sgn);
  }
  if (flag) S = gneg(S);
  else
  {
    S = gmul2n(S, -1);
    S = (sgn < 0) ? gneg(S): mulcxI(S);
  }
  return gerepileupto(ltop, gadd(SI, S));
}
GEN
sumnum(void *E, GEN (*f)(void *, GEN), GEN a,GEN sig,GEN tab,long flag,long prec)
{ return sumnumall(E,f,a,sig,tab,flag,1,prec); }
GEN
sumnumalt(void *E, GEN (*f)(void *, GEN),GEN a,GEN s,GEN tab,long flag,long prec)
{ return sumnumall(E,f,a,s,tab,flag,-1,prec); }

GEN
sumnum0(GEN a, GEN sig, GEN code, GEN tab, long flag, long prec)
{ EXPR_WRAP(code, sumnum(EXPR_ARG, a, sig, tab, flag, prec)); }
GEN
sumnumalt0(GEN a, GEN sig, GEN code, GEN tab, long flag, long prec)
{ EXPR_WRAP(code, sumnumalt(EXPR_ARG, a, sig, tab, flag, prec)); }
