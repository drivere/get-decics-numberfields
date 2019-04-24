/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */
#include "pari.h"
#include "paripriv.h"

/********************************************************************/
/**                                                                **/
/**                       IGUSA INVARIANTS                         **/
/**                       (GP2C-generated)                         **/
/**                                                                **/
/********************************************************************/
/*
j2(a0,a1,a2,a3,a4,a5,a6) = (-120*a0*a6+20*a1*a5-8*a2*a4+3*a3^2) / 4;
*/
static GEN
igusaj2(GEN a0, GEN a1, GEN a2, GEN a3, GEN a4, GEN a5, GEN a6)
{
  pari_sp av = avma;
  return gerepileupto(av, gmul2n(gadd(gsub(gadd(gmul(gmulsg(-120, a0), a6), gmul(gmulsg(20, a1), a5)), gmul(gmulsg(8, a2), a4)), gmulsg(3, gsqr(a3))), -2));
}

/*
j4(a0,a1,a2,a3,a4,a5,a6) = (240*(a0*a3*a4*a5+a1*a2*a3*a6)-400*(a0*a2*a5^2+a1^2*a4*a6)-64*(a0*a4^3+a2^3*a6)+16*(a1*a3*a4^2+a2^2*a3*a5)-672*a0*a3^2*a6+240*a1^2*a5^2-112*a1*a2*a4*a5-8*a1*a3^2*a5+16*a2^2*a4^2-16*a2*a3^2*a4+3*a3^4+2640*a0^2*a6^2-880*a0*a1*a5*a6+1312*a0*a2*a4*a6) / 2^7
*/
static GEN
igusaj4(GEN a0, GEN a1, GEN a2, GEN a3, GEN a4, GEN a5, GEN a6)
{
  pari_sp av = avma;
  return gerepileupto(av,
gmul2n(gadd(gsub(gadd(gadd(gsub(gadd(gsub(gsub(gadd(gsub(gadd(gsub(gsub(gmulsg(240,
gadd(gmul(gmul(gmul(a0, a3), a4), a5), gmul(gmul(gmul(a1, a2), a3), a6))),
gmulsg(400, gadd(gmul(gmul(a0, a2), gsqr(a5)), gmul(gmul(gsqr(a1), a4), a6)))),
gmulsg(64, gadd(gmul(a0, gpowgs(a4, 3)), gmul(gpowgs(a2, 3), a6)))), gmulsg(16,
gadd(gmul(gmul(a1, a3), gsqr(a4)), gmul(gmul(gsqr(a2), a3), a5)))),
gmul(gmul(gmulsg(672, a0), gsqr(a3)), a6)), gmul(gmulsg(240, gsqr(a1)),
gsqr(a5))), gmul(gmul(gmul(gmulsg(112, a1), a2), a4), a5)), gmul(gmul(gmulsg(8,
a1), gsqr(a3)), a5)), gmul(gmulsg(16, gsqr(a2)), gsqr(a4))),
gmul(gmul(gmulsg(16, a2), gsqr(a3)), a4)), gmulsg(3, gpowgs(a3, 4))),
gmul(gmulsg(2640, gsqr(a0)), gsqr(a6))), gmul(gmul(gmul(gmulsg(880, a0), a1),
a5), a6)), gmul(gmul(gmul(gmulsg(1312, a0), a2), a4), a6)), -7));
}

/*
j6(a0,a1,a2,a3,a4,a5,a6) = (1600*(a0^2*a4^2*a5^2+a1^2*a2^2*a6^2)+1600*(a0*a1*a2*a5^3+a1^3*a4*a5*a6)+640*(a0*a1*a3*a4*a5^2+a1^2*a2*a3*a5*a6)-4000*(a0^2*a3*a5^3+a1^3*a3*a6^2)-384*(a0*a1*a4^3*a5+a1*a2^3*a5*a6)-640*(a0*a2^2*a4*a5^2+a1^2*a2*a4^2*a6)+80*(a0*a2*a3^2*a5^2+a1^2*a3^2*a4*a6)+192*(a0*a2*a3*a4^2*a5+a1*a2^2*a3*a4*a6)-48*(a0*a3^3*a4*a5+a1*a2*a3^3*a6)-224*(a1^2*a3*a4^2*a5+a1*a2^2*a3*a5^2)+64*(a1^2*a4^4+a2^4*a5^2)-64*(a1*a2*a3*a4^3+a2^3*a3*a4*a5)+16*(a1*a3^3*a4^2+a2^2*a3^3*a5)-4096*(a0^2*a4^3*a6+a0*a2^3*a6^2)+6400*(a0^2*a2*a5^2*a6+a0*a1^2*a4*a6^2)+10560*(a0^2*a3*a4*a5*a6+a0*a1*a2*a3*a6^2)+2624*(a0*a1*a3*a4^2*a6+a0*a2^2*a3*a5*a6)-4432*a0*a1*a3^2*a5*a6-8*a2*a3^4*a4+a3^6-320*a1^3*a5^3+64*a1^2*a2*a4*a5^2+176*a1^2*a3^2*a5^2+128*a1*a2^2*a4^2*a5+112*a1*a2*a3^2*a4*a5-28*a1*a3^4*a5+16*a2^2*a3^2*a4^2+5120*a0^3*a6^3-2544*a0^2*a3^2*a6^2+312*a0*a3^4*a6-14336*a0^2*a2*a4*a6^2+1024*a0*a2^2*a4^2*a6-2560*a0^2*a1*a5*a6^2-2240*a0*a1^2*a5^2*a6-6528*a0*a1*a2*a4*a5*a6-1568*a0*a2*a3^2*a4*a6) / 2^10
*/
static GEN
igusaj6(GEN a0, GEN a1, GEN a2, GEN a3, GEN a4, GEN a5, GEN a6)
{
  pari_sp av = avma;
  return gerepileupto(av,
gmul2n(gsub(gsub(gsub(gsub(gadd(gsub(gadd(gsub(gadd(gadd(gsub(gadd(gadd(gadd(gadd(gsub(gadd(gsub(gsub(gadd(gadd(gadd(gsub(gadd(gsub(gadd(gsub(gsub(gadd(gadd(gsub(gsub(gsub(gadd(gadd(gmulsg(1600,
gadd(gmul(gmul(gsqr(a0), gsqr(a4)), gsqr(a5)), gmul(gmul(gsqr(a1), gsqr(a2)),
gsqr(a6)))), gmulsg(1600, gadd(gmul(gmul(gmul(a0, a1), a2), gpowgs(a5, 3)),
gmul(gmul(gmul(gpowgs(a1, 3), a4), a5), a6)))), gmulsg(640,
gadd(gmul(gmul(gmul(gmul(a0, a1), a3), a4), gsqr(a5)),
gmul(gmul(gmul(gmul(gsqr(a1), a2), a3), a5), a6)))), gmulsg(4000,
gadd(gmul(gmul(gsqr(a0), a3), gpowgs(a5, 3)), gmul(gmul(gpowgs(a1, 3), a3),
gsqr(a6))))), gmulsg(384, gadd(gmul(gmul(gmul(a0, a1), gpowgs(a4, 3)), a5),
gmul(gmul(gmul(a1, gpowgs(a2, 3)), a5), a6)))), gmulsg(640,
gadd(gmul(gmul(gmul(a0, gsqr(a2)), a4), gsqr(a5)), gmul(gmul(gmul(gsqr(a1),
a2), gsqr(a4)), a6)))), gmulsg(80, gadd(gmul(gmul(gmul(a0, a2), gsqr(a3)),
gsqr(a5)), gmul(gmul(gmul(gsqr(a1), gsqr(a3)), a4), a6)))), gmulsg(192,
gadd(gmul(gmul(gmul(gmul(a0, a2), a3), gsqr(a4)), a5), gmul(gmul(gmul(gmul(a1,
gsqr(a2)), a3), a4), a6)))), gmulsg(48, gadd(gmul(gmul(gmul(a0, gpowgs(a3, 3)),
a4), a5), gmul(gmul(gmul(a1, a2), gpowgs(a3, 3)), a6)))), gmulsg(224,
gadd(gmul(gmul(gmul(gsqr(a1), a3), gsqr(a4)), a5), gmul(gmul(gmul(a1,
gsqr(a2)), a3), gsqr(a5))))), gmulsg(64, gadd(gmul(gsqr(a1), gpowgs(a4, 4)),
gmul(gpowgs(a2, 4), gsqr(a5))))), gmulsg(64, gadd(gmul(gmul(gmul(a1, a2), a3),
gpowgs(a4, 3)), gmul(gmul(gmul(gpowgs(a2, 3), a3), a4), a5)))), gmulsg(16,
gadd(gmul(gmul(a1, gpowgs(a3, 3)), gsqr(a4)), gmul(gmul(gsqr(a2), gpowgs(a3,
3)), a5)))), gmulsg(4096, gadd(gmul(gmul(gsqr(a0), gpowgs(a4, 3)), a6),
gmul(gmul(a0, gpowgs(a2, 3)), gsqr(a6))))), gmulsg(6400,
gadd(gmul(gmul(gmul(gsqr(a0), a2), gsqr(a5)), a6), gmul(gmul(gmul(a0,
gsqr(a1)), a4), gsqr(a6))))), gmulsg(10560, gadd(gmul(gmul(gmul(gmul(gsqr(a0),
a3), a4), a5), a6), gmul(gmul(gmul(gmul(a0, a1), a2), a3), gsqr(a6))))),
gmulsg(2624, gadd(gmul(gmul(gmul(gmul(a0, a1), a3), gsqr(a4)), a6),
gmul(gmul(gmul(gmul(a0, gsqr(a2)), a3), a5), a6)))),
gmul(gmul(gmul(gmul(gmulsg(4432, a0), a1), gsqr(a3)), a5), a6)),
gmul(gmul(gmulsg(8, a2), gpowgs(a3, 4)), a4)), gpowgs(a3, 6)), gmul(gmulsg(320,
gpowgs(a1, 3)), gpowgs(a5, 3))), gmul(gmul(gmul(gmulsg(64, gsqr(a1)), a2), a4),
gsqr(a5))), gmul(gmul(gmulsg(176, gsqr(a1)), gsqr(a3)), gsqr(a5))),
gmul(gmul(gmul(gmulsg(128, a1), gsqr(a2)), gsqr(a4)), a5)),
gmul(gmul(gmul(gmul(gmulsg(112, a1), a2), gsqr(a3)), a4), a5)),
gmul(gmul(gmulsg(28, a1), gpowgs(a3, 4)), a5)), gmul(gmul(gmulsg(16, gsqr(a2)),
gsqr(a3)), gsqr(a4))), gmul(gmulsg(5120, gpowgs(a0, 3)), gpowgs(a6, 3))),
gmul(gmul(gmulsg(2544, gsqr(a0)), gsqr(a3)), gsqr(a6))), gmul(gmul(gmulsg(312,
a0), gpowgs(a3, 4)), a6)), gmul(gmul(gmul(gmulsg(14336, gsqr(a0)), a2), a4),
gsqr(a6))), gmul(gmul(gmul(gmulsg(1024, a0), gsqr(a2)), gsqr(a4)), a6)),
gmul(gmul(gmul(gmulsg(2560, gsqr(a0)), a1), a5), gsqr(a6))),
gmul(gmul(gmul(gmulsg(2240, a0), gsqr(a1)), gsqr(a5)), a6)),
gmul(gmul(gmul(gmul(gmul(gmulsg(6528, a0), a1), a2), a4), a5), a6)),
gmul(gmul(gmul(gmul(gmulsg(1568, a0), a2), gsqr(a3)), a4), a6)), -10));
}

/********************************************************************/
/**                                                                **/
/**   A REDUCTION ALGORITHM "A LA TATE" FOR CURVES OF GENUS 2      **/
/**                                                                **/
/********************************************************************/
/* Based on genus2reduction-0.3, http://www.math.u-bordeaux1.fr/~liu/G2R/
 * by Qing Liu <liu@math.u-bordeaux1.fr>
 * and Henri Cohen <cohen@math.u-bordeaux1.fr>

 * Qing Liu: Modeles minimaux des courbes de genre deux
 * J. fuer die Reine und Angew. Math., 453 (1994), 137-164.
 * http://www.math.u-bordeaux1.fr/~liu/articles/modregE.ps */

/* some auxiliary polynomials, gp2c-generated */

/*
apol2(a0,a1,a2) = -5*a1^2+12*a0*a2;
*/
static GEN
apol2(GEN a0, GEN a1, GEN a2)
{
  return gadd(gmulsg(-5, gsqr(a1)), gmul(gmulsg(12, a0), a2));
}

/*
apol3(a0,a1,a2,a3) = 5*a1^3+9*a0*(-2*a1*a2+3*a0*a3);
*/
static GEN
apol3(GEN a0, GEN a1, GEN a2, GEN a3)
{
  return gadd(gmulsg(5, gpowgs(a1, 3)), gmul(gmulsg(9, a0), gadd(gmul(gmulsg(-2, a1), a2), gmul(gmulsg(3, a0), a3))));
}

/*
apol5(a0,a1,a2,a3,a4,a5) = a1^5+3*a0*(-2*a1^3*a2+9*a0*a1^2*a3-36*a0^2*a1*a4+108*a0^3*a5);
*/
static GEN
apol5(GEN a0, GEN a1, GEN a2, GEN a3, GEN a4, GEN a5)
{
  return gadd(gpowgs(a1, 5), gmul(gmulsg(3, a0), gadd(gsub(gadd(gmul(gmulsg(-2, gpowgs(a1, 3)), a2), gmul(gmul(gmulsg(9, a0), gsqr(a1)), a3)), gmul(gmul(gmulsg(36, gsqr(a0)), a1), a4)), gmul(gmulsg(108, gpowgs(a0, 3)), a5))));
}

/*
bpol2(a0,a1,a2,a3,a4) = 2*a2^2-5*a1*a3+10*a0*a4;
*/
static GEN
bpol2(GEN a0, GEN a1, GEN a2, GEN a3, GEN a4)
{
  return gadd(gsub(gmulsg(2, gsqr(a2)), gmul(gmulsg(5, a1), a3)), gmul(gmulsg(10, a0), a4));
}

static const long VERYBIG = (1L<<20);
static long
myval(GEN x, GEN p) { return signe(x)? Z_pval(x,p): VERYBIG; }
static long
my3val(GEN x) { return signe(x)? Z_lval(x,3): VERYBIG; }
/* largest power of p dividing pol */
static long
polval(GEN pol, GEN p)
{
  long v, i, lx = lg(pol);
  if (!signe(pol)) return VERYBIG;
  v = myval(gel(pol,2),p);
  for(i = 3;i<lx;i++) v = minss(v, myval(gel(pol,i),p));
  return v;
}
/* b in Z[i], return v_3(b) */
static long
myval_zi(GEN b) { return minss(my3val(real_i(b)), my3val(imag_i(b))); }
/* b in Z[i, Y]/(Y^2-3), return v_Y(b) */
static long
myval_zi2(GEN b)
{
  long v0, v1;
  b = lift(b);
  v0 = myval_zi(RgX_coeff(b,0));
  v1 = myval_zi(RgX_coeff(b,1));
  return minss(2*v0, 2*v1+1);
}

/* min(a,b,c) */
static long
min3(long a, long b, long c)
{
  long m = a;
  if (b < m) m = b;
  if (c < m) m = c;
  return m;
}
/* min(a,b,c) */
static GEN
gmin3(GEN a, GEN b, GEN c)
{
  GEN m = a;
  if (gcmp(b, m) < 0) m = b;
  if (gcmp(c, m) < 0) m = c;
  return m;
}

/* a/b */
static GEN
frac2s(long a, long b) { return b == 1? stoi(a): gdivgs(stoi(a), b); }

/* Vector of p-adic factors (over Q_p) to accuracy r of pol. */
static GEN
padicfactors(GEN pol, GEN p, long r) { return gel(factorpadic(pol,p,r),1); }

/* x(1/t)*t^6, deg x <= 6 */
static GEN
RgX_recip6(GEN x)
{
  long lx = lg(x), i, j;
  GEN y = cgetg(9, t_POL);
  y[1] = x[1];
  for (i=8,j=2; j < lx; i--,j++) gel(y,i) = gel(x,j);
  for (       ; j <  9; i--,j++) gel(y,i) = gen_0;
  return normalizepol_lg(y, 9);
}
/* extract coefficients of a polynomial a0 X^6 + ... + a6, of degree <= 6 */
static void
RgX_to_6(GEN q, GEN *a0, GEN *a1, GEN *a2, GEN *a3, GEN *a4, GEN *a5, GEN *a6)
{
  *a0 = gen_0;
  *a1 = gen_0;
  *a2 = gen_0;
  *a3 = gen_0;
  *a4 = gen_0;
  *a5 = gen_0;
  *a6 = gen_0;
  switch(degpol(q))
  {
    case 6: *a0 = gel(q,8); /*fall through*/
    case 5: *a1 = gel(q,7); /*fall through*/
    case 4: *a2 = gel(q,6); /*fall through*/
    case 3: *a3 = gel(q,5); /*fall through*/
    case 2: *a4 = gel(q,4); /*fall through*/
    case 1: *a5 = gel(q,3); /*fall through*/
    case 0: *a6 = gel(q,2); /*fall through*/
  }
}

/* return a factor of maximal multiplicity (maxord) of the FpX Q, deg Q < 7.
 * In the special case maxord = 3 or maxord = 2 and p <= 5, make sure
 * the factor is irreducible */
static GEN
factmz(GEN Q, GEN p, long *maxord)
{
  GEN D, z = Q;
  long m = 0;
  if (cmpiu(p,5) <= 0)
  {
    if (FpX_is_squarefree(Q, p)) m = 1;
    else
    {
      GEN F = FpX_factor(Q,p), P = gel(F,1), E = gel(F,2);
      long i, l = 1;
      for(i = 1;i<lg(E);i++)
      {
        long e = E[i];
        if (e >= m) { m = e; l = i; }
      }
      z = gel(P,l);
    }
    *maxord = m; return z;
  }
  D = Q;
  for(;;)
  {
    GEN T;
    m++;
    D = FpX_deriv(D, p);
    T = FpX_gcd(z, D, p);
    if (degpol(T) == 0) break;
    z = T;
  }
  if (m >= 3 && degpol(z) == 2)
  {
    GEN F = FpX_factor(z,p);
    z = gcoeff(F,1,1);
  }
  *maxord = m; return z;
}

/* deg(H mod p) = 3, return v_p( disc(correspondig p-adic factor) ) */
static long
discpart(GEN H, GEN p, long prec)
{
  GEN list, prod, dis;
  long i, j;

  if (degpol(FpX_red(H,p)) != 3)
    pari_err_BUG("discpart [must not reach]");
  list = padicfactors(H,p,prec);
  prod = pol_1(varn(H));
  for(i = 1; i < lg(list); i++)
  {
    GEN t = gel(list,i);
    for(j = 3; j < lg(t); j++) /* include if non-constant mod p */
      if (!valp(gel(t,j))) { prod = RgX_mul(prod,t); break; }
  }
  if (degpol(prod) != 3) pari_err_BUG("discpart [prod degree]");
  dis = RgX_disc(prod);
  return gequal0(dis)? prec+1: valp(dis);
}


/* B = b0 X^6 + ... + b6 a ZX, 0 <= j <= 3.
 * Return theta_j(H) := min { v_p(b_i) / (i - j), lambda < i <= 6 } >= 0.
 * N.B. 60 theta \in Z */
static GEN
theta_j(GEN B, GEN p, long j)
{
  GEN theta, b0, b1, b2, b3, b4, b5, b6, v = new_chunk(7);
  long i;

  RgX_to_6(B, &b0,&b1,&b2,&b3,&b4,&b5,&b6);
  v[0] = myval(b0,p);
  v[1] = myval(b1,p);
  v[2] = myval(b2,p);
  v[3] = myval(b3,p);
  v[4] = myval(b4,p);
  v[5] = myval(b5,p);
  v[6] = myval(b6,p);
  theta = stoi(v[1+j]);
  for(i = 2+j; i <= 6; i++) theta = gmin(theta, frac2s(v[i], i-j));
  return theta;
}
/* compute theta_3 for B in Z[i][X], p = 3 */
static GEN
theta_3_zi(GEN B)
{
  long v2 = myval_zi(RgX_coeff(B,2));
  long v1 = myval_zi(RgX_coeff(B,1));
  long v0 = myval_zi(RgX_coeff(B,0));
  return frac2s(min3(6*v2, 3*v1, 2*v0), 6);
}
/* compute theta_3 for B in (Z[i,Y]/(Y^2-3))[X], p = 3 */
static GEN
theta_3_zi2(GEN B)
{
  long v2 = myval_zi2(RgX_coeff(B,2));
  long v1 = myval_zi2(RgX_coeff(B,1));
  long v0 = myval_zi2(RgX_coeff(B,0));
  return frac2s(min3(6*v2, 3*v1, 2*v0), 6);
}

/* T an FpX of degree 1, return its root */
static GEN
deg1root(GEN T, GEN p)
{
  GEN a = gel(T,2), b = gel(T,3);
  return Fp_neg(Fp_div(a, b, p), p);
}
/* H = minimal minimal over Z_p, p > 2.
 * alpha = 0,1
 * quad = 1 if root of order 3 in F_p^2 \ F_p, 0 otherwise
 * 0 <= lambda <= 3, t_INT
 * theta = theta(H, p), rational
 * beta >= 0, t_INT */
static GEN
polymini(GEN pol, GEN p)
{
  GEN a0, a1, a2, a3, a4, a5, a6;
  GEN H, Hp, rac, theta, polf, pro, quad;
  long alpha, lambda, maxord, beta;

  alpha = polval(pol,p);
  H = RgX_Rg_div(pol, powiu(p,alpha));
  RgX_to_6(H, &a0,&a1,&a2,&a3,&a4,&a5,&a6);
  if (dvdii(a0,p) && dvdii(a1,p) && dvdii(a2,p) && dvdii(a3,p))
  {
    H = RgX_recip6(H);
    RgX_to_6(H, &a0,&a1,&a2,&a3,&a4,&a5,&a6);
  }
  alpha = alpha&1;
  beta = 0;
  lambda = 0;
  if (!dvdii(a1,p)) lambda = 1;
  if (!dvdii(a2,p)) lambda = 2;
  if (!dvdii(a3,p)) lambda = 3;
  quad = gen_0;

  for(;;)
  {
    theta = theta_j(H,p,lambda);
    if (gcmp(theta,gen_1)>= 0)
    {
      long ent = itos(gfloor(theta));
      GEN pent = powiu(p,ent);
      H = RgX_Rg_div(RgX_unscale(H,pent), powiu(pent,6-lambda));
      alpha = (alpha+lambda*ent)&1;
      beta += ent;
      theta = gsubgs(theta,ent);
    }
    Hp = FpX_red(H, p);
    if (!gequal0(theta)) break;

    rac = factmz(Hp,p, &maxord);
    if (maxord <= 2)
    {
      if (degpol(Hp) <= 3) break;
      goto end;
    }
    else
    { /* maxord >= 3 */
      if (degpol(rac) == 2) { quad = gen_1; goto end; }
      rac = deg1root(rac, p);
      H = RgX_translate(H, rac);
      lambda = 6-maxord;
    }
  }

  if (lambda <= 2)
  {
    if (myval(RgX_coeff(H,2),p) > 1-alpha &&
        myval(RgX_coeff(H,1),p) > 2-alpha &&
        myval(RgX_coeff(H,0),p) > 3-alpha)
    {
      pol = RgX_unscale(H, p);
      if (alpha) pol = RgX_Rg_mul(pol, p);
      return polymini(pol, p);
    }
  }
  else if (lambda == 3 && alpha == 1)
  {
    if (degpol(Hp) == 3)
    {
      if (myval(RgX_coeff(H,6),p) >= 3 &&
          myval(RgX_coeff(H,5),p) >= 2)
      {
        H = RgX_rescale(H, p); /* H(x/p)p^(deg H) */
        H = RgX_Rg_div(H, powiu(p, degpol(H)-3)); /* H(x/p)p^3 */
        theta = gadd(theta,gen_1);
        alpha = 0;
        beta--;
      }
    }
    else if (degpol(Hp) == 6 && !gequal0(theta))
    {
      rac = factmz(RgX_mulXn(Hp, -3), p, &maxord);
      if (maxord == 3)
      {
        rac = deg1root(rac, p);
        pro = RgX_translate(RgX_unscale(H,p), rac); /* H(rac + px) */
        if (polval(pro,p)>= 3)
        {
          H = RgX_Rg_div(pro, powiu(p,3));
          alpha = 0;
          beta--;
          theta = theta_j(H,p,3);
        }
      }
    }
  }
end:
  polf = cgetg(7, t_VEC);
  gel(polf,1) = H;
  gel(polf,2) = stoi(lambda);
  gel(polf,3) = theta;
  gel(polf,4) = stoi(alpha);
  gel(polf,5) = quad;
  gel(polf,6) = stoi(beta);
  return polf;
}

/* a in Q[i], return a^3 mod 3 */
static GEN
zi_pow3mod(GEN a)
{
  GEN x, y;
  if (typ(a) != t_COMPLEX) return gmodgs(a,3);
  x = gmodgs(gel(a,1), 3);
  y = gmodgs(gel(a,2), 3);
  return mkcomplex(x, negi(y));
}
static GEN
polymini_zi(GEN pol) /* polynome minimal dans Z[i] */
{
  GEN p, polh, rac, theta;
  GEN a0, a1, a2, a3, a4, a5, a6;
  long alpha,beta;

  p = stoi(3);
  alpha = polval(pol,p) & 1;
  polh = alpha? RgX_Rg_div(pol, p): pol;
  beta = 0;
  rac = mkcomplex(Fp_div(RgX_coeff(polh,3), RgX_coeff(polh,6), p), gen_1);
  for(;;)
  {
    polh = RgX_translate(polh, rac);
    theta = theta_3_zi(polh);
    if (gcmp(theta,gen_1) >= 0)
    {
      long ent = itos(gfloor(theta));
      GEN pent = powiu(p,ent);
      polh = RgX_Rg_div(RgX_unscale(polh,pent), powiu(pent,3));
      alpha = (alpha+ent)&1;
      beta += ent;
      theta = gsubgs(theta,ent);
    }
    RgX_to_6(polh, &a0,&a1,&a2,&a3,&a4,&a5,&a6);
    if (!gequal0(theta) || !myval_zi(a4) || !myval_zi(a5)) break;
    rac = zi_pow3mod(gdiv(a6, gneg(a3)));
  }
  if (alpha && myval_zi(a0) >= 3 && myval_zi(a1) >= 2 && myval_zi(a2) >= 1)
  {
    theta = gadd(theta, gen_1);
    beta--;
    alpha = 0;
  }
  return mkvec3(theta, stoi(alpha), stoi(beta));
}

/* pol is a ZX, minimal polynomial over Z_3[i,Y]/(Y^2-3) */
static GEN
polymini_zi2(GEN pol)
{
  long alpha, beta;
  GEN a0, a1, a2, a3, a4, a5, a6;
  GEN p, polh, rac, theta, y = pol_x(fetch_var());

  p = stoi(3);
  if (polval(pol,p)) pari_err_BUG("polymini_zi2 [polynomial not minimal]");
  y = mkpolmod(y, gsubgs(gsqr(y), 3)); /* mod(y,y^2-3) */
  polh = pol;
  polh = gdivgs(RgX_unscale(polh, y),27); /* H(y*x) / 27 */
  if (myval_zi2(RgX_coeff(polh,4)) <= 0 ||
      myval_zi2(RgX_coeff(polh,2)) <= 0)
  {
    (void)delete_var();
    return mkcol2(gen_0, gen_0);
  }

  if (myval_zi2(gsub(RgX_coeff(polh,6), RgX_coeff(polh,0))) > 0)
    rac = gen_I();
  else
    rac = gen_1;
  alpha = 0;
  beta  = 0;
  for(;;)
  {
    polh = RgX_translate(polh, rac);
    theta = theta_3_zi2(polh);
    if (gcmp(theta,gen_1) >= 0)
    {
      long ent = itos(gfloor(theta));
      GEN pent = gpowgs(y, ent);
      polh = RgX_Rg_div(RgX_unscale(polh, pent), gpowgs(pent,3));
      alpha = (alpha+ent)&1;
      beta += ent;
      theta = gsubgs(theta,ent);
    }
    RgX_to_6(polh, &a0,&a1,&a2,&a3,&a4,&a5,&a6);
    if (!gequal0(theta) || !myval_zi2(a4) || !myval_zi2(a5)) break;
    a3 = liftpol_shallow(a3); if (typ(a3)==t_POL) a3 = RgX_coeff(a3,0);
    a6 = liftpol_shallow(a6); if (typ(a6)==t_POL) a6 = RgX_coeff(a6,0);
    rac = zi_pow3mod(gdiv(a6,gneg(a3)));
  }
  if (alpha)
  {
    if (myval_zi2(a0) >= 3 && myval_zi2(a1) >= 2 && myval_zi2(a2) >= 1)
    {
      theta = gadd(theta,gen_1);
      beta--;
      alpha = 0;
    }
    else pari_err_BUG("polymini_zi2 [alpha]");
  }
  (void)delete_var();
  return mkcol2(theta, stoi(beta));
}


struct igusa {
  GEN j2, i4, j4, j6, j8, j10, i12;
  GEN a0, A2, A3, A5, B2;
};
struct igusa_p {
  long eps, eps2, tt, r1, r2, R, tame;
  GEN p, stable, val, neron;
  const char *type;
};

static void
stable_reduction(struct igusa *I, struct igusa_p *Ip)
{
  static const long deg[9] = { 0,2,4,4,6,8,10,12 };
  GEN j2 = I->j2, i4 = I->i4, j6 = I->j6, j8 = I->j8, j10 = I->j10;
  GEN i12 = I->i12, p = Ip->p, val = Ip->val;
  GEN J, v, s, Ieps;
  long r1, r2, r3, r4, i, eps, eps2;

  v = cgetg(8,t_COL);
  for(i = 1; i <= 7; i++) gel(v,i) = frac2s(val[i], deg[i]);
  s = gel(v,1);
  for(i = 2; i <= 7; i++)
    if (gcmp(gel(v,i),s) < 0) s = gel(v,i);
  switch(itos_or_0(p))
  {
    case 2:  eps = 4; eps2 = 5; Ieps = j8; break;
    case 3:  eps = 3; eps2 = 4; Ieps = j6; break;
    default: eps = 1; eps2 = 1; Ieps = gdivgs(j2,12); break;
  }
  Ip->eps  = eps;
  Ip->eps2 = eps2;

  r1 = 3*eps*val[3];
  r3 = eps*val[6] + val[eps2];
  r2 = eps*val[7];
  r4 = min3(r1, r2, r3);

  /* s = max(v_p(X) / deg(X)) */
  J = cgetg(1, t_VEC);
  if (gequal(s,gel(v,6)))
    Ip->tt = 1;
  else if (gequal(s,gel(v,7)))
  {
    J = mkvec( Fp_to_mod(gmod(gdiv(gpowgs(i4,3),i12), p), p) );
    Ip->tt = 2;
  }
  else if (gequal(s,gel(v,3)))
    Ip->tt = (val[2] == val[3] || 2*val[4] == 3*val[3])? 3: 4;
  else if (r3 == r4)
  {
    GEN a,b, P, sj, pj, t = gmul(gpowgs(j10,eps),Ieps);
    sj = gaddsg(1728, gdiv(gpowgs(i12,eps), t));
    pj = gdiv(gpowgs(i4,3*eps), t);
    a = gmod(sj, p);
    b = gmod(pj, p);
    P = mkpoln(3, gen_1, Fp_neg(a,p), b, 0); /* X^2 - SX + P: roots j1,j2 */
    J = FpX_roots(P, p);
    switch(lg(J)-1)
    {
      case 0:
        P = FpX_to_mod(P, p);
        a = FpX_to_mod(pol_x(0), p);
        b = FpX_to_mod(deg1pol_shallow(b, gen_m1,0), p);
        J = mkvec2(mkpolmod(a,P), mkpolmod(b,P)); break;
      case 1:
        a = Fp_to_mod(gel(J,1), p);
        J = mkvec2(a, a); break;
      case 2:
        settyp(J, t_VEC);
        J = FpV_to_mod(J, p); break;
    }
    Ip->tt = 5;
  }
  else if (r2 == r4)
  {
    J = mkvec( Fp_to_mod(gmod(gdiv(gpowgs(i4,3),i12), p), p) );
    Ip->tt = 6;
  }
  else
    Ip->tt = 7; /* r1 == r4 */
  Ip->stable = mkvec2(stoi(Ip->tt), J);
}

struct red {
  const char *t, *pages;
  GEN g;
};

/* destroy v */
static GEN
zv_snf(GEN v)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++)
  {
    long j, a = v[i];
    for (j = i+1; j < l; j++)
    {
      long b = v[j], d = ugcd(a,b);
      v[i] = a = a*(b/d);
      v[j] = d;
    }
  }
  for (i = l-1; i > 0; i--)
    if (v[i] != 1) { setlg(v, i+1); break; }
  return zv_to_ZV(v);
}

static GEN
cyclic(long n)
{ return (n <= 1)? cgetg(1, t_VECSMALL): mkvecsmall(n); }
static GEN
dicyclic(long a, long b)
{
  long d;
  if (!a) a = 1;
  if (!b) b = 1;
  if (a < b) lswap(a,b);
  d = ugcd(a,b);
  if (d == 1) return cyclic(a*b);
  return mkvecsmall2(a*b/d, d);
}
/* Z/2xZ/2, resp Z/4 for n even, resp. odd */
static GEN
groupH(long n) { return odd(n)? cyclic(4): dicyclic(2,2); }

static long
get_red(struct red *S, struct igusa_p *Ip, GEN polh, GEN p, long alpha, long r)
{
  GEN val = Ip->val;
  long indice;
  switch(r)
  {
    case 0:
      indice = FpX_is_squarefree(FpX_red(polh,p), p)
               ? 0
               : val[6] - val[7] + val[Ip->eps2]/Ip->eps;
      S->t = stack_sprintf("I{%ld}", indice);
      S->pages = "159-177";
      S->g = cyclic(indice);
      return indice ? indice: 1;
    case 6:
      if (alpha == 0) /* H(px) /p^3 */
        polh = RgX_Rg_div(RgX_unscale(polh,p), powiu(p,3));
      indice = FpX_is_squarefree(FpX_red(polh,p), p)
               ? 0
               : val[6] - val[7] + val[Ip->eps2]/Ip->eps;
      S->t = stack_sprintf("I*{%ld}", indice);
      S->pages = "159-177";
      S->g = groupH(indice);
      return indice + 5;
    case 3:
      S->t = "III";
      S->pages = "161-177";
      S->g = cyclic(2);
      return 2;
    case 9:
      S->t = "III*";
      S->pages = "162-177";
      S->g = cyclic(2);
      return 8;
    case 2:
      S->t = "II";
      S->pages = "159-174";
      S->g = cyclic(1);
      return 1;
    case 8:
      S->t = "IV*";
      S->pages = "160-175";
      S->g = cyclic(3);
      return 7;
    case 4:
      S->t = "IV";
      S->pages = "160-174";
      S->g = cyclic(3);
      return 3;
    case 10:
      S->t = "II*";
      S->pages = "160-174";
      S->g = cyclic(1);
      return 9;
    default: pari_err_BUG("get_red [type]");
      S->t = "";
      S->pages = ""; /* gcc -Wall */
      S->g = NULL;
      return -1; /*notreached*/
  }
}

static long labelm3(GEN polh, GEN theta, long alpha, long dismin, struct igusa *I, struct igusa_p *Ip);

/* Ip->tt = 1 */
static long
tame_1(struct igusa *I, struct igusa_p *Ip)
{
  GEN p = Ip->p, val = Ip->val;
  GEN r, n, pro1, pro2;
  long condp = -1, va0, va5;
  va0 = myval(I->a0,p);
  va5 = myval(I->A5,p);
  if (!gequal0(I->A5) && 20*va0+val[6] > 6*va5)
  {
    pro1 = frac2s(val[6]-2*va5, 20);
    pro2 = frac2s(5*val[6]-6*va5, 40);
  }
  else
  {
    pro1 = frac2s(10*va0-val[6], 30);
    pro2 = frac2s(5*va0-val[6], 10);
  }
  n = lcmii(denom(pro1),denom(pro2));
  r = modii(gmul(n,pro1), n);
  switch(itos(n))
  {
    case 1:
      condp = 0;
      Ip->type = "[I{0-0-0}] page 155";
      Ip->neron = cyclic(1); break;
    case 2:
      switch(itos(r))
      {
        case 0:
          condp = 4;
          Ip->type = "[I*{0-0-0}] page 155";
          Ip->neron = mkvecsmall4(2,2,2,2); break;
        case 1:
          condp = 2;
          Ip->type = "[II] page 155";
          Ip->neron = cyclic(1); break;
        default: pari_err_BUG("tame_1 [bug1]");
      }
      break;
    case 4:
      condp = 4;
      Ip->type = "[VI] page 156";
      Ip->neron = dicyclic(2,2); break;
    default: pari_err_BUG("tame_1 [bug8]");
  }
  return condp;
}

static void
tame_234_init(struct igusa *I, struct igusa_p *Ip, long v12,
                long *pn, long *pq, long *pr, long *flc)
{
  long va0, va5, vb2;
  GEN p = Ip->p, pro1, pro2, n, r, q;
  va0 = myval(I->a0,p);
  va5 = myval(I->A5,p);
  vb2 = myval(I->B2,p);
  if (9*vb2 >= 6*va0+v12 && 36*va5 >= 120*va0+5*v12)
  {
    pro1 = frac2s(12*va0-v12, 36);
    pro2 = frac2s(6*va0-v12, 12);
    n = lcmii(denom(pro1),denom(pro2));
    r = gmul(n,pro1);
    q = gmul(n,pro2);
    *flc = 1;
  }
  else if (120*va0+5*v12 > 36*va5 && 60*vb2 >= 12*va5+5*v12)
  {
    pro1 = frac2s(36*va5-25*v12, 240);
    n = denom(pro1);
    q = gmul(n,pro1);
    r = gmulsg(-2,q);
    *flc = 1;
  }
  else if (6*va0+v12 > 9*vb2 && 12*va5+5*v12 > 60*vb2)
  {
    pro1 = frac2s(v12-6*vb2, 12);
    pro2 = frac2s(v12-9*vb2, 12);
    n = lcmii(denom(pro1),denom(pro2));
    r = gmul(n,pro1);
    q = gmul(n,pro2);
    *flc = 2;
  }
  else
  {
    pari_err_BUG("tame234 [bug9]");
    return; /*not reached*/
  }
  r = gmod(r,n);
  q = gmod(q,n);
  *pn = itos(n);
  *pq = itos(q);
  *pr = itos(r);
}

/* Ip->tt = 2 */
static long
tame_2(struct igusa *I, struct igusa_p *Ip, long v12)
{
  long condp = -1, d, n, q, r, flc;
  GEN val = Ip->val;
  tame_234_init(I, Ip, v12, &n, &q, &r, &flc);
  d = n * (6*val[6]-5*val[7]) / 6;
  switch(n)
  {
    case 1: condp = 1;
      Ip->type = stack_sprintf("[I{%ld-0-0}] page 170", d);
      Ip->neron = cyclic(d); break;
    case 2:
      switch(r)
      {
        case 0: condp = 4;
          Ip->type = stack_sprintf("[I*{%ld-0-0}] page 171",d/2);
          Ip->neron = concat(dicyclic(2,2),groupH(d/2)); break;
        case 1:
          switch(q)
          {
            case 0: condp = 2;
              Ip->type = stack_sprintf("[II*{%ld-0}] page 172",d/2);
              Ip->neron = cyclic(1); break;
            case 1: condp = 3;
              Ip->type = stack_sprintf("[II{%ld-0}] page 171",d/2);
              Ip->neron = cyclic(2*d); break;
            default: pari_err_BUG("tame2 [bug10]");
          }
          break;
        default: pari_err_BUG("tame2 [bug11]");
      }
      break;
    case 3: condp = 3;
      Ip->neron = cyclic(d);
      switch(r)
      {
        case 1:
          Ip->type = stack_sprintf("[IV-II{%ld}] page 175", (d-2)/3);
          break;
        case 2:
          Ip->type = stack_sprintf("[IV*-II{%ld}] page 175", (d-1)/3);
          break;
        default: pari_err_BUG("tame2 [bug12]");
      }
      break;
    case 4:
      switch(r)
      {
        case 1:
          switch(q)
          {
            case 1: condp = 3;
              Ip->type = stack_sprintf("[III-II{%ld}] page 177",(d-2)/4);
              Ip->neron = cyclic(d/2); break;
            case 3: condp = 4;
              Ip->type = stack_sprintf("[III*-II*{%ld}] page 178",(d-2)/4);
              Ip->neron = cyclic(8); break;
            default: pari_err_BUG("tame2 [bug13]");
          }
          break;
        case 3:
          switch(q)
          {
            case 1: condp = 4;
              Ip->type = stack_sprintf("[III-II*{%ld}] page 178",(d-2)/4);
              Ip->neron = cyclic(8); break;
            case 3: condp = 3;
              Ip->type = stack_sprintf("[III*-II{%ld}] page 178",(d-2)/4);
              Ip->neron = cyclic(d/2); break;
            default: pari_err_BUG("tame2 [bug14]");
          }
          break;
        default: pari_err_BUG("tame2 [bug15]");
      }
      break;
    case 6:
      switch(r)
      {
        case 2: condp = 4;
          Ip->type = stack_sprintf("[II*-II*{%ld}] page 176", (d-4)/6);
          Ip->neron = groupH((d+2)/6); break;
        case 4: condp = 4;
          Ip->type = stack_sprintf("[II-II*{%ld}] page 176", (d-2)/6);
          Ip->neron = groupH((d+4)/6); break;
          break;
        default: pari_err_BUG("tame2 [bug16]");
      }
      break;
    default: pari_err_BUG("tame2 [bug17]");
  }
  return condp;
}

/* Ip->tt = 3 */
static long
tame_3(struct igusa *I, struct igusa_p *Ip, long v12)
{
  long condp = -1, n, q, r, flc;
  long va5, d1, d2;
  GEN val = Ip->val, e1, e2;
  tame_234_init(I, Ip, v12, &n, &q, &r, &flc);

  va5 = 2*val[6]-5*val[3];
  e1 = gmin(stoi(val[7]-3*val[3]),gmul2n(stoi(va5),-2));
  e2 = gsub(gmul2n(stoi(va5),-1),e1);
  d1 = itos(gmulsg(n,e1));
  d2 = itos(gmulsg(n,e2));
  switch(n)
  {
    case 1: condp = 2;
      Ip->type = stack_sprintf("[I{%ld-%ld-0}] page 179", d1,d2);
      Ip->neron = dicyclic(d1,d2); break;
    case 2:
      switch(r)
      {
        case 0: condp = 4;
          Ip->type = stack_sprintf("[I*{%ld-%ld-0}] page 180", d1/2,d2/2);
          Ip->neron = concat(groupH(d1/2),groupH(d2/2)); break;
        case 1:
          switch(flc)
          {
            case 1:condp = 3;
              Ip->type = stack_sprintf("[2I{%ld}-0] page 181", d1);
              Ip->neron = cyclic(d1); break;
            case 2: condp = 3;
              Ip->type = stack_sprintf("[II{%ld-%ld}] page 182",d1/2,d2/2);
              if ((d1*d2-4)&7)
                Ip->neron = cyclic(2*d1);
              else
                Ip->neron = dicyclic(d1,2);
              /* FIXME: "or" same with d1<->d2 */
              break;
          }
          break;
        default: pari_err_BUG("tame3 [bug20]");
      }
      break;
    case 4: condp = 4;
      Ip->type = stack_sprintf("[III{%ld}] page 182", d1/2);
      Ip->neron = groupH(d1/2); break;
    default: pari_err_BUG("tame3 [bug21]");
  }
  return condp;
}

/* Ip->tt = 4 */
static long
tame_4(struct igusa *I, struct igusa_p *Ip, long v12)
{
  long condp = -1, d1, d2, d3, f1, f2, g, h, n, q, r, flc;
  GEN val = Ip->val, e1, e2, e3, vl, vn, vm;
  tame_234_init(I, Ip, v12, &n, &q, &r, &flc);
  vl = stoi(val[6]-5*val[1]);
  vn = stoi(val[7]-6*val[1]);
  vm = stoi(val[2]-2*val[1]);
  e1 = gmin3(gdivgs(vl,3), gmul2n(vn,-1), vm);
  e2 = gmin(gmul2n(gsub(vl,e1),-1), gsub(vn,e1));
  e3 = gsub(vl,gadd(e1,e2));
  d1 = itos(gmulsg(n,e1));
  d2 = itos(gmulsg(n,e2));
  d3 = itos(gmulsg(n,e3));
  g = d1*d2 + d1*d3 + d2*d3;
  h = cgcd(cgcd(d1,d2),d3);
  switch(n)
  {
    case 1: condp = 2;
      Ip->type = stack_sprintf("[I{%ld-%ld-%ld}] page 182",d1,d2,d3);
      Ip->neron = dicyclic(h,g/h); break;
    case 2:
      switch(r)
      {
        case 0: condp = 4;
          Ip->type = stack_sprintf("[I*{%ld-%ld-%ld}] page 183",d1/2,d2/2,d3/2);
          Ip->neron = concat(groupH(g/4), groupH(2-((h&2)>>1))); break;
        case 1:
          if      (d1 == d2 || d1 == d3) f2 = d1;
          else if (d2 == d3) f2 = d2;
          else {
            pari_err_BUG("tame4 [bug23]");
            return -1; /*not reached*/
          }
          f1 = d1+d2+d3-2*f2;
          switch(q)
          {
            case 0: condp = 3;
              Ip->type = stack_sprintf("[II*{%ld-%ld}] page 184", f1/2,f2);
              Ip->neron = cyclic(f2); break;
            case 1: condp = 3;
              Ip->type = stack_sprintf("[II{%ld-%ld}] page 183", f1/2,f2);
              Ip->neron = cyclic(2*f1+f2); break;
            default: pari_err_BUG("tame4 [bug24]");
          }
          break;
        default: pari_err_BUG("tame4 [bug25]");
      }
      break;
    case 3: condp = 4;
      Ip->type = stack_sprintf("[III{%ld}] page 184",d1);
      Ip->neron = (d1%3)? cyclic(9): dicyclic(3,3); break;
    case 6: condp = 4;
      Ip->type = stack_sprintf("[III*{%ld}] page 184",d1/2);
      Ip->neron = cyclic(1); break;
    default: pari_err_BUG("tame4 [bug26]");
  }
  return condp;
}

/* p = 3 */
static void
tame_567_init_3(struct igusa_p *Ip, GEN dk,
                long *pd, long *pn, long *pdm, long *pr)
{
  long n = 1 + Ip->r1/6;
  *pd = itos(gmulgs(dk,n));
  *pn = n;
  *pr = -1; /* unused */
  *pdm = 0;
}

static void
tame_567_init(struct igusa *I, struct igusa_p *Ip, GEN dk,
              long *pd, long *pn, long *pdm, long *pr)
{
  long va0, va2, va3, va5, vb2;
  long d, v1, v2;
  GEN r, n, m;
  GEN pro1, dm, rk;
  GEN p = Ip->p, val = Ip->val;
  long v5;

  if (equalis(p, 3)) { tame_567_init_3(Ip, dk, pd, pn, pdm, pr); return; }
  /* assume p > 3 */
  va0 = myval(I->a0,p);
  va2 = myval(I->A2,p);
  va3 = myval(I->A3,p);
  va5 = myval(I->A5,p);
  vb2 = myval(I->B2,p);
  v5 = myval(subii(mulii(I->A2,I->A3),mulsi(3,I->A5)),p);
  rk = gadd(frac2s(va0, 2),
            gmin3(gmul2n(dk,-1),
                  frac2s(2*va3-3*va2, 8),
                  frac2s(2*v5 - 5*va2, 12)));
  v1 = 2*va3-4*va0-val[1];
  v2 = 6*va5-20*va0-5*val[1];
  /* the definition of n differs according to the parity of val[1] */
  if (! odd(val[Ip->eps2]))
  {
    if (3*vb2 >= 2*va0+2*val[1] && v1 >= 0 && v2 >= 0
                                && (v1 == 0 || v2 == 0))
    { /* Prop 4.3.1 (a) */
      pro1 = frac2s(va0+val[1], 6);
      n = lcmii(denom(dk),denom(pro1));
      r = gmul(n,pro1);
    }
    else if (20*va0+5*val[1] > 6*va5 && 10*vb2 >= 2*va5+5*val[1])
    { /* Prop 4.3.1 (b) */
      pro1 = frac2s(2*va5+val[1], 8);
      n = lcmii(denom(dk),denom(pro1));
      r = gmul(n,pro1);
    }
    else if (2*va0+2*val[1] > 3*vb2 && 2*va5+5*val[1] > 10*vb2)
    { /* Prop 4.3.1 (c) */
      pro1 = gmul2n(stoi(vb2),-2);
      n = lcmii(denom(dk),denom(pro1));
      r = gmul(n,pro1);
    }
    else if (3*vb2 >= 2*va0+2*val[1] && 2*va3 > 4*va0+val[1]
                                     && 6*va5 > 20*va0+5*val[1])
    { /* Prop 4.3.1 (d) */
      if (gequal0(I->A2)) pari_err_BUG("tame567 [bug27]");
      n = lcmii(denom(dk),denom(rk));
      r = gmul(n,rk);
    }
    else
    {
      pari_err_BUG("tame567 [bug29]");
      return; /*not reached*/
    }
  }
  else
  {
    m = denom(dk);
    r = gmul(m,dk);
    n = gmul2n(m,1);
  }
  d = itos(gmul(n,dk));
  dm = modsi(d,n);
  r = modii(r,n);
  *pd = d;
  *pn = itos(n);
  *pr = itos(r);
  *pdm = itos(dm);
}

static long
tame_5(struct igusa *I, struct igusa_p *Ip, GEN dk)
{
  long condp = -1, d, n, dm, r;
  GEN val = Ip->val;

  tame_567_init(I, Ip, dk, &d, &n, &dm, &r);
  if (! odd(val[Ip->eps2]))
  {
    switch(n)
    {
      case 1: condp = 0;
        Ip->type = stack_sprintf("[I{0}-I{0}-%ld] page 158", d);
        Ip->neron = cyclic(1); break;
      case 2:
        switch(dm)
        {
          case 0: condp = 4;
            Ip->type = stack_sprintf("[I*{0}-I*{0}-%ld] page 158",(d-2)/2);
            Ip->neron = mkvecsmall4(2,2,2,2); break;
          case 1: condp = 2;
            Ip->type = stack_sprintf("[I{0}-I*{0}-%ld] page 159",(d-1)/2);
            Ip->neron = dicyclic(2,2); break;
        }
        break;
      case 3:
        switch(dm)
        {
          case 0: condp = 4;
            Ip->type = stack_sprintf("[IV-IV*-%ld] page 165",(d-3)/3);
            Ip->neron = dicyclic(3,3); break;
          case 1:
            switch(r)
            {
              case 0: case 1: condp = 2;
                Ip->type = stack_sprintf("[I{0}-IV-%ld] page 160",(d-1)/3);
                Ip->neron = cyclic(3); break;
              case 2: condp = 4;
                Ip->type = stack_sprintf("[IV*-IV*-%ld] page 166",(d-4)/3);
                Ip->neron = dicyclic(3,3); break;
            }
            break;
          case 2:
            switch(r)
            {
              case 0: case 2: condp = 2;
                Ip->type = stack_sprintf("[I{0}-IV*-%ld] page 160",(d-2)/3);
                Ip->neron = cyclic(3); break;
              case 1: condp = 4;
                Ip->type = stack_sprintf("[IV-IV-%ld] page 165",(d-2)/3);
                Ip->neron = dicyclic(3,3); break;
            }
            break;
        }
        break;
      case 4:
        switch(dm)
        {
          case 0: condp = 4;
            Ip->type = stack_sprintf("[III-III*-%ld] page 169",(d-4)/4);
            Ip->neron = dicyclic(2,2); break;
          case 1:
            switch(r)
            {
              case 0: case 1: condp = 2;
                Ip->type = stack_sprintf("[I{0}-III-%ld] page 161",(d-1)/4);
                Ip->neron = cyclic(2); break;
              case 2: case 3: condp = 4;
                Ip->type = stack_sprintf("[I*{0}-III*-%ld] page 162",(d-5)/4);
                Ip->neron = mkvecsmall3(2,2,2); break;
            }
            break;
          case 2: condp = 4;
            Ip->neron = dicyclic(2,2);
            switch(r)
            {
              case 1:
                Ip->type = stack_sprintf("[III-III-%ld] page 169",(d-2)/4);
                break;
              case 3:
                Ip->type = stack_sprintf("[III*-III*-%ld] page 169",(d-6)/4);
                break;
              default: pari_err_BUG("tame5 [bug29]");
            }
            break;
          case 3:
            switch(r)
            {
              case 0: case 3: condp = 2;
                Ip->type = stack_sprintf("[I{0}-III*-%ld] page 162",(d-3)/4);
                Ip->neron = cyclic(2); break;
              case 1: case 2: condp = 4;
                Ip->type = stack_sprintf("[I*{0}-III-%ld] page 162",(d-3)/4);
                Ip->neron = mkvecsmall3(2,2,2); break;
            }
            break;
        }
        break;
      case 6:
        switch(dm)
        {
          case 0: condp = 4;
            Ip->type = stack_sprintf("[II-II*-%ld] page 163",(d-6)/6);
            Ip->neron = cyclic(1); break;
          case 1:
            switch(r)
            {
              case 0: case 1: condp = 2;
                Ip->type = stack_sprintf("[I{0}-II-%ld] page 159",(d-1)/6);
                Ip->neron = cyclic(1); break;
              case 2: case 5: condp = 4;
                Ip->type = stack_sprintf("[II*-IV-%ld] page 164",(d-7)/6);
                Ip->neron = cyclic(3); break;
              case 3: case 4: condp = 4;
                Ip->type = stack_sprintf("[I*{0}-IV*-%ld] page 161",(d-7)/6);
                Ip->neron = mkvecsmall2(6,2); break;
            }
            break;
          case 2:
            switch(r)
            {
              case 1: condp = 4;
                Ip->type = stack_sprintf("[II-II-%ld] page 163",(d-2)/6);
                Ip->neron = cyclic(1); break;
              case 3: case 5: condp = 4;
                Ip->type = stack_sprintf("[I*{0}-II*-%ld] page 160",(d-8)/6);
                Ip->neron = dicyclic(2,2); break;
              default: pari_err_BUG("tame5 [bug30]");
            }
            break;
          case 3:
            Ip->neron = cyclic(3);
            switch(r)
            {
              case 1: case 2: condp = 4;
                Ip->type = stack_sprintf("[II-IV-%ld] page 164",(d-3)/6);
                break;
              case 4: case 5: condp = 4;
                Ip->type = stack_sprintf("[II*-IV*-%ld] page 164",(d-9)/6);
                break;
              default: pari_err_BUG("tame5 [bug31]");
            }
            break;
          case 4:
            switch(r)
            {
              case 1: case 3: condp = 4;
                Ip->type = stack_sprintf("[I*{0}-II-%ld] page 160",(d-4)/6);
                Ip->neron = dicyclic(2,2); break;
              case 5: condp = 4;
                Ip->type = stack_sprintf("[II*-II*-%ld] page 163",(d-10)/6);
                Ip->neron = cyclic(1); break;
              default: pari_err_BUG("tame5 [bug32]");
            }
            break;
          case 5:
            switch(r)
            {
              case 0: case 5: condp = 2;
                Ip->type = stack_sprintf("[I{0}-II*-%ld] page 160",(d-5)/6);
                Ip->neron = cyclic(1); break;
              case 1: case 4: condp = 4;
                Ip->type = stack_sprintf("[II-IV*-%ld] page 164",(d-5)/6);
                Ip->neron = cyclic(3); break;
              case 2: case 3: condp = 4;
                Ip->type = stack_sprintf("[I*{0}-IV-%ld] page 161",(d-5)/6);
                Ip->neron = mkvecsmall2(6,2); break;
            }
            break;
          default: pari_err_BUG("tame5 [bug33]");
        }
        break;
      case 12:
        condp = 4;
        switch(dm)
        {
          case 1:
            switch(r)
            {
              case 3: case 10:
                Ip->type = stack_sprintf("[II*-III-%ld] page 166",(d-13)/12);
                Ip->neron = cyclic(2); break;
              case 4: case 9:
                Ip->type = stack_sprintf("[IV-III*-%ld] page 167",(d-13)/12);
                Ip->neron = cyclic(6); break;
              default: pari_err_BUG("tame5 [bug34]");
            }
            break;
          case 5:
            switch(r)
            {
              case 2: case 3:
                Ip->type = stack_sprintf("[II-III-%ld] page 166",(d-5)/12);
                Ip->neron = cyclic(2); break;
              case 8: case 9:
                Ip->type = stack_sprintf("[IV*-III*-%ld] page 168",(d-17)/12);
                Ip->neron = cyclic(6); break;
              default: pari_err_BUG("tame5 [bug35]");
            }
            break;
          case 7:
            switch(r)
            {
              case 3: case 4:
                Ip->type = stack_sprintf("[IV-III-%ld] page 167",(d-7)/12);
                Ip->neron = cyclic(6); break;
              case 9: case 10:
                Ip->type = stack_sprintf("[II*-III*-%ld] page 167",(d-19)/12);
                Ip->neron = cyclic(2); break;
              default: pari_err_BUG("tame5 [bug36]");
            }
            break;
          case 11:
            switch(r)
            {
              case 3: case 8:
                Ip->type = stack_sprintf("[IV*-III-%ld] page 168",(d-11)/12);
                Ip->neron = cyclic(6); break;
              case 2: case 9:
                Ip->type = stack_sprintf("[II-III*-%ld] page 166",(d-11)/12);
                Ip->neron = cyclic(2); break;
              default: pari_err_BUG("tame5 [bug37]");
            }
            break;
          default: pari_err_BUG("tame5 [bug38]");
        }
        break;
      default: pari_err_BUG("tame5 [bug39]");
    }
  }
  else
  {
    r %= (n >> 1);
    switch(n)
    {
      case 2: condp = 2;
        Ip->type = stack_sprintf("[2I{0}-%ld] page 159",(d/2));
        Ip->neron = cyclic(1); break;
      case 4: condp = 4;
        Ip->type = stack_sprintf("[2I*{0}-%ld] page 159",(d/2-1)/2);
        Ip->neron = dicyclic(2,2); break;
      case 6: condp = 4;
        Ip->neron = cyclic(3);
        switch(r)
          {
          case 1:
            Ip->type = stack_sprintf("[2IV-%ld] page 165",(d/2-1)/3);
            break;
          case 2:
            Ip->type = stack_sprintf("[2IV*-%ld] page 165",(d/2-2)/3);
            break;
          default: pari_err_BUG("tame5 [bug40]");
          }
        break;
      case 8: condp = 4;
        Ip->neron = cyclic(2);
        switch(r)
        {
          case 1:
            Ip->type = stack_sprintf("[2III-%ld] page 168",(d/2-1)/4);
            break;
          case 3:
            Ip->type = stack_sprintf("[2III*-%ld] page 168",(d/2-3)/4);
            break;
          default: pari_err_BUG("tame5 [bug41]");
        }
        break;
      case 12: condp = 4;
        Ip->neron = cyclic(1);
        switch(r)
        {
          case 1:
            Ip->type = stack_sprintf("[2II-%ld] page 162",(d/2-1)/6);
            break;
          case 5:
            Ip->type = stack_sprintf("[2II*-%ld] page 163",(d/2-5)/6);
            break;
          default: pari_err_BUG("tame5 [bug42]");
        }
        break;
      default: pari_err_BUG("tame5 [bug43]");
    }
  }
  return condp;
}

static long
tame_6(struct igusa *I, struct igusa_p *Ip, GEN dk,
         GEN polh, GEN theta, long alpha, long dismin)
{
  long condp = -1, d, d1, n, dm, r;
  GEN val = Ip->val, d1k;

  tame_567_init(I, Ip, dk, &d, &n, &dm, &r);
  d1k = frac2s(Ip->eps*(val[6]-val[7])+val[Ip->eps2], Ip->eps);
  d1 = itos(gmulsg(n,d1k));
  switch(n)
  {
    case 1: condp = 1;
      Ip->type = stack_sprintf("[I{%ld}-I{0}-%ld] page 170",d1,d);
      Ip->neron = cyclic(d1); break;
    case 2:
      switch(dm)
      {
        case 0: condp = 4;
          Ip->type=stack_sprintf("[I*{0}-I*{%ld}-%ld] page 171", d1/2,(d-2)/2);
          Ip->neron = concat(groupH(d1/2), dicyclic(2,2)); break;
        case 1: return labelm3(polh,theta,alpha,dismin,I,Ip);
        default: pari_err_BUG("tame6 [bug44]");
      }
      break;
    case 3: condp = 3;
      Ip->neron = dicyclic(3,d1/3);
      switch(dm)
      {
        case 1:
          Ip->type = stack_sprintf("[IV-I{%ld}-%ld] page 173",d1/3,(d-1)/3);
          break;
        case 2:
          Ip->type = stack_sprintf("[IV*-I{%ld}-%ld] page 173",d1/3,(d-2)/3);
          break;
        default: pari_err_BUG("tame6 [bug45]");
      }
      break;
    case 4:
      switch(dm)
      {
        case 1:
          switch(r)
          {
            case 0: case 1: condp = 3;
              Ip->type=stack_sprintf("[III-I{%ld}-%ld] page 176",d1/4,(d-1)/4);
              Ip->neron = dicyclic(2,d1/4); break;
            case 2: case 3: condp = 4;
              Ip->type=stack_sprintf("[III*-I*{%ld}-%ld] page 177",d1/4,(d-5)/4);
              Ip->neron = concat(groupH(d1/4), cyclic(2)); break;
              break;
            default: pari_err_BUG("tame6 [bug46]");
          }
          break;
        case 3:
          switch(r)
          {
            case 0: case 3: condp = 3;
              Ip->type=stack_sprintf("[III*-I{%ld}-%ld] page 176",d1/4,(d-3)/4);
              Ip->neron = dicyclic(2,d1/4); break;
            case 1: case 2: condp = 4;
              Ip->type=stack_sprintf("[III-I*{%ld}-%ld] page 177",d1/4,(d-3)/4);
              Ip->neron = concat(groupH(d1/4), cyclic(2)); break;
            default: pari_err_BUG("tame6 [bug47]");
          }
          break;
        default: pari_err_BUG("tame6 [bug48]");
      }
      break;
    case 6:
      switch(dm)
      {
        case 1:
          switch(r)
          {
            case 0: case 1: condp = 3;
              Ip->type = stack_sprintf("[II-I{%ld}-%ld] page 172",d1/6,(d-1)/6);
              Ip->neron = cyclic(d1/6); break;
            case 3: case 4: condp = 4;
              Ip->type=stack_sprintf("[IV*-I*{%ld}-%ld] page 174",d1/6,(d-7)/6);
              Ip->neron = concat(groupH(d1/6), cyclic(3)); break;
            default: pari_err_BUG("tame6 [bug49]");
          }
          break;
        case 2: condp = 4;
          Ip->type = stack_sprintf("[II*-I*{%ld}-%ld] page 174",d1/6,(d-8)/6);
          Ip->neron = groupH(d1/6); break;
        case 4: condp = 4;
          Ip->type = stack_sprintf("[II-I*{%ld}-%ld] page 173",d1/6,(d-4)/6);
          Ip->neron = groupH(d1/6); break;
        case 5:
          switch(r)
          {
            case 0: case 5: condp = 3;
              Ip->type=stack_sprintf("[II*-I{%ld}-%ld] page 172",d1/6,(d-5)/6);
              Ip->neron = cyclic(d1/6); break;
            case 2: case 3: condp = 4;
              Ip->type=stack_sprintf("[IV-I*{%ld}-%ld] page 174",d1/6,(d-5)/6);
              Ip->neron = concat(groupH(d1/6), cyclic(3)); break;
            default: pari_err_BUG("tame6 [bug50]");
          }
          break;
        default: pari_err_BUG("tame6 [bug51]");
      }
      break;
    default: pari_err_BUG("tame6 [bug52]");
  }
  return condp;
}

static long
tame_7(struct igusa *I, struct igusa_p *Ip, GEN dk,
         GEN polh, GEN theta, long alpha, long dismin)
{
  long condp = -1, d, d1, d2, n, dm, r;
  GEN val = Ip->val, d1k, d2k, pro1;

  tame_567_init(I, Ip, dk, &d, &n, &dm, &r);
  pro1 = frac2s(Ip->eps*val[6]+val[Ip->eps2]-3*Ip->eps*val[3], Ip->eps);
  d1k = gmin(stoi(val[7]-3*val[3]),gmul2n(pro1,-1));
  d2k = gsub(pro1,d1k);

  d1 = itos(gmulsg(n,d1k));
  d2 = itos(gmulsg(n,d2k));
  switch(n)
  {
    case 1: condp = 2;
      Ip->type = stack_sprintf("[I{%ld}-I{%ld}-%ld] page 179",d1,d2,d);
      Ip->neron = dicyclic(d1,d2); break;
    case 2:
      if ( odd(val[Ip->eps2]) )
      {
        condp = 3;
        Ip->type = stack_sprintf("[2I{%ld}-%ld] page 181",d1,d/2);
        Ip->neron = cyclic(d1);
      }
      else if (dm == 0)
      {
        condp = 4;
        Ip->type = stack_sprintf("[I*{%ld}-I*{%ld}-%ld] page 180", d1/2,d2/2,(d-2)/2);
        Ip->neron = concat(groupH(d1/2),groupH(d2/2));
      }
      else
      {
        GEN H;
        if (d1 != d2) return labelm3(polh,theta,alpha,dismin,I,Ip);
        condp = 3; H = groupH(d1/2);
        Ip->type = stack_sprintf("[I{%ld}-I*{%ld}-%ld] page 180", d1/2,d1/2,(d-1)/2);
        Ip->neron = concat(H, H);
      }
      break;
    case 4: condp = 4;
      Ip->type = stack_sprintf("[2I*{%ld}-%ld] page 181",d1/2,(d-2)/4);
      Ip->neron = groupH(d1/2); break;
    default: pari_err_BUG("tame7 [bug55]");
  }
  return condp;
}

static long
tame(GEN polh, GEN theta, long alpha, long dismin, struct igusa *I, struct igusa_p *Ip)
{
  GEN val = Ip->val, dk;
  Ip->tame = 1;
  switch(Ip->tt)
  {
    case 1: return tame_1(I, Ip);
    case 2: return tame_2(I, Ip, myval(I->i12,  Ip->p));
    case 3: return tame_3(I, Ip, 3*myval(I->i4, Ip->p));
    case 4: return tame_4(I, Ip, 6*myval(I->j2, Ip->p));
    case 5:
      dk = frac2s(Ip->eps*val[6]-5*val[Ip->eps2], 12*Ip->eps);
      return tame_5(I, Ip, dk);
    case 6:
      dk = frac2s(Ip->eps*val[7]-6*val[Ip->eps2], 12*Ip->eps);
      return tame_6(I, Ip, dk, polh, theta, alpha, dismin);
    case 7:
      dk = frac2s(Ip->eps*val[3]-2*val[Ip->eps2], 4*Ip->eps);
      return tame_7(I, Ip, dk, polh, theta, alpha, dismin);
  }
  return -1; /*not reached*/
}

/* maxc = maximum conductor valuation at p */
static long
get_maxc(GEN p)
{
  switch (itos_or_0(p))
  {
    case 2:  return 20; break;
    case 3:  return 10; break;
    case 5:  return 9; break;
    default: return 4; break; /* p > 5 */
  }
}

/* p = 3 */
static long
quartic(GEN polh, long alpha, long dismin, struct igusa_p *Ip)
{
  GEN theta, val = Ip->val, p = Ip->p;
  GEN polf = polymini_zi2(ZX_Z_mul(polh, powiu(p, alpha)));
  long condp = -1, d, R, r1, beta;
  theta = gel(polf,1);
  beta = itos(gel(polf,2));
  if (odd(beta)) pari_err_BUG("quartic [type over Z[i] must be [K-K-(2*m)]]");
  R = beta/2;
  r1 = itos(gmulgs(theta,6));
  switch(Ip->tt)
  {
    case 1: case 5: d = 0;break;
    case 3: d = val[6] - 5*val[3]/2;break;
    case 7: d = val[6] - 3*val[3] + val[Ip->eps2]/Ip->eps;break;
    default: pari_err_BUG("quartic [type choices]");
             d = 0; /*not reached*/
  }
  switch(r1)
  {
    case 0:
      if (d)
      {
        condp = 3;
        Ip->type = stack_sprintf("[2I{%ld}-%ld] page 181",d,R);
        Ip->neron = cyclic(d);
      }
      else
      {
        condp = 2;
        Ip->neron = cyclic(1);
        if (R) Ip->type = stack_sprintf("[2I{0}-%ld] page 159",R);
        else   Ip->type = "[II] page 155";
      }
      break;
    case 6: condp = 4;
      Ip->type = stack_sprintf("[2I*{%ld}-%ld] pages 159, 181",d,R);
      Ip->neron = dicyclic(2,2); break;
    case 3: condp = 4;
      Ip->type = stack_sprintf("[2III-%ld] page 168",R);
      Ip->neron = cyclic(2); break;
    case 9: condp = 4;
      Ip->type = stack_sprintf("[2III*-%ld] page 168",R);
      Ip->neron = cyclic(2); break;
    case 2: condp = dismin-12*R-13;
      Ip->type = stack_sprintf("[2II-%ld] page 162",R);
      Ip->neron = cyclic(1); break;
    case 8: condp = dismin-12*R-19;
      Ip->type = stack_sprintf("[2IV*-%ld] page 165",R);
      Ip->neron = cyclic(3); break;
    case 4: condp = dismin-12*R-15;
      Ip->type = stack_sprintf("[2IV-%ld] page 165",R);
      Ip->neron = cyclic(3); break;
    case 10: condp = dismin-12*R-21;
      Ip->type = stack_sprintf("[2II*-%ld] page 163",R);
      Ip->neron = cyclic(1); break;
    default: pari_err_BUG("quartic [type1]");
  }
  if (condp > get_maxc(p) || condp < 0) pari_err_BUG("quartic [conductor]");
  return condp;
}

static long
litredtp(long alpha, long alpha1, GEN theta, GEN theta1, GEN polh, GEN polh1,
         long dismin, struct igusa *I, struct igusa_p *Ip)
{
  GEN val = Ip->val, p = Ip->p;
  long condp = -1, indice, d, R = Ip->R;

  if ((Ip->r1 == 0||Ip->r1 == 6) && (Ip->r2 == 0||Ip->r2 == 6))
  { /* (r1,r2) = (0,0), (0,6), (6,0) or (6,6) */
    if (Ip->tt == 5)
    {
      switch(Ip->r1 + Ip->r2)
      {
      case 0: /* (0,0) */
        condp = 0;
        Ip->type = stack_sprintf("[I{0}-I{0}-%ld] page 158",R);
        Ip->neron = cyclic(1); break;
      case 6: /* (0,6) or (6,0) */
        condp = 2;
        Ip->type = stack_sprintf("[I*{0}-I{0}-%ld] page 159",R);
        Ip->neron = dicyclic(2,2); break;
      case 12: /* (6,6) */
        condp = 4;
        Ip->type = stack_sprintf("[I*{0}-I*{0}-%ld] page 158",R);
        Ip->neron = mkvecsmall4(2,2,2,2); break;
      }
      return condp;
    }
    if (Ip->r1 == Ip->r2) return tame(polh, theta, alpha, dismin, I, Ip);
    if (Ip->tt == 6)
    {
      d = val[6] - val[7] + (val[Ip->eps2]/Ip->eps);
      if (Ip->r1 && alpha1 == 0) /* H(px) / p^3 */
        polh1 = RgX_Rg_div(RgX_unscale(polh1,p), powiu(p,3));
      if (FpX_is_squarefree(FpX_red(polh1,p),p))
      { indice = 0; condp = 3-Ip->r2/6; }
      else
      { indice = d; condp = 3-Ip->r1/6; }
    }
    else
    { /* Ip->tt == 7 */
      long d1;
      d = val[6] - 3*val[3] + (val[Ip->eps2]/Ip->eps);
      if (gequal1(theta1)) /* H(px) / p^3 */
        polh1 = RgX_Rg_div(RgX_unscale(polh1,p), powiu(p,3));
      d1 = minss(val[7]-3*val[3],d/2);
      if (d == 2*d1) indice = d1;
      else
      {
        indice = discpart(polh1,p,d1+1);
        if (indice>= d1+1) indice = d-d1;
        else indice = d1;
      }
      condp = 3;
    }
    if (Ip->r1)
    { /* (6,0) */
      Ip->neron = concat(cyclic(d-indice),groupH(indice));
      if (Ip->tt == 6)
        Ip->type = stack_sprintf("[I*{%ld}-I{%ld}-%ld] page 170",indice,d-indice,R);
      else
        Ip->type = stack_sprintf("[I*{%ld}-I{%ld}-%ld] page 180",indice,d-indice,R);
    }
    else
    { /* (0,6) */
      Ip->neron = concat(cyclic(indice),groupH(d-indice));
      if (Ip->tt == 6)
        Ip->type = stack_sprintf("[I{%ld}-I*{%ld}-%ld] page 170", indice,d-indice,R);
      else
        Ip->type = stack_sprintf("[I{%ld}-I*{%ld}-%ld] page 180", indice,d-indice,R);
    }
    return condp;
  }
  if (Ip->tt == 7) pari_err_BUG("litredtp [switch ri]");
  {
    struct red S1, S;
    long comp = get_red(&S1, Ip, polh1, p, alpha1, Ip->r1)
              + get_red(&S,  Ip, polh, p, alpha, Ip->r2);
    Ip->type = stack_sprintf("[%s-%s-%ld] pages %s", S1.t, S.t, R, S.pages);
    Ip->neron = concat(S1.g, S.g);
    condp = (R >= 0)? dismin-comp+2-12*R: dismin-comp+4;
  }
  if (condp > get_maxc(p)) pari_err_BUG("litredtp [conductor]");
  return condp;
}

static long
labelm3(GEN polh, GEN theta, long alpha, long dismin,
        struct igusa *I, struct igusa_p *Ip)
{
  GEN polh1, theta1, polf, val = Ip->val, p = Ip->p;
  long alpha1, lambda, beta, R;

  polh1 = polh;
  theta1 = theta;
  alpha1 = alpha;
  polf = polymini(ZX_Z_mul(RgX_recip6(polh), powiu(p,alpha)), p);
  polh  = gel(polf,1);
  lambda= itos(gel(polf,2));
  theta = gel(polf,3);
  alpha = itos(gel(polf,4));
  beta  = itos(gel(polf,6));
  if (lambda != 3) pari_err_BUG("labelm3 [lambda = 3]");
  R = beta-alpha1-alpha;
  if (R&1) pari_err_BUG("labelm3 [R odd]");
  R >>= 1;
  if (R <= -2) pari_err_BUG("labelm3 [R <= -2]");
  if (val[Ip->eps2] % (2*Ip->eps)) pari_err_BUG("labelm3 [val(eps2)]");
  if (R >= 0 && (alpha+alpha1) >= 1) pari_err_BUG("labelm3 [minimal equation]");
  Ip->r1 = itos(gmulgs(theta1,6)) + 6*alpha1;
  Ip->r2 = itos(gmulgs(theta, 6)) + 6*alpha;
  Ip->R = R;
  return litredtp(alpha, alpha1, theta, theta1, polh, polh1, dismin, I, Ip);
}

/* p = 3 */
static long
quadratic(GEN polh, long alpha, long dismin,
          struct igusa *I, struct igusa_p *Ip)
{
  long alpha1, beta, R;
  GEN polf, polh1, theta, theta1;
  alpha1 = alpha;
  polf = polymini_zi(ZX_Z_mul(polh, powiu(Ip->p,alpha)));
  theta = gel(polf,1);
  alpha = itos(gel(polf,2));
  beta  = itos(gel(polf,3));
  if (alpha && beta >= 1) pari_err_BUG("quadratc");
  R = beta-alpha;
  if (R >= 0 && alpha1)
  {
    dismin -= 10;
    if (DEBUGLEVEL)
      err_printf("(Care: minimal discriminant over Z[i] smaller than over Z)\n");
  }
  Ip->r1 = itos(gmulgs(theta,6))+6*alpha;
  Ip->r2 = Ip->r1;
  Ip->R = R;
  alpha1 = alpha;
  theta1 = theta;
  polh1 = polh; /* FIXME !!! */
  return litredtp(alpha, alpha1, theta, theta1, polh, polh1, dismin, I, Ip);
}

static long
genus2localred(struct igusa *I, struct igusa_p *Ip, GEN p, GEN polmini)
{
  GEN val, polh, theta, list, c1, c2, c3, c4, c5, c6, prod;
  long i, vb5, vb6, d, dismin, alpha, lambda;
  long condp = -1, indice, vc6, mm, nb, dism;

  val = cgetg(8, t_VECSMALL);
  Ip->tame = 0;
  Ip->neron = NULL;
  Ip->type = NULL;
  Ip->p = p;
  Ip->val = val;
  val[1] = myval(I->j2,p);
  val[2] = myval(I->j4,p);
  val[3] = myval(I->i4,p);
  val[4] = myval(I->j6,p);
  val[5] = myval(I->j8,p);
  val[6] = myval(I->j10,p);
  val[7] = myval(I->i12,p);
  dismin = val[6];
  stable_reduction(I, Ip);
  if (dismin == 0)
  {
    Ip->tame = 1;
    Ip->type = "[I{0-0-0}] page 155";
    Ip->neron = cyclic(1); return 0;
  }
  if (dismin == 1)
  {
    Ip->type = "[I{1-0-0}] page 170";
    Ip->neron = cyclic(1); return 1;
  }
  if (dismin == 2) switch(Ip->tt)
  {
    case 2:
      Ip->type = "[I{2-0-0}] page 170";
      Ip->neron = cyclic(2); return 1;
    case 3:
      Ip->type = "[I{1-1-0}] page 179";
      Ip->neron = cyclic(1); return 2;
    case 5:
      if (cmpis(p,3) <= 0) pari_err_BUG("genus2localred [tt 1]");
      Ip->type = "[I{0}-II-0] page 159";
      Ip->neron = cyclic(1); return 2;
    default: pari_err_BUG("genus2localred [tt 2]");
  }
  if (equaliu(p,2)) return -1;
  polh = gel(polmini,1);
  lambda = itos(gel(polmini,2));
  theta = gel(polmini,3);
  alpha = itos(gel(polmini,4));
  if (!gequal0(gel(polmini,5)))
    return equalis(p,3)? quadratic(polh, alpha, dismin, I, Ip):
                         tame(polh, theta, alpha, dismin, I, Ip);
  if (gequal0(theta) && lambda<= 2)
  {
    if (Ip->tt >= 5) pari_err_BUG("genus2localred [tt 3]");
    return tame(polh, theta, alpha, dismin, I, Ip);
  }
  if (dismin == 3)
  {
    switch(Ip->tt)
    {
      case 2: return tame(polh, theta, alpha, dismin, I, Ip);
      case 3: Ip->type = "[I{2-1-0}] page 179"; Ip->neron = cyclic(2); return 2;
      case 4: Ip->type = "[I{1-1-1}] page 182"; Ip->neron = cyclic(3); return 2;
      case 5:
        if (equalis(p,3) && !gequal(theta,ghalf))
          return labelm3(polh,theta,alpha,dismin,I,Ip);
        Ip->type = "[I{0}-III-0] page 161"; Ip->neron = cyclic(2); return 2;
      case 6:
        if (equalis(p,3)) pari_err_BUG("genus2localred [conductor]");
        Ip->type = "[I{1}-II-0] page 172"; Ip->neron = cyclic(1); return 3;
    }
    pari_err_BUG("genus2localred [switch tt 4]");
    return -1; /* not reached */
  }
  switch(lambda)
  {
    case 0:
      switch(itos(gmulgs(theta, 60))+alpha)
      {
        case 10:
          condp = dismin-1;
          Ip->type = "[V] page 156";
          Ip->neron = cyclic(3); break;
        case 11:
          condp = dismin-11;
          Ip->type = "[V*] page 156";
          Ip->neron = cyclic(3); break;
        case 12:
          condp = dismin-2;
          Ip->type = "[IX-2] page 157";
          Ip->neron = cyclic(5); break;
        case 13:
          condp = dismin-12;
          Ip->type = "[VIII-4] page 157";
          Ip->neron = cyclic(1); break;
        case 24:
          condp = dismin-8;
          Ip->type = "[IX-4] page 158";
          Ip->neron = cyclic(5);
          break;
        case 15: case 16:
          if (Ip->tt>= 5) pari_err_BUG("genus2localred [tt 6]");
          return tame(polh, theta, alpha, dismin, I, Ip);
        case 20: case 21:
          {
            GEN b0, b1, b2, b3, b4, b5, b6, b02, b03, b04, b05;
            RgX_to_6(polh, &b0,&b1,&b2,&b3,&b4,&b5,&b6);
            vb5 = myval(b5,p);
            vb6 = myval(b6,p);
            if (vb6 >= 3)
            {
              if (vb5 < 2) pari_err_BUG("genus2localred [red1]");
              if (vb5 >= 3)
              {
                condp = dismin-8;
                Ip->type = "[II*-IV-(-1)] page 164";
                Ip->neron = cyclic(3);
              }
              else
              {
                condp = dismin-7;
                Ip->type = "[IV-III*-(-1)] page 167";
                Ip->neron = cyclic(6);
              }
              break;
            }
            if (dvdii(b0,p)) pari_err_BUG("genus2localred [b0]");
            b02 = gsqr(b0);
            b03 = gmul(b02, b0);
            b04 = gmul(b03, b0);
            b05 = gmul(b04, b0);
            c1 = gmul2n(b1,-1);
            c2 = gmul2n(gsub(gmul(b0,b2), gsqr(c1)),-1);
            c3 = gmul2n(gsub(gmul(b02,b3), gmul2n(gmul(c1,c2),1)),-1);
            c4 = gsub(gmul(b03,b4), gadd(gmul2n(gmul(c1,c3),1),gsqr(c2)));
            c5 = gsub(gmul(b04,b5), gmul2n(gmul(c2,c3),1));
            c6 = gsub(gmul(b05,b6), gsqr(c3));
            /* b0^5*H(x/b0) = (x^3+c1*x^2+c2*x+c3)^2+c4*x^2+c5*x+c6 */
            vc6 = myval(c6,p);
            if (vc6 == 2)
            {
              if (alpha)
              {
                condp = dismin-16;
                Ip->type = "[IV] page 155";
                Ip->neron = cyclic(1);
              }
              else
              {
                condp = dismin-6;
                Ip->type = "[III] page 155";
                Ip->neron = dicyclic(3,3);
              }
            }
            else
            {
              if (myval(c3,p) > 1) pari_err_BUG("genus2localred [c3]");
              mm = min3(3*myval(c4,p)-4, 3*myval(c5,p)-5, 3*vc6-6);
              if (alpha)
              {
                condp = dismin-mm-16;
                Ip->type = stack_sprintf("[III*{%ld}] page 184", mm);
                Ip->neron = cyclic(1);
              }
              else
              {
                condp = dismin-mm-6;
                Ip->type = stack_sprintf("[III{%ld}] page 184", mm);
                Ip->neron = (mm%3)? cyclic(9): dicyclic(3,3);
              }
            }
          }
          break;
        case 30:
          return equalis(p,3)? quartic(polh, alpha, dismin, Ip)
                             : tame(polh, theta, alpha, dismin, I, Ip);
        default: pari_err_BUG("genus2localred [red2]");
      }
      break;
    case 1:
      switch(itos(gmulgs(theta, 60))+alpha)
      {
        case 12:
          condp = dismin;
          Ip->type = "[VIII-1] page 156";
          Ip->neron = cyclic(1); break;
        case 13:
          condp = dismin-10;
          Ip->type = "[IX-3] page 157";
          Ip->neron = cyclic(5); break;
        case 24:
          condp = dismin-4;
          Ip->type = "[IX-1] page 157";
          Ip->neron = cyclic(5); break;
        case 25:
          condp = dismin-14;
          Ip->type = "[VIII-3] page 157";
          Ip->neron = cyclic(1); break;
        case 36:
          condp = dismin-8;
          Ip->type = "[VIII-2] page 157";
          Ip->neron = cyclic(1); break;
        case 15:
          condp = dismin-1;
          Ip->type = "[VII] page 156";
          Ip->neron = cyclic(2); break;
        case 16:
          condp = dismin-11;
          Ip->type = "[VII*] page 156";
          Ip->neron = cyclic(2); break;
        case 20:
          if (cmpis(p,3))
          {
            d = 6*val[6]-5*val[7]-2;
            if (d%6) pari_err_BUG("genus2localred [index]");
            dism = (d/6);
          }
          else
          {
            list = padicfactors(polh,p,dismin-5);
            nb = lg(list);
            prod = pol_1(varn(polh));
            for(i = 1;i<nb;i++)
            {
              GEN c = gel(list,i);
              if (valp(gel(c,2)) && degpol(c)<= 2) prod = RgX_mul(prod,c);
            }
            if (degpol(prod) > 2) pari_err_BUG("genus2localred [padicfactors]");
            dism = valp(RgX_disc(prod)) - 1;
          }
          condp = dismin-dism-3;
          Ip->type = stack_sprintf("[II-II*{%ld}] page 176", dism);
          Ip->neron = groupH(dism+1); break;
        case 21:
          vb6 = myval(RgX_coeff(polh,0),p);
          if (vb6<2) pari_err_BUG("genus2localred [red3]");
          condp = dismin-14;
          Ip->type = "[IV*-II{0}] page 175";
          Ip->neron = cyclic(1); break;
        case 30:
          vb5 = myval(RgX_coeff(polh,1),p);
          if (vb5 == 2)
          {
            if (Ip->tt >= 5) pari_err_BUG("genus2localred [tt 6]");
            return tame(polh, theta, alpha, dismin, I, Ip);
          }
          condp = dismin-7;
          Ip->type = "[II*-III-(-1)] page 167";
          Ip->neron = cyclic(2); break;
      }
      break;
    case 2:
      if (equalis(denom(theta),4))
      {
        if (Ip->tt>4) pari_err_BUG("genus2localred [tt 5]");
        return tame(polh, theta, alpha, dismin, I, Ip);
      }
      if (!equalis(p,3) && equalis(denom(theta),3))
        return tame(polh, theta, alpha, dismin, I, Ip);
      list = padicfactors(polh,p,dismin-10*alpha);
      nb = lg(list); prod = pol_1(varn(polh));
      for(i = 1;i<nb;i++)
      {
        GEN c = gel(list,i);
        if (!valp(gel(c,2))) prod = RgX_mul(prod,c);
      }
      switch(degpol(prod))
      {
        GEN e0, e1, e2;
        case 0:
          dism = 0; break;
        case 1:
          e1 = gel(prod,3);
          dism = 2*valp(e1); break;
        case 2:
          e0 = gel(prod,2);
          e1 = gel(prod,3);
          e2 = gel(prod,4);
          dism = valp(gsub(gsqr(e1),gmul2n(gmul(e0,e2),2))); break;
        default:
          pari_err_BUG("genus2localred [padicfactors 2]");
          dism = 0;
      }
      switch(itos(gmulgs(theta,12))+alpha-4)
      {
        case 0:
          condp = dismin-dism-1;
          Ip->type = stack_sprintf("[IV-II{%ld}] page 175", dism);
          Ip->neron = cyclic(3*dism+2); break;
        case 1:
          condp = dismin-dism-10;
          Ip->type = stack_sprintf("[II*-II*{%ld}] page 176",dism);
          Ip->neron = groupH(dism+1); break;
          break;
        case 2: case 3:
          if (myval(RgX_coeff(polh,0),p) == 2)
          {
            if (Ip->tt>4) pari_err_BUG("genus2localred [tt 5]");
            return tame(polh, theta, alpha, dismin, I, Ip);
          }
          dism++;
          indice = val[6]-(5*val[3]/2)-dism;
          condp = dismin-dism-indice-2;
          Ip->type = stack_sprintf("[II{%ld-%ld}] page 182", dism,indice);
          Ip->neron = both_odd(dism,indice)? dicyclic(2,2*dism): cyclic(4*dism);
          break;
        case 4:
          condp = dismin-dism-5;
          Ip->type = stack_sprintf("[IV*-II{%ld}] page 175",dism+1);
          Ip->neron = cyclic(3*dism+4); break;
      }
      break;
    case 3:
      if (!equalis(p,3) || Ip->tt <= 4)
        return tame(polh, theta, alpha, dismin, I, Ip);
      return labelm3(polh,theta,alpha,dismin,I,Ip); /* p = 3 */
    default: pari_err_BUG("genus2localred [switch lambda]");
  }
  if (condp < 2 || condp > get_maxc(p))
    pari_err_BUG("genus2localred [conductor]");
  return condp;
}

static long
chk_pol(GEN P) {
  switch(typ(P))
  {
    case t_INT: break;
    case t_POL: RgX_check_ZX(P,"genus2red"); return varn(P); break;
    default: pari_err_TYPE("genus2red", P);
  }
  return -1;
}

/* P,Q are ZX, study Y^2 + Q(X) Y = P(X) */
GEN
genus2red(GEN PQ, GEN p)
{
  pari_sp av = avma;
  struct igusa I;
  GEN P, Q;
  GEN j22, j42, j2j6, a0,a1,a2,a3,a4,a5,a6, V,polr,facto,factp, vecmini, cond;
  long i, l, dd, vP,vQ;

  if (typ(PQ) == t_VEC && lg(PQ) == 3)
  {
    P = gel(PQ,1);
    Q = gel(PQ,2);
  }
  else
  {
    P = PQ;
    Q = gen_0;
  }

  vP = chk_pol(P);
  vQ = chk_pol(Q);
  if (vP < 0)
  {
    if (vQ < 0) pari_err_TYPE("genus2red",mkvec2(P,Q));
    P = scalarpol(P,vQ);
  }
  else if (vQ < 0) Q = scalarpol(Q,vP);
  if (p && typ(p) != t_INT) pari_err_TYPE("genus2red", p);

  polr = ZX_add(ZX_sqr(Q), gmul2n(P,2)); /* ZX */
  switch(degpol(polr))
  {
    case 5: case 6: break;
    default: pari_err_DOMAIN("genus2red","genus","!=", gen_2,mkvec2(P,Q));
  }

  RgX_to_6(polr, &a0,&a1,&a2,&a3,&a4,&a5,&a6);
  I.j10 = !signe(a0)? mulii(sqri(a1), ZX_disc(polr)): ZX_disc(polr);
  if (!signe(I.j10))
    pari_err_DOMAIN("genus2red","genus","<",gen_2,mkvec2(P,Q));
  I.j10 = gmul2n(I.j10, -12); /* t_INT */

  if (p == NULL)
  {
    facto = factor(absi(I.j10));
    factp = gel(facto,1);
  }
  else
  {
    factp = mkcol(p);
    facto = mkmat2(factp, mkcol(gen_1));
  }
  l = lg(factp);
  vecmini = cgetg(l, t_COL);
  for(i = 1; i<l; i++)
  {
    GEN l = gel(factp,i), pm;
    if (i == 1 && equalis(l, 2)) { gel(vecmini,1) = gen_0; continue; }
    gel(vecmini,i) = pm = polymini(polr, l);
    polr = RgX_Rg_mul(gel(pm,1), powii(l, gel(pm,4)));
  }
  RgX_to_6(polr, &a0,&a1,&a2,&a3,&a4,&a5,&a6);
  I.j10 = !signe(a0)? mulii(sqri(a1), ZX_disc(polr)): ZX_disc(polr);
  I.j10 = gmul2n(I.j10,-12);

  I.a0 = a0;
  I.A2 = apol2(a0,a1,a2);
  I.A3 = apol3(a0,a1,a2,a3);
  I.A5 = apol5(a0,a1,a2,a3,a4,a5);
  I.B2 = bpol2(a0,a1,a2,a3,a4);

  I.j2 = igusaj2(a0,a1,a2,a3,a4,a5,a6);
  I.j4 = igusaj4(a0,a1,a2,a3,a4,a5,a6);
  I.i4 = gsub(gsqr(I.j2), gmulsg(24,I.j4));
  I.j6 = igusaj6(a0,a1,a2,a3,a4,a5,a6);
  j42 = gsqr(I.j4);
  j22 = gsqr(I.j2);
  j2j6 = gmul(I.j2,I.j6);
  I.j8 = gmul2n(gsub(j2j6,j42), -2);
  I.i12= gmul2n(gsub(gadd(gmul(j22,j42),gmulsg(36,gmul(j2j6,I.j4))),
                     gadd(gadd(gmulsg(32,gmul(j42,I.j4)),gmul(j2j6,j22)),gmulsg(108,gsqr(I.j6)))),-2);

  for(i = 1; i < l; i++)
    gcoeff(facto,i,2) = stoi(Q_pval(I.j10, gel(factp,i)));
  dd = polval(polr,gen_2) & (~1); /* = 2 floor(val/2) */
  polr = gmul2n(polr, -dd);

  V = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN q = gel(factp,i), red, N = NULL;
    struct igusa_p Ip;
    long f = genus2localred(&I, &Ip, q, gel(vecmini,i));
    gcoeff(facto,i,2) = stoi(f);
    if (Ip.tame) Ip.type = stack_strcat("(tame) ", Ip.type);
    if (f >= 0)
      N = zv_snf(Ip.neron);
    if (DEBUGLEVEL)
    {
      if (!p) err_printf("p = %Ps\n", q);
      err_printf("(potential) stable reduction: %Ps\n", Ip.stable);
      if (f >= 0) {
        err_printf("reduction at p: %s, %Ps", Ip.type, N);
        err_printf(", f = %ld\n", f);
      }
    }
    red = f >= 0? mkvec2(strtoGENstr(Ip.type), N): cgetg(1, t_VEC);
    gel(V, i) = mkvec3(q, Ip.stable, red);
  }
  if (p) V = gel(V,1);
  cond = factorback(facto);
  /* remove denominator 2 coming from f = -1 in genuslocalred(, p = 2) */
  if (typ(cond) != t_INT) cond = gel(cond,1);
  return gerepilecopy(av, mkvec4(cond, facto, polr, V));
}
