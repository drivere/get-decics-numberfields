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
/**                                                                **/
/**                       ELLIPTIC CURVES                          **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"
#undef coordch

/* Transforms a curve E into short Weierstrass form E' modulo p.
   Returns a vector, the first two entries of which are a4' and a6'.
   The third entry is a vector describing the isomorphism E' \to E.
*/

static ulong
Fl_c4_to_a4(ulong c4, ulong p)
{ return Fl_neg(Fl_mul(c4, 27, p), p); }
static void
Fl_c4c6_to_a4a6(ulong c4, ulong c6, ulong p, ulong *a4, ulong *a6)
{
  *a4 = Fl_c4_to_a4(c4, p);
  *a6 = Fl_neg(Fl_mul(c6, 54, p), p);
}
static GEN
c4_to_a4(GEN c4, GEN p)
{ return Fp_neg(Fp_mulu(c4, 27, p), p); }
static void
c4c6_to_a4a6(GEN c4, GEN c6, GEN p, GEN *a4, GEN *a6)
{
  *a4 = c4_to_a4(c4, p);
  *a6 = Fp_neg(Fp_mulu(c6, 54, p), p);
}
static void
ell_to_a4a6(GEN E, GEN p, GEN *a4, GEN *a6)
{
  GEN c4 = Rg_to_Fp(ell_get_c4(E),p);
  GEN c6 = Rg_to_Fp(ell_get_c6(E),p);
  c4c6_to_a4a6(c4, c6, p, a4, a6);
}
static void
Fl_ell_to_a4a6(GEN E, ulong p, ulong *a4, ulong *a6)
{
  ulong c4 = Rg_to_Fl(ell_get_c4(E),p);
  ulong c6 = Rg_to_Fl(ell_get_c6(E),p);
  Fl_c4c6_to_a4a6(c4, c6, p, a4, a6);
}

/* [6,3b2,3a1,108a3] */
static GEN
a4a6_ch(GEN E, GEN p)
{
  GEN a1 = Rg_to_Fp(ell_get_a1(E),p);
  GEN a3 = Rg_to_Fp(ell_get_a3(E),p);
  GEN b2 = Rg_to_Fp(ell_get_b2(E),p);
  retmkvec4(modsi(6,p),Fp_mulu(b2,3,p),Fp_mulu(a1,3,p),Fp_mulu(a3,108,p));
}
static GEN
a4a6_ch_Fl(GEN E, ulong p)
{
  ulong a1 = Rg_to_Fl(ell_get_a1(E),p);
  ulong a3 = Rg_to_Fl(ell_get_a3(E),p);
  ulong b2 = Rg_to_Fl(ell_get_b2(E),p);
  return mkvecsmall4(6 % p,Fl_mul(b2,3,p),Fl_mul(a1,3,p),Fl_mul(a3,108,p));
}

static GEN
ell_to_a4a6_bc(GEN E, GEN p)
{
  GEN A4, A6;
  ell_to_a4a6(E, p, &A4, &A6);
  retmkvec3(A4, A6, a4a6_ch(E,p));
}
GEN
point_to_a4a6(GEN E, GEN P, GEN p, GEN *pa4)
{
  GEN c4 = Rg_to_Fp(ell_get_c4(E),p);
  *pa4 = c4_to_a4(c4, p);
  return FpE_changepointinv(RgV_to_FpV(P,p), a4a6_ch(E,p), p);
}
GEN
point_to_a4a6_Fl(GEN E, GEN P, ulong p, ulong *pa4)
{
  ulong c4 = Rg_to_Fl(ell_get_c4(E),p);
  *pa4 = Fl_c4_to_a4(c4, p);
  return Fle_changepointinv(RgC_to_Flc(P,p), a4a6_ch_Fl(E,p), p);
}

void
checkellpt(GEN z)
{
  if (typ(z)!=t_VEC) pari_err_TYPE("checkellpt", z);
  switch(lg(z))
  {
    case 3: break;
    case 2: if (isintzero(gel(z,1))) break;
    /* fall through */
    default: pari_err_TYPE("checkellpt", z);
  }
}
void
checkell5(GEN E)
{
  long l = lg(E);
  if (typ(E)!=t_VEC || (l != 17 && l != 6)) pari_err_TYPE("checkell5",E);
}
void
checkell(GEN E)
{ if (typ(E)!=t_VEC || lg(E) != 17) pari_err_TYPE("checkell",E); }
void
checkellisog(GEN v)
{ if (typ(v)!=t_VEC || lg(v) != 4) pari_err_TYPE("checkellisog",v); }

void
checkell_Q(GEN E)
{
  if (typ(E)!=t_VEC || lg(E) != 17 || ell_get_type(E)!=t_ELL_Q)
    pari_err_TYPE("checkell over Q",E);
}

void
checkell_Qp(GEN E)
{
  if (typ(E)!=t_VEC || lg(E) != 17 || ell_get_type(E)!=t_ELL_Qp)
    pari_err_TYPE("checkell over Qp",E);
}

static int
ell_over_Fq(GEN E)
{
  long t = ell_get_type(E);
  return t==t_ELL_Fp || t==t_ELL_Fq;
}

void
checkell_Fq(GEN E)
{
  if (typ(E)!=t_VEC || lg(E) != 17 || !ell_over_Fq(E))
  pari_err_TYPE("checkell over Fq", E);
}

GEN
ellff_get_p(GEN E)
{
  GEN fg = ellff_get_field(E);
  return typ(fg)==t_INT? fg: FF_p_i(fg);
}

int
ell_is_integral(GEN E)
{
  return typ(ell_get_a1(E)) == t_INT
      && typ(ell_get_a2(E)) == t_INT
      && typ(ell_get_a3(E)) == t_INT
      && typ(ell_get_a4(E)) == t_INT
      && typ(ell_get_a6(E)) == t_INT;
}

static void
checkcoordch(GEN z)
{ if (typ(z)!=t_VEC || lg(z) != 5) pari_err_TYPE("checkcoordch",z); }

/* 4 X^3 + b2 X^2 + 2b4 X + b6 */
GEN
ec_bmodel(GEN e)
{
  GEN b2 = ell_get_b2(e), b6 = ell_get_b6(e), b42 = gmul2n(ell_get_b4(e),1);
  return mkpoln(4, utoipos(4), b2, b42, b6);
}

static int
invcmp(void *E, GEN x, GEN y) { (void)E; return -gcmp(x,y); }

static GEN
doellR_roots(GEN e, long prec0)
{
  GEN R, d1, d2, d3, e1, e2, e3;
  long s = ellR_get_sign(e), prec = prec0;
START:
  R = roots(ec_bmodel(e), prec);
  if (s > 0)
  { /* sort 3 real roots in decreasing order */
    R = real_i(R);
    gen_sort_inplace(R, NULL, &invcmp, NULL);
    e1 = gel(R,1);
    e2 = gel(R,2);
    e3 = gel(R,3);
    d3 = subrr(e1,e2);
    d1 = subrr(e2,e3);
    d2 = subrr(e1,e3);
    if (realprec(d3) < prec0 || realprec(d1) < prec0)
    {
      prec = precdbl(prec);
      if (DEBUGLEVEL) pari_warn(warnprec,"doellR_roots", prec);
      goto START;
    }
  } else {
    e1 = gel(R,1);
    e2 = gel(R,2);
    e3 = gel(R,3);
    if (s < 0)
    { /* make sure e1 is real, imag(e2) > 0 and imag(e3) < 0 */
      e1 = real_i(e1);
      if (signe(gel(e2,2)) < 0) swap(e2, e3);
    }
    d3 = gsub(e1,e2);
    d1 = gsub(e2,e3);
    d2 = gsub(e1,e3);
  }
  return mkcol6(e1,e2,e3,d1,d2,d3);
}
static GEN
ellR_root(GEN e, long prec) { return gel(ellR_roots(e,prec),1); }

/* Given E and the x-coordinate of a point Q = [xQ, yQ], return
 *   f(xQ) = xQ^3 + E.a2 * xQ^2 + E.a4 * xQ + E.a6
 * where E is given by y^2 + h(x)y = f(x). */
GEN
ec_f_evalx(GEN E, GEN x)
{
  pari_sp av = avma;
  GEN z;
  z = gadd(ell_get_a2(E),x);
  z = gadd(ell_get_a4(E), gmul(x,z));
  z = gadd(ell_get_a6(E), gmul(x,z));
  return gerepileupto(av, z); /* ((x + E.a2) * x + E.a4) * x + E.a6 */
}

/* a1 x + a3 */
GEN
ec_h_evalx(GEN e, GEN x)
{
  GEN a1 = ell_get_a1(e);
  GEN a3 = ell_get_a3(e);
  return gadd(a3, gmul(x,a1));
}
static GEN
Zec_h_evalx(GEN e, GEN x)
{
  GEN a1 = ell_get_a1(e);
  GEN a3 = ell_get_a3(e);
  return signe(a1)? addii(a3, mulii(x, a1)): a3;
}
/* y^2 + a1 xy + a3 y = y^2 + h(x)y */
static GEN
ec_LHS_evalQ(GEN e, GEN Q)
{
  GEN x = gel(Q,1), y = gel(Q,2);
  return gmul(y, gadd(y, ec_h_evalx(e,x)));
}

/* Given E and a point Q = [xQ, yQ], return
 *   3 * xQ^2 + 2 * E.a2 * xQ + E.a4 - E.a1 * yQ.
 * which is the derivative of the curve equation
 *   f(x) - (y^2 + h(x)y) = 0
 * wrt x evaluated at Q */
GEN
ec_dFdx_evalQ(GEN E, GEN Q)
{
  pari_sp av = avma;
  GEN x = gel(Q,1), y = gel(Q,2);
  GEN a1 = ell_get_a1(E);
  GEN a2 = ell_get_a2(E);
  GEN a4 = ell_get_a4(E);
  GEN tmp = gmul(gadd(gmulsg(3L,x), gmul2n(a2,1)), x);
  return gerepileupto(av, gadd(tmp, gsub(a4, gmul(a1, y))));
}

/* 2y + a1 x + a3 = -ec_dFdy_evalQ */
GEN
ec_dmFdy_evalQ(GEN e, GEN Q)
{
  GEN x = gel(Q,1), y = gel(Q,2);
  return gadd(ec_h_evalx(e,x), gmul2n(y,1));
}
/* Given E and a point Q = [xQ, yQ], return
 *  -(2 * yQ + E.a1 * xQ + E.a3)
 * which is the derivative of the curve equation
 *  f(x) - (y^2 + h(x)y) = 0
 * wrt y evaluated at Q */
GEN
ec_dFdy_evalQ(GEN E, GEN Q)
{
  pari_sp av = avma;
  return gerepileupto(av, gneg(ec_dmFdy_evalQ(E,Q)));
}

/* Given E and a point Q = [xQ, yQ], return
 *   4 xQ^3 + E.b2 xQ^2 + 2 E.b4 xQ + E.b6
 * which is the 2-division polynomial of E evaluated at Q */
GEN
ec_2divpol_evalx(GEN E, GEN x)
{
  pari_sp av = avma;
  GEN b2 = ell_get_b2(E);
  GEN b4 = ell_get_b4(E);
  GEN b6 = ell_get_b6(E);
  GEN t1 = gmul(gadd(gmulsg(4L, x), b2), x);
  GEN t2 = gadd(t1, gmulsg(2L, b4));
  return gerepileupto(av, gadd(gmul(t2, x), b6));
}

/* Given E and a point Q = [xQ, yQ], return
 *   6 xQ^2 + E.b2 xQ + E.b4
 * which, if f is the curve equation, is 2 dfdx - E.a1 dfdy evaluated at Q */
GEN
ec_half_deriv_2divpol_evalx(GEN E, GEN x)
{
  pari_sp av = avma;
  GEN b2 = ell_get_b2(E);
  GEN b4 = ell_get_b4(E);
  GEN res = gadd(gmul(gadd(gmulsg(6L, x), b2), x), b4);
  return gerepileupto(av, res);
}

/* Return the characteristic of the ring over which E is defined. */
GEN
ellbasechar(GEN E)
{
  pari_sp av = avma;
  GEN D = ell_get_disc(E);
  return gerepileuptoint(av, characteristic(D));
}

/* return basic elliptic struct y[1..13], y[14] (domain type) and y[15]
 * (domain-specific data) are left uninitialized, from x[1], ..., x[5].
 * Also allocate room for n dynamic members (actually stored in the last
 * component y[16])*/
static GEN
initsmall(GEN x, long n)
{
  GEN a1,a2,a3,a4,a6, b2,b4,b6,b8, c4,c6, D, j;
  GEN y = obj_init(15, n);
  switch(lg(x))
  {
    case 1:
    case 2:
    case 4:
    case 5:
      pari_err_TYPE("ellxxx [not an elliptic curve (ell5)]",x);
      return NULL; break; /* not reached */
    case 3:
      a1 = a2 = a3 = gen_0;
      a4 = gel(x,1);
      a6 = gel(x,2);
      b2 = gen_0;
      b4 = gmul2n(a4,1);
      b6 = gmul2n(a6,2);
      b8 = gneg(gsqr(a4));
      c4 = gmulgs(a4,-48);
      c6 = gmulgs(a6,-864);
      D = gadd(gmul(gmulgs(a4,-64), gsqr(a4)), gmulsg(-432,gsqr(a6)));
      break;
    default: /* l > 5 */
    { GEN a11, a13, a33, b22;
      a1 = gel(x,1);
      a2 = gel(x,2);
      a3 = gel(x,3);
      a4 = gel(x,4);
      a6 = gel(x,5);
      a11= gsqr(a1);
      b2 = gadd(a11, gmul2n(a2,2));
      a13= gmul(a1, a3);
      b4 = gadd(a13, gmul2n(a4,1));
      a33= gsqr(a3);
      b6 = gadd(a33, gmul2n(a6,2));
      b8 = gsub(gadd(gmul(a11,a6), gmul(b6, a2)), gmul(a4, gadd(a4,a13)));
      b22= gsqr(b2);
      c4 = gadd(b22, gmulsg(-24,b4));
      c6 = gadd(gmul(b2,gsub(gmulsg(36,b4),b22)), gmulsg(-216,b6));
      D  = gsub(gmul(b4, gadd(gmulsg(9,gmul(b2,b6)),gmulsg(-8,gsqr(b4)))),
                gadd(gmul(b22,b8),gmulsg(27,gsqr(b6))));
      break;
    }
  }
  gel(y,1) = a1;
  gel(y,2) = a2;
  gel(y,3) = a3;
  gel(y,4) = a4;
  gel(y,5) = a6;
  gel(y,6) = b2; /* a1^2 + 4a2 */
  gel(y,7) = b4; /* a1 a3 + 2a4 */
  gel(y,8) = b6; /* a3^2 + 4 a6 */
  gel(y,9) = b8; /* a1^2 a6 + 4a6 a2 + a2 a3^2 - a4(a4 + a1 a3) */
  gel(y,10)= c4; /* b2^2 - 24 b4 */
  gel(y,11)= c6; /* 36 b2 b4 - b2^3 - 216 b6 */
  gel(y,12)= D;
  if (gequal0(D)) { gel(y, 13) = gen_0; return NULL; }

  if (typ(D) == t_POL && typ(c4) == t_POL && varn(D) == varn(c4))
  { /* c4^3 / D, simplifying incrementally */
    GEN g = RgX_gcd(D, c4);
    if (degpol(g) == 0)
      j = gred_rfrac_simple(gmul(gsqr(c4),c4), D);
    else
    {
      GEN d, c = RgX_div(c4, g);
      D = RgX_div(D, g);
      g = RgX_gcd(D,c4);
      if (degpol(g) == 0)
        j = gred_rfrac_simple(gmul(gsqr(c4),c), D);
      else
      {
        D = RgX_div(D, g);
        d = RgX_div(c4, g);
        g = RgX_gcd(D,c4);
        if (degpol(g))
        {
          D = RgX_div(D, g);
          c4 = RgX_div(c4, g);
        }
        j = gred_rfrac_simple(gmul(gmul(c4, d),c), D);
      }
    }
  }
  else
    j = gdiv(gmul(gsqr(c4),c4), D);
  gel(y,13) = j;
  gel(y,16) = zerovec(n); return y;
}

void
ellprint(GEN e)
{
  pari_sp av = avma;
  long vx, vy;
  GEN z;
  checkell5(e);
  vx = fetch_var(); name_var(vx, "X");
  vy = fetch_var(); name_var(vy, "Y"); z = mkvec2(pol_x(vx), pol_x(vy));
  err_printf("%Ps - (%Ps)\n", ec_LHS_evalQ(e, z), ec_f_evalx(e, pol_x(vx)));
  (void)delete_var();
  (void)delete_var(); avma = av;
}

/* compute a,b such that E1: y^2 = x(x-a)(x-b) ~ E */
static GEN
doellR_ab(GEN E, long prec)
{
  GEN b2 = ell_get_b2(E), R = ellR_roots(E, prec);
  GEN e1 = gel(R,1), d2 = gel(R,5), d3 =  gel(R,6), a, b, t;

  t = gmul2n(gadd(mulur(12,e1), b2), -4); /* = (12 e1 + b2) / 16 */
  if (ellR_get_sign(E) > 0)
    b = mulrr(d3,d2);
  else
    b = cxnorm(d3);
  b = sqrtr(b); /* = sqrt( (e1 - e2)(e1 - e3) ) */
  if (gsigne(t) > 0) togglesign(b);
  a = gsub(gmul2n(b,-1),t);
  return mkvec2(a, b);
}
GEN
ellR_ab(GEN E, long prec)
{ return obj_checkbuild_realprec(E, R_AB, &doellR_ab, prec); }

/* return x mod p */
static GEN
padic_mod(GEN x) { return modii(gel(x,4), gel(x,2)); }

/* a1, b1 are t_PADICs, a1/b1 = 1 (mod p) if p odd, (mod 2^4) otherwise.
 * Return u^2 = 1 / 4M2(a1,b1), where M2(A,B) = B AGM(sqrt(A/B),1)^2; M2(A,B)
 * is the common limit of (A_n, B_n), A_0 = A, B _0 = B;
 *   A_{n+1} = (A_n + B_n + 2 B_{n+1}) / 4
 *   B_{n+1} = B_n sqrt(A_n / B_n) = the square root of A_n B_n congruent to B_n
 * Update (x,y) using p-adic Landen transform; if *pty = NULL, don't update y */
static GEN
do_padic_agm(GEN *ptx, GEN *pty, GEN a1, GEN b1)
{
  GEN bp = padic_mod(b1), x = *ptx;
  for(;;)
  {
    GEN p1, d, a = a1, b = b1;
    b1 = Qp_sqrt(gmul(a,b));
    if (!b1) pari_err_PREC("p-adic AGM");
    if (!equalii(padic_mod(b1), bp)) b1 = gneg_i(b1);
    a1 = gmul2n(gadd(gadd(a,b),gmul2n(b1,1)),-2);
    d = gsub(a1,b1);
    if (gequal0(d)) { *ptx = x; return ginv(gmul2n(a1,2)); }
    p1 = Qp_sqrt(gdiv(gadd(x,d),x)); /* = 1 (mod p) */
    /* x_{n+1} = x_n  ((1 + sqrt(1 + r_n/x_n)) / 2)^2 */
    x = gmul(x, gsqr(gmul2n(gaddsg(1,p1),-1)));
    /* y_{n+1} = y_n / (1 - (r_n/4x_{n+1})^2) */
    if (pty) *pty = gdiv(*pty, gsubsg(1, gsqr(gdiv(d,gmul2n(x,2)))));
  }
}

/* q a t_REAL*/
static long
real_prec(GEN q)
{ return signe(q)? realprec(q): LONG_MAX; }
/* q a t_PADIC */
static long
padic_prec(GEN q)
{ return signe(gel(q,4))? precp(q)+valp(q): valp(q); }

/* check whether moduli are consistent */
static void
chk_p(GEN p, GEN p2)
{ if (!equalii(p, p2)) pari_err_MODULUS("ellinit", p,p2); }

static int
fix_nftype(GEN *pp)
{
  switch(nftyp(*pp))
  {
    case typ_NF: case typ_BNF: break;
    case typ_BNR:*pp = bnr_get_bnf(*pp); break;
    default: return 0;
  }
  return 1;
}
static long
base_ring(GEN x, GEN *pp, long *prec)
{
  long i, e = *prec, imax = minss(lg(x), 6);
  GEN p = NULL;
  long t = t_FRAC;
  if (*pp) switch(t = typ(*pp))
  {
    case t_INT:
      if (cmpis(*pp,2) < 0) { t = t_FRAC; p = NULL; break; }
      p = *pp;
      t = t_INTMOD;
      break;
    case t_INTMOD:
      p = gel(*pp, 1);
      break;
    case t_REAL:
      e = real_prec(*pp);
      p = NULL;
      break;
    case t_PADIC:
      e = padic_prec(*pp);
      p = gel(*pp, 2);
      break;
    case t_FFELT:
      p = *pp;
      break;
    case t_VEC:
      t = t_VEC; p = *pp;
      if (fix_nftype(&p)) break;
    default:
      pari_err_TYPE("elliptic curve base_ring", *pp);
      return 0;
  }
  /* Possible cases:
   * t = t_VEC (p an nf or bnf)
   * t = t_FFELT (p t_FFELT)
   * t = t_INTMOD (p a prime)
   * t = t_PADIC (p a prime, e = padic prec)
   * t = t_REAL (p = NULL, e = real prec)
   * t = t_FRAC (p = NULL) */
  for (i = 1; i < imax; i++)
  {
    GEN p2, q = gel(x,i);
    switch(typ(q)) {
      case t_PADIC:
        p2 = gel(q,2);
        switch(t)
        {
          case t_FRAC:  t = t_PADIC; p = p2; break;
          case t_PADIC: chk_p(p,p2); break;
          default: pari_err_TYPE("elliptic curve base_ring", x);
        }
        e = minss(e, padic_prec(q));
        break;
      case t_INTMOD:
        p2 = gel(q,1);
        switch(t)
        {
          case t_FRAC:  t = t_INTMOD; p = p2; break;
          case t_FFELT: chk_p(FF_p_i(p),p2); break;
          case t_INTMOD:chk_p(p,p2); break;
          default: pari_err_TYPE("elliptic curve base_ring", x);
        }
        break;
      case t_FFELT:
        switch(t)
        {
          case t_INTMOD: chk_p(p, FF_p_i(q)); /* fall through */
          case t_FRAC:   t = t_FFELT; p = q; break;
          case t_FFELT:
            if (!FF_samefield(p,q)) pari_err_MODULUS("ellinit", p,q);
            break;
          default: pari_err_TYPE("elliptic curve base_ring", x);
        }
        break;

      case t_INT: case t_FRAC: break;
      case t_REAL:
        switch(t)
        {
          case t_REAL: e = minss(e, real_prec(q)); break;
          case t_FRAC: e = real_prec(q); t = t_REAL; break;
          default: pari_err_TYPE("elliptic curve base_ring", x);
        }
        break;
      case t_COL:
      case t_POL:
      case t_POLMOD:
        if (t == t_VEC) break;
      default: /* base ring too general */
        return t_COMPLEX;
    }
  }
  *pp = p; *prec = e; return t;
}

static GEN
ellinit_Rg(GEN x, int real, long prec)
{
  GEN y;
  long s;
  if (!(y = initsmall(x, 4))) return NULL;
  s = real? gsigne( ell_get_disc(y) ): 0;
  gel(y,14) = mkvecsmall(t_ELL_Rg);
  gel(y,15) = mkvec(mkvecsmall2(prec2nbits(prec), s));
  return y;
}

static GEN
ellinit_Qp(GEN x, GEN p, long prec)
{
  GEN y;
  if (lg(x) > 6) x = vecslice(x,1,5);
  x = QpV_to_QV(x); /* make entries rational */
  if (!(y = initsmall(x, 2))) return NULL;
  gel(y,14) = mkvecsmall(t_ELL_Qp);
  gel(y,15) = mkvec(zeropadic(p, prec));
  return y;
}

static GEN
ellinit_Q(GEN x, long prec)
{
  GEN y;
  long s;
  if (!(y = initsmall(x, 8))) return NULL;
  s = gsigne( ell_get_disc(y) );
  gel(y,14) = mkvecsmall(t_ELL_Q);
  gel(y,15) = mkvec(mkvecsmall2(prec2nbits(prec), s));
  return y;
}

/* shallow basistoalg */
static GEN
nftoalg(GEN nf, GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_FRAC: case t_POLMOD: return x;
    default: return basistoalg(nf, x);
  }
}
static GEN
nfVtoalg(GEN nf, GEN x)
{
  long i, l;
  GEN y = cgetg_copy(x,&l);
  for (i=1; i<l; i++) gel(y,i) = nftoalg(nf,gel(x,i));
  return y;
}

static GEN
ellinit_nf(GEN x, GEN p)
{
  GEN y;
  if (lg(x) > 6) x = vecslice(x,1,5);
  x = nfVtoalg(p, x);
  if (!(y = initsmall(x, 1))) return NULL;
  gel(y,14) = mkvecsmall(t_ELL_NF);
  gel(y,15) = mkvec(p);
  return y;
}

static GEN
ellinit_Fp(GEN x, GEN p)
{
  long i;
  GEN y, disc;
  if (!(y = initsmall(x, 4))) return NULL;
  if (cmpiu(p,3)<=0) /* ell_to_a4a6_bc does not handle p<=3 */
    return FF_ellinit(y,p_to_FF(p,0));
  disc = Rg_to_Fp(ell_get_disc(y),p);
  if (!signe(disc)) return NULL;
  for(i=1;i<=13;i++)
    gel(y,i) = Fp_to_mod(Rg_to_Fp(gel(y,i),p),p);
  gel(y,14) = mkvecsmall(t_ELL_Fp);
  gel(y,15) = mkvec2(p, ell_to_a4a6_bc(y, p));
  return y;
}

static GEN
ellinit_Fq(GEN x, GEN fg)
{
  GEN y;
  if (!(y = initsmall(x, 4))) return NULL;
  return FF_ellinit(y,fg);
}

static GEN
ellinit_nf_to_Fq(GEN x, GEN P)
{
  GEN nf = ellnf_get_nf(x), e = vecslice(x,1,5);
  GEN T,p, modP;
  if (get_modpr(P))
  { /* modpr accept */
    modP = P;
    p = modpr_get_p(modP);
  }
  else
  { /* pr, initialize modpr */
    GEN d = Q_denom(e);
    p = pr_get_p(P);
    modP = dvdii(d,p)? nfmodprinit(nf,P): zkmodprinit(nf,P);
  }
  T = modpr_get_T(modP);
  e = nfV_to_FqV(e, nf, modP);
  return T? ellinit_Fq(e,Tp_to_FF(T,p)): ellinit_Fp(e,p);
}
GEN
ellinit(GEN x, GEN D, long prec)
{
  pari_sp av = avma;
  GEN y;
  switch(typ(x))
  {
    case t_STR: x = gel(ellsearchcurve(x),2); break;
    case t_VEC:
      if (lg(x) > 6) checkell(x);
      break;
    default: pari_err_TYPE("ellxxx [not an elliptic curve (ell5)]",x);
  }
  if (D && get_prid(D))
  {
    if (ell_get_type(x) != t_ELL_NF) pari_err_TYPE("ellinit",x);
    y = ellinit_nf_to_Fq(x, D);
    goto END;
  }
  switch (base_ring(x, &D, &prec))
  {
  case t_PADIC:
    y = ellinit_Qp(x, D, prec);
    break;
  case t_INTMOD:
    y = ellinit_Fp(x, D);
    break;
  case t_FFELT:
    y = ellinit_Fq(x, D);
    break;
  case t_FRAC:
    y = ellinit_Q(x, prec);
    break;
  case t_REAL:
    y = ellinit_Rg(x, 1, prec);
    break;
  case t_VEC:
    y = ellinit_nf(x, D);
    break;
  default:
    y = ellinit_Rg(x, 0, prec);
  }
END:
  if (!y) { avma = av; return cgetg(1,t_VEC); }
  return gerepilecopy(av,y);
}

/********************************************************************/
/**                                                                **/
/**                     COORDINATE CHANGE                          **/
/**  Apply [u,r,s,t]. All coordch_* functions update E[1..14] only **/
/**  and copy E[15] (type-specific data), E[16] (dynamic data)     **/
/**  verbatim                                                      **/
/**                                                                **/
/********************************************************************/
/* [1,0,0,0] */
static GEN
init_ch(void) { return mkvec4(gen_1,gen_0,gen_0,gen_0); }
static int
is_trivial_change(GEN v)
{
  GEN u, r, s, t;
  if (typ(v) == t_INT) return 1;
  u = gel(v,1); r = gel(v,2); s = gel(v,3); t = gel(v,4);
  return isint1(u) && isintzero(r) && isintzero(s) && isintzero(t);
}

/* compose coordinate changes, *vtotal = v is a ZV */
/* v = [u,0,0,0] o v, u t_INT */
static void
composev_u(GEN *vtotal, GEN u)
{
  GEN v = *vtotal;
  if (typ(v) == t_INT)
    *vtotal = mkvec4(u,gen_0,gen_0,gen_0);
  else if (!equali1(u))
  {
    GEN U = gel(v,1);
    GEN uU = equali1(U)? u: mulii(u, U);
    gel(v,1) = uU;
  }
}
/* v = [1,r,0,0] o v, r t_INT */
static void
composev_r(GEN *vtotal, GEN r)
{
  GEN v = *vtotal;
  if (typ(v) == t_INT)
    *vtotal = mkvec4(gen_1,r,gen_0,gen_0);
  else if (signe(r))
  {
    GEN U = gel(v,1), R = gel(v,2), S = gel(v,3), T = gel(v,4);
    GEN rU2 = equali1(U)? r: mulii(r, sqri(U));
    gel(v,2) = addii(R, rU2);
    gel(v,4) = addii(T, mulii(rU2, S));
  }
}
/* v = [1,0,s,0] o v, s t_INT */
static void
composev_s(GEN *vtotal, GEN s)
{
  GEN v = *vtotal;
  if (typ(v) == t_INT)
    *vtotal = mkvec4(gen_1,gen_0,s,gen_0);
  else if (signe(s))
  {
    GEN U = gel(v,1), S = gel(v,3);
    GEN sU = equali1(U)? s: mulii(s,U);
    gel(v,3) = addii(S, sU);
  }
}
/* v = [1,0,0,t] o v, t t_INT */
static void
composev_t(GEN *vtotal, GEN t)
{
  GEN v = *vtotal;
  if (typ(v) == t_INT)
    *vtotal = mkvec4(gen_1,gen_0,gen_0,t);
  else if (signe(t))
  {
    GEN U = gel(v,1), T = gel(v,4);
    GEN tU3 = equali1(U)? t: mulii(t, powiu(U,3));
    gel(v,4) = addii(T, tU3);
  }
}
/* v = [1,0,s,t] o v, s,t t_INT */
static void
composev_st(GEN *vtotal, GEN s, GEN t)
{
  GEN v = *vtotal;
  if (typ(v) == t_INT)
    *vtotal = mkvec4(gen_1,gen_0,s,t);
  else if (!signe(t)) composev_s(vtotal, s);
  else if (!signe(s)) composev_t(vtotal, t);
  else
  {
    GEN U = gel(v,1), S = gel(v,3), T = gel(v,4);
    if (!equali1(U))
    {
      GEN U3 = mulii(sqri(U), U);
      t = mulii(U3, t);
      s = mulii(U, s);
    }
    gel(v,3) = addii(S, s);
    gel(v,4) = addii(T, t);
  }
}
/* v = [1,r,s,t] o v, r,s,t t_INT */
static void
composev_rst(GEN *vtotal, GEN r, GEN s, GEN t)
{
  GEN v = *vtotal, U, R, S, T;
  if (typ(v) == t_INT) { *vtotal = mkvec4(gen_1,r,s,t); return; }
  if (!signe(r)) { composev_st(vtotal, s,t); return; }
  v = *vtotal;
  U = gel(v,1); R = gel(v,2); S = gel(v,3); T = gel(v,4);
  if (equali1(U))
    t = addii(t, mulii(S, r));
  else
  {
    GEN U2 = sqri(U);
    t = mulii(U2, addii(mulii(U, t), mulii(S, r)));
    r = mulii(U2, r);
    s = mulii(U, s);
  }
  gel(v,2) = addii(R, r);
  gel(v,3) = addii(S, s);
  gel(v,4) = addii(T, t);
}

/* Accumulate the effects of variable changes w o v, where
 * w = [u,r,s,t], *vtotal = v = [U,R,S,T]. No assumption on types */
static void
gcomposev(GEN *vtotal, GEN w)
{
  GEN v = *vtotal;
  GEN U2, U, R, S, T, u, r, s, t;

  if (typ(v) == t_INT) { *vtotal = w; return; }
  U = gel(v,1); R = gel(v,2); S = gel(v,3); T = gel(v,4);
  u = gel(w,1); r = gel(w,2); s = gel(w,3); t = gel(w,4);
  U2 = gsqr(U);
  gel(v,1) = gmul(U, u);
  gel(v,2) = gadd(R, gmul(U2, r));
  gel(v,3) = gadd(S, gmul(U, s));
  gel(v,4) = gadd(T, gmul(U2, gadd(gmul(U, t), gmul(S, r))));
}

/* [u,r,s,t]^-1 = [ 1/u,-r/u^2,-s/u, (rs-t)/u^3 ] */
GEN
ellchangeinvert(GEN w)
{
  GEN u,r,s,t, u2,u3, U,R,S,T;
  if (typ(w) == t_INT) return w;
  u = gel(w,1);
  r = gel(w,2);
  s = gel(w,3);
  t = gel(w,4);
  u2 = gsqr(u); u3 = gmul(u2,u);
  U = ginv(u);
  R = gdiv(gneg(r), u2);
  S = gdiv(gneg(s), u);
  T = gdiv(gsub(gmul(r,s), t), u3);
  return mkvec4(U,R,S,T);
}

/* apply [u,0,0,0] */
static GEN
coordch_u(GEN e, GEN u)
{
  GEN y, u2, u3, u4, u6;
  long lx;
  if (gequal1(u)) return e;
  y = cgetg_copy(e, &lx);
  u2 = gsqr(u); u3 = gmul(u,u2); u4 = gsqr(u2); u6 = gsqr(u3);
  gel(y,1) = gdiv(ell_get_a1(e),  u);
  gel(y,2) = gdiv(ell_get_a2(e), u2);
  gel(y,3) = gdiv(ell_get_a3(e), u3);
  gel(y,4) = gdiv(ell_get_a4(e), u4);
  gel(y,5) = gdiv(ell_get_a6(e), u6);
  if (lx == 6) return y;
  gel(y,6) = gdiv(ell_get_b2(e), u2);
  gel(y,7) = gdiv(ell_get_b4(e), u4);
  gel(y,8) = gdiv(ell_get_b6(e), u6);
  gel(y,9) = gdiv(ell_get_b8(e), gsqr(u4));
  gel(y,10)= gdiv(ell_get_c4(e), u4);
  gel(y,11)= gdiv(ell_get_c6(e), u6);
  gel(y,12)= gdiv(ell_get_disc(e), gsqr(u6));
  gel(y,13)= ell_get_j(e);
  gel(y,14)= gel(e,14);
  gel(y,15)= gel(e,15);
  gel(y,16)= gel(e,16);
  return y;
}
/* apply [1,r,0,0] */
static GEN
coordch_r(GEN e, GEN r)
{
  GEN a2, b4, b6, y, p1, r2, b2r, rx3;
  if (gequal0(r)) return e;
  y = leafcopy(e);
  a2 = ell_get_a2(e);
  rx3 = gmulsg(3,r);

  /* A2 = a2 + 3r */
  gel(y,2) = gadd(a2,rx3);
  /* A3 = a1 r + a3 */
  gel(y,3) = ec_h_evalx(e,r);
  /* A4 = 3r^2 + 2a2 r + a4 */
  gel(y,4) = gadd(ell_get_a4(e), gmul(r,gadd(gmul2n(a2,1),rx3)));
  /* A6 = r^3 + a2 r^2 + a4 r + a6 */
  gel(y,5) = ec_f_evalx(e,r);
  if (lg(y) == 6) return y;

  b4 = ell_get_b4(e);
  b6 = ell_get_b6(e);
  /* B2 = 12r + b2 */
  gel(y,6) = gadd(ell_get_b2(e),gmul2n(rx3,2));
  b2r = gmul(r, ell_get_b2(e));
  r2 = gsqr(r);
  /* B4 = 6r^2 + b2 r + b4 */
  gel(y,7) = gadd(b4,gadd(b2r, gmulsg(6,r2)));
  /* B6 = 4r^3 + 2b2 r^2 + 2b4 r + b6 */
  gel(y,8) = gadd(b6,gmul(r,gadd(gmul2n(b4,1), gadd(b2r,gmul2n(r2,2)))));
  /* B8 = 3r^4 + b2 r^3 + 3b4 r^2 + 3b6 r + b8 */
  p1 = gadd(gmulsg(3,b4),gadd(b2r, gmulsg(3,r2)));
  gel(y,9) = gadd(ell_get_b8(e), gmul(r,gadd(gmulsg(3,b6), gmul(r,p1))));
  return y;
}
/* apply [1,0,s,0] */
static GEN
coordch_s(GEN e, GEN s)
{
  GEN a1, y;
  if (gequal0(s)) return e;
  a1 = ell_get_a1(e);
  y = leafcopy(e);

  /* A1 = a1 + 2s */
  gel(y,1) = gadd(a1,gmul2n(s,1));
  /* A2 = a2 - (a1 s + s^2) */
  gel(y,2) = gsub(ell_get_a2(e),gmul(s,gadd(a1,s)));
  /* A4 = a4 - s a3 */
  gel(y,4) = gsub(ell_get_a4(e),gmul(s,ell_get_a3(e)));
  return y;
}
/* apply [1,0,0,t] */
static GEN
coordch_t(GEN e, GEN t)
{
  GEN a1, a3, y;
  if (gequal0(t)) return e;
  a1 = ell_get_a1(e); a3 = ell_get_a3(e);
  y = leafcopy(e);
  /* A3 = 2t + a3 */
  gel(y,3) = gadd(a3, gmul2n(t,1));
  /* A4 = a4 - a1 t */
  gel(y,4) = gsub(ell_get_a4(e), gmul(t,a1));
  /* A6 = a6 - t(t + a3) */
  gel(y,5) = gsub(ell_get_a6(e), gmul(t,gadd(t, a3)));
  return y;
}
/* apply [1,0,s,t] */
static GEN
coordch_st(GEN e, GEN s, GEN t)
{
  GEN y, a1, a3;
  if (gequal0(s)) return coordch_t(e, t);
  if (gequal0(t)) return coordch_s(e, s);
  a1 = ell_get_a1(e); a3 = ell_get_a3(e);
  y = leafcopy(e);
  /* A1 = a1 + 2s */
  gel(y,1) = gadd(a1,gmul2n(s,1));
  /* A2 = a2 - (a1 s + s^2) */
  gel(y,2) = gsub(ell_get_a2(e),gmul(s,gadd(a1,s)));
  /* A3 = 2t + a3 */
  gel(y,3) = gadd(a3,gmul2n(t,1));
  /* A4 = a4 - (a1 t + s (2t + a3)) */
  gel(y,4) = gsub(ell_get_a4(e),gadd(gmul(t,a1),gmul(s,gel(y,3))));
  /* A6 = a6 - t(t + a3) */
  gel(y,5) = gsub(ell_get_a6(e), gmul(t,gadd(t, a3)));
  return y;
}
/* apply [1,r,s,t] */
static GEN
coordch_rst(GEN e, GEN r, GEN s, GEN t)
{
  e = coordch_r(e, r);
  return coordch_st(e, s, t);
}
/* apply w = [u,r,s,t] */
static GEN
coordch(GEN e, GEN w)
{
  if (typ(w) == t_INT) return e;
  e = coordch_rst(e, gel(w,2), gel(w,3), gel(w,4));
  return coordch_u(e, gel(w,1));
}

/* the ch_* routines update E[14] (type), E[15] (type specific data), E[16]
 * (dynamic data) */
static GEN
ch_Qp(GEN E, GEN e, GEN w)
{
  GEN S, p = ellQp_get_zero(E), u2 = NULL, u = gel(w,1), r = gel(w,2);
  long prec = valp(p);
  if (base_ring(E, &p, &prec) != t_PADIC) return ellinit(E, p, prec);
  if ((S = obj_check(e, Qp_ROOT)))
  {
    if (!u2) u2 = gsqr(u);
    obj_insert_shallow(E, Qp_ROOT, gdiv(gsub(S, r), u2));
  }
  if ((S = obj_check(e, Qp_TATE)))
  {
    GEN U2 = gel(S,1), U = gel(S,2), Q = gel(S,3), AB = gel(S,4);
    if (!u2) u2 = gsqr(u);
    U2 = gmul(U2, u2);
    U = gmul(U, u);
    AB = gdiv(AB, u2);
    obj_insert_shallow(E, Qp_TATE, mkvec4(U2,U,Q,AB));
  }
  return E;
}

/* common to Q and Rg */
static GEN
ch_R(GEN E, GEN e, GEN w)
{
  GEN S, u = gel(w,1), r = gel(w,2);
  if ((S = obj_check(e, R_PERIODS)))
    obj_insert(E, R_PERIODS, gmul(S, u));
  if ((S = obj_check(e, R_ETA)))
    obj_insert(E, R_ETA, gmul(S, u));
  if ((S = obj_check(e, R_ROOTS)))
  {
    GEN ro = cgetg(4, t_VEC), u2 = gsqr(u);
    long i;
    for (i = 1; i <= 3; i++) gel(ro,i) = gdiv(gsub(gel(S,i), r), u2);
    obj_insert(E, R_ROOTS, ro);
  }
  return E;
}

static GEN
ch_Rg(GEN E, GEN e, GEN w)
{
  GEN p = NULL;
  long prec = ellR_get_prec(E);
  if (base_ring(E, &p, &prec) != t_REAL) return ellinit(E, p, prec);
  ch_R(E, e, w); return E;
}

static GEN
ch_Q(GEN E, GEN e, GEN w)
{
  long prec = ellR_get_prec(E);
  GEN S, v = NULL, p = NULL;
  if (base_ring(E, &p, &prec) != t_FRAC) return ellinit(E, p, prec);
  ch_R(E, e, w);
  if ((S = obj_check(e, Q_GROUPGEN)))
    S = obj_insert_shallow(E, Q_GROUPGEN, ellchangepoint(S, w));
  if ((S = obj_check(e, Q_MINIMALMODEL)))
  {
    if (lg(S) == 2)
    { /* model was minimal */
      if (!is_trivial_change(w)) /* no longer minimal */
        S = mkvec3(gel(S,1), ellchangeinvert(w), e);
      (void)obj_insert_shallow(E, Q_MINIMALMODEL, S);
    }
    else
    {
      v = gel(S,2);
      if (gequal(v, w) || (is_trivial_change(v) && is_trivial_change(w)))
        S = mkvec(gel(S,1)); /* now minimal */
      else
      {
        w = ellchangeinvert(w);
        gcomposev(&w, v); v = w;
        S = leafcopy(S); /* don't modify S in place: would corrupt e */
        gel(S,2) = v;
      }
      (void)obj_insert_shallow(E, Q_MINIMALMODEL, S);
    }
  }
  if ((S = obj_check(e, Q_GLOBALRED)))
    S = obj_insert_shallow(E, Q_GLOBALRED, S);
  if ((S = obj_check(e, Q_ROOTNO)))
    S = obj_insert_shallow(E, Q_ROOTNO, S);
  return E;
}

static void
ch_FF(GEN E, GEN e, GEN w)
{
  GEN S;
  if ((S = obj_check(e, FF_CARD)))
    S = obj_insert_shallow(E, FF_CARD, S);
  if ((S = obj_check(e, FF_GROUP)))
    S = obj_insert_shallow(E, FF_GROUP, S);
  if ((S = obj_check(e, FF_GROUPGEN)))
    S = obj_insert_shallow(E, FF_GROUPGEN, ellchangepoint(S, w));
  if ((S = obj_check(e, FF_O)))
    S = obj_insert_shallow(E, FF_O, S);
}

/* FF_CARD, FF_GROUP, FF_O are invariant */
static GEN
ch_Fp(GEN E, GEN e, GEN w)
{
  long prec = 0;
  GEN p = ellff_get_field(E);
  if (base_ring(E, &p, &prec) != t_INTMOD) return ellinit(E, p, prec);
  gel(E,15) = mkvec2(p, ell_to_a4a6_bc(E, p));
  ch_FF(E, e, w); return E;
}
static GEN
ch_Fq(GEN E, GEN e, GEN w)
{
  long prec = 0;
  GEN p = ellff_get_field(E);
  if (base_ring(E, &p, &prec) != t_FFELT) return ellinit(E, p, prec);
  gel(E,15) = FF_elldata(E, p);
  ch_FF(E, e, w); return E;
}

static void
ell_reset(GEN E)
{ gel(E,16) = zerovec(lg(gel(E,16))-1); }

GEN
ellchangecurve(GEN e, GEN w)
{
  pari_sp av = avma;
  GEN E;
  checkell5(e);
  if (equali1(w)) return gcopy(e);
  checkcoordch(w);
  E = coordch(leafcopy(e), w);
  if (lg(E) != 6)
  {
    ell_reset(E);
    switch(ell_get_type(E))
    {
      case t_ELL_Qp: E = ch_Qp(E,e,w); break;
      case t_ELL_Fp: E = ch_Fp(E,e,w); break;
      case t_ELL_Fq: E = ch_Fq(E,e,w); break;
      case t_ELL_Q:  E = ch_Q(E,e,w);  break;
      case t_ELL_Rg: E = ch_Rg(E,e,w); break;
    }
  }
  return gerepilecopy(av, E);
}

static void
E_compose_u(GEN *vtotal, GEN *e, GEN u) {*e=coordch_u(*e,u); composev_u(vtotal,u);}
static void
E_compose_r(GEN *vtotal, GEN *e, GEN r) {*e=coordch_r(*e,r); composev_r(vtotal,r);}
#if 0
static void
E_compose_s(GEN *vtotal, GEN *e, GEN s) {*e=coordch_s(*e,s); composev_s(vtotal,s);}
#endif
static void
E_compose_t(GEN *vtotal, GEN *e, GEN t) {*e=coordch_t(*e,t); composev_t(vtotal,t);}
static void
E_compose_rst(GEN *vtotal, GEN *e, GEN r, GEN s, GEN t)
{ *e=coordch_rst(*e,r,s,t); composev_rst(vtotal,r,s,t); }

/* X = (x-r)/u^2
 * Y = (y - s(x-r) - t) / u^3 */
static GEN
ellchangepoint0(GEN P, GEN v2, GEN v3, GEN r, GEN s, GEN t)
{
  GEN a, x, y;
  if (ell_is_inf(P)) return P;
  x = gel(P,1); y = gel(P,2); a = gsub(x,r);
  retmkvec2(gmul(v2, a), gmul(v3, gsub(y, gadd(gmul(s,a),t))));
}

GEN
ellchangepoint(GEN x, GEN ch)
{
  GEN y, v, v2, v3, r, s, t, u;
  long tx, i, lx = lg(x);
  pari_sp av = avma;

  if (typ(x) != t_VEC) pari_err_TYPE("ellchangepoint",x);
  if (equali1(ch)) return gcopy(x);
  checkcoordch(ch);
  if (lx == 1) return cgetg(1, t_VEC);
  u = gel(ch,1); r = gel(ch,2); s = gel(ch,3); t = gel(ch,4);
  v = ginv(u); v2 = gsqr(v); v3 = gmul(v,v2);
  tx = typ(gel(x,1));
  if (is_matvec_t(tx))
  {
    y = cgetg(lx,tx);
    for (i=1; i<lx; i++)
      gel(y,i) = ellchangepoint0(gel(x,i),v2,v3,r,s,t);
  }
  else
    y = ellchangepoint0(x,v2,v3,r,s,t);
  return gerepilecopy(av,y);
}

/* x = u^2*X + r
 * y = u^3*Y + s*u^2*X + t */
static GEN
ellchangepointinv0(GEN P, GEN u2, GEN u3, GEN r, GEN s, GEN t)
{
  GEN a, X, Y;
  if (ell_is_inf(P)) return P;
  X = gel(P,1); Y = gel(P,2); a = gmul(u2,X);
  return mkvec2(gadd(a, r), gadd(gmul(u3, Y), gadd(gmul(s, a), t)));
}
GEN
ellchangepointinv(GEN x, GEN ch)
{
  GEN y, u, r, s, t, u2, u3;
  long tx, i, lx = lg(x);
  pari_sp av = avma;

  if (typ(x) != t_VEC) pari_err_TYPE("ellchangepointinv",x);
  if (equali1(ch)) return gcopy(x);
  checkcoordch(ch);
  if (lx == 1) return cgetg(1, t_VEC);
  u = gel(ch,1); r = gel(ch,2); s = gel(ch,3); t = gel(ch,4);
  u2 = gsqr(u); u3 = gmul(u,u2);
  tx = typ(gel(x,1));
  if (is_matvec_t(tx))
  {
    y = cgetg(lx,tx);
    for (i=1; i<lx; i++)
      gel(y,i) = ellchangepointinv0(gel(x,i),u2,u3,r,s,t);
  }
  else
    y = ellchangepointinv0(x,u2,u3,r,s,t);
  return gerepilecopy(av,y);
}

GEN
elltwist(GEN E, GEN P)
{
  pari_sp av = avma;
  GEN a1, a2, a3, a4, a6;
  GEN a, b, c, ac, D, D2;
  GEN V;
  checkell(E);
  if (!P)
  {
    GEN a4, a6;
    checkell_Fq(E);
    switch (ell_get_type(E))
    {
      case t_ELL_Fp:
        {
          GEN p = ellff_get_field(E), e = ellff_get_a4a6(E);
          Fp_elltwist(gel(e,1), gel(e, 2), p, &a4, &a6);
          return gerepilecopy(av, FpV_to_mod(mkvec5(gen_0, gen_0, gen_0, a4, a6), p));
        }
      case t_ELL_Fq:
        return FF_elltwist(E);
    }
  }
  a1 = ell_get_a1(E); a2 = ell_get_a2(E); a3 = ell_get_a3(E);
  a4 = ell_get_a4(E); a6 = ell_get_a6(E);
  if (typ(P) == t_INT)
  {
    if (equali1(P))
      retmkvec5(gcopy(a1),gcopy(a2),gcopy(a3),gcopy(a4),gcopy(a6));
    P = quadpoly(P);
  } else
  {
    if (typ(P) != t_POL) pari_err_TYPE("elltwist",P);
    if (degpol(P) != 2 )
      pari_err_DOMAIN("elltwist", "degree(P)", "!=", gen_2, P);
  }
  a = gel(P, 4); b = gel(P, 3); c = gel(P, 2);
  ac = gmul(a, c);
  D = gsub(gsqr(b), gmulsg(4, ac));
  D2 = gsqr(D);
  V = cgetg(6, t_VEC);
  gel(V, 1) =  gmul(a1, b);
  gel(V, 2) =  gsub(gmul(a2, D), gmul(gsqr(a1), ac));
  gel(V, 3) =  gmul(gmul(a3, b), D);
  gel(V, 4) =  gsub(gmul(a4, D2), gmul(gmul(gmul(gmulsg(2, a3), a1), ac), D));
  gel(V, 5) =  gsub(gmul(a6, gmul(D, D2)), gmul(gmul(gsqr(a3), ac), D2));
  return gerepilecopy(av, V);
}

static ulong
smod2BIL(GEN x)
{
  long s = signe(x);
  return s==0 ? 0: s==1 ? *int_LSW(x) : -*int_LSW(x);
}

static long
safe_Z_pval(GEN n, GEN p)
{
  return signe(n)==0? -1: Z_pval(n, p);
}

/* Return D such that E_D has minimal discriminant.
   It also has minimal conductor in Z[1/2]
Reference:
Ian Connell, Elliptic Curve Handbook,
http://www.math.mcgill.ca/connell/
*/
GEN
ellminimaltwist(GEN e)
{
  pari_sp av = avma;
  GEN c4, c6, disc;
  GEN D = gen_1;
  GEN N, M, F, E;
  long i, lF;
  E = ellminimalmodel(e, NULL);
  c4 = ell_get_c4(E);
  c6 = ell_get_c6(E);
  disc = ell_get_disc(E);
  ellQ_get_Nfa(E, &N, &M);
  obj_free(E);
  F = gel(M, 1); lF = lg(F);
  for(i=1; i < lF; i++)
  {
    GEN p = gel(F, i);
    long v4 = safe_Z_pval(c4, p), v6 = safe_Z_pval(c6,p), vD = Z_pval(disc,p);
    long l = v4<0 ? minss(2*v6, vD): v6<0 ? minss(3*v4, vD): minss(minss(3*v4, 2*v6), vD);
    if (cmpiu(p, 3)>0)
    {
      if (l>=6) D = mulii(D,mod4(p)==1 ? p: negi(p));
    }
    else if (equaliu(p, 3))
    {
      if (l>=6 && v6!=5) D = mulis(D,-3);
    }
    else /* p == 2*/
    {
      if ((v4==4 && v6==6 && vD>=12) || ((v4<0 || v4>=8) && v6==9 && vD==12))
        D = mulis(D,-4);
      else if (v4==6 && v6==9 && vD>=18)
        D = mulis(D, ((smod2BIL(c6)>>9)&3UL) == 1 ? -8: 8);
      else if ((v4<0 || v4>=6) && v6==6 && vD==6)
        D = mulis(D, ((smod2BIL(c6)>>6)&3UL) == 1 ? 8: -8);
      else
        if (!(v4==4 || v4==5 || v6==3 || v6==5 || v6==7 || (v4==0 && v6==0)))
          D = mulis(D, -8);
    }
  }
  return gerepileuptoleaf(av, D);
}

/*
Reference:
William A. Stein and Mark Watkins
A Database of Elliptic Curves-First Report
ANTS 5
<http://modular.math.washington.edu/papers/stein-watkins/ants.pdf>
*/
GEN
ellminimaltwistcond(GEN e)
{
  pari_sp av = avma;
  GEN D = ellminimaltwist(e);
  GEN eD = ellinit(elltwist(e, D), NULL, DEFAULTPREC);
  GEN E = ellminimalmodel(eD, NULL);
  GEN R = elllocalred(E, gen_2);
  long f = itos(gel(R,1)), v = vali(D);
  obj_free(eD); obj_free(E);
  if (f==4) D = negi(v==3 ? D: shifti(D, v==0? 2: -2));
  else if (f==6)
  {
    if (v < 3) D = shifti(D, v==0? 3: 1);
    else
    {
      long si = (mod32(D)>>3)==1? 1: -1;
      D = shifti(D, signe(D)==si ? -3: -1);
    }
  }
  return gerepileuptoleaf(av, D);
}

GEN
ellminimaltwist0(GEN e, long flag)
{
  switch(flag)
  {
    case 0:
      return ellminimaltwist(e);
    case 1:
      return ellminimaltwistcond(e);
  }
  pari_err_FLAG("ellminimaltwist");
  return NULL; /* NOT REACHED */
}

static long
ellexpo(GEN E)
{
  long i, f, e = -(long)HIGHEXPOBIT;
  for (i=1; i<=5; i++)
  {
    f = gexpo(gel(E,i));
    if (f > e) e = f;
  }
  return e;
}

/* Exactness of lhs and rhs in the following depends in non-obvious ways
 * on the coeffs of the curve as well as on the components of the point z.
 * Thus if e is exact, with a1==0, and z has exact y coordinate only, the
 * lhs will be exact but the rhs won't. */
int
oncurve(GEN e, GEN z)
{
  GEN LHS, RHS, x;
  long pl, pr, ex, expx;
  pari_sp av;

  checkellpt(z); if (ell_is_inf(z)) return 1; /* oo */
  if (ell_get_type(e) == t_ELL_NF) z = nfVtoalg(ellnf_get_nf(e), z);
  av = avma;
  LHS = ec_LHS_evalQ(e,z);
  RHS = ec_f_evalx(e,gel(z,1)); x = gsub(LHS,RHS);
  if (gequal0(x)) { avma = av; return 1; }
  pl = precision(LHS);
  pr = precision(RHS);
  if (!pl && !pr) { avma = av; return 0; } /* both of LHS, RHS are exact */
  /* at least one of LHS,RHS is inexact */
  ex = pr? gexpo(RHS): gexpo(LHS); /* don't take exponent of exact 0 */
  if (!pr || (pl && pl < pr)) pr = pl; /* min among nonzero elts of {pl,pr} */
  expx = gexpo(x);
  pr = (expx < ex - prec2nbits(pr) + 15
     || expx < ellexpo(e) - prec2nbits(pr) + 5);
  avma = av; return pr;
}

GEN
ellisoncurve(GEN e, GEN x)
{
  long i, tx = typ(x), lx;

  checkell(e);
  if (!is_vec_t(tx)) pari_err_TYPE("ellisoncurve [point]", x);
  lx = lg(x); if (lx==1) return cgetg(1,tx);
  tx = typ(gel(x,1));
  if (is_vec_t(tx))
  {
    GEN z = cgetg(lx,tx);
    for (i=1; i<lx; i++) gel(z,i) = ellisoncurve(e,gel(x,i));
    return z;
  }
  return oncurve(e, x)? gen_1: gen_0;
}

/* y1 = y2 or -LHS0-y2 */
static GEN
slope_samex(GEN e, GEN x, GEN y1, GEN y2)
{
  GEN dy,dx;
  if (y1 != y2)
  {
    int eq;
    if (precision(y1) || precision(y2))
      eq = (gexpo(gadd(ec_h_evalx(e,x),gadd(y1,y2))) >= gexpo(y1));
    else
      eq = gequal(y1,y2);
    if (!eq) return NULL;
  }
  dx = ec_dmFdy_evalQ(e,mkvec2(x,y1));
  if (gequal0(dx)) return NULL;
  dy = gadd(gsub(ell_get_a4(e),gmul(ell_get_a1(e),y1)),
            gmul(x,gadd(gmul2n(ell_get_a2(e),1),gmulsg(3,x))));
  return gdiv(dy,dx);
}
static GEN
get_slope(GEN e, GEN x1, GEN x2, GEN y1, GEN y2)
{
  GEN dy,dx;
  if (x1 == x2 || gequal(x1,x2))
    return slope_samex(e, x1, y1, y2);
  dx = gsub(x2,x1);
  if (typ(dx) == t_COMPLEX) /* its Norm may be 0 */
  {
    GEN N = gnorm(dx);
    if (gequal0(N)) return slope_samex(e,x1,y1,y2);
    dy = gsub(y2,y1);
    return gdiv(gmul(dy,gconj(dx)),N); /* dy/dx */
  }
  dy = gsub(y2,y1);
  return gdiv(dy,dx);
}

GEN
elladd(GEN e, GEN z1, GEN z2)
{
  GEN s, z, x, y, x1, x2, y1, y2;
  pari_sp av = avma;

  checkell(e); checkellpt(z1); checkellpt(z2);
  if (ell_is_inf(z1)) return gcopy(z2);
  if (ell_is_inf(z2)) return gcopy(z1);

  x1 = gel(z1,1); y1 = gel(z1,2);
  x2 = gel(z2,1); y2 = gel(z2,2);
  if (ell_get_type(e) == t_ELL_NF)
  {
    GEN nf = ellnf_get_nf(e);
    x1 = nftoalg(nf, x1);
    x2 = nftoalg(nf, x2);
    y1 = nftoalg(nf, y1);
    y2 = nftoalg(nf, y2);
  }
  s = get_slope(e,x1,x2,y1,y2);
  if (!s) { avma = av; return ellinf(); }
  x = gsub(gmul(s,gadd(s,ell_get_a1(e))), gadd(gadd(x1,x2),ell_get_a2(e)));
  y = gadd(gadd(y1, ec_h_evalx(e,x)), gmul(s,gsub(x,x1)));
  z = cgetg(3,t_VEC);
  gel(z,1) = gcopy(x);
  gel(z,2) = gneg(y); return gerepileupto(av, z);
}

static GEN
ellneg_i(GEN e, GEN z)
{
  GEN t, x, y;
  if (ell_is_inf(z)) return z;
  x = gel(z,1);
  y = gel(z,2);
  if (ell_get_type(e) == t_ELL_NF)
  {
    GEN nf = ellnf_get_nf(e);
    x = nftoalg(nf,x);
    y = nftoalg(nf,y);
  }
  t = cgetg(3,t_VEC);
  gel(t,1) = x;
  gel(t,2) = gneg_i(gadd(y, ec_h_evalx(e,x)));
  return t;
}

GEN
ellneg(GEN e, GEN z)
{
  pari_sp av;
  GEN t, y;
  checkell(e); checkellpt(z);
  if (ell_is_inf(z)) return z;
  t = cgetg(3,t_VEC);
  gel(t,1) = gcopy(gel(z,1));
  av = avma;
  y = gneg(gadd(gel(z,2), ec_h_evalx(e,gel(z,1))));
  gel(t,2) = gerepileupto(av, y);
  return t;
}

GEN
ellsub(GEN e, GEN z1, GEN z2)
{
  pari_sp av = avma;
  checkell(e); checkellpt(z2);
  return gerepileupto(av, elladd(e, z1, ellneg_i(e,z2)));
}

/* E an ell, x a scalar */
static GEN
ellordinate_i(GEN E, GEN x, long prec)
{
  pari_sp av = avma;
  GEN a, b, D, d, y, p, nf = NULL;

  if (ell_get_type(E) == t_ELL_NF)
  {
    nf = ellnf_get_nf(E);
    x = nftoalg(nf,x);
  }
  a = ec_f_evalx(E,x);
  b = ec_h_evalx(E,x);
  D = gadd(gsqr(b), gmul2n(a,2));
  /* solve y*(y+b) = a */
  if (gequal0(D)) {
    if (ell_get_type(E) == t_ELL_Fq && equaliu(ellff_get_p(E),2))
      retmkvec( FF_sqrt(a) );
    b = gneg_i(b); y = cgetg(2,t_VEC);
    gel(y,1) = gmul2n(b,-1);
    return gerepileupto(av,y);
  }
  /* D != 0 */
  switch(ell_get_type(E))
  {
    case t_ELL_Fp: /* imply p!=2 */
      p = ellff_get_p(E);
      D = gel(D,2);
      if (kronecker(D, p) < 0) { avma = av; return cgetg(1,t_VEC); }
      d = Fp_sqrt(D, p);
      break;
    case t_ELL_Fq:
      if (equaliu(ellff_get_p(E),2))
      {
        GEN F = FFX_roots(mkpoln(3, gen_1, b, a), D);
        if (lg(F) == 1) { avma = av; return cgetg(1,t_VEC); }
        return gerepileupto(av, F);
      }
      if (!FF_issquareall(D,&d)) { avma = av; return cgetg(1,t_VEC); }
      break;
    case t_ELL_Q:
      if (typ(x) == t_COMPLEX) { d = gsqrt(D, prec); break; }
      if (!issquareall(D,&d)) { avma = av; return cgetg(1,t_VEC); }
      break;

    case t_ELL_NF:
    {
      GEN T = mkpoln(3, gen_1, gen_0, gneg(D));
      setvarn(T, fetch_var_higher());
      d = nfroots(nf, T);
      delete_var();
      if (lg(d) == 1) { avma = av; return cgetg(1, t_VEC); }
      d = gel(d,1);
      break;
    }

    case t_ELL_Qp:
      p = ellQp_get_p(E);
      D = cvtop(D, p, ellQp_get_prec(E));
      if (!issquare(D)) { avma = av; return cgetg(1,t_VEC); }
      d = Qp_sqrt(D);
      break;

    default:
      d = gsqrt(D,prec);
  }
  a = gsub(d,b); y = cgetg(3,t_VEC);
  gel(y,1) = gmul2n(a, -1);
  gel(y,2) = gsub(gel(y,1),d);
  return gerepileupto(av,y);
}

GEN
ellordinate(GEN e, GEN x, long prec)
{
  checkell(e);
  if (is_matvec_t(typ(x)))
  {
    long i, lx;
    GEN v = cgetg_copy(x, &lx);
    for (i=1; i<lx; i++) gel(v,i) = ellordinate(e,gel(x,i),prec);
    return v;
  }
  return ellordinate_i(e, x, prec);
}

GEN
ellrandom(GEN E)
{
  GEN fg;
  checkell_Fq(E);
  fg = ellff_get_field(E);
  if (typ(fg)==t_FFELT)
    return FF_ellrandom(E);
  else
  {
    pari_sp av = avma;
    GEN p = fg, e = ellff_get_a4a6(E);
    GEN P = random_FpE(gel(e,1),gel(e,2),p);
    P = FpE_to_mod(FpE_changepoint(P,gel(e,3),p),p);
    return gerepileupto(av, P);
  }
}

/* n t_QUAD or t_COMPLEX, z != [0] */
static GEN
ellmul_CM(GEN e, GEN z, GEN n)
{
  GEN p1p, q1p, x, y, p0, p1, q0, q1, z1, z2, grdx, b2ov12, N = gnorm(n);
  long ln, ep, vn;

  if (typ(N) != t_INT)
    pari_err_TYPE("ellmul (non integral CM exponent)",N);
  ln = itos_or_0(shifti(addsi(1, N), 3));
  if (!ln) pari_err_OVERFLOW("ellmul_CM [norm too large]");
  vn = ((ln>>1)-4)>>2;
  z1 = ellwpseries(e, 0, ln);
  z2 = gsubst(z1, 0, monomial(n, 1, 0));
  p0 = gen_0; p1 = gen_1;
  q0 = gen_1; q1 = gen_0;
  do
  {
    GEN p2,q2, ss = gen_0;
    do
    {
      ep = (-valp(z2)) >> 1;
      ss = gadd(ss, gmul(gel(z2,2), monomial(gen_1, ep, 0)));
      z2 = gsub(z2, gmul(gel(z2,2), gpowgs(z1, ep)));
    }
    while (valp(z2) <= 0);
    p2 = gadd(p0, gmul(ss,p1)); p0 = p1; p1 = p2;
    q2 = gadd(q0, gmul(ss,q1)); q0 = q1; q1 = q2;
    if (!signe(z2)) break;
    z2 = ginv(z2);
  }
  while (degpol(p1) < vn);
  if (degpol(p1) > vn || signe(z2))
    pari_err_TYPE("ellmul [not a complex multiplication]", n);
  q1p = RgX_deriv(q1);
  b2ov12 = gdivgs(ell_get_b2(e), 12); /* x - b2/12 */
  grdx = gadd(gel(z,1), b2ov12);
  q1 = poleval(q1, grdx);
  if (gequal0(q1)) return ellinf();

  p1p = RgX_deriv(p1);
  p1 = poleval(p1, grdx);
  p1p = poleval(p1p, grdx);
  q1p = poleval(q1p, grdx);

  x = gdiv(p1,q1);
  y = gdiv(gsub(gmul(p1p,q1), gmul(p1,q1p)), gmul(n,gsqr(q1)));
  x = gsub(x, b2ov12);
  y = gsub( gmul(ec_dmFdy_evalQ(e,z), y), ec_h_evalx(e,x));
  return mkvec2(x, gmul2n(y,-1));
}

static GEN
_sqr(void *e, GEN x) { return elladd((GEN)e, x, x); }
static GEN
_mul(void *e, GEN x, GEN y) { return elladd((GEN)e, x, y); }

static GEN
ellffmul(GEN E, GEN P, GEN n)
{
  GEN fg = ellff_get_field(E);
  if (typ(fg)==t_FFELT)
    return FF_ellmul(E, P, n);
  else
  {
    pari_sp av = avma;
    GEN p = fg, e = ellff_get_a4a6(E), Q;
    GEN Pp = FpE_changepointinv(RgE_to_FpE(P, p), gel(e,3), p);
    GEN Qp = FpE_mul(Pp, n, gel(e,1), p);
    Q = FpE_to_mod(FpE_changepoint(Qp, gel(e,3), p), p);
    return gerepileupto(av, Q);
  }
}
/* [n] z, n integral */
static GEN
ellmul_Z(GEN e, GEN z, GEN n)
{
  long s;
  if (ell_is_inf(z)) return ellinf();
  if (ell_over_Fq(e)) return ellffmul(e,z,n);
  s = signe(n);
  if (!s) return ellinf();
  if (s < 0) z = ellneg_i(e,z);
  if (is_pm1(n)) return z;
  return gen_pow(z, n, (void*)e, &_sqr, &_mul);
}

/* x a t_REAL, try to round it to an integer */
enum { OK, LOW_PREC, NO };
static long
myroundr(GEN *px)
{
  GEN x = *px;
  long e;
  if (bit_prec(x) - expo(x) < 5) return LOW_PREC;
  *px = grndtoi(x, &e);
  if (e >= -5) return NO;
  return OK;
}

/* E has CM by Q, t_COMPLEX or t_QUAD. Return q such that E has CM by Q/q
 * or gen_1 (couldn't find q > 1)
 * or NULL (doesn't have CM by Q) */
static GEN
CM_factor(GEN E, GEN Q)
{
  GEN w, tau, D, v, x, y, F, dF, q, r, fk, fkb, fkc;
  long prec;

  if (ell_get_type(E) != t_ELL_Q) return gen_1;
  switch(typ(Q))
  {
    case t_COMPLEX:
      D = utoineg(4);
      v = gel(Q,2);
      break;
    case t_QUAD:
      D = quad_disc(Q);
      v = gel(Q,3);
      break;
    default:
      return NULL; /*-Wall*/
  }
  /* disc Q = v^2 D, D < 0 fundamental */
  w = ellR_omega(E, DEFAULTPREC + nbits2nlong(expi(D)));
  tau = gdiv(gel(w,2), gel(w,1));
  prec = precision(tau);
  /* disc tau = -4 k^2 (Im tau)^2 for some integral k
   * Assuming that E has CM by Q, then disc Q / disc tau = f^2 is a square.
   * Compute f*k */
  x = gel(tau,1);
  y = gel(tau,2); /* tau = x + Iy */
  fk = gmul(gdiv(v, gmul2n(y, 1)), sqrtr_abs(itor(D, prec)));
  switch(myroundr(&fk))
  {
    case NO: return NULL;
    case LOW_PREC: return gen_1;
  }
  fk = absi(fk);

  fkb = gmul(fk, gmul2n(x,1));
  switch(myroundr(&fkb))
  {
    case NO: return NULL;
    case LOW_PREC: return gen_1;
  }

  fkc = gmul(fk, cxnorm(tau));
  switch(myroundr(&fkc))
  {
    case NO: return NULL;
    case LOW_PREC: return gen_1;
  }

  /* tau is a root of fk (X^2 - b X + c) \in Z[X],  */
  F = Q_primpart(mkvec3(fk, fkb, fkc));
  dF = qfb_disc(F); /* = disc tau, E has CM by orders of disc dF q^2, all q */
  q = dvmdii(dF, D, &r);
  if (r != gen_0 || !Z_issquareall(q, &q)) return NULL;
  /* disc(Q) = disc(tau) (v / q)^2 */
  v = dvmdii(absi(v), q, &r);
  if (r != gen_0) return NULL;
  return is_pm1(v)? gen_1: v; /* E has CM by Q/q: [Q] = [q] o [Q/q] */
}

/* [a + w] z, a integral, w pure imaginary */
static GEN
ellmul_CM_aux(GEN e, GEN z, GEN a, GEN w)
{
  GEN A, B, q;
  if (typ(a) != t_INT) pari_err_TYPE("ellmul_Z",a);
  q = CM_factor(e, w);
  if (!q) pari_err_TYPE("ellmul [not a complex multiplication]",w);
  if (q != gen_1) w = gdiv(w, q);
  /* compute [a + q w] z, z has CM by w */
  if (typ(w) == t_QUAD && is_pm1(gel(gel(w,1), 3)))
  { /* replace w by w - u, u in Z, so that N(w-u) is minimal
     * N(w - u) = N w - Tr w u + u^2, minimal for u = Tr w / 2 */
    GEN u = gtrace(w);
    if (typ(u) != t_INT) pari_err_TYPE("ellmul_CM",w);
    u = shifti(u, -1);
    if (signe(u))
    {
      w = gsub(w, u);
      a = addii(a, mulii(q,u));
    }
    /* [a + w]z = [(a + qu)] z + [q] [(w - u)] z */
  }
  A = ellmul_Z(e,z,a);
  B = ellmul_CM(e,z,w);
  if (q != gen_1) B = ellmul_Z(e, B, q);
  return elladd(e, A, B);
}
GEN
ellmul(GEN e, GEN z, GEN n)
{
  pari_sp av = avma;

  checkell(e); checkellpt(z);
  if (ell_is_inf(z)) return ellinf();
  switch(typ(n))
  {
    case t_INT: return gerepilecopy(av, ellmul_Z(e,z,n));
    case t_QUAD: {
      GEN pol = gel(n,1), a = gel(n,2), b = gel(n,3);
      if (signe(gel(pol,2)) < 0) pari_err_TYPE("ellmul_CM",n); /* disc > 0 ? */
      return gerepileupto(av, ellmul_CM_aux(e,z,a,mkquad(pol, gen_0,b)));
    }
    case t_COMPLEX: {
      GEN a = gel(n,1), b = gel(n,2);
      return gerepileupto(av, ellmul_CM_aux(e,z,a,mkcomplex(gen_0,b)));
    }
  }
  pari_err_TYPE("ellmul (non integral, non CM exponent)",n);
  return NULL; /* not reached */
}

/********************************************************************/
/**                                                                **/
/**                       Periods                                  **/
/**                                                                **/
/********************************************************************/

/* References:
  The complex AGM, periods of elliptic curves over C and complex elliptic logarithms
  John E. Cremona, Thotsaphon Thongjunthug, arXiv:1011.0914
*/

static GEN
ellomega_agm(GEN a, GEN b, GEN c, long prec)
{
  GEN pi = mppi(prec), mIpi = mkcomplex(gen_0, negr(pi));
  GEN Mac = agm(a,c,prec), Mbc = agm(b,c,prec);
  retmkvec2(gdiv(pi, Mac), gdiv(mIpi, Mbc));
}

static GEN
ellomega_cx(GEN E, long prec)
{
  pari_sp av = avma;
  GEN roots = ellR_roots(E,prec);
  GEN d1=gel(roots,4), d2=gel(roots,5), d3=gel(roots,6);
  GEN a = gsqrt(d3,prec), b = gsqrt(d1,prec), c = gsqrt(d2,prec);
  return gerepileupto(av, ellomega_agm(a,b,c,prec));
}

/* return [w1,w2] for E / R; w1 > 0 is real.
 * If e.disc > 0, w2 = -I r; else w2 = w1/2 - I r, for some real r > 0.
 * => tau = w1/w2 is in upper half plane */
static GEN
doellR_omega(GEN E, long prec)
{
  pari_sp av = avma;
  GEN roots, d2, z, a, b, c;
  if (ellR_get_sign(E) >= 0) return ellomega_cx(E,prec);
  roots = ellR_roots(E,prec);
  d2 = gel(roots,5);
  z = gsqrt(d2,prec); /* imag(e1-e3) > 0, so that b > 0*/
  a = gel(z,1); /* >= 0 */
  b = gel(z,2);
  c = gabs(z, prec);
  z = ellomega_agm(a,b,c,prec);
  return gerepilecopy(av, mkvec2(gel(z,1),gmul2n(gadd(gel(z,1),gel(z,2)),-1)));
}
static GEN
doellR_eta(GEN E, long prec)
{ GEN w = ellR_omega(E, prec); return elleta(w, prec); }

GEN
ellR_omega(GEN E, long prec)
{ return obj_checkbuild_realprec(E, R_PERIODS, &doellR_omega, prec); }
GEN
ellR_eta(GEN E, long prec)
{ return obj_checkbuild_realprec(E, R_ETA, &doellR_eta, prec); }
GEN
ellR_roots(GEN E, long prec)
{ return obj_checkbuild_realprec(E, R_ROOTS, &doellR_roots, prec); }

/********************************************************************/
/**                                                                **/
/**                       ELLIPTIC FUNCTIONS                       **/
/**                                                                **/
/********************************************************************/
/* P = [x,0] is 2-torsion on y^2 = g(x). Return w1/2, (w1+w2)/2, or w2/2
 * depending on whether x is closest to e1,e2, or e3, the 3 complex root of g */
static GEN
zell_closest_0(GEN om, GEN x, GEN ro)
{
  GEN e1 = gel(ro,1), e2 = gel(ro,2), e3 = gel(ro,3);
  GEN d1 = gnorm(gsub(x,e1));
  GEN d2 = gnorm(gsub(x,e2));
  GEN d3 = gnorm(gsub(x,e3));
  GEN z = gel(om,2);
  if (gcmp(d1, d2) <= 0)
  { if (gcmp(d1, d3) <= 0) z = gel(om,1); }
  else
  { if (gcmp(d2, d3)<=0) z = gadd(gel(om,1),gel(om,2)); }
  return gmul2n(z, -1);
}

static GEN
zellcx(GEN E, GEN P, long prec)
{
  GEN R = ellR_roots(E, prec+EXTRAPRECWORD);
  GEN x0 = gel(P,1), y0 = ec_dmFdy_evalQ(E,P);
  if (gequal0(y0))
    return zell_closest_0(ellomega_cx(E,prec),x0,R);
  else
  {
    GEN e2 = gel(R,2), e3 = gel(R,3), d2 = gel(R,5), d3 = gel(R,6);
    GEN a = gsqrt(d2,prec), b = gsqrt(d3,prec);
    GEN r = gsqrt(gdiv(gsub(x0,e3), gsub(x0,e2)),prec);
    GEN t = gdiv(gneg(y0), gmul2n(gmul(r,gsub(x0,e2)),1));
    GEN ar = real_i(a), br = real_i(b), ai = imag_i(a), bi = imag_i(b);
    /* |a+b| < |a-b| */
    if (gcmp(gmul(ar,br), gneg(gmul(ai,bi))) < 0) b = gneg(b);
    return zellagmcx(a,b,r,t,prec);
  }
}

/* Assume E/R, disc E < 0, and P \in E(R) ==> z \in R */
static GEN
zellrealneg(GEN E, GEN P, long prec)
{
  GEN x0 = gel(P,1), y0 = ec_dmFdy_evalQ(E,P);
  if (gequal0(y0)) return gmul2n(gel(ellR_omega(E,prec),1),-1);
  else
  {
    GEN R = ellR_roots(E, prec+EXTRAPRECWORD);
    GEN d2 = gel(R,5), e3 = gel(R,3);
    GEN a = gsqrt(d2,prec);
    GEN z = gsqrt(gsub(x0,e3), prec);
    GEN ar = real_i(a), zr = real_i(z), ai = imag_i(a), zi = imag_i(z);
    GEN t = gdiv(gneg(y0), gmul2n(gnorm(z),1));
    GEN r2 = ginv(gsqrt(gaddsg(1,gdiv(gmul(ai,zi),gmul(ar,zr))),prec));
    return zellagmcx(ar,gabs(a,prec),r2,gmul(t,r2),prec);
  }
}

/* Assume E/R, disc E > 0, and P \in E(R) */
static GEN
zellrealpos(GEN E, GEN P, long prec)
{
  GEN R = ellR_roots(E, prec+EXTRAPRECWORD);
  GEN d2,d3,e1,e2,e3, a,b, x0 = gel(P,1), y0 = ec_dmFdy_evalQ(E,P);
  if (gequal0(y0)) return zell_closest_0(ellR_omega(E,prec), x0,R);
  e1 = gel(R,1);
  e2 = gel(R,2);
  e3 = gel(R,3);
  d2 = gel(R,5);
  d3 = gel(R,6);
  a = gsqrt(d2,prec);
  b = gsqrt(d3,prec);
  if (gcmp(x0,e1)>0) {
    GEN r = gsqrt(gdiv(gsub(x0,e3), gsub(x0,e2)),prec);
    GEN t = gdiv(gneg(y0), gmul2n(gmul(r,gsub(x0,e2)),1));
    return zellagmcx(a,b,r,t,prec);
  } else {
    GEN om = ellR_omega(E,prec);
    GEN r = gdiv(a,gsqrt(gsub(e1,x0),prec));
    GEN t = gdiv(gmul(r,y0),gmul2n(gsub(x0,e3),1));
    return gsub(zellagmcx(a,b,r,t,prec),gmul2n(gel(om,2),-1));
  }
}

/* Let T = 4x^3 + b2 x^2 + 2b4 x + b6, where T has a unique p-adic root 'a'.
 * Return a lift of a to padic accuracy prec. We have
 * 216 T = 864 X^3 - 18 c4X - c6, where X = x + b2/12 */
static GEN
doellQp_root(GEN E, long prec)
{
  GEN c4=ell_get_c4(E), c6=ell_get_c6(E), j=ell_get_j(E), p=ellQp_get_p(E);
  GEN c4p, c6p, T, a, pe;
  long alpha;
  int pis2 = equaliu(p, 2);
  if (Q_pval(j, p) >= 0) pari_err_DOMAIN(".root", "v_p(j)", ">=", gen_0, j);
  /* v(j) < 0 => v(c4^3) = v(c6^2) = 2 alpha */
  alpha = Q_pvalrem(ell_get_c4(E), p, &c4) >> 1;
  if (alpha) (void)Q_pvalrem(ell_get_c6(E), p, &c6);
  /* Renormalized so that v(c4) = v(c6) = 0; multiply by p^alpha at the end */
  if (prec < 4 && pis2) prec = 4;
  pe = powiu(p, prec);
  c4 = Rg_to_Fp(c4, pe); c4p = remii(c4,p);
  c6 = Rg_to_Fp(c6, pe); c6p = remii(c6,p);
  if (pis2)
  { /* Use 432T(X/4) = 27X^3 - 9c4 X - 2c6 to have integral root; a=0 mod 2 */
    T = mkpoln(4, utoipos(27), gen_0, Fp_muls(c4, -9, pe), Fp_muls(c6, -2, pe));
    a = ZpX_liftroot(T, gen_0, p, prec);
    alpha -= 2;
  }
  else if (equaliu(p, 3))
  { /* Use 216T(X/3) = 32X^3 - 6c4 X - c6 to have integral root; a=-c6 mod 3 */
    a = Fp_neg(c6p, p);
    T = mkpoln(4, utoipos(32), gen_0, Fp_muls(c4, -6, pe), Fp_neg(c6, pe));
    a = ZX_Zp_root(T, a, p, prec);
    switch(lg(a)-1)
    {
      case 1: /* single root */
        a = gel(a,1); break;
      case 3: /* three roots, e.g. "15a1", choose the right one */
      {
        GEN a1 = gel(a,1), a2 = gel(a,2), a3 = gel(a,3);
        long v1 = Z_lval(subii(a2, a3), 3);
        long v2 = Z_lval(subii(a1, a3), 3);
        long v3 = Z_lval(subii(a1, a2), 3);
        if      (v1 == v2) a = a3;
        else if (v1 == v3) a = a2;
        else a = a1;
      }
      break;
    }
    alpha--;
  }
  else
  { /* p != 2,3: T = 4(x-a)(x-b)^2 = 4x^3 - 3a^2 x - a^3 when b = -a/2
     * (so that the trace coefficient vanishes) => a = c6/6c4 (mod p)*/
    a = Fp_div(c6p, Fp_mulu(c4p, 6, p), p);
    T = mkpoln(4, utoipos(864), gen_0, Fp_muls(c4, -18, pe), Fp_neg(c6, pe));
    a = ZpX_liftroot(T, a, p, prec);
  }
  a = cvtop(a, p, prec);
  if (alpha) setvalp(a, valp(a)+alpha);
  return gsub(a, gdivgs(ell_get_b2(E), 12));
}
GEN
ellQp_root(GEN E, long prec)
{ return obj_checkbuild_padicprec(E, Qp_ROOT, &doellQp_root, prec); }

/* compute a,b such that E1: y^2 = x(x-a)(x-b) ~ E */
static void
doellQp_ab(GEN E, GEN *pta, GEN *ptb, long prec)
{
  GEN b2 = ell_get_b2(E), b4 = ell_get_b4(E), e1 = ellQp_root(E, prec);
  GEN w, t = gadd(gdivgs(b2,4), gmulsg(3,e1));
  w = Qp_sqrt(gmul2n(gadd(b4,gmul(e1,gadd(b2,gmulsg(6,e1)))),1));
  if (valp(gadd(t,w)) <= valp(w)) w = gneg_i(w); /* <=> v(d) > v(w) */
  /* w^2 = 2b4 + 2b2 e1 + 12 e1^2 = 4(e1-e2)(e1-e3) */
  *pta = gmul2n(gsub(w,t),-2);
  *ptb = gmul2n(w,-1);
}

static GEN
doellQp_Tate_uniformization(GEN E, long prec0)
{
  GEN p = ellQp_get_p(E), j = ell_get_j(E);
  GEN u, u2, q, x1, a, b, d, s, t;
  long v, prec = prec0+2;

  if (Q_pval(j, p) >= 0) pari_err_DOMAIN(".tate", "v_p(j)", ">=", gen_0, j);
START:
  doellQp_ab(E, &a, &b, prec);
  d = gsub(a,b);
  v = prec0 - precp(d);
  if (v > 0) { prec += v; goto START; }
  x1 = gmul2n(d,-2);
  u2 = do_padic_agm(&x1,NULL,a,b);

  t = gaddsg(1, ginv(gmul2n(gmul(u2,x1),1)));
  s = Qp_sqrt(gsubgs(gsqr(t), 1));
  q = gadd(t,s);
  if (gequal0(q)) q = gsub(t,s);
  v = prec0 - precp(q);
  if (v > 0) { prec += v; goto START; }
  if (valp(q) < 0) q = ginv(q);
  if (issquare(u2))
    u = Qp_sqrt(u2);
  else
  {
    GEN T = mkpoln(3, gen_1, gen_0, gneg(u2));
    u = mkpolmod(pol_x(0), T);
  }
  return mkvec4(u2, u, q, mkvec2(a, b));
}
GEN
ellQp_Tate_uniformization(GEN E, long prec)
{return obj_checkbuild_padicprec(E,Qp_TATE,&doellQp_Tate_uniformization,prec);}
GEN
ellQp_u(GEN E, long prec)
{ GEN T = ellQp_Tate_uniformization(E, prec); return gel(T,2); }
GEN
ellQp_u2(GEN E, long prec)
{ GEN T = ellQp_Tate_uniformization(E, prec); return gel(T,1); }
GEN
ellQp_q(GEN E, long prec)
{ GEN T = ellQp_Tate_uniformization(E, prec); return gel(T,3); }
GEN
ellQp_ab(GEN E, long prec)
{ GEN T = ellQp_Tate_uniformization(E, prec); return gel(T,4); }

static GEN
zellQp(GEN E, GEN z, long prec)
{
  pari_sp av = avma;
  GEN b2, a, b, ab, c0, r0, r1, ar1, e1, x, y, delta, x0,x1, y0,y1, t;
  if (ell_is_inf(z)) return gen_1;
  b2 = ell_get_b2(E);
  e1 = ellQp_root(E, prec);
  ab = ellQp_ab(E, prec);
  a = gel(ab,1);
  b = gel(ab,2); r1 = gsub(a,b);
  x = gel(z,1);
  y = gel(z,2);
  r0 = gadd(e1,gmul2n(b2,-2));
  c0 = gadd(x, gmul2n(r0,-1)); ar1 = gmul(a,r1);
  delta = gdiv(ar1, gsqr(c0));
  x0 = gmul2n(gmul(c0,gaddsg(1,Qp_sqrt(gsubsg(1,gmul2n(delta,2))))),-1);
  y0 = gdiv(gadd(y, gmul2n(ec_dmFdy_evalQ(E,z), -1)), gsubsg(1, gdiv(ar1,gsqr(x0))));

  x1 = gmul(x0, gsqr(gmul2n(gaddsg(1, Qp_sqrt(gdiv(gadd(x0,r1),x0))),-1)));
  y1 = gdiv(y0, gsubsg(1, gsqr(gdiv(r1,gmul2n(x1,2)))));
  if (gequal0(x1)) pari_err_PREC("ellpointtoz");

  (void)do_padic_agm(&x1,&y1, a,b);
  t = gmul(ellQp_u(E, prec), gmul2n(y1,1)); /* 2u y_oo */
  t = gdiv(gsub(t, x1), gadd(t, x1));
  if (padicprec_relative(t) > prec) t = gprec(t, prec);
  return gerepileupto(av, t);
}

/* t to w := -1/y */
GEN
ellformalw(GEN e, long n, long v)
{
  pari_sp av = avma, av2;
  GEN a1,a2,a3,a4,a6, a63;
  GEN w = cgetg(3, t_SER), t, U, V, W, U2;
  ulong mask, nold = 1;
  if (v < 0) v = 0;
  if (n <= 0) pari_err_DOMAIN("ellformalw","precision","<=",gen_0,stoi(n));
  mask = quadratic_prec_mask(n);
  t = pol_x(v);
  checkell(e);
  a1 = ell_get_a1(e); a2 = ell_get_a2(e); a3 = ell_get_a3(e);
  a4 = ell_get_a4(e); a6 = ell_get_a6(e); a63 = gmulgs(a6,3);
  w[1] = evalsigne(1)|evalvarn(v)|evalvalp(3);
  gel(w,2) = gen_1; /* t^3 + O(t^4) */
  /* use Newton iteration, doubling accuracy at each step
   *
   *            w^3 a6 + w^2(a4 t + a3) + w (a2 t^2 + a1 t - 1) + t^3
   * w  <-  w - -----------------------------------------------------
   *              w^2 (3a6) + w (2a4 t + 2a3) + (a2 t^2 + a1 t - 1)
   *
   *              w^3 a6 + w^2 U + w V + W
   *      =: w -  -----------------------
   *                w^2 (3a6) + 2w U + V
   */
  U = gadd(gmul(a4,t), a3);
  U2 = gmul2n(U,1);
  V = gsubgs(gadd(gmul(a2,gsqr(t)), gmul(a1,t)), 1);
  W = gpowgs(t,3);
  av2 = avma;
  while (mask > 1)
  { /* nold correct terms in w */
    ulong i, nnew = nold << 1;
    GEN num, den, wnew, w2, w3;
    if (mask & 1) nnew--;
    mask >>= 1;
    wnew = cgetg(nnew+2, t_SER);
    wnew[1] = w[1];
    for (i = 2; i < nold+2; i++) gel(wnew,i) = gel(w,i);
    for (     ; i < nnew+2; i++) gel(wnew,i) = gen_0;
    w = wnew;
    w2 = gsqr(w); w3 = gmul(w2,w);
    num = gadd(gmul(a6,w3), gadd(gmul(U,w2), gadd(gmul(V,w), W)));
    den = gadd(gmul(a63,w2), gadd(gmul(w,U2), V));

    w = gerepileupto(av2, gsub(w, gdiv(num, den)));
    nold = nnew;
  }
  return gerepilecopy(av, w);
}

static GEN
ellformalpoint_i(GEN w, GEN wi)
{ return mkvec2(gmul(pol_x(varn(w)),wi), gneg(wi)); }

/* t to [x,y] */
GEN
ellformalpoint(GEN e, long n, long v)
{
  pari_sp av = avma;
  GEN w = ellformalw(e, n, v), wi = inv_ser(w);
  return gerepilecopy(av, ellformalpoint_i(w, wi));
}

static GEN
ellformaldifferential_i(GEN e, GEN w, GEN wi, GEN *px)
{
  GEN x, w1;
  if (gequal0(ell_get_a1(e)) && gequal0(ell_get_a3(e)))
  { /* dx/2y = dx * -w/2, avoid division */
    x = gmul(pol_x(varn(w)), wi);
    w1 = gmul(derivser(x), gneg(gmul2n(w,-1)));
  }
  else
  {
    GEN P = ellformalpoint_i(w, wi);
    x = gel(P,1);
    w1 = gdiv(derivser(x), ec_dmFdy_evalQ(e, P));
  }
  *px = x; return w1;
}
/* t to [ dx / (2y + a1 x + a3), x * ... ]*/
GEN
ellformaldifferential(GEN e, long n, long v)
{
  pari_sp av = avma;
  GEN w = ellformalw(e, n, v), wi = inv_ser(w), x;
  GEN w1 = ellformaldifferential_i(e, w, wi, &x);
  return gerepilecopy(av, mkvec2(w1,gmul(x,w1)));
}

/* t to z, dz = w1 dt */
GEN
ellformallog(GEN e, long n, long v)
{
  pari_sp av = avma;
  GEN w = ellformalw(e, n, v), wi = inv_ser(w), x;
  GEN w1 = ellformaldifferential_i(e, w, wi, &x);
  return gerepileupto(av, integser(w1));
}
/* z to t */
GEN
ellformalexp(GEN e, long n, long v)
{
  pari_sp av = avma;
  return gerepileupto(av, serreverse(ellformallog(e,n,v)));
}
/* [log_p (sigma(t) / t), log_E t], as power series, d (log_E t) := w1 dt;
 * As a fonction of z: odd, = e.b2/12 * z + O(z^3).
 *   sigma(z) = ellsigma(e) exp(e.b2/24*z^2)
 * log_p(sigma(t)/t)=log(subst(sigma(z), x, ellformallog(e))/x) */
static GEN
ellformallogsigma_t(GEN e, long n)
{
  pari_sp av = avma;
  GEN w = ellformalw(e, n, 0), wi = inv_ser(w), t = pol_x(0);
  GEN x, s = ellformaldifferential_i(e, w, wi, &x);
  GEN f = gmul(s, gadd(integser(gmul(x,s)), gmul2n(ell_get_a1(e),-1)));
  return gerepilecopy(av, mkvec2(integser( gsub(ginv(gneg(t)), f) ),
                                 integser(s)));
}

/* P = rational point of exact denominator d. Is Q singular on E(Fp) ? */
static int
FpE_issingular(GEN E, GEN P, GEN d, GEN p)
{
  pari_sp av = avma;
  GEN t, x, y, a1, a2, a3, a4;
  if (ell_is_inf(E) || !signe(remii(d,p))) return 0; /* 0_E is smooth */
  P = Q_muli_to_int(P,d);
  x = gel(P,1);
  y = gel(P,2);
  a1 = ell_get_a1(E);
  a3 = ell_get_a3(E);
  t = addii(shifti(y,1), addii(mulii(a1,x), mulii(a3,d)));
  if (signe(remii(t,p))) { avma = av; return 0; }
  a2 = ell_get_a2(E);
  a4 = ell_get_a4(E);
  d = Fp_inv(d, p);
  x = Fp_mul(x,d,p);
  y = Fp_mul(y,d,p);
  t = subii(mulii(a1,y), addii(a4, mulii(x, addii(gmul2n(a2,1), muliu(x,3)))));
  avma = av; return signe(remii(t,p))? 0: 1;
}

/* E/Q, P on E(Q). Let g > 0 minimal such that the image of R = [g]P in a
 * minimal model is everywhere non-singular. return [R,g] */
GEN
ellnonsingularmultiple(GEN e, GEN P)
{
  pari_sp av = avma;
  GEN ch, E = ellanal_globalred(e, &ch), NP, L, S, d, g = gen_1;
  long i, l;
  checkellpt(P);
  if (ell_is_inf(P)) retmkvec2(gcopy(P), gen_1);
  if (E != e) P = ellchangepoint(P, ch);
  S = obj_check(E, Q_GLOBALRED);
  NP = gmael(S,3,1);
  L = gel(S,4);
  l = lg(NP);
  d = Q_denom(P);
  for (i = 1; i < l; i++)
  {
    GEN c,kod, G = gel(L,i), p = gel(NP,i);/* prime of bad reduction */
    if (!FpE_issingular(E, P, d, p)) continue;
    c = gel(G, 4); /* Tamagawa number at p */
    kod = gel(G, 2); /* Kodaira type */
    if (cmpis(kod, 5) >= 0) /* I_nu */
    {
      long nu = itos(kod) - 4;
      long n = minss(Q_pval(ec_dmFdy_evalQ(E,P), p), nu/2);
      nu /= ugcd(nu, n);
      g = muliu(g, nu);
      P = ellmul_Z(E, P, utoipos(nu));
      d = Q_denom(P);
    } else if (cmpis(kod, -5) <= 0) /* I^*_nu */
    { /* either 2 or 4 */
      long nu = - itos(kod) - 4;
      P = elladd(E, P,P);
      d = Q_denom(P);
      g = shifti(g,1);
      if (odd(nu) && FpE_issingular(E, P, d, p))
      { /* it's 4 */
        P = elladd(E, P,P);
        d = Q_denom(P);
        g = shifti(g,1);
      }
    } else {
      if (equaliu(c, 4)) c = gen_2;
      P = ellmul(E, P, c);
      d = Q_denom(P);
      g = mulii(g, c);
    }
  }
  if (E != e) P = ellchangepointinv(P, ch);
  return gerepilecopy(av, mkvec2(P,g));
}

/* m >= 0, T = b6^2, g4 = b6^2 - b4 b8, return g_m(xP) mod N, in Mazur-Tate's
 * notation (Duke 1991)*/
static GEN
rellg(hashtable *H, GEN m, GEN T, GEN g4, GEN b8, GEN N)
{
  hashentry *h;
  GEN n, z, np2, np1, nm2, nm1, fp2, fp1, fm2, fm1, f;
  ulong m4;
  if (cmpiu(m, 4) <= 0) switch(itou(m))
  {
    case 0: return gen_0;
    case 1: return gen_1;
    case 2: return subiu(N,1);
    case 3: return b8;
    case 4: return g4;
  }
  if ((h = hash_search(H, (void*)m))) return (GEN)h->val;
  m4 = mod4(m);
  n = shifti(m, -1); f   = rellg(H,n,T,g4,b8,N);
  np2 = addiu(n, 2); fp2 = rellg(H,np2,T,g4,b8,N);
  np1 = addiu(n, 1); fp1 = rellg(H,np1,T,g4,b8,N);
  nm2 = subiu(n, 2); fm2 = rellg(H,nm2,T,g4,b8,N);
  nm1 = subiu(n, 1); fm1 = rellg(H,nm1,T,g4,b8,N);
  if (odd(m4))
  {
    GEN t1 = Fp_mul(fp2, Fp_powu(f,3,N), N);
    GEN t2 = Fp_mul(fm1, Fp_powu(fp1,3,N), N);
    if (mpodd(n))
      z = Fp_sub(t1, Fp_mul(T,t2,N), N);
    else
      z = Fp_sub(Fp_mul(T,t1,N), t2, N);
  }
  else
  {
    GEN t1 = Fp_mul(fm2, Fp_sqr(fp1,N), N);
    GEN t2 = Fp_mul(fp2, Fp_sqr(fm1,N), N);
    z = Fp_mul(f, Fp_sub(t1, t2, N), N);
  }
  hash_insert(H, (void*)m, (void*)z);
  return z;
}

static GEN
addii3(GEN x, GEN y, GEN z) { return addii(x,addii(y,z)); }
static GEN
addii4(GEN x, GEN y, GEN z, GEN t) { return addii(x,addii3(y,z,t)); }
static GEN
addii5(GEN x, GEN y, GEN z, GEN t, GEN u) { return addii(x,addii4(y,z,t,u)); }

/* xP = [n,d] (corr. to n/d, coprime), such that the reduction of the point
 * P = [xP,yP] is non singular at all places. Return x([m] P) mod N as
 * [num,den] (coprime) */
static GEN
xmP(GEN e, GEN xP, GEN m, GEN N)
{
  pari_sp av = avma;
  ulong k = expi(m);
  hashtable *H = hash_create((5+k)*k, (ulong(*)(void*))&hash_GEN,
                                      (int(*)(void*,void*))&gidentical, 1);
  GEN b2 = ell_get_b2(e), b4 = ell_get_b4(e), n = gel(xP,1), d = gel(xP,2);
  GEN b6 = ell_get_b6(e), b8 = ell_get_b8(e);
  GEN B4, B6, B8, T, g4;
  GEN d2 = Fp_sqr(d,N), d3 = Fp_mul(d2,d,N), d4 = Fp_sqr(d2,N);
  GEN n2 = Fp_sqr(n,N), n3 = Fp_mul(n2,n,N), n4 = Fp_sqr(n2,N);
  GEN nd = Fp_mul(n,d,N), n2d2 = Fp_sqr(nd,N);
  GEN b2nd = Fp_mul(b2,nd, N), b2n2d = Fp_mul(b2nd,n,N);
  GEN b6d3 = Fp_mul(b6,d3,N), g,gp1,gm1, C,D;
  B8 = addii5(muliu(n4,3), mulii(b2n2d,n), mulii(muliu(b4,3), n2d2),
              mulii(muliu(b6d3,3), n), mulii(b8,d4));
  B6 = addii4(muliu(n3,4), mulii(b2nd,n),
              shifti(mulii(b4,Fp_mul(n,d2,N)), 1),
              b6d3);
  B4 = addii3(muliu(n2,6), b2nd,  mulii(b4,d2));

  B4 = modii(B4,N);
  B6 = modii(B6,N);
  B8 = modii(B8,N);

  g4 = Fp_sub(sqri(B6), mulii(B4,B8), N);
  T = Fp_sqr(B6,N);

  g = rellg(H, m, T,g4,B8, N);
  gp1 = rellg(H, addiu(m,1), T,g4,B8, N);
  gm1 = rellg(H, subiu(m,1), T,g4,B8, N);
  C = Fp_sqr(g, N);
  D = Fp_mul(gp1,gm1, N);

  if(mpodd(m))
  {
    n = Fp_sub(mulii(C,n), mulii(D,B6), N);
    d = Fp_mul(C,d, N);
  }
  else
  {
    n = Fp_sub(Fp_mul(Fp_mul(B6,C,N), n, N), D, N);
    d = Fp_mul(Fp_mul(C,d,N), B6, N);
  }
  return gerepilecopy(av, mkvec2(n,d));
}
/* given [n,d2], x = n/d2 (coprime, d2 = d^2), p | den,
 * return t = -x/y + O(p^v) */
static GEN
tfromx(GEN e, GEN x, GEN p, long v, GEN N, GEN *pd)
{
  GEN n = gel(x,1), d2 = gel(x,2), d;
  GEN a1, a3, b2, b4, b6, B, C, d4, d6, Y;
  if (!signe(n)) { *pd = gen_1; return zeropadic(p, v); }
  a1 = ell_get_a1(e);
  b2 = ell_get_b2(e);
  a3 = ell_get_a3(e);
  b4 = ell_get_b4(e);
  b6 = ell_get_b6(e);
  d = Qp_sqrt(cvtop(d2, p, v - Z_pval(d2,p)));
  if (!d) pari_err_BUG("ellpadicheight");
  /* Solve Y^2 = 4n^3 + b2 n^2 d2+ 2b4 n d2^2 + b6 d2^3,
   * Y = 2y + a1 n d + a3 d^3 */
  d4 = Fp_sqr(d2, N);
  d6 = Fp_mul(d4, d2, N);
  B = gmul(d, Fp_add(mulii(a1,n), mulii(a3,d2), N));
  C = mkpoln(4, utoipos(4), Fp_mul(b2, d2, N),
                Fp_mul(shifti(b4,1), d4, N),
                Fp_mul(b6,d6,N));
  C = FpX_eval(C, n, N);
  if (!signe(C))
    Y = zeropadic(p, v >> 1);
  else
    Y = Qp_sqrt(cvtop(C, p, v - Z_pval(C,p)));
  if (!Y) pari_err_BUG("ellpadicheight");
  *pd = d;
  return gdiv(gmulgs(gmul(n,d), -2), gsub(Y,B));
}

/* return minimal i s.t. -v_p(j+1) - log_p(j-1) + (j+1)*t >= v for all j>=i */
static long
logsigma_prec(GEN p, long v, long t)
{
  double log2p = dbllog2(p);
  long j, i = ceil((v - t) / (t - 2*LOG2/(3*log2p)) + 0.01);
  if (equaliu(p,2) && i < 5) i = 5;
  /* guaranteed to work, now optimize */
  for (j = i-1; j >= 2; j--)
  {
    if (- u_pval(j+1,p) - log2(j-1)/log2p + (j+1)*t + 0.01 < v) break;
    i = j;
  }
  if (j == 1)
  {
    if (- equaliu(p,2) + 2*t + 0.01 >= v) i = 1;
  }
  return i;
}
/* return minimal i s.t. -v_p(j+1) + (j+1)*t >= v for all j>=i */
static long
log_prec(GEN p, long v, long t)
{
  double log2p = dbllog2(p);
  long j, i = ceil(v / (t - LOG2/(2*log2p)) + 0.01);
  /* guaranteed to work, now optimize */
  for (j = i-1; j >= 1; j--)
  {
    if (- u_pval(j+1,p) + (j+1)*t + 0.01 < v) break;
    i = j;
  }
  return i;
}

static GEN
parse_p(GEN p, GEN *ab)
{
  *ab = NULL;
  switch(typ(p))
  {
    case t_INT: break;
    case t_VEC:
      if (lg(p) != 3) pari_err_TYPE("ellpadicheight",p);
      *ab = gel(p,2);
      if (typ(*ab) != t_VEC || lg(*ab) != 3) pari_err_TYPE("ellpadicheight",p);
      p = gel(p,1);
  }
  if (cmpis(p,2) < 0) pari_err_PRIME("ellpadicheight",p);
  return p;
}

static GEN
precp_fix(GEN h, long v)
{ return (precp(h) > v)? gprec(h,v): h; }

GEN
ellpadicheight(GEN e, GEN p, long v0, GEN P)
{
  pari_sp av = avma;
  GEN N, H, h, t, ch, g, E, x, n, d, D, ls, lt, S, a,b, ab;
  long v, vd;
  int is2;
  checkellpt(P);
  if (v0<=0) pari_err_DOMAIN("ellpadicheight","precision","<=",gen_0,stoi(v0));
  checkell_Q(e);
  p = parse_p(p, &ab);
  if (ellorder_Q(e,P)) return ab? gen_0: mkvec2(gen_0,gen_0);
  E = ellanal_globalred(e, &ch);
  if (E != e) P = ellchangepoint(P, ch);
  S = ellnonsingularmultiple(E, P);
  P = gel(S,1);
  g = gel(S,2);
  v = v0 + 2*Z_pval(g, p);
  is2 = equaliu(p,2);
  if (is2) v += 2;
  x = gel(P,1);
  n = numer(x);
  d = denom(x);
  x = mkvec2(n, d);
  vd = Z_pval(d, p);
  if (!vd)
  { /* P not in kernel of reduction mod p */
    GEN m, X, Pp, Ep = ellinit_Fp(E, p);
    long w = v+2;
    if (!Ep) pari_err(e_MISC,"ellpadicheight: bad reduction");
    Pp = RgV_to_FpV(P, p);
    m = ellorder(Ep, Pp, NULL);
    g = mulii(g,m);
    for(;;)
    {
      N = powiu(p, w);
      X = xmP(E, x, m, N);
      d = gel(X,2);
      if (!signe(d))
        w <<= 1;
      else
      {
        vd = Z_pval(d, p);
        if (w >= v+2*vd + is2) break;
        w = v+2*vd + is2;
      }
    }
    x = X;
  }
  /* we will want t mod p^(v+vd) because of t/D in H later, and
   * we lose p^vd in tfromx because of sqrt(d) (p^(vd+1) if p=2)*/
  v += 2*vd + is2;
  N = powiu(p,v);
  t = tfromx(E, x, p, v, N, &D); /* D^2=denom(x)=x[2] */
  S = ellformallogsigma_t(E, logsigma_prec(p, v-vd, valp(t)) + 1);
  ls = ser2rfrac_i(gel(S,1)); /* log_p (sigma(T)/T) */
  lt = ser2rfrac_i(gel(S,2)); /* log_E (T) */
  /* evaluate our formal power series at t */
  H = gadd(poleval(ls, t), glog(gdiv(t, D), 0));
  h = gsqr(poleval(lt, t));
  g = sqri(g);
  a = gdiv(gmulgs(H,-2), g);
  b = gdiv(gneg(h), g);
  if (E != e)
  {
    GEN u = gel(ch,1), r = gel(ch,2);
    a = gdiv(gadd(a, gmul(r,b)), u);
    b = gmul(u,b);
  }
  H = mkvec2(a,b);
  if (ab)
  {
    H = RgV_dotproduct(H, ab);
    H = precp_fix(H,v0);
  }
  else
  {
    gel(H,1) = precp_fix(gel(H,1),v0);
    gel(H,2) = precp_fix(gel(H,2),v0);
  }
  return gerepilecopy(av, H);
}

GEN
ellpadiclog(GEN E, GEN p, long n, GEN P)
{
  pari_sp av = avma;
  long vt;
  GEN t, x, y, L;
  checkellpt(P);
  if (ell_is_inf(P)) return gen_0;
  x = gel(P,1);
  y = gel(P,2); t = gneg(gdiv(x,y));
  vt = gvaluation(t, p); /* can be a t_INT, t_FRAC or t_PADIC */
  if (vt <= 0)
    pari_err_DOMAIN("ellpadiclog","P","not in the kernel of reduction at",p,P);
  L = ser2rfrac_i(ellformallog(E, log_prec(p, n, vt) + 1, 0));
  return gerepileupto(av, poleval(L, cvtop(t, p, n)));
}

/* s2 = (b_2-E_2)/12 */
GEN
ellpadics2(GEN E, GEN p, long n)
{
  pari_sp av = avma;
  GEN sqrtD, D, l, F, a,b,d, ap;
  ulong pp;
  if (typ(p) != t_INT) pari_err_TYPE("ellpadics2",p);
  if (cmpis(p,2) < 0) pari_err_PRIME("ellpadics2",p);
  pp = itou_or_0(p);
  F = ellpadicfrobenius(E, itou(p), n);
  a = gcoeff(F,1,1);
  b = gcoeff(F,1,2);
  d = gcoeff(F,2,2); ap = gadd(a,d);
  if(valp(ap) > 0) pari_err_DOMAIN("ellpadics2","E","is supersingular at", p,E);
  if (pp == 2 || (pp <= 13 && n == 1)) /* 2sqrt(p) > p/2: ambiguity */
    ap = ellap(E,p);
  else
  { /* either 2sqrt(p) < p/2 or n > 1 and 2sqrt(p) < p^2/2 (since p!=2) */
    GEN q = cmpiu(p,13) <= 0? sqri(p): p;
    ap = padic_to_Fp(ap, q);
    ap = Fp_center(ap,q,shifti(q,-1));
  }
  D = subii(sqri(ap), shifti(p,2));
  if (equaliu(p,2)) n++;
  sqrtD = Zp_sqrtlift(D, ap, p, n); /* congruent to ap mod p */
  l = gmul2n(gadd(ap, cvtop(sqrtD,p,n)), -1); /*unit eigenvalue of F*/
  return gerepileupto(av, gdiv(b, gsub(l, a))); /* slope of eigenvector */
}

GEN
zell(GEN e, GEN z, long prec)
{
  pari_sp av = avma;
  GEN t;
  long s;

  checkell(e); checkellpt(z);
  switch(ell_get_type(e))
  {
    case t_ELL_Qp:
      prec = minss(ellQp_get_prec(e), padicprec_relative(z));
      return zellQp(e, z, prec);
    case t_ELL_Q: break;
    case t_ELL_Rg: break;
    default: pari_err_TYPE("ellpointtoz", e);
  }
  (void)ellR_omega(e, prec); /* type checking */
  if (ell_is_inf(z)) return gen_0;
  s = ellR_get_sign(e);
  if (s && typ(gel(z,1))!=t_COMPLEX && typ(gel(z,2))!=t_COMPLEX)
    t = (s < 0)? zellrealneg(e,z,prec): zellrealpos(e,z,prec);
  else
    t = zellcx(e,z,prec);
  return gerepileupto(av,t);
}

enum period_type { t_PER_W, t_PER_WETA, t_PER_ELL };
/* normalization / argument reduction for ellptic functions */
typedef struct {
  enum period_type type;
  GEN in; /* original input */
  GEN w1,w2,tau; /* original basis for L = <w1,w2> = w2 <1,tau> */
  GEN W1,W2,Tau; /* new basis for L = <W1,W2> = W2 <1,tau> */
  GEN a,b,c,d; /* t_INT; tau in F = h/Sl2, tau = g.t, g=[a,b;c,d] in SL(2,Z) */
  GEN z,Z; /* z/w2 defined mod <1,tau>, Z = z + x*tau + y reduced mod <1,tau> */
  GEN x,y; /* t_INT */
  int swap; /* 1 if we swapped w1 and w2 */
  int some_q_is_real; /* exp(2iPi g.tau) for some g \in SL(2,Z) */
  int some_z_is_real; /* z + xw1 + yw2 is real for some x,y \in Z */
  int some_z_is_pure_imag; /* z + xw1 + yw2 = it, t \in R */
  int q_is_real; /* exp(2iPi tau) \in R */
  int abs_u_is_1; /* |exp(2iPi Z)| = 1 */
  long prec; /* precision(Z) */
} ellred_t;

/* compute g in SL_2(Z), g.t is in the usual
   fundamental domain. Internal function no check, no garbage. */
static void
set_gamma(GEN t, GEN *pa, GEN *pb, GEN *pc, GEN *pd)
{
  GEN a, b, c, d, run = dbltor(1. - 1e-8);
  pari_sp av = avma;

  a = d = gen_1;
  b = c = gen_0;
  for(;;)
  {
    GEN m, n = ground(real_i(t));
    if (signe(n))
    { /* apply T^n */
      t = gsub(t,n);
      a = subii(a, mulii(n,c));
      b = subii(b, mulii(n,d));
    }
    m = cxnorm(t); if (gcmp(m,run) > 0) break;
    t = gneg_i(gdiv(gconj(t), m)); /* apply S */
    togglesign_safe(&c); swap(a,c);
    togglesign_safe(&d); swap(b,d);
    if (gc_needed(av, 1)) {
      if (DEBUGMEM>1) pari_warn(warnmem, "redimagsl2");
      gerepileall(av, 5, &t, &a,&b,&c,&d);
    }
  }
  *pa = a;
  *pb = b;
  *pc = c;
  *pd = d;
}
/* Im t > 0. Return U.t in PSl2(Z)'s standard fundamental domain.
 * Set *pU to U. */
GEN
redtausl2(GEN t, GEN *pU)
{
  pari_sp av = avma;
  GEN U, a,b,c,d;
  set_gamma(t, &a, &b, &c, &d);
  U = mkmat2(mkcol2(a,c), mkcol2(b,d));
  t = gdiv(gadd(gmul(a,t), b),
           gadd(gmul(c,t), d));
  gerepileall(av, 2, &t, &U);
  *pU = U; return t;
}

/* swap w1, w2 so that Im(t := w1/w2) > 0. Set tau = representative of t in
 * the standard fundamental domain, and g in Sl_2, such that tau = g.t */
static void
red_modSL2(ellred_t *T, long prec)
{
  long s, p;
  T->tau = gdiv(T->w1,T->w2);
  if (isexactzero(real_i(T->tau))) T->some_q_is_real = 1;
  s = gsigne(imag_i(T->tau));
  if (!s) pari_err_DOMAIN("elliptic function", "det(w1,w2)", "=", gen_0,
                          mkvec2(T->w1,T->w2));
  T->swap = (s < 0);
  if (T->swap) { swap(T->w1, T->w2); T->tau = ginv(T->tau); }
  set_gamma(T->tau, &T->a, &T->b, &T->c, &T->d);
  /* update lattice */
  T->W1 = gadd(gmul(T->a,T->w1), gmul(T->b,T->w2));
  T->W2 = gadd(gmul(T->c,T->w1), gmul(T->d,T->w2));
  T->Tau = gdiv(T->W1, T->W2);
  if (isexactzero(real_i(T->Tau))) T->some_q_is_real = T->q_is_real = 1;
  p = precision(T->Tau); if (!p) p = prec;
  T->prec = p;
}
static void
reduce_z(GEN z, ellred_t *T)
{
  long p;
  GEN Z;
  T->abs_u_is_1 = 0;
  T->some_z_is_real = 0;
  T->some_z_is_pure_imag = 0;
  switch(typ(z))
  {
    case t_INT: case t_REAL: case t_FRAC: case t_COMPLEX: break;
    case t_QUAD:
      z = isexactzero(gel(z,2))? gel(z,1): quadtofp(z, T->prec);
      break;
    default: pari_err_TYPE("reduction mod 2-dim lattice (reduce_z)", z);
  }
  T->z = z;
  Z = gdiv(z, T->W2);
  T->x = ground(gdiv(imag_i(Z), imag_i(T->Tau)));
  if (signe(T->x)) Z = gsub(Z, gmul(T->x,T->Tau));
  T->y = ground(real_i(Z));
  if (signe(T->y)) Z = gsub(Z, T->y);
  if (typ(Z) != t_COMPLEX)
    T->some_z_is_real = T->abs_u_is_1 = 1;
  else if (typ(z) != t_COMPLEX)
    T->some_z_is_real = 1;
  else if (isexactzero(gel(z,1)) || isexactzero(gel(Z,1)))
    T->some_z_is_pure_imag = 1;
  p = precision(Z);
  if (gequal0(Z) || (p && gexpo(Z) < 5 - prec2nbits(p)))
    Z = NULL; /*z in L*/
  if (p && p < T->prec) T->prec = p;
  T->Z = Z;
}
/* return x.eta1 + y.eta2 */
static GEN
eta_correction(ellred_t *T, GEN eta)
{
  GEN y1 = NULL, y2 = NULL;
  if (signe(T->x)) y1 = gmul(T->x, gel(eta,1));
  if (signe(T->y)) y2 = gmul(T->y, gel(eta,2));
  if (!y1) return y2? y2: gen_0;
  return y2? gadd(y1, y2): y1;
}
/* e is either
 * - [w1,w2]
 * - [[w1,w2],[eta1,eta2]]
 * - an ellinit structure */
static void
compute_periods(ellred_t *T, GEN z, long prec)
{
  GEN w, e;
  T->q_is_real = 0;
  T->some_q_is_real = 0;
  switch(T->type)
  {
    case t_PER_ELL:
    {
      long pr, p = prec;
      if (z && (pr = precision(z))) p = pr;
      e = T->in;
      w = ellR_omega(e, p);
      T->some_q_is_real = T->q_is_real = 1;
      break;
    }
    case t_PER_W:
      w = T->in; break;
    default: /*t_PER_WETA*/
      w = gel(T->in,1); break;
  }
  T->w1 = gel(w,1);
  T->w2 = gel(w,2);
  red_modSL2(T, prec);
  if (z) reduce_z(z, T);
}
static int
check_periods(GEN e, ellred_t *T)
{
  GEN w1;
  if (typ(e) != t_VEC) return 0;
  T->in = e;
  switch(lg(e))
  {
    case 17:
      T->type = t_PER_ELL;
      break;
    case 3:
      w1 = gel(e,1);
      if (typ(w1) != t_VEC)
        T->type = t_PER_W;
      else
      {
        if (lg(w1) != 3) return 0;
        T->type = t_PER_WETA;
      }
      break;
    default: return 0;
  }
  return 1;
}
static int
get_periods(GEN e, GEN z, ellred_t *T, long prec)
{
  if (!check_periods(e, T)) return 0;
  compute_periods(T, z, prec); return 1;
}

/* 2iPi/x, more efficient when x pure imaginary */
static GEN
PiI2div(GEN x, long prec) { return gdiv(Pi2n(1, prec), mulcxmI(x)); }
/* exp(I x y), more efficient for x in R, y pure imaginary */
GEN
expIxy(GEN x, GEN y, long prec) { return gexp(gmul(x, mulcxI(y)), prec); }

static GEN
check_real(GEN q)
{ return (typ(q) == t_COMPLEX && gequal0(gel(q,2)))? gel(q,1): q; }

/* Return E_k(tau). Slow if tau is not in standard fundamental domain */
static GEN
trueE(GEN tau, long k, long prec)
{
  pari_sp av;
  GEN p1, q, y, qn;
  long n = 1;

  if (k == 2) return trueE2(tau, prec);
  q = expIxy(Pi2n(1, prec), tau, prec);
  q = check_real(q);
  y = gen_0;
  av = avma; qn = gen_1;
  for(;; n++)
  { /* compute y := sum_{n>0} n^(k-1) q^n / (1-q^n) */
    qn = gmul(q,qn);
    p1 = gdiv(gmul(powuu(n,k-1),qn), gsubsg(1,qn));
    if (gequal0(p1) || gexpo(p1) <= - prec2nbits(prec) - 5) break;
    y = gadd(y, p1);
    if (gc_needed(av,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"elleisnum");
      gerepileall(av, 2, &y,&qn);
    }
  }
  return gadd(gen_1, gmul(y, gdiv(gen_2, szeta(1-k, prec))));
}

/* (2iPi/W2)^k E_k(W1/W2) */
static GEN
_elleisnum(ellred_t *T, long k)
{
  GEN y = trueE(T->Tau, k, T->prec);
  y = gmul(y, gpowgs(mulcxI(gdiv(Pi2n(1,T->prec), T->W2)),k));
  return check_real(y);
}

/* Return (2iPi)^k E_k(L) = (2iPi/w2)^k E_k(tau), with L = <w1,w2>, k > 0 even
 * E_k(tau) = 1 + 2/zeta(1-k) * sum(n>=1, n^(k-1) q^n/(1-q^n))
 * If flag is != 0 and k=4 or 6, compute g2 = E4/12 or g3 = -E6/216 resp. */
GEN
elleisnum(GEN om, long k, long flag, long prec)
{
  pari_sp av = avma;
  GEN y;
  ellred_t T;

  if (k<=0) pari_err_DOMAIN("elleisnum", "k", "<=", gen_0, stoi(k));
  if (k&1) pari_err_DOMAIN("elleisnum", "k % 2", "!=", gen_0, stoi(k));
  if (!get_periods(om, NULL, &T, prec)) pari_err_TYPE("elleisnum",om);
  y = _elleisnum(&T, k);
  if (k==2 && signe(T.c))
  {
    GEN a = gmul(Pi2n(1,T.prec), mului(12, T.c));
    y = gsub(y, mulcxI(gdiv(a, gmul(T.w2, T.W2))));
  }
  else if (k==4 && flag) y = gdivgs(y,  12);
  else if (k==6 && flag) y = gdivgs(y,-216);
  return gerepileupto(av,y);
}

/* return quasi-periods associated to [T->W1,T->W2] */
static GEN
_elleta(ellred_t *T)
{
  GEN y1, y2, e2 = gdivgs(_elleisnum(T,2), 12);
  y2 = gmul(T->W2, e2);
  y1 = gadd(PiI2div(T->W2, T->prec), gmul(T->W1,e2));
  retmkvec2(gneg(y1), gneg(y2));
}

/* compute eta1, eta2 */
GEN
elleta(GEN om, long prec)
{
  pari_sp av = avma;
  GEN y1, y2, E2, pi;
  ellred_t T;

  if (!check_periods(om, &T)) pari_err_TYPE("elleta",om);
  if (T.type == t_PER_ELL) return ellR_eta(om, prec);

  compute_periods(&T, NULL, prec);
  prec = T.prec;
  pi = mppi(prec);
  E2 = trueE2(T.Tau, prec); /* E_2(Tau) */
  if (signe(T.c))
  {
    GEN u = gdiv(T.w2, T.W2);
    /* E2 := u^2 E2 + 6iuc/pi = E_2(tau) */
    E2 = gadd(gmul(gsqr(u), E2), mulcxI(gdiv(gmul(mului(6,T.c), u), pi)));
  }
  y2 = gdiv(gmul(E2, sqrr(pi)), gmulsg(3, T.w2));
  if (T.swap)
  {
    y1 = y2;
    y2 = gadd(gmul(T.tau,y1), PiI2div(T.w2, prec));
  }
  else
    y1 = gsub(gmul(T.tau,y2), PiI2div(T.w2, prec));
  switch(typ(T.w1))
  {
    case t_INT: case t_FRAC: case t_REAL:
      y1 = real_i(y1);
  }
  return gerepilecopy(av, mkvec2(y1,y2));
}
GEN
ellperiods(GEN w, long flag, long prec)
{
  pari_sp av = avma;
  ellred_t T;
  if (!get_periods(w, NULL, &T, prec)) pari_err_TYPE("ellperiods",w);
  switch(flag)
  {
    case 0: return gerepilecopy(av, mkvec2(T.W1, T.W2));
    case 1: return gerepilecopy(av, mkvec2(mkvec2(T.W1, T.W2), _elleta(&T)));
    default: pari_err_FLAG("ellperiods");
             return NULL;/*not reached*/
  }
}

/* 2Pi Im(z)/log(2) */
static double
get_toadd(GEN z) { return (2*M_PI/LOG2)*gtodouble(imag_i(z)); }

/* computes the numerical value of wp(z | L), L = om1 Z + om2 Z
 * return NULL if z in L.  If flall=1, compute also wp' */
static GEN
ellwpnum_all(GEN e, GEN z, long flall, long prec)
{
  long toadd;
  pari_sp av = avma, av1;
  GEN pi2, q, u, y, yp, u1, u2, qn;
  ellred_t T;
  int simple_case;

  if (!get_periods(e, z, &T, prec)) pari_err_TYPE("ellwp",e);
  if (!T.Z) return NULL;
  prec = T.prec;

  /* Now L,Z normalized to <1,tau>. Z in fund. domain of <1, tau> */
  pi2 = Pi2n(1, prec);
  q = expIxy(pi2, T.Tau, prec);
  u = expIxy(pi2, T.Z, prec);
  u1 = gsubsg(1,u);
  u2 = gsqr(u1); /* (1-u)^2 = -4u sin^2(Pi Z) */
  if (gequal0(gnorm(u2))) return NULL; /* possible if loss of accuracy */
  y = gdiv(u,u2); /* -1/4(sin^2(Pi Z)) */
  if (T.abs_u_is_1) y = real_i(y);
  simple_case = T.abs_u_is_1 && T.q_is_real;
  y = gadd(mkfrac(gen_1, utoipos(12)), y);
  yp = flall? gen_0: NULL;
  toadd = (long)ceil(get_toadd(T.Z));

  av1 = avma; qn = q;
  for(;;)
  { /* y += u q^n [ 1/(1-q^n u)^2 + 1/(q^n-u)^2 ] - 2q^n /(1-q^n)^2 */
    /* analogous formula for yp */
    GEN yadd, ypadd = NULL;
    GEN qnu = gmul(qn,u); /* q^n u */
    GEN a = gsubsg(1,qnu);/* 1 - q^n u */
    GEN a2 = gsqr(a);     /* (1 - q^n u)^2 */
    if (yp) ypadd = gdiv(gaddsg(1,qnu),gmul(a,a2));
    if (simple_case) /* conj(u) = 1/u: formula simplifies */
      yadd = gmul2n(real_i(gdiv(u,a2)), 1);
    else
    {
      GEN b = gsub(qn,u);/* q^n - u */
      GEN b2 = gsqr(b);  /* (q^n - u)^2 */
      yadd = gmul(u, gadd(ginv(a2),ginv(b2)));
      if (yp) ypadd = gadd(ypadd, gdiv(gadd(qn,u),gmul(b,b2)));
    }
    yadd = gsub(yadd, gmul2n(ginv(gsqr(gsubsg(1,qn))), 1));
    y = gadd(y, gmul(qn,yadd));
    if (yp) yp = gadd(yp, gmul(qn,ypadd));

    qn = gmul(q,qn);
    if (gexpo(qn) <= - prec2nbits(prec) - 5 - toadd) break;
    if (gc_needed(av1,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ellwp");
      gerepileall(av1, flall? 3: 2, &y, &qn, &yp);
    }
  }
  if (yp)
  {
    if (simple_case) yp = gsub(yp, gconj(gmul(yp,gsqr(u))));
    yp = gadd(yp, gdiv(gaddsg(1,u), gmul(u1,u2)));
  }

  u1 = gdiv(pi2, mulcxmI(T.W2));
  u2 = gsqr(u1);
  y = gmul(u2,y); /* y *= (2i pi / w2)^2 */
  if (T.some_q_is_real && (T.some_z_is_real || T.some_z_is_pure_imag))
    y = real_i(y);
  if (yp)
  {
    yp = gmul(u, gmul(gmul(u1,u2),yp));/* yp *= u (2i pi / w2)^3 */
    if (T.some_q_is_real && T.some_z_is_real) yp = real_i(yp);
    y = mkvec2(y, gmul2n(yp,-1));
  }
  return gerepilecopy(av, y);
}
static GEN
ellwpseries_aux(GEN c4, GEN c6, long v, long PRECDL)
{
  long i, k, l;
  pari_sp av;
  GEN t, res = cgetg(PRECDL+2,t_SER), *P = (GEN*)(res + 2);

  res[1] = evalsigne(1) | _evalvalp(-2) | evalvarn(v);
  if (!PRECDL) { setsigne(res,0); return res; }

  for (i=1; i<PRECDL; i+=2) P[i]= gen_0;
  switch(PRECDL)
  {
    default:P[6] = gdivgs(c6,6048);
    case 6:
    case 5: P[4] = gdivgs(c4, 240);
    case 4:
    case 3: P[2] = gen_0;
    case 2:
    case 1: P[0] = gen_1;
    case 0: break;
  }
  if (PRECDL <= 8) return res;
  av = avma;
  P[8] = gerepileupto(av, gdivgs(gsqr(P[4]), 3));
  for (k=5; (k<<1) < PRECDL; k++)
  {
    av = avma;
    t = gmul(P[4], P[(k-2)<<1]);
    for (l=3; (l<<1) < k; l++) t = gadd(t, gmul(P[l<<1], P[(k-l)<<1]));
    t = gmul2n(t, 1);
    if ((k & 1) == 0) t = gadd(gsqr(P[k]), t);
    if (k % 3 == 2)
      t = gdivgs(gmulsg(3, t), (k-3)*(2*k+1));
    else /* same value, more efficient */
      t = gdivgs(t, ((k-3)*(2*k+1)) / 3);
    P[k<<1] = gerepileupto(av, t);
  }
  return res;
}

static int
get_c4c6(GEN w, GEN *c4, GEN *c6, long prec)
{
  if (typ(w) == t_VEC) switch(lg(w))
  {
    case 17:
      *c4 = ell_get_c4(w);
      *c6 = ell_get_c6(w);
      return 1;
    case 3:
    {
      ellred_t T;
      if (!get_periods(w,NULL,&T, prec)) break;
      *c4 = _elleisnum(&T, 4);
      *c6 = gneg(_elleisnum(&T, 6));
      return 1;
    }
  }
  *c4 = *c6 = NULL;
  return 0;
}

GEN
ellwpseries(GEN e, long v, long PRECDL)
{
  GEN c4, c6;
  checkell(e);
  c4 = ell_get_c4(e);
  c6 = ell_get_c6(e); return ellwpseries_aux(c4,c6,v,PRECDL);
}

GEN
ellwp(GEN w, GEN z, long prec)
{ return ellwp0(w,z,0,prec); }

GEN
ellwp0(GEN w, GEN z, long flag, long prec)
{
  pari_sp av = avma;
  GEN y;

  if (flag && flag != 1) pari_err_FLAG("ellwp");
  if (!z) z = pol_x(0);
  y = toser_i(z);
  if (y)
  {
    long vy = varn(y), v = valp(y);
    GEN P, Q, c4,c6;
    if (!get_c4c6(w,&c4,&c6,prec)) pari_err_TYPE("ellwp",w);
    if (v <= 0) pari_err(e_IMPL,"ellwp(t_SER) away from 0");
    if (gequal0(y)) {
      avma = av;
      if (!flag) return zeroser(vy, -2*v);
      retmkvec2(zeroser(vy, -2*v), zeroser(vy, -3*v));
    }
    P = ellwpseries_aux(c4,c6, vy, lg(y)-2);
    Q = gsubst(P, varn(P), y);
    if (!flag)
      return gerepileupto(av, Q);
    else
    {
      GEN R = mkvec2(Q, gdiv(derivser(Q), derivser(y)));
      return gerepilecopy(av, R);
    }
  }
  y = ellwpnum_all(w,z,flag,prec);
  if (!y) pari_err_DOMAIN("ellwp", "argument","=", gen_0,z);
  return gerepileupto(av, y);
}

GEN
ellzeta(GEN w, GEN z, long prec0)
{
  long prec;
  pari_sp av = avma;
  GEN pi2, q, u, v, y, et = NULL;
  ellred_t T;
  int simple_case;

  if (!z) z = pol_x(0);
  y = toser_i(z);
  if (y)
  {
    long vy = varn(y), v = valp(y);
    GEN P, Q, c4,c6;
    if (!get_c4c6(w,&c4,&c6,prec0)) pari_err_TYPE("ellzeta",w);
    if (v <= 0) pari_err(e_IMPL,"ellzeta(t_SER) away from 0");
    if (gequal0(y)) { avma = av; return zeroser(vy, -v); }
    P = ellwpseries_aux(c4,c6, vy, lg(y)-2);
    P = integser(gneg(P)); /* \zeta' = - \wp*/
    Q = gsubst(P, varn(P), y);
    return gerepileupto(av, Q);
  }
  if (!get_periods(w, z, &T, prec0)) pari_err_TYPE("ellzeta", w);
  if (!T.Z) pari_err_DOMAIN("ellzeta", "z", "=", gen_0, z);
  prec = T.prec;
  if (signe(T.x) || signe(T.y)) et = eta_correction(&T, _elleta(&T));

  pi2 = Pi2n(1, prec);
  q = expIxy(pi2, T.Tau, prec);
  u = expIxy(pi2, T.Z, prec);
  simple_case = T.abs_u_is_1 && T.q_is_real;

  y = mulcxI(gmul(trueE2(T.Tau,prec), gmul(T.Z,divrs(pi2,-12))));
  v = gadd(ghalf, ginv(gsubgs(u, 1)));
  if (T.abs_u_is_1) gel(v,1) = gen_0; /*v = (u+1)/2(u-1), pure imaginary*/
  y = gadd(y, v);

  if (!simple_case)/* otherwise |u|=1 and all terms in sum are 0 */
  {
    long toadd = (long)ceil(get_toadd(T.Z));
    pari_sp av1 = avma;
    GEN qn;
    for (qn = q;;)
    { /* y += sum q^n ( u/(u*q^n - 1) + 1/(u - q^n) ) */
      GEN p1 = gadd(gdiv(u,gsubgs(gmul(qn,u),1)), ginv(gsub(u,qn)));
      y = gadd(y, gmul(qn,p1));
      qn = gmul(q,qn);
      if (gexpo(qn) <= - prec2nbits(prec) - 5 - toadd) break;
      if (gc_needed(av1,1))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"ellzeta");
        gerepileall(av1,2, &y,&qn);
      }
    }
  }
  y = mulcxI(gmul(gdiv(pi2,T.W2), y));
  if (et) y = gadd(y,et);
  if (T.some_q_is_real)
  {
    if (T.some_z_is_real)
      y = real_i(y);
    else if (T.some_z_is_pure_imag)
      gel(y,1) = gen_0;
  }
  return gerepilecopy(av, y);
}

/* if flag=0, return ellsigma, otherwise return log(ellsigma) */
GEN
ellsigma(GEN w, GEN z, long flag, long prec0)
{
  long toadd, prec, n;
  pari_sp av = avma, av1;
  GEN zinit, pi, pi2, q, q8, qn2, qn, y, y1, uinv, et, etnew;
  GEN u, uhalf, urn, urninv;
  ellred_t T;

  if (flag < 0 || flag > 1) pari_err_FLAG("ellsigma");

  if (!z) z = pol_x(0);
  y = toser_i(z);
  if (y)
  {
    long vy = varn(y), v = valp(y);
    GEN P, Q, c4,c6;
    if (!get_c4c6(w,&c4,&c6,prec0)) pari_err_TYPE("ellsigma",w);
    if (v <= 0) pari_err_IMPL("ellsigma(t_SER) away from 0");
    if (flag) pari_err_TYPE("log(ellsigma)",y);
    if (gequal0(y)) { avma = av; return zeroser(vy, -v); }
    P = ellwpseries_aux(c4,c6, vy, lg(y)-2);
    P = integser(gneg(P)); /* \zeta' = - \wp*/
    /* (log \sigma)' = \zeta; remove log-singularity first */
    P = integser(gsub(P, monomial(gen_1,-1,vy)));
    P = gexp(P, prec0);
    setvalp(P, valp(P)+1);
    Q = gsubst(P, varn(P), y);
    return gerepileupto(av, Q);
  }
  if (!get_periods(w, z, &T, prec0)) pari_err_TYPE("ellsigma",w);
  if (!T.Z)
  {
    if (!flag) return gen_0;
    pari_err_DOMAIN("log(ellsigma)", "argument","=",gen_0,z);
  }
  prec = T.prec;
  pi2 = Pi2n(1,prec);
  pi  = mppi(prec);

  toadd = (long)ceil(fabs( get_toadd(T.Z) ));
  uhalf = expIxy(pi, T.Z, prec); /* exp(i Pi Z) */
  u = gsqr(uhalf);
  q8 = expIxy(gmul2n(pi2,-3), T.Tau, prec);
  q = gpowgs(q8,8);
  u = gneg_i(u); uinv = ginv(u);
  y = gen_0;
  av1 = avma;
  qn = q; qn2 = gen_1;
  urn = uhalf; urninv = ginv(uhalf);
  for(n=0;;n++)
  {
    y = gadd(y,gmul(qn2,gsub(urn,urninv)));
    qn2 = gmul(qn,qn2);
    if (gexpo(qn2) + n*toadd <= - prec2nbits(prec) - 5) break;
    qn  = gmul(q,qn);
    urn = gmul(urn,u);
    urninv = gmul(urninv,uinv);
    if (gc_needed(av1,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ellsigma");
      gerepileall(av1,5, &y,&qn,&qn2,&urn,&urninv);
    }
  }
  y = gmul(gmul(y,q8),
           gdiv(mulcxmI(T.W2), gmul(pi2,gpowgs(trueeta(T.Tau,prec),3))));

  et = _elleta(&T);
  etnew = eta_correction(&T, et);
  zinit = gmul(T.Z,T.W2);
  etnew = gmul(etnew, gadd(zinit,
                           gmul2n(gadd(gmul(T.x,T.W1), gmul(T.y,T.W2)),-1)));
  if (mpodd(T.x) || mpodd(T.y)) etnew = gadd(etnew, mulcxI(pi));
  y1 = gadd(etnew, gmul2n(gmul(gmul(T.Z,zinit),gel(et,2)),-1));
  if (flag)
  {
    y = gadd(y1, glog(y,prec));
    if (T.some_q_is_real && T.some_z_is_real)
    { /* y = log(some real number): im(y) is 0 or Pi */
      if (gexpo(imag_i(y)) < 1) y = real_i(y);
    }
  }
  else
  {
    y = gmul(y, gexp(y1,prec));
    if (T.some_q_is_real)
    {
      if (T.some_z_is_real)
        y = real_i(y);
      else if (T.some_z_is_pure_imag)
        gel(y,1) = gen_0;
    }
  }
  return gerepilecopy(av, y);
}

GEN
pointell(GEN e, GEN z, long prec)
{
  pari_sp av = avma;
  GEN v;

  checkell(e);
  v = ellwpnum_all(e,z,1,prec);
  if (!v) { avma = av; return ellinf(); }
  gel(v,1) = gsub(gel(v,1), gdivgs(ell_get_b2(e),12));
  gel(v,2) = gsub(gel(v,2), gmul2n(ec_h_evalx(e,gel(v,1)),-1));
  return gerepilecopy(av, v);
}

/********************************************************************/
/**                                                                **/
/**                 Tate's algorithm e (cf Anvers IV)              **/
/**               Kodaira types, global minimal model              **/
/**                                                                **/
/********************************************************************/

/* Given an integral elliptic curve in ellinit form, and a prime p, returns the
  type of the fiber at p of the Neron model, as well as the change of variables
  in the form [f, kod, v, c].

  * The integer f is the conductor's exponent.

  * The integer kod is the Kodaira type using the following notation:
    II , III , IV  -->  2, 3, 4
    I0  -->  1
    Inu --> 4+nu for nu > 0
  A '*' negates the code (e.g I* --> -2)

  * v is a quadruple [u, r, s, t] yielding a minimal model

  * c is the Tamagawa number.

  Uses Tate's algorithm (Anvers IV). Given the remarks at the bottom of
  page 46, the "long" algorithm is used for p = 2,3 only. */
static GEN
localred_result(long f, long kod, long c, GEN v)
{
  GEN z = cgetg(5, t_VEC);
  gel(z,1) = stoi(f);
  gel(z,2) = stoi(kod);
  gel(z,3) = gcopy(v);
  gel(z,4) = stoi(c); return z;
}
static GEN
localredbug(GEN p, const char *s)
{
  if (BPSW_psp(p)) pari_err_BUG(s);
  pari_err_PRIME("localred",p);
  return NULL; /* not reached */
}

/* v_p( denom(j(E)) ) >= 0 */
static long
j_pval(GEN E, GEN p) { return Z_pval(Q_denom(ell_get_j(E)), p); }

#if 0
/* Here p > 3. e assumed integral, return v_p(N). Simplified version of
 * localred_p */
static long
localred_p_get_f(GEN e, GEN p)
{
  long nuj, nuD;
  GEN D = ell_get_disc(e);
  nuj = j_pval(e, p);
  nuD = Z_pval(D, p);
  if (nuj == 0) return (nuD % 12)? 2 : 0;
  return (nuD - nuj) % 12 ? 2: 1;
}
#endif
/* p > 3, e integral */
static GEN
localred_p(GEN e, GEN p)
{
  long k, f, kod, c, nuj, nuD;
  GEN p2, v, tri, c4, c6, D = ell_get_disc(e);

  c4 = ell_get_c4(e);
  c6 = ell_get_c6(e);
  nuj = j_pval(e, p);
  nuD = Z_pval(D, p);
  k = (nuD - nuj) / 12;
  if (k <= 0) v = init_ch();
  else
  { /* model not minimal */
    GEN pk = powiu(p,k), p2k = sqri(pk), p4k = sqri(p2k), p6k = mulii(p4k,p2k);
    GEN r, s, t;

    s = negi(ell_get_a1(e));
    if (mpodd(s)) s = addii(s, pk);
    s = shifti(s, -1);

    r = subii(ell_get_a2(e), mulii(s, addii(ell_get_a1(e), s)));
    switch(umodiu(r, 3))
    {
      default: break; /* 0 */
      case 2: r = addii(r, p2k); break;
      case 1: r = subii(r, p2k); break;
    }
    r = negi( diviuexact(r, 3) );

    t = negi(Zec_h_evalx(e,r));
    if (mpodd(t)) t = addii(t, mulii(pk, p2k));
    t = shifti(t, -1);

    v = mkvec4(pk,r,s,t);
    nuD -= 12 * k;
    c4 = diviiexact(c4, p4k);
    c6 = diviiexact(c6, p6k);
    D = diviiexact(D, sqri(p6k));
  }

  if (nuj > 0) switch(nuD - nuj)
  {
    case 0: f = 1; kod = 4+nuj; /* Inu */
      switch(kronecker(negi(c6),p))
      {
        case  1: c = nuD; break;
        case -1: c = odd(nuD)? 1: 2; break;
        default: return localredbug(p,"localred (p | c6)");
      }
      break;
    case 6:
    {
      GEN d = Fp_red(diviiexact(D, powiu(p, 6+nuj)), p);
      if (nuj & 1) d = Fp_mul(d, diviiexact(c6, powiu(p,3)), p);
      f = 2; kod = -4-nuj; c = 3 + kronecker(d, p); /* Inu* */
      break;
    }
    default: return localredbug(p,"localred (nu_D - nu_j != 0,6)");
  }
  else switch(nuD)
  {
    case  0: f = 0; kod = 1; c = 1; break; /* I0, regular */
    case  2: f = 2; kod = 2; c = 1; break; /* II   */
    case  3: f = 2; kod = 3; c = 2; break; /* III  */
    case  4: f = 2; kod = 4; /* IV   */
      c = 2 + krosi(-6,p) * kronecker(diviiexact(c6,sqri(p)), p);
      break;
    case  6: f = 2; kod = -1; /* I0*  */
      p2 = sqri(p);
      /* x^3 - 3c4/p^2 x - 2c6/p^3 */
      tri = mkpoln(4, gen_1, gen_0,
                            negi(mului(3, diviiexact(c4, p2))),
                            negi(shifti(diviiexact(c6, mulii(p2,p)), 1)));
      c = 1 + FpX_nbroots(tri, p);
      break;
    case  8: f = 2; kod = -4; /* IV*  */
      c = 2 + krosi(-6,p) * kronecker(diviiexact(c6, sqri(sqri(p))), p);
      break;
    case  9: f = 2; kod = -3; c = 2; break; /* III* */
    case 10: f = 2; kod = -2; c = 1; break; /* II*  */
    default: return localredbug(p,"localred");
  }
  return localred_result(f, kod, c, v);
}

/* return a_{ k,l } in Tate's notation, pl = p^l */
static ulong
aux(GEN ak, ulong q, ulong pl)
{
  return umodiu(ak, q) / pl;
}

static ulong
aux2(GEN ak, ulong p, GEN pl)
{
  pari_sp av = avma;
  ulong res = umodiu(diviiexact(ak, pl), p);
  avma = av; return res;
}

/* number of distinct roots of X^3 + aX^2 + bX + c modulo p = 2 or 3
 * assume a,b,c in {0, 1} [ p = 2 ] or {0, 1, 2} [ p = 3 ]
 * if there's a multiple root, put it in *mult */
static long
numroots3(long a, long b, long c, long p, long *mult)
{
  if (p == 2)
  {
    if ((c + a * b) & 1) return 3;
    *mult = b; return (a + b) & 1 ? 2 : 1;
  }
  /* p = 3 */
  if (!a) { *mult = -c; return b ? 3 : 1; }
  *mult = a * b;
  if (b == 2)
    return (a + c) == 3 ? 2 : 3;
  else
    return c ? 3 : 2;
}

/* same for aX^2 +bX + c */
static long
numroots2(long a, long b, long c, long p, long *mult)
{
  if (p == 2) { *mult = c; return b & 1 ? 2 : 1; }
  /* p = 3 */
  *mult = a * b; return (b * b - a * c) % 3 ? 2 : 1;
}

/* p = 2 or 3 */
static GEN
localred_23(GEN e, long p)
{
  long c, nu, nuD, r, s, t;
  long theroot, p2, p3, p4, p5, p6, a21, a42, a63, a32, a64;
  GEN v;

  nuD = Z_lval(ell_get_disc(e), (ulong)p);
  v = init_ch();
  if (p == 2) { p2 = 4; p3 = 8;  p4 = 16; p5 = 32; p6 = 64;}
  else        { p2 = 9; p3 = 27; p4 = 81; p5 =243; p6 =729; }

  for (;;)
  {
    if (!nuD) return localred_result(0, 1, 1, v);
        /* I0   */
    if (umodiu(ell_get_b2(e), p)) /* p \nmid b2 */
    {
      if (umodiu(negi(ell_get_c6(e)), p == 2 ? 8 : 3) == 1)
        c = nuD;
      else
        c = 2 - (nuD & 1);
      return localred_result(1, 4 + nuD, c, v);
    }
        /* Inu  */
    if (p == 2)
    {
      r = umodiu(ell_get_a4(e), 2);
      s = umodiu(ell_get_a2(e), 2);
      t = umodiu(ell_get_a6(e), 2);
      if (r) { t = (s + t) & 1; s = (s + 1) & 1; }
    }
    else /* p == 3 */
    {
      r = - umodiu(ell_get_b6(e), 3);
      s = umodiu(ell_get_a1(e), 3);
      t = umodiu(ell_get_a3(e), 3);
      if (s) { t  = (t + r*s) % 3; if (t < 0) t += 3; }
    }
    /* p | (a1, a2, a3, a4, a6) */
    if (r || s || t) E_compose_rst(&v, &e, stoi(r), stoi(s), stoi(t));
    if (umodiu(ell_get_a6(e), p2))
      return localred_result(nuD, 2, 1, v);
        /* II   */
    if (umodiu(ell_get_b8(e), p3))
      return localred_result(nuD - 1, 3, 2, v);
        /* III  */
    if (umodiu(ell_get_b6(e), p3))
    {
      if (umodiu(ell_get_b6(e), (p==2)? 32: 27) == (ulong)p2)
        c = 3;
      else
        c = 1;
      return localred_result(nuD - 2, 4, c, v);
    }
        /* IV   */

    if (umodiu(ell_get_a6(e), p3))
      E_compose_t(&v, &e, p == 2? gen_2: modis(ell_get_a3(e), 9));
        /* p | a1, a2; p^2  | a3, a4; p^3 | a6 */
    a21 = aux(ell_get_a2(e), p2, p);
    a42 = aux(ell_get_a4(e), p3, p2);
    a63 = aux(ell_get_a6(e), p4, p3);
    switch (numroots3(a21, a42, a63, p, &theroot))
    {
      case 3:
        c = a63 ? 1: 2;
        if (p == 2)
          c += ((a21 + a42 + a63) & 1);
        else {
          if (((1 + a21 + a42 + a63) % 3) == 0) c++;
          if (((1 - a21 + a42 - a63) % 3) == 0) c++;
        }
        return localred_result(nuD - 4, -1, c, v);
      case 2: /* I0*  */
      { /* compute nu */
        GEN pk, pk1, p2k;
        long al, be, ga;
        if (theroot) E_compose_r(&v, &e, stoi(theroot * p));
            /* p | a1; p^2  | a2, a3; p^3 | a4; p^4 | a6 */
        nu = 1;
        pk  = utoipos(p2);
        p2k = utoipos(p4);
        for(;;)
        {
          be =  aux2(ell_get_a3(e), p, pk);
          ga = -aux2(ell_get_a6(e), p, p2k);
          al = 1;
          if (numroots2(al, be, ga, p, &theroot) == 2) break;
          if (theroot) E_compose_t(&v, &e, mulsi(theroot,pk));
          pk1 = pk;
          pk  = mului(p, pk);
          p2k = mului(p, p2k); nu++;

          al = a21;
          be = aux2(ell_get_a4(e), p, pk);
          ga = aux2(ell_get_a6(e), p, p2k);
          if (numroots2(al, be, ga, p, &theroot) == 2) break;
          if (theroot) E_compose_r(&v, &e, mulsi(theroot, pk1));
          p2k = mului(p, p2k); nu++;
        }
        if (p == 2)
          c = 4 - 2 * (ga & 1);
        else
          c = 3 + kross(be * be - al * ga, 3);
        return localred_result(nuD - 4 - nu, -4 - nu, c, v);
      }
      case 1: /* Inu* */
        if (theroot) E_compose_r(&v, &e, stoi(theroot*p));
            /* p | a1; p^2  | a2, a3; p^3 | a4; p^4 | a6 */
        a32 = aux(ell_get_a3(e), p3, p2);
        a64 = aux(ell_get_a6(e), p5, p4);
        if (numroots2(1, a32, -a64, p, &theroot) == 2)
        {
          if (p == 2)
            c = 3 - 2 * a64;
          else
            c = 2 + kross(a32 * a32 + a64, 3);
          return localred_result(nuD - 6, -4, c, v);
        }
            /* IV*  */
        if (theroot) E_compose_t(&v, &e, stoi(theroot*p2));
            /* p | a1; p^2 | a2; p^3 | a3, a4; p^5 | a6 */
        if (umodiu(ell_get_a4(e), p4))
          return localred_result(nuD - 7, -3, 2, v);
            /* III* */

        if (umodiu(ell_get_a6(e), p6))
          return localred_result(nuD - 8, -2, 1, v);
            /* II*  */
        E_compose_u(&v, &e, utoipos(p)); /* not minimal */
        nuD -= 12;
    }
  }
}

static GEN
localred(GEN e, GEN p)
{
  if (cmpiu(p, 3) > 0) /* p != 2,3 */
    return localred_p(e,p);
  else
  {
    long l = itos(p);
    if (l < 2) pari_err_PRIME("localred",p);
    return localred_23(e, l);
  }
}

/* Given J an ideal in HNF coprime to 2 and z algebraic integer,
 * return b algebraic integer such that z + 2b in  J */
static GEN
approx_mod2(GEN J, GEN z)
{
  GEN b = z;
  long i;
  if (typ(b) == t_INT)
  {
    if (mpodd(b)) b = addii(b, gcoeff(J,1,1));
    return shifti(negi(b),-1);
  }
  for (i = lg(J)-1; i >= 1; i--)
  {
    if (mpodd(gel(b,i))) b = ZC_add(b, gel(J,i));
  }
  return gshift(ZC_neg(b), -1);
}

/* Given J an ideal in HNF coprime to 3 and z algebraic integer,
 * return b algebraic integer such that z + 3b in  J */
static GEN
approx_mod3(GEN J, GEN z)
{
  GEN b = z;
  long i;
  if (typ(b) == t_INT)
  {
    long s = smodis(b,3);
    if (s)
    {
      GEN Jz = gcoeff(J,1,1);
      if (smodis(Jz, 3) == s)
        b = subii(b, Jz);
      else
        b = addii(b, Jz);
    }
    return diviiexact(b, stoi(-3));
  }
  for (i = lg(J)-1; i >= 1; i--)
  {
    long s = smodis(gel(b,i), 3);
    if (!s) continue;
    if (smodis(gcoeff(J,i,i), 3) == s)
      b = ZC_sub(b, gel(J,i));
    else
      b = ZC_add(b, gel(J,i));
  }
  return ZC_Z_divexact(b, stoi(-3));
}

/* Local reduction, residual characteristic >= 5. E/nf, P prid
* Output: f, kod, [u,r,s,t], c */
static GEN
nflocalred_p(GEN e, GEN P)
{
  GEN nf = ellnf_get_nf(e), T,p, modP = nf_to_Fq_init(nf,&P,&T,&p);
  long c, f, vD, nuj, kod, m;
  GEN ch, c4, c6, D, z, pi, piinv;

  c4 = ell_get_c4(e);
  c6 = ell_get_c6(e);
  D = ell_get_disc(e);
  vD = nfval(nf,D,P);
  nuj = nfval(nf,ell_get_j(e),P);
  nuj = nuj >= 0? 0: -nuj; /* v_P(denom(j)) */
  m = (vD - nuj)/12;
  piinv = pr_get_tau(P);
  if (typ(piinv) == t_MAT) piinv = gel(piinv,1);
  piinv = gdiv(piinv, p); /* v_P(piinv) = -1, v_Q(piinv) >= 0, Q!=P */
  pi = nfinv(nf, piinv); /* local uniformizer */

  if(m <= 0) ch = init_ch();
  else
  { /* model not minimal */
    GEN r,s,t, a1,a2,a3, u,ui,ui2,ui4,ui6,ui12;
    u = nfpow_u(nf,pi,m);
    ui = nfpow_u(nf,piinv,m);
    ui2 = nfsqr(nf,ui);
    ui4 = nfsqr(nf,ui2);
    ui6 = nfmul(nf,ui2,ui4);
    ui12 = nfsqr(nf,ui6);
    c4 = nfmul(nf,c4,ui4);
    c6 = nfmul(nf,c6,ui6);
    D = nfmul(nf,D,ui12);  vD -= 12*m;
    a1 = nf_to_scalar_or_basis(nf, ell_get_a1(e));
    a2 = nf_to_scalar_or_basis(nf, ell_get_a2(e));
    a3 = nf_to_scalar_or_basis(nf, ell_get_a3(e));
    s = approx_mod2(idealpow(nf,P,stoi(m)),   a1);
    r = gsub(a2, nfmul(nf,s,gadd(a1,s)));
    r = approx_mod3(idealpow(nf,P,stoi(2*m)), r);
    t = gadd(a3, nfmul(nf,r,a1));
    t = approx_mod2(idealpow(nf,P,stoi(3*m)), t);
    ch = mkvec4(u,r,s,t);
  }

  kod = 0; c = 1;
  /* minimal at P */
  if (nuj > 0)
  { /* v(j) < 0 */
    if (vD == nuj)
    { /* v(c4) = v(c6) = 0, multiplicative reduction */
      f = 1; kod = 4+vD;
      z = Fq_neg(nf_to_Fq(nf,c6,modP), T,p);
      if (Fq_issquare(z,T,p))
        c = vD;/* split */
      else
        c = odd(vD)?1 : 2; /* non-split */
    }
    else
    { /* v(c4) = 2, v(c6) = 3, potentially multiplicative */
      GEN Du;
      f = 2; kod = 2-vD;
      (void)nfvalrem(nf, D, P, &Du);
      z = nf_to_Fq(nf, Du, modP);
      if(odd(vD))
      {
        GEN c6u;
        (void)nfvalrem(nf, c6, P, &c6u);
        c6u = nf_to_Fq(nf, c6u, modP);
        z = Fq_mul(z, c6u, T,p);
      }
      c = Fq_issquare(z,T,p)? 4: 2;
    }
  }
  else
  { /* v(j) >= 0 */
    f = vD? 2: 0;
    switch(vD)
    {
      GEN piinv2, piinv3, piinv4, w;
      case 0: kod = 0; c = 1; break;
      case 2: kod = 2; c = 1; break;
      case 3: kod = 3; c = 2; break;
      case 4: kod = 4;
        z = nfmul(nf,c6,nfsqr(nf,piinv));
        z = nf_to_Fq(nf, z, modP);
        z = Fq_Fp_mul(z,stoi(-6),T,p);
        c = Fq_issquare(z,T,p)? 3: 1;
        break;
      case 6: kod = -1;
        piinv2 = nfsqr(nf,piinv);
        piinv3 = nfmul(nf,piinv,piinv2);
        z = nfmul(nf,c4,piinv2); z = nf_to_Fq(nf, z, modP);
        z = Fq_Fp_mul(z,stoi(-3), T,p);
        w = nfmul(nf,c6,piinv3); w = nf_to_Fq(nf, w, modP);
        w = Fq_Fp_mul(w,gen_m2, T,p);
        c = 1 + FqX_nbroots(mkpoln(4, gen_1,gen_0,z,w), T,p);
        break;
      case 8: kod = -4;
        piinv4 = nfpow_u(nf,piinv,4);
        z = nfmul(nf,c6,piinv4); z = nf_to_Fq(nf, z, modP);
        z = Fq_Fp_mul(z,stoi(-6),T,p);
        c = Fq_issquare(z,T,p)? 3: 1;
        break;
      case 9: kod = -3; c = 2; break;
      case 10: kod = -2; c = 1; break;
    }
  }
  return localred_result(f,kod,c,ch);
}
static GEN
nflocalred(GEN e, GEN  pr)
{
  GEN p = pr_get_p(pr);
  if (cmpiu(p, 3) <= 0) pari_err_IMPL("nflocalred (p < 5)");
  return nflocalred_p(e,pr);
}

GEN
elllocalred(GEN e, GEN p)
{
  pari_sp av = avma;
  checkell(e);
  switch(ell_get_type(e))
  {
    case t_ELL_Q:
      if (typ(ell_get_disc(e)) != t_INT)
        pari_err_TYPE("elllocalred [not an integral curve]",e);
      if (typ(p) != t_INT) pari_err_TYPE("elllocalred [prime]",p);
      if (signe(p) <= 0) pari_err_PRIME("elllocalred",p);
      return gerepileupto(av, localred(e, p));
    default: pari_err_TYPE("elllocalred", e);
    case t_ELL_NF:
      checkprid(p);
      return gerepileupto(av, nflocalred(e, p));
  }
}

/* typ(c) = t_INT or t_FRAC */
static GEN
handle_Q(GEN c, GEN *pd)
{
  *pd = (typ(c) == t_INT)? NULL: gel(c,2);
  return c;
}
static GEN
handle_coeff(GEN nf, GEN c, GEN *pd)
{
  *pd = NULL;
  switch(typ(c))
  {
    case t_INT: *pd = NULL; return c;
    case t_FRAC: *pd = gel(c,2); return c;
    case t_POL: case t_POLMOD: case t_COL:
      if (nf)
      {
        c = nf_to_scalar_or_basis(nf,c);
        return handle_Q(Q_content(c), pd);
      }
    default: pari_err_TYPE("ellintegralmodel",c);
      return NULL;
  }
}
/* Return an integral model for e / Q. Set v = NULL (already integral)
 * or the variable change [u,0,0,0], u = 1/t, t > 1 integer making e integral */
GEN
ellintegralmodel(GEN e, GEN *pv)
{
  GEN a = cgetg(6,t_VEC), t, u, L, nf;
  long i, l, k;

  nf = (ell_get_type(e) == t_ELL_NF)?checknf(ellnf_get_nf(e)): NULL;
  L = cgetg(1, t_VEC);
  for (i = 1; i < 6; i++)
  {
    GEN d;
    gel(a,i) = handle_coeff(nf, gel(e,i), &d);
    if (d) /* partial factorization of denominator */
      L = shallowconcat(L, gel(Z_factor_limit(d, 0),1));
  }
  /* a = [a1, a2, a3, a4, a6] */
  l = lg(L); if (l == 1) { if (pv) *pv = NULL; return e; }
  L = ZV_sort_uniq(L);
  l = lg(L);

  t = gen_1;
  for (k = 1; k < l; k++)
  {
    GEN p = gel(L,k);
    long n = 0, m;
    for (i = 1; i < 6; i++)
      if (!gequal0(gel(a,i)))
      {
        long r = (i == 5)? 6: i; /* a5 is missing */
        m = r * n + Q_pval(gel(a,i), p);
        while (m < 0) { n++; m += r; }
      }
    t = mulii(t, powiu(p, n));
  }
  u = ginv(t);
  if (pv) *pv = mkvec4(u,gen_0,gen_0,gen_0);
  return coordch_u(e, u);
}

/* FIXME: export ? */
static ulong
Mod32(GEN x) {
  long s = signe(x);
  ulong m;
  if (!s) return 0;
  m = mod32(x); if (!m) return m;
  if (s < 0) m = 32 - m;
  return m;
}
#define Mod16(x) Mod32(x)&15
#define Mod2(x) Mod32(x)&1

/* structure to hold incremental computation of standard minimal model/Q */
typedef struct {
  long a1; /*{0,1}*/
  long a2; /*{-1,0,1}*/
  long a3; /*{0,1}*/
  long b2; /* centermod(-c6, 12), in [-5,6] */
  GEN u, u2, u3, u4, u6;
  GEN a4, a6, b4, b6, b8, c4, c6, D;
} ellmin_t;

/* u from [u,r,s,t] */
static void
min_set_u(ellmin_t *M, GEN u)
{
  M->u = u;
  if (is_pm1(u))
    M->u2 = M->u3 = M->u4 = M->u6 = gen_1;
  else
  {
    M->u2 = sqri(u);
    M->u3 = mulii(M->u2, u);
    M->u4 = sqri(M->u2);
    M->u6 = sqri(M->u3);
  }
}
/* E = original curve */
static void
min_set_c(ellmin_t *M, GEN E)
{
  GEN c4 = ell_get_c4(E), c6 = ell_get_c6(E);
  if (!is_pm1(M->u4)) {
    c4 = diviiexact(c4, M->u4);
    c6 = diviiexact(c6, M->u6);
  }
  M->c4 = c4;
  M->c6 = c6;
}
static void
min_set_D(ellmin_t *M, GEN E)
{
  GEN D = ell_get_disc(E);
  if (!is_pm1(M->u6)) D = diviiexact(D, sqri(M->u6));
  M->D = D;
}
static void
min_set_b(ellmin_t *M)
{
  long b2 = Fl_center(12 - umodiu(M->c6,12), 12, 6);
  long b22 = b2*b2; /* in [0,36] */
  M->b2 = b2;
  M->b4 = diviuexact(subui(b22, M->c4), 24);
  M->b6 = diviuexact(subii(mulsi(b2, subiu(mului(36,M->b4),b22)), M->c6), 216);
}
static void
min_set_a(ellmin_t *M)
{
  long a1, a2, a3, a13, b2 = M->b2;
  GEN b4 = M->b4, b6 = M->b6;
  if (odd(b2))
  {
    a1 = 1;
    a2 = (b2 - 1) >> 2;
  }
  else
  {
    a1 = 0;
    a2 = b2 >> 2;
  }
  M->a1 = a1;
  M->a2 = a2;
  M->a3 = a3 = Mod2(b6)? 1: 0;
  a13 = a1 & a3; /* a1 * a3 */
  M->a4 = shifti(subiu(b4, a13), -1);
  M->a6 = shifti(subiu(b6, a3), -2);
}
static GEN
min_to_ell(ellmin_t *M, GEN E)
{
  GEN b8, y = obj_init(15, 8);
  long a11, a13;
  gel(y,1) = M->a1? gen_1: gen_0;
  gel(y,2) = stoi(M->a2);
  gel(y,3) = M->a3? gen_1: gen_0;
  gel(y,4) = M->a4;
  gel(y,5) = M->a6;
  gel(y,6) = stoi(M->b2);
  gel(y,7) = M->b4;
  gel(y,8) = M->b6;
  a11 = M->a1;
  a13 = M->a1 & M->a3;
  b8 = subii(addii(mului(a11,M->a6), mulis(M->b6, M->a2)),
             mulii(M->a4, addiu(M->a4,a13)));
  gel(y,9) = b8; /* a1^2 a6 + 4a6 a2 + a2 a3^2 - a4(a4 + a1 a3) */
  gel(y,10)= M->c4;
  gel(y,11)= M->c6;
  gel(y,12)= M->D;
  gel(y,13)= gel(E,13);
  gel(y,14)= gel(E,14);
  gel(y,15)= gel(E,15);
  return y;
}
static GEN
min_get_v(ellmin_t *M, GEN E)
{
  GEN r, s, t;
  r = diviuexact(subii(mulis(M->u2,M->b2), ell_get_b2(E)), 12);
  s = shifti(subii(M->a1? M->u: gen_0, ell_get_a1(E)), -1);
  t = shifti(subii(M->a3? M->u3: gen_0, ec_h_evalx(E,r)), -1);
  return mkvec4(M->u,r,s,t);
}

static long
F2_card(ulong a1, ulong a2, ulong a3, ulong a4, ulong a6)
{
  long N = 1; /* oo */
  if (!a3) N ++; /* x = 0, y=0 or 1 */
  else if (!a6) N += 2; /* x = 0, y arbitrary */
  if ((a3 ^ a1) == 0) N++; /* x = 1, y = 0 or 1 */
  else if (a2 ^ a4 ^ a6) N += 2; /* x = 1, y arbitrary */
  return N;
}
static long
F3_card(ulong b2, ulong b4, ulong b6)
{
  ulong Po = 1+2*b4, Pe = b2+b6;
  /* kro(x,3)+1 = (x+1)%3, N = 4 + sum(kro) = 1+ sum(1+kro) */
  return 1+(b6+1)%3+(Po+Pe+1)%3+(2*Po+Pe+1)%3;
}
static long
cardmod2(GEN e)
{ /* solve y(1 + a1x + a3) = x (1 + a2 + a4) + a6 */
  ulong a1 = Rg_to_F2(ell_get_a1(e));
  ulong a2 = Rg_to_F2(ell_get_a2(e));
  ulong a3 = Rg_to_F2(ell_get_a3(e));
  ulong a4 = Rg_to_F2(ell_get_a4(e));
  ulong a6 = Rg_to_F2(ell_get_a6(e));
  return F2_card(a1,a2,a3,a4,a6);
}
static long
cardmod3(GEN e)
{
  ulong b2 = Rg_to_Fl(ell_get_b2(e), 3);
  ulong b4 = Rg_to_Fl(ell_get_b4(e), 3);
  ulong b6 = Rg_to_Fl(ell_get_b6(e), 3);
  return F3_card(b2,b4,b6);
}

/* return v_p(u), where [u,r,s,t] is the variable change to minimal model */
static long
get_vu_p_small(GEN E, ulong p, long *pv6, long *pvD)
{
  GEN c6 = ell_get_c6(E), D = ell_get_disc(E);
  long d, v6, vD = Z_lval(D,p);
  if (!signe(c6))
  {
    d = vD / 12;
    if (d)
    {
      if (p == 2)
      {
        GEN c4 = ell_get_c4(E);
        long a = Mod16( shifti(c4, -4*d) );
        if (a) d--;
      }
      if (d) vD -= 12*d; /* non minimal model */
    }
    v6 = 12; /* +oo */
  }
  else
  {
    v6 = Z_lval(c6,p);
    d = minss(2*v6, vD) / 12;
    if (d) {
      if (p == 2) {
        GEN c4 = ell_get_c4(E);
        long a = Mod16( shifti(c4, -4*d) );
        long b = Mod32( shifti(c6, -6*d) );
        if ((b & 3) != 3 && (a || (b && b!=8))) d--;
      } else if (p == 3) {
        if (v6 == 6*d+2) d--;
      }
      if (d) { v6 -= 6*d; vD -= 12*d; } /* non minimal model */
    }
  }
  *pv6 = v6; *pvD = vD; return d;
}

static ulong
ZtoF2(GEN x) { return (ulong)mpodd(x); }

/* complete local reduction at 2, u = 2^d */
static void
min_set_2(ellmin_t *M, GEN E, long d)
{
  min_set_u(M, int2n(d));
  min_set_c(M, E);
  min_set_b(M);
  min_set_a(M);
}
/* local reduction at 3, u = 3^d, don't compute the a_i */
static void
min_set_3(ellmin_t *M, GEN E, long d)
{
  min_set_u(M, powuu(3, d));
  min_set_c(M, E);
  min_set_b(M);
}

static long
is_minimal_ap_small(GEN E, ulong p, int *good_red)
{
  long vc6, vD, d = get_vu_p_small(E, p, &vc6, &vD);
  if (vD) /* bad reduction */
  {
    GEN c6;
    long s;
    *good_red = 0;
    if (vc6) return 0;
    c6 = ell_get_c6(E);
    if (d) c6 = diviiexact(c6, powuu(p, 6*d));
    s = kroiu(c6,p);
    if ((p & 3) == 3) s = -s;
    return s;
  }
  *good_red = 1;
  if (p == 2)
  {
    ellmin_t M;
    if (!d) return 3 - cardmod2(E);
    min_set_2(&M, E, d);
    return 3 - F2_card(M.a1, M.a2 & 1, M.a3, ZtoF2(M.a4), ZtoF2(M.a6));
  }
  else if (p == 3)
  {
    ellmin_t M;
    if (!d) return 4 - cardmod3(E);
    min_set_3(&M, E, d);
    return 4 - F3_card(M.b2, umodiu(M.b4,3), umodiu(M.b6,3));
  }
  else
  {
    ellmin_t M;
    GEN a4, a6, pp = utoipos(p);
    min_set_u(&M, powuu(p,d));
    min_set_c(&M, E);
    c4c6_to_a4a6(M.c4, M.c6, pp, &a4,&a6);
    return itos( subui(p+1, Fp_ellcard(a4, a6, pp)) );
  }
}

static GEN
is_minimal_ap(GEN E, GEN p, int *good_red)
{
  GEN a4,a6, c4, c6, D;
  long vc6, vD, d;
  if (lgefint(p) == 3) return stoi( is_minimal_ap_small(E, p[2], good_red) );
  c6 = ell_get_c6(E);
  D = ell_get_disc(E);
  vc6 = Z_pval(c6,p); vD = Z_pval(D,p);
  d = minss(2*vc6, vD) / 12;
  if (d) { vc6 -= 6*d; vD -= 12*d; } /* non minimal model */
  if (vD) /* bad reduction */
  {
    long s;
    *good_red = 0;
    if (vc6) return gen_0;
    if (d) c6 = diviiexact(c6, powiu(p, 6*d));
    s = kronecker(c6,p);
    if (mod4(p) == 3) s = -s;
    return s < 0? gen_m1: gen_1;
  }
  *good_red = 1;
  c4 = ell_get_c4(E);
  if (d)
  {
    GEN u2 = powiu(p, 2*d), u4 = sqri(u2), u6 = mulii(u2,u4);
    c4 = diviiexact(c4, u4);
    c6 = diviiexact(c6, u6);
  }
  c4c6_to_a4a6(c4, c6, p, &a4,&a6);
  return subii(addiu(p,1), Fp_ellcard(a4, a6, p));
}

/* E/Q, integral model, Laska-Kraus-Connell algorithm */
static GEN
get_u(GEN E, GEN *pc4c6P, GEN P)
{
  pari_sp av;
  GEN c4, c6, g, u, D, c4c6P;
  long l, k;

  D = ell_get_disc(E);
  c4 = ell_get_c4(E);
  c6 = ell_get_c6(E);
  if (!P) P = gel(Z_factor(gcdii(c4,c6)),1); /* primes dividing gcd(c4,c6) */
  l = lg(P);
  c4c6P = vectrunc_init(l); settyp(c4c6P,t_COL);
  av = avma;
  g = gcdii(sqri(c6), D);
  u = gen_1;
  for (k = 1; k < l; k++)
  {
    GEN p = gel(P, k);
    long vg = Z_pval(g, p), d = vg / 12, r = vg % 12;
    if (!d) { vectrunc_append(c4c6P, p); continue; }
    switch(itou_or_0(p))
    {
      case 2:
      {
        long a, b;
        a = Mod16( shifti(c4, -4*d) );
        b = Mod32( shifti(c6, -6*d) );
        if ((b & 3) != 3 && (a || (b && b!=8))) { d--; r += 12; }
        break;
      }
      case 3:
        if (Z_lval(c6,3) == 6*d+2) { d--; r += 12; }
        break;
    }
    if (r) vectrunc_append(c4c6P, p);
    if (d) u = mulii(u, powiu(p, d));
  }
  *pc4c6P = c4c6P;
  return gerepileuptoint(av, u);
}

/* update Q_MINIMALMODEL entry in E, but don't update type-specific data on
 * ellminimalmodel(E) */
static GEN
ellminimalmodel_i(GEN E, GEN *ptv)
{
  GEN S, y, e, v, v0, u;
  GEN c4c6P;
  ellmin_t M;
  if ((S = obj_check(E, Q_MINIMALMODEL)))
  {
    if (lg(S) != 2)
    {
      E = gel(S,3);
      v = gel(S,2);
    }
    else
      v = init_ch();
    if (ptv) *ptv = v;
    return gcopy(E);
  }
  e = ellintegralmodel(E, &v0);
  u = get_u(e, &c4c6P, NULL);
  min_set_u(&M, u);
  min_set_c(&M, e);
  min_set_D(&M, e);
  min_set_b(&M);
  min_set_a(&M);
  y = min_to_ell(&M, e);
  v = min_get_v(&M, e);
  if (v0) { gcomposev(&v0, v); v = v0; }
  if (is_trivial_change(v))
  {
    v = init_ch();
    S = mkvec(c4c6P);
  }
  else
    S = mkvec3(c4c6P, v, y);
  obj_insert(E, Q_MINIMALMODEL, S);
  *ptv = v; return y;
}
GEN
ellminimalmodel(GEN E, GEN *ptv)
{
  pari_sp av = avma;
  GEN S, y, v;
  checkell_Q(E);
  y = ellminimalmodel_i(E, &v);
  if (!is_trivial_change(v)) ch_Q(y, E, v);
  S = obj_check(E, Q_MINIMALMODEL);
  obj_insert_shallow(y, Q_MINIMALMODEL, mkvec(gel(S,1)));
  if (!ptv)
    y = gerepilecopy(av, y);
  else
  { *ptv = v; gerepileall(av, 2, &y, ptv); }
  return y;
}

/* Reduction of a rational curve E to its standard minimal model, don't
 * update type-dependant components.
 * Set v = [u, r, s, t] = change of variable E -> minimal model, with u > 0
 * Set gr = [N, [u,r,s,t], c, fa, L], where
 *   N = arithmetic conductor of E
 *   c = product of the local Tamagawa numbers cp
 *   fa = factorization of N
 *   L = list of localred(E,p) for p | N.
 * Return standard minimal model (a1,a3 = 0 or 1, a2 = -1, 0 or 1) */
static GEN
ellglobalred_all(GEN e, GEN *pgr, GEN *pv)
{
  long k, l, iN;
  GEN S, E, c, L, P, NP, NE, D;

  E = ellminimalmodel_i(e, pv);
  S = obj_check(e, Q_MINIMALMODEL);
  P = gel(S,1); l = lg(P); /* prime divisors of (c4,c6) */
  D  = ell_get_disc(E);
  for (k = 1; k < l; k++) (void)Z_pvalrem(D, gel(P,k), &D);
  if (!is_pm1(D)) P = ZV_sort( shallowconcat(P, gel(absi_factor(D),1)) );
  l = lg(P); c = gen_1;
  iN = 1;
  NP = cgetg(l, t_COL);
  NE = cgetg(l, t_COL);
  L = cgetg(l, t_VEC);
  for (k = 1; k < l; k++)
  {
    GEN p = gel(P,k), q = localred(E, p), ex = gel(q,1);
    if (signe(ex))
    {
      gel(NP, iN) = p;
      gel(NE, iN) = ex;
      gel(L, iN) = q; iN++;
      gel(q,3) = gen_0; /*delete variable change*/
      c = mulii(c, gel(q,4));
    }
  }
  setlg(L, iN);
  setlg(NP, iN);
  setlg(NE, iN);
  *pgr = mkvec4(factorback2(NP,NE), c, mkmat2(NP,NE), L);
  return E;
}
static GEN
doellglobalred(GEN E)
{
  GEN v, gr;
  E = ellglobalred_all(E, &gr, &v);
  return gr;
}
static GEN
ellglobalred_i(GEN E)
{ return obj_checkbuild(E, Q_GLOBALRED, &doellglobalred); }
GEN
ellglobalred(GEN E)
{
  pari_sp av = avma;
  GEN S, gr, v;
  checkell_Q(E); gr = ellglobalred_i(E);
  S = obj_check(E, Q_MINIMALMODEL);
  v = (lg(S) == 2)? init_ch(): gel(S,2);
  return gerepilecopy(av, mkvec5(gel(gr,1), v, gel(gr,2),gel(gr,3),gel(gr,4)));
}

static GEN doellrootno(GEN e);
/* Return E = ellminimalmodel(e), but only update E[1..14].
 * insert MINIMALMODEL, GLOBALRED, ROOTNO in both e (regular insertion)
 * and E (shallow insert) */
GEN
ellanal_globalred(GEN e, GEN *ch)
{
  GEN E, S, v = NULL;
  checkell_Q(e);
  if (!(S = obj_check(e, Q_MINIMALMODEL)))
  {
    E = ellminimalmodel_i(e, &v);
    S = obj_check(e, Q_MINIMALMODEL);
    obj_insert_shallow(E, Q_MINIMALMODEL, mkvec(gel(S,1)));
  }
  else if (lg(S) == 2) /* trivial change */
    E = e;
  else
  {
    v = gel(S,2);
    E = gcopy(gel(S,3));
    obj_insert_shallow(E, Q_MINIMALMODEL, mkvec(gel(S,1)));
  }
  if (ch) *ch = v;
  S = ellglobalred_i(e);
  if (E != e) obj_insert_shallow(E, Q_GLOBALRED, S);
  S = obj_check(e, Q_ROOTNO);
  if (!S)
  {
    S = doellrootno(E);
    obj_insert(e, Q_ROOTNO, S); /* insert in e */
  }
  if (E != e) obj_insert_shallow(E, Q_ROOTNO, S); /* ... and in E */
  return E;
}

/********************************************************************/
/**                                                                **/
/**           ROOT NUMBER (after Halberstadt at p = 2,3)           **/
/**                                                                **/
/********************************************************************/
/* x a t_INT */
static long
val_aux(GEN x, long p, long pk, long *u)
{
  long v;
  GEN z;
  if (!signe(x)) { *u = 0; return 12; }
  v = Z_lvalrem(x,p,&z);
  *u = umodiu(z,pk); return v;
}
static void
val_init(GEN e, long p, long pk,
         long *v4, long *u, long *v6, long *v, long *vD, long *d1)
{
  GEN c4 = ell_get_c4(e), c6 = ell_get_c6(e), D = ell_get_disc(e);
  pari_sp av = avma;
  *v4 = val_aux(c4, p,pk, u);
  *v6 = val_aux(c6, p,pk, v);
  *vD = val_aux(D , p,pk, d1); avma = av;
}

static long
kod_23(GEN e, long p)
{
  GEN S, nv;
  if ((S = obj_check(e, Q_GLOBALRED)))
  {
    GEN NP = gmael(S,3,1), L = gel(S,4);
    nv = equaliu(gel(NP,1), p)? gel(L,1): gel(L,2); /* localred(p) */
  }
  else
    nv = localred_23(e, p);
  return itos(gel(nv,2));
}

/* v(c4), v(c6), v(D) for minimal model, +oo is coded by 12 */
static long
neron_2(long v4, long v6, long vD, long kod)
{
  if (kod > 4) return 1;
  switch(kod)
  {
    case 1: return (v6>0) ? 2 : 1;
    case 2:
      if (vD==4) return 1;
      else
      {
        if (vD==7) return 3;
        else return v4==4 ? 2 : 4;
      }
    case 3:
      switch(vD)
      {
        case 6: return 3;
        case 8: return 4;
        case 9: return 5;
        default: return v4==5 ? 2 : 1;
      }
    case 4: return v4>4 ? 2 : 1;
    case -1:
      switch(vD)
      {
        case 9: return 2;
        case 10: return 4;
        default: return v4>4 ? 3 : 1;
      }
    case -2:
      switch(vD)
      {
        case 12: return 2;
        case 14: return 3;
        default: return 1;
      }
    case -3:
      switch(vD)
      {
        case 12: return 2;
        case 14: return 3;
        case 15: return 4;
        default: return 1;
      }
    case -4: return v6==7 ? 2 : 1;
    case -5: return (v6==7 || v4==6) ? 2 : 1;
    case -6:
      switch(vD)
      {
        case 12: return 2;
        case 13: return 3;
        default: return v4==6 ? 2 : 1;
      }
    case -7: return (vD==12 || v4==6) ? 2 : 1;
    default: return v4==6 ? 2 : 1;
  }
}
/* p = 3; v(c4), v(c6), v(D) for minimal model, +oo is coded by 12 */
static long
neron_3(long v4, long v6, long vD, long kod)
{
  if (labs(kod) > 4) return 1;
  switch(kod)
  {
    case -1: case 1: return v4&1 ? 2 : 1;
    case -3: case 3: return (2*v6>vD+3) ? 2 : 1;
    case -4: case 2:
      switch (vD%6)
      {
        case 4: return 3;
        case 5: return 4;
        default: return v6%3==1 ? 2 : 1;
      }
    default: /* kod = -2 et 4 */
      switch (vD%6)
      {
        case 0: return 2;
        case 1: return 3;
        default: return 1;
      }
  }
}

static long
ellrootno_2(GEN e)
{
  long n2, kod, u, v, x1, y1, D1, vD, v4, v6;
  long d = get_vu_p_small(e, 2, &v6, &vD);

  if (!vD) return 1;
  if (d) { /* not minimal */
    ellmin_t M;
    min_set_2(&M, e, d);
    min_set_D(&M, e);
    e = min_to_ell(&M, e);
  }
  val_init(e, 2,64,&v4,&u, &v6,&v, &vD,&D1);
  kod = kod_23(e,2);
  n2 = neron_2(v4,v6,vD, kod);
  if (kod>=5)
  {
    long a2, a3;
    a2 = ZtoF2(ell_get_a2(e));
    a3 = ZtoF2(ell_get_a3(e));
    return odd(a2 + a3) ? 1 : -1;
  }
  if (kod<-9) return (n2==2) ? -kross(-1,v) : -1;
  x1 = u+v+v;
  switch(kod)
  {
    case 1: return 1;
    case 2:
      switch(n2)
      {
        case 1:
          switch(v4)
          {
            case 4: return kross(-1,u);
            case 5: return 1;
            default: return -1;
          }
        case 2: return (v6==7) ? 1 : -1;
        case 3: return (v%8==5 || (u*v)%8==5) ? 1 : -1;
        case 4: if (v4>5) return kross(-1,v);
          return (v4==5) ? -kross(-1,u) : -1;
      }
    case 3:
      switch(n2)
      {
        case 1: return -kross(2,u*v);
        case 2: return -kross(2,v);
        case 3: y1 = (u - (v << (v6-5))) & 15;
          return (y1==7 || y1==11) ? 1 : -1;
        case 4: return (v%8==3 || (2*u+v)%8==7) ? 1 : -1;
        case 5: return v6==8 ? kross(2,x1) : kross(-2,u);
      }
    case -1:
      switch(n2)
      {
        case 1: return -kross(2,x1);
        case 2: return (v%8==7) || (x1%32==11) ? 1 : -1;
        case 3: return v4==6 ? 1 : -1;
        case 4: if (v4>6) return kross(-1,v);
          return v4==6 ? -kross(-1,u*v) : -1;
      }
    case -2: return n2==1 ? kross(-2,v) : kross(-1,v);
    case -3:
      switch(n2)
      {
        case 1: y1=(u-2*v)%64; if (y1<0) y1+=64;
          return (y1==3) || (y1==19) ? 1 : -1;
        case 2: return kross(2*kross(-1,u),v);
        case 3: return -kross(-1,u)*kross(-2*kross(-1,u),u*v);
        case 4: return v6==11 ? kross(-2,x1) : -kross(-2,u);
      }
    case -5:
      if (n2==1) return x1%32==23 ? 1 : -1;
      else return -kross(2,2*u+v);
    case -6:
      switch(n2)
      {
        case 1: return 1;
        case 2: return v6==10 ? 1 : -1;
        case 3: return (u%16==11) || ((u+4*v)%16==3) ? 1 : -1;
      }
    case -7:
      if (n2==1) return 1;
      else
      {
        y1 = (u + (v << (v6-8))) & 15;
        if (v6==10) return (y1==9 || y1==13) ? 1 : -1;
        else return (y1==9 || y1==5) ? 1 : -1;
      }
    case -8: return n2==2 ? kross(-1,v*D1) : -1;
    case -9: return n2==2 ? -kross(-1,D1) : -1;
    default: return -1;
  }
}

static long
ellrootno_3(GEN e)
{
  long n2, kod, u, v, D1, r6, K4, K6, vD, v4, v6;
  long d = get_vu_p_small(e, 3, &v6, &vD);

  if (!vD) return 1;
  if (d) { /* not minimal */
    ellmin_t M;
    min_set_3(&M, e, d);
    min_set_a(&M);
    min_set_D(&M, e);
    e = min_to_ell(&M, e);
  }
  val_init(e, 3,81, &v4,&u, &v6,&v, &vD,&D1);
  kod = kod_23(e,3);
  K6 = kross(v,3); if (kod>4) return K6;
  n2 = neron_3(v4,v6,vD,kod);
  r6 = v%9; K4 = kross(u,3);
  switch(kod)
  {
    case 1: case 3: case -3: return 1;
    case 2:
      switch(n2)
      {
        case 1: return (r6==4 || r6>6) ? 1 : -1;
        case 2: return -K4*K6;
        case 3: return 1;
        case 4: return -K6;
      }
    case 4:
      switch(n2)
      {
        case 1: return K6*kross(D1,3);
        case 2: return -K4;
        case 3: return -K6;
      }
    case -2: return n2==2 ? 1 : K6;
    case -4:
      switch(n2)
      {
        case 1:
          if (v4==4) return (r6==4 || r6==8) ? 1 : -1;
          else return (r6==1 || r6==2) ? 1 : -1;
        case 2: return -K6;
        case 3: return (r6==2 || r6==7) ? 1 : -1;
        case 4: return K6;
      }
    default: return -1;
  }
}

/* p > 3. Don't assume that e is minimal or even integral at p */
static long
ellrootno_p(GEN e, GEN p)
{
  long nuj, nuD, nu;
  GEN D = ell_get_disc(e);
  long ep, z;

  nuD = Q_pval(D, p);
  if (!nuD) return 1;
  nuj = j_pval(e, p);
  nu = (nuD - nuj) % 12;
  if (nu == 0)
  {
    GEN c6;
    long d, vg;
    if (!nuj) return 1; /* good reduction */
   /* p || N */
    c6 = ell_get_c6(e); /* != 0 */
    vg = minss(2*Q_pval(c6, p), nuD);
    d = vg / 12;
    if (d)
    {
      GEN q = powiu(p,6*d);
      c6 = (typ(c6) == t_INT)? diviiexact(c6, q): gdiv(c6, q);
    }
    if (typ(c6) != t_INT) c6 = Rg_to_Fp(c6,p);
    /* c6 in minimal model */
    return -kronecker(negi(c6), p);
  }
  if (nuj) return krosi(-1,p);
  ep = 12 / ugcd(12, nu);
  if (ep==4) z = 2; else z = (ep&1) ? 3 : 1;
  return krosi(-z, p);
}

static GEN
doellrootno(GEN e)
{
  GEN S, V, v, P;
  long i, l, s = -1;
  if ((S = obj_check(e, Q_GLOBALRED)))
  {
    GEN S2 = obj_check(e, Q_MINIMALMODEL);
    if (lg(S2) != 2) e = gel(S2,3);
  }
  else
  {
    GEN E = ellglobalred_all(e, &S, &v);
    obj_insert(e, Q_GLOBALRED, S);
    e = E;
  }
  P = gmael(S,3,1); l = lg(P);
  V = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++)
  {
    GEN p = gel(P,i);
    long t;
    switch(itou_or_0(p))
    {
      case 2: t = ellrootno_2(e); break;
      case 3: t = ellrootno_3(e); break;
      default:t = ellrootno_p(e, p);
    }
    V[i] = t; s *= t;
  }
  return mkvec2(stoi(s), V);
}
long
ellrootno_global(GEN e)
{
  pari_sp av = avma;
  GEN S = obj_checkbuild(e, Q_ROOTNO, &doellrootno);
  avma = av; return itos(gel(S,1));
}

/* local epsilon factor at p (over Q), including p=0 for the infinite place.
 * Global if p==1 or NULL. */
long
ellrootno(GEN e, GEN p)
{
  pari_sp av = avma;
  GEN S;
  long s;
  checkell_Q(e);
  if (!p || isint1(p)) return ellrootno_global(e);
  if (typ(p) != t_INT) pari_err_TYPE("ellrootno", p);
  if (signe(p) < 0) pari_err_PRIME("ellrootno",p);
  if (!signe(p)) return -1; /* local factor at infinity */
  if ( (S = obj_check(e, Q_ROOTNO)) )
  {
    GEN T = obj_check(e, Q_GLOBALRED), NP = gmael(T,3,1);
    long i, l = lg(NP);
    for (i = 1; i < l; i++)
    {
      GEN q = gel(NP,i);
      if (equalii(p, q)) { GEN V = gel(S,2); return V[i]; }
    }
    return 1;
  }
  switch(itou_or_0(p))
  {
    case 2:
      e = ellintegralmodel(e, NULL);
      s = ellrootno_2(e); break;
    case 3:
      e = ellintegralmodel(e, NULL);
      s = ellrootno_3(e); break;
    default:
      s = ellrootno_p(e,p); break;
  }
  avma = av; return s;
}

/********************************************************************/
/**                                                                **/
/**                       TRACE OF FROBENIUS                       **/
/**                                                                **/
/********************************************************************/

/* assume p does not divide disc E */
long
ellap_CM_fast(GEN E, ulong p, long CM)
{
  ulong a4, a6;
  if (p == 2) return 3 - cardmod2(E);
  if (p == 3) return 4 - cardmod3(E);
  Fl_ell_to_a4a6(E, p, &a4, &a6);
  return Fl_elltrace_CM(CM, a4, a6, p);
}

static void
checkell_int(GEN e)
{
  checkell_Q(e);
  if (typ(ell_get_a1(e)) != t_INT ||
      typ(ell_get_a2(e)) != t_INT ||
      typ(ell_get_a3(e)) != t_INT ||
      typ(ell_get_a4(e)) != t_INT ||
      typ(ell_get_a6(e)) != t_INT) pari_err_TYPE("anellsmall [not an integral model]",e);
}

long
ellQ_get_CM(GEN e)
{
  GEN j = ell_get_j(e);
  long CM = 0;
  if (typ(j) == t_INT) switch(itos_or_0(j))
  {
    case 0:
      if (!signe(j)) CM = -3;
      break;
    case 1728: CM = -4; break;
    case -3375: CM = -7; break;
    case  8000: CM = -8; break;
    case 54000: CM = -12; break;
    case -32768: CM = -11; break;
    case 287496: CM = -16; break;
    case -884736: CM = -19; break;
    case -12288000: CM = -27; break;
    case  16581375: CM = -28; break;
    case -884736000: CM = -43; break;
#ifdef LONG_IS_64BIT
    case -147197952000: CM = -67; break;
    case -262537412640768000: CM = -163; break;
#endif
  }
  return CM;
}

/* bad reduction at p */
static void
sievep_bad(ulong p, GEN an, ulong n)
{
  ulong m, N;
  switch (an[p]) /* (-c6/p) */
  {
    case -1: /* non-split */
      N = n/p;
      for (m=2; m<=N; m++)
        if (an[m] != LONG_MAX) an[m*p] = -an[m];
      break;
    case 0: /* additive */
      for (m=2*p; m<=n; m+=p) an[m] = 0;
      break;
    case 1: /* split */
      N = n/p;
      for (m=2; m<=N; m++)
        if (an[m] != LONG_MAX) an[m*p] = an[m];
      break;
  }
}
/* good reduction at p */
static void
sievep_good(ulong p, GEN an, ulong n, ulong SQRTn)
{
  const long ap = an[p];
  ulong m;
  if (p <= SQRTn) {
    ulong pk, oldpk = 1;
    for (pk=p; pk <= n; oldpk=pk, pk *= p)
    {
      if (pk != p) an[pk] = ap * an[oldpk] - p * an[oldpk/p];
      for (m = n/pk; m > 1; m--)
        if (an[m] != LONG_MAX && m%p) an[m*pk] = an[m] * an[pk];
    }
  } else {
    for (m = n/p; m > 1; m--)
      if (an[m] != LONG_MAX) an[m*p] = ap * an[m];
  }
}
static void
sievep(ulong p, GEN an, ulong n, ulong SQRTn, int good_red)
{
  if (good_red)
    sievep_good(p, an, n, SQRTn);
  else
    sievep_bad(p, an, n);
}

static long
ellan_get_ap(ulong p, int *good_red, int CM, GEN e)
{
  if (!umodiu(ell_get_disc(e),p)) /* p|D, bad reduction or non-minimal model */
    return is_minimal_ap_small(e, p, good_red);
  else /* good reduction */
  {
    *good_red = 1;
    return ellap_CM_fast(e, p, CM);
  }
}
GEN
anellsmall(GEN e, long n0)
{
  pari_sp av;
  ulong p, SQRTn, n = (ulong)n0;
  GEN an;
  int CM;

  checkell_int(e);
  if (n0 <= 0) return cgetg(1,t_VEC);
  if (n >= LGBITS)
    pari_err_IMPL( stack_sprintf("ellan for n >= %lu", LGBITS) );
  SQRTn = (ulong)sqrt(n);
  CM = ellQ_get_CM(e);

  an = const_vecsmall(n, LONG_MAX);
  an[1] = 1; av = avma;
  for (p=2; p<=n; p++)
  {
    int good_red;
    if (an[p] != LONG_MAX) continue; /* p not prime */
    an[p] = ellan_get_ap(p, &good_red, CM, e);
    sievep(p, an, n, SQRTn, good_red);
  }
  avma = av; return an;
}

GEN
anell(GEN e, long n0)
{
  GEN v = anellsmall(e, n0);
  long i;
  for (i = 1; i <= n0; i++) gel(v,i) = stoi(v[i]);
  settyp(v, t_VEC); return v;
}

static GEN
apk_good(GEN ap, GEN p, long e)
{
  GEN u, v, w;
  long j;
  if (e == 1) return ap;
  u = ap;
  w = subii(sqri(ap), p);
  for (j=3; j<=e; j++)
  {
    v = u; u = w;
    w = subii(mulii(ap,u), mulii(p,v));
  }
  return w;
}

GEN
akell(GEN e, GEN n)
{
  long i, j, s;
  pari_sp av = avma;
  GEN fa, P, E, D, u, y;

  checkell_int(e);
  if (typ(n) != t_INT) pari_err_TYPE("akell",n);
  if (signe(n)<= 0) return gen_0;
  if (gequal1(n)) return gen_1;
  D = ell_get_disc(e);
  u = coprime_part(n, D);
  y = gen_1;
  s = 1;
  if (!equalii(u, n))
  { /* bad reduction at primes dividing n/u */
    fa = Z_factor(diviiexact(n, u));
    P = gel(fa,1);
    E = gel(fa,2);
    for (i=1; i<lg(P); i++)
    {
      GEN p = gel(P,i);
      long ex = itos(gel(E,i));
      int good_red;
      GEN ap = is_minimal_ap(e,p,&good_red);
      if (good_red) { y = mulii(y, apk_good(ap, p, ex)); continue; }
      j = signe(ap);
      if (!j) { avma = av; return gen_0; }
      if (odd(ex) && j < 0) s = -s;
    }
  }
  if (s < 0) y = negi(y);
  fa = Z_factor(u);
  P = gel(fa,1);
  E = gel(fa,2);
  for (i=1; i<lg(P); i++)
  { /* good reduction */
    GEN p = gel(P,i);
    GEN ap = ellap(e,p);
    y = mulii(y, apk_good(ap, p, itos(gel(E,i))));
  }
  return gerepileuptoint(av,y);
}

GEN
ellQ_get_N(GEN e)
{ GEN v = ellglobalred_i(e); return gel(v,1); }
void
ellQ_get_Nfa(GEN e, GEN *N, GEN *faN)
{ GEN v = ellglobalred_i(e); *N = gel(v,1); *faN = gel(v,3); }

GEN
elllseries(GEN e, GEN s, GEN A, long prec)
{
  pari_sp av = avma, av1;
  ulong l, n;
  long eps, flun;
  GEN z, cg, v, cga, cgb, s2, K, gs, N;

  if (!A) A = gen_1;
  else
  {
    if (gsigne(A)<=0)
      pari_err_DOMAIN("elllseries", "cut-off point", "<=", gen_0,A);
    if (gcmpgs(A,1) < 0) A = ginv(A);
  }
  if (isint(s, &s) && signe(s) <= 0) { avma = av; return gen_0; }
  flun = gequal1(A) && gequal1(s);
  checkell_Q(e);
  e = ellanal_globalred(e, NULL);
  N = ellQ_get_N(e);
  eps = ellrootno_global(e);
  if (flun && eps < 0) { avma = av; return real_0(prec); }

  gs = ggamma(s, prec);
  cg = divrr(Pi2n(1, prec), gsqrt(N,prec));
  cga = gmul(cg, A);
  cgb = gdiv(cg, A);
  l = (ulong)((prec2nbits_mul(prec, LOG2) +
              fabs(gtodouble(real_i(s))-1.) * log(rtodbl(cga)))
            / rtodbl(cgb) + 1);
  if ((long)l < 1) l = 1;
  v = anellsmall(e, minss(l,LGBITS-1));
  s2 = K = NULL; /* gcc -Wall */
  if (!flun) { s2 = gsubsg(2,s); K = gpow(cg, gsubgs(gmul2n(s,1),2),prec); }
  z = gen_0;
  av1 = avma;
  for (n = 1; n <= l; n++)
  {
    GEN p1, an, gn = utoipos(n), ns;
    an = ((ulong)n<LGBITS)? stoi(v[n]): akell(e,gn);
    if (!signe(an)) continue;

    ns = gpow(gn,s,prec);
    p1 = gdiv(incgam0(s,mulur(n,cga),gs,prec), ns);
    if (flun)
      p1 = gmul2n(p1, 1);
    else
    {
      GEN p2 = gdiv(gmul(gmul(K,ns), incgam(s2,mulur(n,cgb),prec)), sqru(n));
      if (eps < 0) p2 = gneg_i(p2);
      p1 = gadd(p1, p2);
    }
    z = gadd(z, gmul(p1, an));
    if (gc_needed(av1,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"lseriesell");
      z = gerepilecopy(av1,z);
    }
  }
  return gerepileupto(av, gdiv(z,gs));
}

/********************************************************************/
/**                                                                **/
/**                       CANONICAL HEIGHT                         **/
/**                                                                **/
/********************************************************************/

static GEN
Q_numer(GEN x) { return typ(x) == t_INT? x: gel(x,1); }

/* one root of X^2 - t X + c */
static GEN
quad_root(GEN t, GEN c, long prec)
{
  return gmul2n(gadd(t, gsqrt(gsub(gsqr(t), gmul2n(c,2)),prec)), -1);
}

/* exp( h_oo(z) ), assume z on neutral component.
 * If flag, return exp(4 h_oo(z)) instead */
static GEN
exphellagm(GEN e, GEN z, int flag, long prec)
{
  GEN x_a, ab, a, b, e1, r, V = cgetg(1, t_VEC), x = gel(z,1);
  long n, ex = 5-prec2nbits(prec), p = prec+EXTRAPRECWORD;

  if (typ(x) == t_REAL && realprec(x) < p) x = gprec_w(x, p);
  ab = ellR_ab(e, p);
  a = gel(ab, 1);
  b = gel(ab, 2);
  e1= gel(obj_check(e,R_ROOTS), 1); /* use maximal accuracy, don't truncate */
  x = gsub(x, e1);
  x = quad_root(gadd(x,b), gmul(a,x), prec);

  x_a = gsub(x, a);
  if (gsigne(a) > 0)
  {
    GEN a0 = a;
    x = gsub(x, b);
    a = gneg(b);
    b = gsub(a0, b);
  }
  a = gsqrt(gneg(a), prec);
  b = gsqrt(gneg(b), prec);
  /* compute height on isogenous curve E1 ~ E0 */
  for(n=0; ; n++)
  {
    GEN p1, p2, ab, a0 = a;
    a = gmul2n(gadd(a0,b), -1);
    r = gsub(a, a0);
    if (gequal0(r) || gexpo(r) < ex) break;
    ab = gmul(a0, b);
    b = gsqrt(ab, prec);

    p1 = gmul2n(gsub(x, ab), -1);
    p2 = gsqr(a);
    x = gadd(p1, gsqrt(gadd(gsqr(p1), gmul(x, p2)), prec));
    V = shallowconcat(V, gadd(x, p2));
  }
  if (n) {
    x = gel(V,n);
    while (--n > 0) x = gdiv(gsqr(x), gel(V,n));
  } else {
    x = gadd(x, gsqr(a));
  }
  /* height on E1 is log(x)/2. Go back to E0 */
  return flag? gsqr( gdiv(gsqr(x), x_a) )
             : gdiv(x, sqrtr( mpabs(x_a) ));
}
/* is P \in E(R)^0, the neutral component ? */
static int
ellR_on_neutral(GEN E, GEN P, long prec)
{
  GEN x = gel(P,1), e1 = ellR_root(E, prec);
  return gcmp(x, e1) >= 0;
}

/* hoo + 1/2 log(den(x)) */
static GEN
hoo_aux(GEN E, GEN z, GEN d, long prec)
{
  pari_sp av = avma;
  GEN h;
  checkell_Q(E);
  if (!ellR_on_neutral(E, z, prec))
  {
    GEN eh = exphellagm(E, elladd(E, z,z), 0, prec);
    /* h_oo(2P) = 4h_oo(P) - log |2y + a1x + a3| */
    h = gmul(eh, gabs(ec_dmFdy_evalQ(E, z), prec));
  }
  else
    h = exphellagm(E, z, 1, prec);
  if (!is_pm1(d)) h = gmul(h, sqri(d));
  return gerepileuptoleaf(av, gmul2n(mplog(h), -2));
}
GEN
ellheightoo(GEN E, GEN z, long prec) { return hoo_aux(E, z, gen_1, prec); }

static GEN
_hell(GEN E, GEN p, long n, GEN P)
{ return p? ellpadicheight(E,p,n, P): ellheight(E,P,n); }
static GEN
ellheightpairing(GEN E, GEN p, long n, GEN P, GEN Q)
{
  pari_sp av = avma;
  GEN a = _hell(E,p,n, elladd(E,P,Q));
  GEN b = _hell(E,p,n, ellsub(E,P,Q));
  return gerepileupto(av, gmul2n(gsub(a,b), -2));
}
GEN
ellheight0(GEN e, GEN a, GEN b, long n)
{ return b? ellheightpairing(e,NULL,n, a,b): ellheight(e,a,n); }
GEN
ellpadicheight0(GEN e, GEN p, long n, GEN P, GEN Q)
{ return Q? ellheightpairing(e,p,n, P,Q): ellpadicheight(e,p,n, P); }

GEN
ellheight(GEN e, GEN a, long prec)
{
  long i, lx;
  pari_sp av = avma;
  GEN Lp, x, y, z, phi2, psi2, psi3;
  GEN v, S, b2, b4, b6, b8, a1, a2, a4, c4, D;

  checkell_Q(e);
  checkellpt(a);
  if (ell_is_inf(a)) return gen_0;
  if ((S = obj_check(e, Q_MINIMALMODEL)))
  { /* switch to minimal model if needed */
    if (lg(S) != 2)
    {
      v = gel(S,2);
      e = gel(S,3);
      a = ellchangepoint(a, v);
    }
  }
  else
  {
    e = ellminimalmodel_i(e, &v);
    a = ellchangepoint(a, v);
  }
  if (!oncurve(e,a))
    pari_err_DOMAIN("ellheight", "point", "not on", strtoGENstr("E"),a);
  psi2 = Q_numer(ec_dmFdy_evalQ(e,a));
  if (!signe(psi2)) { avma = av; return gen_0; }
  x = gel(a,1);
  y = gel(a,2);
  b2 = ell_get_b2(e);
  b4 = ell_get_b4(e);
  b6 = ell_get_b6(e);
  b8 = ell_get_b8(e);
  psi3 = Q_numer( /* b8 + 3x b6 + 3x^2 b4 + x^3 b2 + 3 x^4 */
    poleval(mkvec5(b8, mului(3,b6), mului(3,b4), b2, utoipos(3)), x)
  );
  if (!signe(psi3)) { avma=av; return gen_0; }
  a1 = ell_get_a1(e);
  a2 = ell_get_a2(e);
  a4 = ell_get_a4(e);
  phi2 = Q_numer( /* a4 + 2a2 x + 3x^2 - y a1*/
    poleval(mkvec3(gsub(a4,gmul(a1,y)), shifti(a2,1), utoipos(3)), x)
  );
  c4 = ell_get_c4(e);
  D = ell_get_disc(e);
  z = hoo_aux(e,a,Q_denom(x),prec);  /* hoo(a) + log(den(x))/2 */
  Lp = gel(Z_factor(gcdii(psi2,phi2)),1);
  lx = lg(Lp);
  for (i=1; i<lx; i++)
  {
    GEN p = gel(Lp,i);
    long u, v, n, n2;
    if (signe(remii(c4,p)))
    { /* p \nmid c4 */
      long N = Z_pval(D,p);
      if (!N) continue;
      n2 = Z_pval(psi2,p); n = n2<<1;
      if (n > N) n = N;
      u = n * ((N<<1) - n);
      v = N << 3;
    }
    else
    {
      n2 = Z_pval(psi2, p);
      n  = Z_pval(psi3, p);
      if (n >= 3*n2) { u = n2; v = 3; } else { u = n; v = 8; }
    }
    /* z -= u log(p) / v */
    z = gsub(z, divru(mulur(u, logr_abs(itor(p,prec))), v));
  }
  return gerepileupto(av, gmul2n(z, 1));
}

GEN
ellpadicheightmatrix(GEN e, GEN p, long n, GEN x)
{
  GEN y, D;
  long lx = lg(x), i, j;
  pari_sp av = avma;

  if (!is_vec_t(typ(x))) pari_err_TYPE("ellheightmatrix",x);
  D = cgetg(lx,t_VEC);
  y = cgetg(lx,t_MAT);
  for (i=1; i<lx; i++)
  {
    gel(D,i) = _hell(e,p,n, gel(x,i));
    gel(y,i) = cgetg(lx,t_COL);
  }
  for (i=1; i<lx; i++)
  {
    gcoeff(y,i,i) = gel(D,i);
    for (j=i+1; j<lx; j++)
    {
      GEN h = _hell(e,p,n, elladd(e,gel(x,i),gel(x,j)));
      h = gsub(h, gadd(gel(D,i),gel(D,j)));
      gcoeff(y,j,i) = gcoeff(y,i,j) = gmul2n(h, -1);
    }
  }
  return gerepilecopy(av,y);
}
GEN
ellheightmatrix(GEN E, GEN x, long n)
{ return ellpadicheightmatrix(E,NULL,n, x); }

/* Q an actual point, P a point or vector/matrix of points */
static GEN
bilhell_i(GEN E, GEN P, GEN Q, GEN p, long n)
{
  long l = lg(P);
  if (l==1) return cgetg(1,typ(P));
  if (!is_matvec_t( typ(gel(P,1)) )) return ellheightpairing(E,p,n,P,Q);
  else
  {
    GEN y = cgetg(l, typ(P));
    long i;
    for (i=1; i<l; i++) gel(y,i) = bilhell_i(E,gel(P,i),Q,p,n);
    return y;
  }
}
static GEN
ellpadicbil(GEN E, GEN P, GEN Q, GEN p, long n)
{
  long t1 = typ(P), t2 = typ(Q);
  if (!is_matvec_t(t1)) pari_err_TYPE("ellbil",P);
  if (!is_matvec_t(t2)) pari_err_TYPE("ellbil",Q);
  if (lg(P)==1) return cgetg(1,t1);
  if (lg(Q)==1) return cgetg(1,t2);
  t2 = typ(gel(Q,1));
  if (is_matvec_t(t2))
  {
    t1 = typ(gel(P,1));
    if (is_matvec_t(t1)) pari_err_TYPE("bilhell",P);
    return bilhell_i(E,Q,P, p,n);
  }
  return bilhell_i(E,P,Q, p,n);
}
GEN
bilhell(GEN E, GEN P, GEN Q, long n)
{ return ellpadicbil(E,P,Q, NULL, n); }
/********************************************************************/
/**                                                                **/
/**                    Modular Parametrization                     **/
/**                                                                **/
/********************************************************************/
/* t*x^v (1 + O(x)), t != 0 */
static GEN
triv_ser(GEN t, long v)
{
  GEN s = cgetg(3,t_SER);
  s[1] = evalsigne(1) | _evalvalp(v) | evalvarn(0);
  gel(s,2) = t; return s;
}

GEN
elltaniyama(GEN e, long prec)
{
  GEN x, w, c, d, X, C, b2, b4;
  long n, m;
  pari_sp av = avma;

  checkell_Q(e);
  if (prec < 0) pari_err_DOMAIN("elltaniyama","precision","<",gen_0,stoi(prec));
  if (!prec) retmkvec2(triv_ser(gen_1,-2), triv_ser(gen_m1,-3));

  x = cgetg(prec+3,t_SER);
  x[1] = evalsigne(1) | _evalvalp(-2) | evalvarn(0);
  d = ginv(gtoser(anell(e,prec+1), 0, prec)); setvalp(d,-1);
  /* 2y(q) + a1x + a3 = d qx'(q). Solve for x(q),y(q):
   * 4y^2 = 4x^3 + b2 x^2 + 2b4 x + b6 */
  c = gsqr(d);
  /* solve 4x^3 + b2 x^2 + 2b4 x + b6 = c (q x'(q))^2; c = 1/q^2 + O(1/q)
   * Take derivative then divide by 2x':
   *  b2 x + b4 = (1/2) (q c')(q x') + c q (q x')' - 6x^2.
   * Write X[i] = coeff(x, q^i), C[i] = coeff(c, q^i), we obtain for all n
   *  ((n+1)(n+2)-12) X[n+2] =  b2 X[n] + b4 delta_{n = 0}
   *   + 6    \sum_{m = -1}^{n+1} X[m] X[n-m]
   *   - (1/2)\sum_{m = -2}^{n+1} (n+m) m C[n-m]X[m].
   * */
  C = c+4;
  X = x+4;
  gel(X,-2) = gen_1;
  gel(X,-1) = gmul2n(gel(C,-1), -1); /* n = -3, X[-1] = C[-1] / 2 */
  b2 = ell_get_b2(e);
  b4 = ell_get_b4(e);
  for (n=-2; n <= prec-4; n++)
  {
    pari_sp av2 = avma;
    GEN s1, s2, s3;
    if (n != 2)
    {
      s3 = gmul(b2, gel(X,n));
      if (!n) s3 = gadd(s3, b4);
      s2 = gen_0;
      for (m=-2; m<=n+1; m++)
        if (m) s2 = gadd(s2, gmulsg(m*(n+m), gmul(gel(X,m),gel(C,n-m))));
      s2 = gmul2n(s2,-1);
      s1 = gen_0;
      for (m=-1; m+m < n; m++) s1 = gadd(s1, gmul(gel(X,m),gel(X,n-m)));
      s1 = gmul2n(s1, 1);
      if (m+m==n) s1 = gadd(s1, gsqr(gel(X,m)));
      /* ( (n+1)(n+2) - 12 ) X[n+2] = (6 s1 + s3 - s2) */
      s1 = gdivgs(gsub(gadd(gmulsg(6,s1),s3),s2), (n+2)*(n+1)-12);
    }
    else
    {
      GEN b6 = ell_get_b6(e);
      GEN U = cgetg(9, t_SER);
      U[1] = evalsigne(1) | _evalvalp(-2) | evalvarn(0);
      gel(U,2) = gel(x,2);
      gel(U,3) = gel(x,3);
      gel(U,4) = gel(x,4);
      gel(U,5) = gel(x,5);
      gel(U,6) = gel(x,6);
      gel(U,7) = gel(x,7);
      gel(U,8) = gen_0; /* defined mod q^5 */
      /* write x = U + x_4 q^4 + O(q^5) and expand original equation */
      w = derivser(U); setvalp(w,-2); /* q X' */
      /* 4X^3 + b2 U^2 + 2b4 U + b6 */
      s1 = gadd(b6, gmul(U, gadd(gmul2n(b4,1), gmul(U,gadd(b2,gmul2n(U,2))))));
      /* s2 = (qX')^2 - (4X^3 + b2 U^2 + 2b4 U + b6) = 28 x_4 + O(q) */
      s2 = gsub(gmul(c,gsqr(w)), s1);
      s1 = signe(s2)? gdivgs(gel(s2,2), 28): gen_0; /* = x_4 */
    }
    gel(X,n+2) = gerepileupto(av2, s1);
  }
  w = gmul(d,derivser(x)); setvalp(w, valp(w)+1);
  w = gsub(w, ec_h_evalx(e,x));
  c = cgetg(3,t_VEC);
  gel(c,1) = gcopy(x);
  gel(c,2) = gmul2n(w,-1); return gerepileupto(av, c);
}

/********************************************************************/
/**                                                                **/
/**                       TORSION POINTS (over Q)                  **/
/**                                                                **/
/********************************************************************/
static GEN
doellff_get_o(GEN E)
{
  GEN G = ellgroup(E, NULL), d1 = gel(G,1);
  return mkvec2(d1, Z_factor(d1));
}
GEN
ellff_get_o(GEN E)
{ return obj_checkbuild(E, FF_O, &doellff_get_o); }

GEN
elllog(GEN E, GEN a, GEN g, GEN o)
{
  pari_sp av = avma;
  GEN fg, r;
  checkell_Fq(E); checkellpt(a); checkellpt(g);
  fg = ellff_get_field(E);
  if (!o) o = ellff_get_o(E);
  if (typ(fg)==t_FFELT)
    r = FF_elllog(E, a, g, o);
  else
  {
    GEN p = fg, e = ellff_get_a4a6(E);
    GEN Pp = FpE_changepointinv(RgE_to_FpE(a,p), gel(e,3), p);
    GEN Qp = FpE_changepointinv(RgE_to_FpE(g,p), gel(e,3), p);
    r = FpE_log(Pp, Qp, o, gel(e,1), p);
  }
  return gerepileuptoint(av, r);
}

GEN
ellweilpairing(GEN E, GEN P, GEN Q, GEN m)
{
  GEN fg;
  checkell_Fq(E); checkellpt(P); checkellpt(Q);
  if (typ(m)!=t_INT) pari_err_TYPE("ellweilpairing",m);
  fg = ellff_get_field(E);
  if (typ(fg)==t_FFELT)
    return FF_ellweilpairing(E, P, Q, m);
  else
  {
    pari_sp av = avma;
    GEN p = fg, e = ellff_get_a4a6(E);
    GEN z = FpE_weilpairing(FpE_changepointinv(RgV_to_FpV(P,p),gel(e,3),p),
                            FpE_changepointinv(RgV_to_FpV(Q,p),gel(e,3),p),m,gel(e,1),p);
    return gerepileupto(av, Fp_to_mod(z, p));
  }
}

GEN
elltatepairing(GEN E, GEN P, GEN Q, GEN m)
{
  GEN fg;
  checkell_Fq(E); checkellpt(P); checkellpt(Q);
  if (typ(m)!=t_INT) pari_err_TYPE("elltatepairing",m);
  fg = ellff_get_field(E);
  if (typ(fg)==t_FFELT)
    return FF_elltatepairing(E, P, Q, m);
  else
  {
    pari_sp av = avma;
    GEN p = fg, e = ellff_get_a4a6(E);
    GEN z = FpE_tatepairing(FpE_changepointinv(RgV_to_FpV(P,p),gel(e,3),p),
                            FpE_changepointinv(RgV_to_FpV(Q,p),gel(e,3),p),m,gel(e,1),p);
    return gerepileupto(av, Fp_to_mod(z, p));
  }
}

/* E/Q, return cardinality including the (possible) ramified point */
static GEN
ellcard_ram(GEN E, GEN p, int *good_red)
{
  GEN a4, a6, D = Rg_to_Fp(ell_get_disc(E), p);
  if (!signe(D))
  {
    pari_sp av = avma;
    GEN ap = is_minimal_ap(E, p, good_red);
    return gerepileuptoint(av, subii(addiu(p,1), ap));
  }
  *good_red = 1;
  if (equaliu(p,2)) return utoi(cardmod2(E));
  if (equaliu(p,3)) return utoi(cardmod3(E));
  ell_to_a4a6(E,p,&a4,&a6);
  return Fp_ellcard(a4, a6, p);
}

static GEN
checkellp(GEN E, GEN p, const char *s)
{
  GEN q;
  if (p) switch(typ(p))
  {
    case t_INT:
      if (cmpis(p, 2) < 0) pari_err_DOMAIN(s,"p", "<", gen_2, p);
      break;
    case t_VEC:
      q = get_prid(p);
      if (q) { p = q; break; }
    default: pari_err_TYPE(s,p);
  }
  checkell(E);
  switch(ell_get_type(E))
  {
    case t_ELL_Qp:
      q = ellQp_get_p(E);
      if (p && !equalii(p, q)) pari_err_TYPE(s,p);
      return q;

    case t_ELL_Fp:
    case t_ELL_Fq:
      q = ellff_get_p(E);
      if (p && !equalii(p, q)) pari_err_TYPE(s,p);
      return q;
    case t_ELL_NF:
    case t_ELL_Q:
      if (p) return p;
    default:
      pari_err_TYPE(stack_strcat(s," [can't determine p]"), E);
      return NULL;/*not reached*/
  }
}

GEN
ellap(GEN E, GEN p)
{
  pari_sp av = avma;
  GEN q, card;
  int goodred;
  p = checkellp(E, p, "ellap");
  switch(ell_get_type(E))
  {
  case t_ELL_Fp:
    q = p; card = ellff_get_card(E);
    break;
  case t_ELL_Fq:
    q = FF_q(ellff_get_field(E)); card = ellff_get_card(E);
    break;
  case t_ELL_Q:
    q = p; card = ellcard_ram(E, p, &goodred);
    break;
  default:
    pari_err_TYPE("ellap",E);
    return NULL; /*NOT REACHED*/
  }
  return gerepileuptoint(av, subii(addiu(q,1), card));
}

static GEN
doellcard(GEN E)
{
  GEN fg = ellff_get_field(E);
  if (typ(fg)==t_FFELT)
    return FF_ellcard(E);
  else
  {
    GEN e = ellff_get_a4a6(E);
    return Fp_ellcard(gel(e,1),gel(e,2),fg);
  }
}

GEN
ellff_get_card(GEN E)
{ return obj_checkbuild(E, FF_CARD, &doellcard); }

GEN
ellcard(GEN E, GEN p)
{
  p = checkellp(E, p, "ellcard");
  switch(ell_get_type(E))
  {
  case t_ELL_Fp: case t_ELL_Fq:
    return icopy(ellff_get_card(E));
  case t_ELL_Q:
    {
      pari_sp av = avma;
      int goodred;
      GEN N = ellcard_ram(E, p, &goodred);
      if (!goodred) N = subis(N, 1); /* remove singular point */
      return gerepileuptoint(av, N);
    }
  default:
    pari_err_TYPE("ellcard",E);
    return NULL; /*NOT REACHED*/
  }
}

/* D = [d_1, ..., d_r ] the elementary divisors for E(Fp), r = 0,1,2.
 * d_r | ... | d_1 */
static GEN
ellgen(GEN E, GEN D, GEN m, GEN p)
{
  pari_sp av = avma;
  if (cmpiu(p, 3)<=0)
  {
    ulong l = itou(p), r = lg(D)-1;
    long a1 = Rg_to_Fl(ell_get_a1(E),l);
    long a3 = Rg_to_Fl(ell_get_a3(E),l);
    if (r==0) return cgetg(1,t_VEC);
    if (l==2)
    {
      long a2 = Rg_to_Fl(ell_get_a2(E),l);
      long a4 = Rg_to_Fl(ell_get_a4(E),l);
      long a6 = Rg_to_Fl(ell_get_a6(E),l);
      switch(a1|(a2<<1)|(a3<<2)|(a4<<3)|(a6<<4))
      { /* r==0 : 22, 23, 25, 28, 31 */
        case 18: case 29:
          retmkvec(mkvec2s(1,1));
        case 19: case 24: case 26:
          retmkvec(mkvec2s(0,1));
        case 9: case 16: case 17: case 20: case 21: case 27: case 30:
          retmkvec(mkvec2s(1,0));
        default:
          retmkvec(mkvec2s(0,0));
      }
    } else
    { /* y^2 = 4x^3 + b2 x^2 + 2b4 x + b6 */
      long b2 = Rg_to_Fl(ell_get_b2(E),l);
      long b4 = Rg_to_Fl(ell_get_b4(E),l);
      long b6 = Rg_to_Fl(ell_get_b6(E),l);
      long T1 = (1+b2+2*b4+b6)%3; /* RHS(1) */
      long x,y;
      if (r==2) /* [2,2] */
        retmkvec2(mkvec2s(0,a3),mkvec2s(1,Fl_add(a1,a3,3)));
      /* cyclic, order d_1 */
      y = equaliu(gel(D,1),2)? 0 : 1;
      if (equaliu(gel(D,1),6)) /* [6] */
      {
        long b8 = Rg_to_Fl(ell_get_b8(E),l);
        x = (b6==1 && b8!=0) ? 0 : (T1==1 && (b2+b8)%3!=0) ? 1 : 2;
      }
      else /* [2],[3],[4],[5],[7] */
      { /* Avoid [x,y] singular, iff b2 x + b4 = 0 = y. */
        if (y == 1)
          x = (b6==1) ? 0 : (T1==1) ? 1 : 2;
        else
          x = (b6==0 && b4) ? 0 : (T1==0 && (b2 + b4) % 3) ? 1 : 2;
      }
      retmkvec(mkvec2s(x,(2*y+a1*x+a3)%3));
    }
  }
  else
  {
    GEN e = ell_to_a4a6_bc(E, p), a4 = gel(e, 1), a6 = gel(e, 2);
    return gerepileupto(av, Fp_ellgens(a4,a6,gel(e,3),D,m,p));
  }
}

static GEN
ellgroup_m(GEN E, GEN p)
{
  GEN a4, a6, G, m = gen_1, N = ellcard(E, p);
  if (equali1(N)) { G = cgetg(1,t_VEC); goto END; }
  if (equaliu(p, 2)) { G = mkvec(N); goto END; }
  if (equaliu(p, 3))
  { /* The only possible non-cyclic group is [2,2] which happens 9 times */
    ulong b2, b4, b6;
    if (!equaliu(N, 4)) { G = mkvec(N); goto END; }
    /* If the group is not cyclic, T = 4x^3 + b2 x^2 + 2b4 x + b6
     * must have 3 roots else 1 root. Test T(0) = T(1) = 0 mod 3 */
    b6 = Rg_to_Fl(ell_get_b6(E), 3);
    if (b6) { G = mkvec(N); goto END; }
    /* b6 = T(0) = 0 mod 3. Test T(1) */
    b2 = Rg_to_Fl(ell_get_b2(E), 3);
    b4 = Rg_to_Fl(ell_get_b4(E), 3);
    if ((1 + b2 + (b4<<1)) % 3) { G = mkvec(N); goto END; }
    G = mkvec2s(2, 2); goto END;
  } /* Now assume p > 3 */
  ell_to_a4a6(E, p, &a4,&a6);
  G = Fp_ellgroup(a4,a6,N,p, &m);
END:
  return mkvec2(G, m);
}

static GEN
doellgroup(GEN E)
{
  GEN fg = ellff_get_field(E);
  return typ(fg) == t_FFELT ? FF_ellgroup(E): ellgroup_m(E, fg);
}

GEN
ellff_get_group(GEN E)
{ return obj_checkbuild(E, FF_GROUP, &doellgroup); }

/* E / Fp */
static GEN
doellgens(GEN E)
{
  GEN fg = ellff_get_field(E);
  if (typ(fg)==t_FFELT)
    return FF_ellgens(E);
  else
  {
    GEN e, Gm, F, p = fg;
    e = ellff_get_a4a6(E);
    Gm = ellff_get_group(E);
    F = Fp_ellgens(gel(e,1),gel(e,2),gel(e,3), gel(Gm,1),gel(Gm,2), p);
    return FpVV_to_mod(F,p);
  }
}

GEN
ellff_get_gens(GEN E)
{ return obj_checkbuild(E, FF_GROUPGEN, &doellgens); }

GEN
ellgroup(GEN E, GEN p)
{
  pari_sp av = avma;
  GEN G;
  p = checkellp(E,p, "ellgroup");
  if (ell_over_Fq(E)) G = ellff_get_group(E);
  else                G = ellgroup_m(E,p); /* t_ELL_Q */
  return gerepilecopy(av, gel(G,1));
}

GEN
ellgroup0(GEN E, GEN p, long flag)
{
  pari_sp av = avma;
  GEN V;
  if (flag==0) return ellgroup(E, p);
  if (flag!=1) pari_err_FLAG("ellgroup");
  p = checkellp(E, p, "ellgroup");
  if (!ell_over_Fq(E))
  { /* t_ELL_Q */
    GEN Gm = ellgroup_m(E, p), G = gel(Gm,1), m = gel(Gm,2);
    GEN F = FpVV_to_mod(ellgen(E,G,m,p), p);
    return gerepilecopy(av, mkvec3(ZV_prod(G),G,F));
  }
  V = mkvec3(ellff_get_card(E), gel(ellff_get_group(E), 1), ellff_get_gens(E));
  return gerepilecopy(av, V);
}

GEN
ellgenerators(GEN E)
{
  checkell(E);
  switch(ell_get_type(E))
  {
    case t_ELL_Q:
      return obj_checkbuild(E, Q_GROUPGEN, &elldatagenerators);
    case t_ELL_Fp: case t_ELL_Fq:
      return gcopy(ellff_get_gens(E));
    default:
      pari_err_TYPE("ellgenerators",E);
      return NULL;/*not reached*/
  }
}

/* char != 2,3, j != 0, 1728 */
static GEN
ellfromj_simple(GEN j)
{
  pari_sp av = avma;
  GEN k = gsubsg(1728,j), kj = gmul(k, j), k2j = gmul(kj, k);
  GEN E = zerovec(5);
  gel(E,4) = gmulsg(3,kj);
  gel(E,5) = gmulsg(2,k2j); return gerepileupto(av, E);
}
GEN
ellfromj(GEN j)
{
  GEN T = NULL, p = typ(j)==t_FFELT? FF_p_i(j): NULL;
  /* trick: use j^0 to get 1 in the proper base field */
  if ((p || (Rg_is_FpXQ(j,&T,&p) && p)) && lgefint(p) == 3) switch(p[2])
  {
    case 2:
      if (gequal0(j))
        retmkvec5(gen_0,gen_0, gpowgs(j,0), gen_0,gen_0);
      else
        retmkvec5(gpowgs(j,0),gen_0,gen_0, gen_0,ginv(j));
    case 3:
      if (gequal0(j))
        retmkvec5(gen_0,gen_0,gen_0, gpowgs(j,0), gen_0);
      else
      {
        GEN E = zerovec(5);
        pari_sp av = avma;
        gel(E,5) = gerepileupto(av, gneg(gsqr(j)));
        gel(E,2) = gcopy(j);
        return E;
      }
  }
  if (gequal0(j)) retmkvec5(gen_0,gen_0,gen_0,gen_0, gpowgs(j,0));
  if (gequalgs(j,1728)) retmkvec5(gen_0,gen_0,gen_0, gpowgs(j,0), gen_0);
  return ellfromj_simple(j);
}

/********************************************************************/
/**                                                                **/
/**                       IS SUPERSINGULAR                         **/
/**                                                                **/
/********************************************************************/

int
elljissupersingular(GEN x)
{
  pari_sp av = avma;
  int res;

  if (typ(x) == t_INTMOD) {
    GEN p = gel(x, 1);
    GEN j = gel(x, 2);
    res = Fp_elljissupersingular(j, p);
  } else if (typ(x) == t_FFELT) {
    GEN j = FF_to_FpXQ_i(x);
    GEN p = FF_p_i(x);
    GEN T = FF_mod(x);
    res = FpXQ_elljissupersingular(j, T, p);
  } else {
    pari_err_TYPE("elljissupersingular", x);
    return 0; /*NOT REACHED*/
  }
  avma = av;
  return res;
}

int
ellissupersingular(GEN E, GEN p)
{
  if (typ(E)!=t_VEC && !p)
    return elljissupersingular(E);
  p = checkellp(E, p, "ellissupersingular");
  switch(ell_get_type(E))
  {
  case t_ELL_Fp:
  case t_ELL_Fq:
      return elljissupersingular(ell_get_j(E));
    break;
  case t_ELL_Q:
    {
      pari_sp av = avma;
      GEN j = ell_get_j(E);
      int res;
      if (typ(j)==t_FRAC && dvdii(gel(j,2), p)) return 0;
      res = Fp_elljissupersingular(Rg_to_Fp(j, p), p);
      avma = av; return res;
    }
    break;
  default:
    pari_err_TYPE("ellissupersingular",E);
  }
  return 0; /* Not reached */
}

/* n <= 4, N is the characteristic of the base ring or NULL (char 0) */
static GEN
elldivpol4(GEN e, GEN N, long n, long v)
{
  GEN b2,b4,b6,b8, res;
  if (n==0) return pol_0(v);
  if (n<=2) return N? scalarpol_shallow(mkintmod(gen_1,N),v): pol_1(v);
  b2 = ell_get_b2(e); b4 = ell_get_b4(e);
  b6 = ell_get_b6(e); b8 = ell_get_b8(e);
  if (n==3)
    res = mkpoln(5, N? modsi(3,N): utoi(3),b2,gmulsg(3,b4),gmulsg(3,b6),b8);
  else
  {
    GEN b10 = gsub(gmul(b2, b8), gmul(b4, b6));
    GEN b12 = gsub(gmul(b8, b4), gsqr(b6));
    res = mkpoln(7, N? modsi(2,N): gen_2,b2,gmulsg(5,b4),gmulsg(10,b6),gmulsg(10,b8),b10,b12);
  }
  setvarn(res, v); return res;
}

/* T = (2y + a1x + a3)^4 modulo the curve equation. Store elldivpol(e,n,v)
 * in t[n]. N is the caracteristic of the base ring or NULL (char 0) */
static GEN
elldivpol0(GEN e, GEN t, GEN N, GEN T, long n, long v)
{
  GEN ret;
  long m = n/2;
  if (gel(t,n)) return gel(t,n);
  if (n<=4) ret = elldivpol4(e, N, n, v);
  else if (odd(n))
  {
    GEN t1 = RgX_mul(elldivpol0(e,t,N,T,m+2,v),
                     gpowgs(elldivpol0(e,t,N,T,m,v),3));
    GEN t2 = RgX_mul(elldivpol0(e,t,N,T,m-1,v),
                     gpowgs(elldivpol0(e,t,N,T,m+1,v),3));
    if (odd(m))/*f_{4l+3} = f_{2l+3}f_{2l+1}^3 - T f_{2l}f_{2l+2}^3, m=2l+1*/
      ret = RgX_sub(t1, RgX_mul(T,t2));
    else       /*f_{4l+1} = T f_{2l+2}f_{2l}^3 - f_{2l-1}f_{2l+1}^3, m=2l*/
      ret = RgX_sub(RgX_mul(T,t1), t2);
  }
  else
  { /* f_2m = f_m(f_{m+2}f_{m-1}^2 - f_{m-2}f_{m+1}^2) */
    GEN t1 = RgX_mul(elldivpol0(e,t,N,T,m+2,v),
                     RgX_sqr(elldivpol0(e,t,N,T,m-1,v)));
    GEN t2 = RgX_mul(elldivpol0(e,t,N,T,m-2,v),
                     RgX_sqr(elldivpol0(e,t,N,T,m+1,v)));
    ret = RgX_mul(elldivpol0(e,t,N,T,m,v), RgX_sub(t1,t2));
  }
  gel(t,n) = ret;
  return ret;
}

GEN
elldivpol(GEN e, long n, long v)
{
  pari_sp av = avma;
  GEN f, D, N;
  checkell(e); D = ell_get_disc(e);
  if (v==-1) v = 0;
  if (varncmp(gvar(D), v) <= 0) pari_err_PRIORITY("elldivpol", e, "<=", v);
  N = characteristic(D);
  if (!signe(N)) N = NULL;
  if (n<0) n = -n;
  if (n==1 || n==3)
    f = elldivpol4(e, N, n, v);
  else
  {
    GEN d2 = ec_bmodel(e); /* (2y + a1x + 3)^2 mod E */
    setvarn(d2,v);
    if (N && !mod2(N)) { gel(d2,5) = modsi(4,N); d2 = normalizepol(d2); }
    if (n <= 4)
      f = elldivpol4(e, N, n, v);
    else
      f = elldivpol0(e, const_vec(n,NULL), N,RgX_sqr(d2), n, v);
    if (n%2==0) f = RgX_mul(f, d2);
  }
  return gerepilecopy(av, f);
}

/* return [phi_n, (psi_n)^2] such that x[nP] = phi_n / (psi_n)^2 */
GEN
ellxn(GEN e, long n, long v)
{
  pari_sp av = avma;
  GEN d2, D, N, A, B;
  checkell(e); D = ell_get_disc(e);
  if (v==-1) v = 0;
  if (varncmp(gvar(D), v) <= 0) pari_err_PRIORITY("elldivpol", e, "<=", v);
  N = characteristic(D);
  if (!signe(N)) N = NULL;
  if (n < 0) n = -n;
  d2 = ec_bmodel(e); /* (2y + a1x + 3)^2 mod E */
  setvarn(d2,v);
  if (N && !mod2(N)) { gel(d2,5) = modsi(4,N); d2 = normalizepol(d2); }
  if (n == 0)
  {
    A = pol_0(v);
    B = pol_0(v);
  }
  else if (n == 1)
  {
    A = pol_1(v);
    B = pol_x(v);
  }
  else if (n == 2)
  {
    GEN b4 = ell_get_b4(e);
    GEN b6 = ell_get_b6(e);
    GEN b8 = ell_get_b8(e);
    A = d2;
    /* phi_2 = x^4 - b4*x^2 - 2b6*x - b8 */
    B = mkpoln(5, gen_1, gen_0, gneg(b4), gmul2n(gneg(b6),1), gneg(b8));
    setvarn(B,v);
  }
  else
  {
    GEN t = const_vec(n+1,NULL), T = RgX_sqr(d2);
    GEN f = elldivpol0(e, t, N, T, n, v); /* f_n / d2^(n odd)*/
    GEN g = elldivpol0(e, t, N, T, n-1, v); /* f_{n-1} / d2^(n even) */
    GEN h = elldivpol0(e, t, N, T, n+1, v); /* f_{n+1} / d2^(n even) */
    GEN f2 = RgX_sqr(f), u = RgX_mul(g,h);
    if (!odd(n))
      A = RgX_mul(f2, d2);
    else
    { A = f2; u = RgX_mul(u,d2); }
    /* A = psi_n^2, u = psi_{n-1} psi_{n+1} */
    B = RgX_sub(RgX_mulXn(A,1), u);
  }
  return gerepilecopy(av, mkvec2(B,A));
}

GEN
ellpadicfrobenius(GEN E, ulong p, long n)
{
  checkell_Q(E);
  return hyperellpadicfrobenius(ec_bmodel(E), p, n);
}
