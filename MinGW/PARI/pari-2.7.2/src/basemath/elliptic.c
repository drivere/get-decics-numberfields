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

static void
Fl_c4c6_to_a4a6(ulong c4, ulong c6, ulong p, ulong *a4, ulong *a6)
{
  *a4 = Fl_neg(Fl_mul(c4, 27, p), p);
  *a6 = Fl_neg(Fl_mul(c6, 54, p), p);
}
static void
c4c6_to_a4a6(GEN c4, GEN c6, GEN p, GEN *a4, GEN *a6)
{
  *a4 = Fp_neg(Fp_mulu(c4, 27, p), p);
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

static GEN
ell_to_a4a6_bc(GEN E, GEN p)
{
  GEN a1, a3, b2, c4, c6;
  a1 = Rg_to_Fp(ell_get_a1(E),p);
  a3 = Rg_to_Fp(ell_get_a3(E),p);
  b2 = Rg_to_Fp(ell_get_b2(E),p);
  c4 = Rg_to_Fp(ell_get_c4(E),p);
  c6 = Rg_to_Fp(ell_get_c6(E),p);
  /* [-27c4, -54c6, [6,3b2,3a1,108a3]] */
  retmkvec3(Fp_neg(Fp_mulu(c4, 27, p), p), Fp_neg(Fp_mulu(c6, 54, p), p),
            mkvec4(modsi(6,p),Fp_mulu(b2,3,p),Fp_mulu(a1,3,p),Fp_mulu(a3,108,p)));
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

static int
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

/* 4 X^3 + b2 X^2 + 2b4 X + b6, N is the characteristic of the base
 * ring of NULL (char = 0) */
static GEN
RHSpol(GEN e, GEN N)
{
  GEN b2 = ell_get_b2(e), b6 = ell_get_b6(e), b42 = gmul2n(ell_get_b4(e),1);
  return mkpoln(4, N? modsi(4,N): utoipos(4), b2, b42, b6);
}

static int
invcmp(void *E, GEN x, GEN y) { (void)E; return -gcmp(x,y); }

static GEN
doellR_roots(GEN e, long prec)
{
  GEN R = roots(RHSpol(e,NULL), prec);
  long s = ellR_get_sign(e);
  if (s > 0)
  { /* sort 3 real roots in decreasing order */
    R = real_i(R);
    gen_sort_inplace(R, NULL, &invcmp, NULL);
  } else if (s < 0)
  { /* make sure e1 is real, imag(e2) > 0 and imag(e3) < 0 */
    gel(R,1) = real_i(gel(R,1));
    if (signe(gmael(R,2,2)) < 0) swap(gel(R,2), gel(R,3));
  }
  return R;
}
static GEN
ellR_root(GEN e, long prec) { return gel(ellR_roots(e,prec),1); }

/* x^3 + a2 x^2 + a4 x + a6 */
static GEN
ellRHS(GEN e, GEN x)
{
  GEN z;
  z = gadd(ell_get_a2(e),x);
  z = gadd(ell_get_a4(e), gmul(x,z));
  z = gadd(ell_get_a6(e), gmul(x,z));
  return z;
}

/* a1 x + a3 */
static GEN
ellLHS0(GEN e, GEN x)
{
  GEN a1 = ell_get_a1(e);
  GEN a3 = ell_get_a3(e);
  return gequal0(a1)? a3: gadd(a3, gmul(x,a1));
}

static GEN
ellLHS0_i(GEN e, GEN x)
{
  GEN a1 = ell_get_a1(e);
  GEN a3 = ell_get_a3(e);
  return signe(a1)? addii(a3, mulii(x, a1)): a3;
}

/* y^2 + a1 xy + a3 y */
static GEN
ellLHS(GEN e, GEN z)
{
  GEN y = gel(z,2);
  return gmul(y, gadd(y, ellLHS0(e,gel(z,1))));
}

/* 2y + a1 x + a3 */
static GEN
d_ellLHS(GEN e, GEN z)
{
  return gadd(ellLHS0(e, gel(z,1)), gmul2n(gel(z,2),1));
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
  err_printf("%Ps - (%Ps)\n", ellLHS(e, z), ellRHS(e, pol_x(vx)));
  (void)delete_var();
  (void)delete_var(); avma = av;
}

/* compute a,b such that E1: y^2 = x(x-a)(x-b) ~ E */
static GEN
doellR_ab(GEN E, long prec)
{
  GEN b2 = ell_get_b2(E), b4 = ell_get_b4(E), e1 = ellR_root(E, prec);
  GEN a, b, t, w;

  t = gmul2n(gadd(gmulsg(12,e1), b2), -2); /* = (12 e1 + b2) / 4 */
  w = sqrtr( gmul2n(gadd(b4, gmul(e1,gadd(b2, mulur(6,e1)))),1) );
  if (gsigne(t) > 0) setsigne(w, -1);
  /* w^2 = 2b4 + 2b2 e1 + 12 e1^2 = 4(e1-e2)(e1-e3) */
  a = gmul2n(gsub(w,t),-2);
  b = gmul2n(w,-1); /* = sqrt( (e1 - e2)(e1 - e3) ) */
  return mkvec2(a, b);
}
GEN
ellR_ab(GEN E, long prec)
{ return obj_checkbuild_prec(E, R_AB, &doellR_ab, prec); }

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
    default:
      pari_err_TYPE("elliptic curve base_ring", *pp);
      return 0;
  }
  /* Possible cases:
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
      default: /* base ring too general */
        return t_COMPLEX;
    }
  }
  *pp = p; *prec = e; return t;
}

static GEN
ellinit_Rg(GEN x, int real, long prec)
{
  pari_sp av=avma;
  GEN y;
  long s;
  if (!(y = initsmall(x, 4))) return NULL;
  s = real? gsigne( ell_get_disc(y) ): 0;
  gel(y,14) = mkvecsmall(t_ELL_Rg);
  gel(y,15) = mkvec(mkvecsmall2(prec2nbits(prec), s));
  return gerepilecopy(av, y);
}

static GEN
ellinit_Qp(GEN x, GEN p, long prec)
{
  pari_sp av=avma;
  GEN y;
  if (lg(x) > 6) x = vecslice(x,1,5);
  x = QpV_to_QV(x); /* make entries rational */
  if (!(y = initsmall(x, 2))) return NULL;
  gel(y,14) = mkvecsmall(t_ELL_Qp);
  gel(y,15) = mkvec(zeropadic(p, prec));
  return gerepilecopy(av, y);
}

static GEN
ellinit_Q(GEN x, long prec)
{
  pari_sp av=avma;
  GEN y;
  long s;
  if (!(y = initsmall(x, 8))) return NULL;
  s = gsigne( ell_get_disc(y) );
  gel(y,14) = mkvecsmall(t_ELL_Q);
  gel(y,15) = mkvec(mkvecsmall2(prec2nbits(prec), s));
  return gerepilecopy(av, y);
}

static GEN
ellinit_Fp(GEN x, GEN p)
{
  pari_sp av=avma;
  long i;
  GEN y, disc;
  if (!(y = initsmall(x, 4))) return NULL;
  if (cmpiu(p,3)<=0) /* ell_to_a4a6_bc does not handle p<=3 */
  {
    y = FF_ellinit(y,p_to_FF(p,0));
    if (!y) return NULL;
    return gerepilecopy(av, y);
  }
  disc = Rg_to_Fp(ell_get_disc(y),p);
  if (!signe(disc)) return NULL;
  for(i=1;i<=13;i++)
    gel(y,i) = Fp_to_mod(Rg_to_Fp(gel(y,i),p),p);
  gel(y,14) = mkvecsmall(t_ELL_Fp);
  gel(y,15) = mkvec2(p, ell_to_a4a6_bc(y, p));
  return gerepilecopy(av, y);
}

static GEN
ellinit_Fq(GEN x, GEN fg)
{
  pari_sp av=avma;
  GEN y;
  if (!(y = initsmall(x, 4))) return NULL;
  y = FF_ellinit(y,fg);
  return y ? gerepilecopy(av, y): NULL;
}

GEN
ellinit(GEN x, GEN p, long prec)
{
  pari_sp av = avma;
  GEN y;
  switch(typ(x))
  {
    case t_STR: x = gel(ellsearchcurve(x),2); break;
    case t_VEC: break;
    default: pari_err_TYPE("ellxxx [not an elliptic curve (ell5)]",x);
  }
  switch (base_ring(x, &p, &prec))
  {
  case t_PADIC:
    y = ellinit_Qp(x, p, prec);
    break;
  case t_INTMOD:
    y = ellinit_Fp(x, p);
    break;
  case t_FFELT:
    y = ellinit_Fq(x, p);
    break;
  case t_FRAC:
    y = ellinit_Q(x, prec);
    break;
  case t_REAL:
    y = ellinit_Rg(x, 1, prec);
    break;
  default:
    y = ellinit_Rg(x, 0, prec);
  }
  if (!y) { avma = av; return cgetg(1,t_VEC); }
  return y;
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
  gel(y,3) = ellLHS0(e,r);
  /* A4 = 3r^2 + 2a2 r + a4 */
  gel(y,4) = gadd(ell_get_a4(e), gmul(r,gadd(gmul2n(a2,1),rx3)));
  /* A6 = r^3 + a2 r^2 + a4 r + a6 */
  gel(y,5) = ellRHS(e,r);
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
    obj_insert(E, Qp_ROOT, gdiv(gsub(S, r), u2));
  }
  if ((S = obj_check(e, Qp_TATE)))
  {
    GEN U2 = gel(S,1), U = gel(S,2), Q = gel(S,3), AB = gel(S,4);
    if (!u2) u2 = gsqr(u);
    U2 = gmul(U2, u2);
    U = gmul(U, u);
    AB = gdiv(AB, u2);
    obj_insert(E, Qp_TATE, mkvec4(U2,U,Q,AB));
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
    S = obj_insert(E, Q_GROUPGEN, ellchangepoint(S, w));
  if ((S = obj_check(e, Q_MINIMALMODEL)))
  {
    if (lg(S) == 2)
    { /* model was minimal */
      if (!is_trivial_change(w)) /* no longer minimal */
        S = mkvec3(gel(S,1), ellchangeinvert(w), e);
      (void)obj_insert(E, Q_MINIMALMODEL, S);
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
      (void)obj_insert(E, Q_MINIMALMODEL, S);
    }
  }
  if ((S = obj_check(e, Q_GLOBALRED)))
    S = obj_insert(E, Q_GLOBALRED, S);
  if ((S = obj_check(e, Q_ROOTNO)))
    S = obj_insert(E, Q_ROOTNO, S);
  return E;
}

static void
ch_FF(GEN E, GEN e, GEN w)
{
  GEN S;
  if ((S = obj_check(e, FF_CARD)))
    S = obj_insert(E, FF_CARD, S);
  if ((S = obj_check(e, FF_GROUP)))
    S = obj_insert(E, FF_GROUP, S);
  if ((S = obj_check(e, FF_GROUPGEN)))
    S = obj_insert(E, FF_GROUPGEN, ellchangepoint(S, w));
  if ((S = obj_check(e, FF_O)))
    S = obj_insert(E, FF_O, S);
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
  if (lg(E) == 6) return gerepilecopy(av, E);
  ell_reset(E); E = gerepilecopy(av, E);
  switch(ell_get_type(E))
  {
    case t_ELL_Qp: E = ch_Qp(E,e,w); break;
    case t_ELL_Fp: E = ch_Fp(E,e,w); break;
    case t_ELL_Fq: E = ch_Fq(E,e,w); break;
    case t_ELL_Q:  E = ch_Q(E,e,w);  break;
    case t_ELL_Rg: E = ch_Rg(E,e,w); break;
  }
  return E;
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

/* apply [1,r,0,0] to P */
static GEN
ellchangepoint_r(GEN P, GEN r)
{
  GEN x, y, a;
  if (ell_is_inf(P)) return P;
  x = gel(P,1); y = gel(P,2); a = gsub(x,r);
  return mkvec2(a, y);
}

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
  av = avma;
  LHS = ellLHS(e,z);
  RHS = ellRHS(e,gel(z,1)); x = gsub(LHS,RHS);
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

  checkell5(e);
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

GEN
elladd(GEN e, GEN z1, GEN z2)
{
  GEN p1, p2, x, y, x1, x2, y1, y2;
  pari_sp av = avma, tetpil;

  checkell5(e); checkellpt(z1); checkellpt(z2);
  if (ell_is_inf(z1)) return gcopy(z2);
  if (ell_is_inf(z2)) return gcopy(z1);

  x1 = gel(z1,1); y1 = gel(z1,2);
  x2 = gel(z2,1); y2 = gel(z2,2);
  if (x1 == x2 || gequal(x1,x2))
  { /* y1 = y2 or -LHS0-y2 */
    if (y1 != y2)
    {
      int eq;
      if (precision(y1) || precision(y2))
        eq = (gexpo(gadd(ellLHS0(e,x1),gadd(y1,y2))) >= gexpo(y1));
      else
        eq = gequal(y1,y2);
      if (!eq) { avma = av; return ellinf(); }
    }
    p2 = d_ellLHS(e,z1);
    if (gequal0(p2)) { avma = av; return ellinf(); }
    p1 = gadd(gsub(ell_get_a4(e),gmul(ell_get_a1(e),y1)),
              gmul(x1,gadd(gmul2n(ell_get_a2(e),1),gmulsg(3,x1))));
  }
  else {
    p1 = gsub(y2,y1);
    p2 = gsub(x2,x1);
  }
  p1 = gdiv(p1,p2);
  x = gsub(gmul(p1,gadd(p1,ell_get_a1(e))), gadd(gadd(x1,x2),ell_get_a2(e)));
  y = gadd(gadd(y1, ellLHS0(e,x)), gmul(p1,gsub(x,x1)));
  tetpil = avma; p1 = cgetg(3,t_VEC);
  gel(p1,1) = gcopy(x);
  gel(p1,2) = gneg(y); return gerepile(av,tetpil,p1);
}

static GEN
ellneg_i(GEN e, GEN z)
{
  GEN t;
  if (ell_is_inf(z)) return z;
  t = cgetg(3,t_VEC);
  gel(t,1) = gel(z,1);
  gel(t,2) = gneg_i(gadd(gel(z,2), ellLHS0(e,gel(z,1))));
  return t;
}

GEN
ellneg(GEN e, GEN z)
{
  pari_sp av;
  GEN t, y;
  checkell5(e); checkellpt(z);
  if (ell_is_inf(z)) return z;
  t = cgetg(3,t_VEC);
  gel(t,1) = gcopy(gel(z,1));
  av = avma;
  y = gneg(gadd(gel(z,2), ellLHS0(e,gel(z,1))));
  gel(t,2) = gerepileupto(av, y);
  return t;
}

GEN
ellsub(GEN e, GEN z1, GEN z2)
{
  pari_sp av = avma;
  checkell5(e); checkellpt(z2);
  return gerepileupto(av, elladd(e, z1, ellneg_i(e,z2)));
}

/* E an ell, x a scalar */
static GEN
ellordinate_i(GEN E, GEN x, long prec)
{
  pari_sp av = avma;
  GEN a = ellRHS(E,x), b = ellLHS0(E,x), D = gadd(gsqr(b), gmul2n(a,2));
  GEN d, y, p;

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
  y = gsub( gmul(d_ellLHS(e,z), y), ellLHS0(e,x));
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
  if (lg(e)==17 && ell_over_Fq(e)) return ellffmul(e,z,n);
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
  checkell(e);
  if (typ(a) != t_INT) pari_err_TYPE("ellmul_CM",a);
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

  checkell5(e); checkellpt(z);
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
  GEN e1=gel(roots,1), e2=gel(roots,2), e3=gel(roots,3);
  GEN a = gsqrt(gsub(e1,e2),prec);
  GEN b = gsqrt(gsub(e2,e3),prec);
  GEN c = gsqrt(gsub(e1,e3),prec);
  return gerepileupto(av, ellomega_agm(a,b,c,prec));
}

/* return [w1,w2] for E / R; w1 > 0 is real.
 * If e.disc > 0, w2 = -I r; else w2 = w1/2 - I r, for some real r > 0.
 * => tau = w1/w2 is in upper half plane */
static GEN
doellR_omega(GEN E, long prec)
{
  pari_sp av = avma;
  GEN roots, e1, e3, z, a, b, c;
  if (ellR_get_sign(E) >= 0) return ellomega_cx(E,prec);
  roots = ellR_roots(E,prec);
  e1 = gel(roots,1);
  e3 = gel(roots,3);
  z = gsqrt(gsub(e1,e3),prec); /* imag(e1-e3) > 0, so that b > 0*/
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
{ return obj_checkbuild_prec(E, R_PERIODS, &doellR_omega, prec); }
GEN
ellR_eta(GEN E, long prec)
{ return obj_checkbuild_prec(E, R_ETA, &doellR_eta, prec); }
GEN
ellR_roots(GEN E, long prec)
{ return obj_checkbuild_prec(E, R_ROOTS, &doellR_roots, prec); }

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
  GEN roots = ellR_roots(E, prec+EXTRAPRECWORD);
  GEN x0 = gel(P,1), y0 = d_ellLHS(E,P);
  if (gequal0(y0))
    return zell_closest_0(ellomega_cx(E,prec),x0,roots);
  else
  {
    GEN e1 = gel(roots,1), e2 = gel(roots,2), e3 = gel(roots,3);
    GEN a = gsqrt(gsub(e1,e3),prec), b = gsqrt(gsub(e1,e2),prec);
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
  GEN x0 = gel(P,1), y0 = d_ellLHS(E,P);
  if (gequal0(y0)) return gmul2n(gel(ellR_omega(E,prec),1),-1);
  else
  {
    GEN roots = ellR_roots(E, prec+EXTRAPRECWORD);
    GEN e1 = gel(roots,1), e3 = gel(roots,3);
    GEN a = gsqrt(gsub(e1,e3),prec);
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
  GEN roots = ellR_roots(E, prec+EXTRAPRECWORD);
  GEN e1,e2,e3, a,b, x0 = gel(P,1), y0 = d_ellLHS(E,P);
  if (gequal0(y0)) return zell_closest_0(ellR_omega(E,prec), x0,roots);
  e1 = gel(roots,1);
  e2 = gel(roots,2);
  e3 = gel(roots,3);
  a = gsqrt(gsub(e1,e3),prec);
  b = gsqrt(gsub(e1,e2),prec);
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
    long v = fetch_user_var("u");
    GEN T = mkpoln(3, gen_1, gen_0, gneg(u2));
    setvarn(T, v); u = mkpolmod(pol_x(v), T);
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
  y0 = gdiv(gadd(y, gmul2n(d_ellLHS(E,z), -1)), gsubsg(1, gdiv(ar1,gsqr(x0))));

  x1 = gmul(x0, gsqr(gmul2n(gaddsg(1, Qp_sqrt(gdiv(gadd(x0,r1),x0))),-1)));
  y1 = gdiv(y0, gsubsg(1, gsqr(gdiv(r1,gmul2n(x1,2)))));
  if (gequal0(x1)) pari_err_PREC("ellpointtoz");

  (void)do_padic_agm(&x1,&y1, a,b);
  t = gmul(ellQp_u(E, prec), gmul2n(y1,1)); /* 2u y_oo */
  t = gdiv(gsub(t, x1), gadd(t, x1));
  return gerepileupto(av, t);
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
  pari_sp av = avma, lim = stack_lim(av, 1);

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
    if (low_stack(lim, stack_lim(av, 1))) {
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
  pari_sp lim, av;
  GEN p1, q, y, qn;
  long n = 1;

  if (k == 2) return trueE2(tau, prec);
  q = expIxy(Pi2n(1, prec), tau, prec);
  q = check_real(q);
  y = gen_0;
  av = avma; lim = stack_lim(av,2); qn = gen_1;
  for(;; n++)
  { /* compute y := sum_{n>0} n^(k-1) q^n / (1-q^n) */
    qn = gmul(q,qn);
    p1 = gdiv(gmul(powuu(n,k-1),qn), gsubsg(1,qn));
    if (gequal0(p1) || gexpo(p1) <= - prec2nbits(prec) - 5) break;
    y = gadd(y, p1);
    if (low_stack(lim, stack_lim(av,2)))
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
get_toadd(GEN z) { return (2*PI/LOG2)*gtodouble(imag_i(z)); }

/* computes the numerical value of wp(z | L), L = om1 Z + om2 Z
 * return NULL if z in L.  If flall=1, compute also wp' */
static GEN
ellwpnum_all(GEN e, GEN z, long flall, long prec)
{
  long toadd;
  pari_sp av = avma, lim, av1;
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
  if (gequal0(u2)) return NULL; /* possible if loss of accuracy */
  y = gdiv(u,u2); /* -1/4(sin^2(Pi Z)) */
  if (T.abs_u_is_1) y = real_i(y);
  simple_case = T.abs_u_is_1 && T.q_is_real;
  y = gadd(mkfrac(gen_1, utoipos(12)), y);
  yp = flall? gdiv(gaddsg(1,u), gmul(u1,u2)): NULL;
  toadd = (long)ceil(get_toadd(T.Z));

  av1 = avma; lim = stack_lim(av1,1); qn = q;
  for(;;)
  { /* y += u q^n [ 1/(1-q^n u)^2 + 1/(q^n-u)^2 ] - 2q^n /(1-q^n)^2 */
    /* analogous formula for yp */
    GEN yadd, ypadd = NULL;
    GEN qnu = gmul(qn,u); /* q^n u */
    GEN a = gsubsg(1,qnu);/* 1 - q^n u */
    GEN a2 = gsqr(a);     /* (1 - q^n u)^2 */
    if (yp) ypadd = gdiv(gaddsg(1,qnu),gmul(a,a2));
    if (simple_case)
    { /* conj(u) = 1/u: formula simplifies */
      yadd = gdiv(u, a2);
      yadd = gmul2n(real_i(yadd), 1);
      if (yp) ypadd = gmul2n(real_i(ypadd), 1);
    }
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
    if (low_stack(lim, stack_lim(av1,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ellwp");
      gerepileall(av1, flall? 3: 2, &y, &qn, &yp);
    }
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
    pari_sp av1 = avma, lim = stack_lim(av1,1);
    GEN qn;
    for (qn = q;;)
    { /* y += sum q^n ( u/(u*q^n - 1) + 1/(u - q^n) ) */
      GEN p1 = gadd(gdiv(u,gsubgs(gmul(qn,u),1)), ginv(gsub(u,qn)));
      y = gadd(y, gmul(qn,p1));
      qn = gmul(q,qn);
      if (gexpo(qn) <= - prec2nbits(prec) - 5 - toadd) break;
      if (low_stack(lim, stack_lim(av1,1)))
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
  pari_sp av = avma, lim, av1;
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
  av1 = avma; lim = stack_lim(av1,1);
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
    if (low_stack(lim, stack_lim(av1,1)))
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
  gel(v,2) = gsub(gel(v,2), gmul2n(ellLHS0(e,gel(v,1)),-1));
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
/* Here p > 3. e assumed integral, minim = 1 if we only want a minimal model */
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

    t = negi(ellLHS0_i(e,r));
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

GEN
elllocalred(GEN e, GEN p)
{
  pari_sp av = avma;
  checkell_Q(e);
  if (typ(ell_get_disc(e)) != t_INT)
    pari_err_TYPE("elllocalred [not an integral curve]",e);
  if (typ(p) != t_INT) pari_err_TYPE("elllocalred [prime]",p);
  if (signe(p) <= 0) pari_err_PRIME("elllocalred",p);
  return gerepileupto(av, localred(e, p));
}

/* Return an integral model for e / Q. Set v = NULL (already integral)
 * or the variable change [u,0,0,0], u = 1/t, t > 1 integer making e integral */
static GEN
ellintegralmodel(GEN e, GEN *pv)
{
  GEN a = cgetg(6,t_VEC), t, u, L;
  long i, l, k;

  L = cgetg(1, t_VEC);
  for (i = 1; i < 6; i++)
  {
    GEN c = gel(e,i);
    gel(a,i) = c;
    switch(typ(c))
    {
      case t_INT: break;
      case t_FRAC: /* partial factorization */
        L = shallowconcat(L, gel(Z_factor_limit(gel(c,2), 0),1));
        break;
      default: pari_err_TYPE("ellintegralmodel [not a rational curve]",e);
    }
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
  t = shifti(subii(M->a3? M->u3: gen_0, ellLHS0(E,r)), -1);
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
  pari_sp av = avma;
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
    S = mkvec(c4c6P);
  else
    S = mkvec3(c4c6P, v, y);
  S = gclone(S);
  y = gerepilecopy(av, y);
  obj_insert_shallow(E, Q_MINIMALMODEL, S);
  *ptv = lg(S) == 2? init_ch(): gel(S,2);
  return y;
}
GEN
ellminimalmodel(GEN E, GEN *ptv)
{
  GEN S, y, v;
  checkell_Q(E);
  y = ellminimalmodel_i(E, &v);
  if (!is_trivial_change(v)) ch_Q(y, E, v);
  if (ptv) *ptv = gcopy(v);
  S = obj_check(E, Q_MINIMALMODEL);
  obj_insert(y, Q_MINIMALMODEL, mkvec(gel(S,1)));
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

/* assume e has good reduction mod p */
static long
ellap_small_goodred(int CM, GEN E, ulong p)
{
  ulong a4, a6;
  if (p == 2) return 3 - cardmod2(E);
  if (p == 3) return 4 - cardmod3(E);
  Fl_ell_to_a4a6(E, p, &a4, &a6);
  return CM? Fl_elltrace_CM(CM, a4, a6, p): Fl_elltrace(a4, a6, p);
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

static int
ell_get_CM(GEN e)
{
  GEN j = ell_get_j(e);
  int CM = 0;
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
GEN
anellsmall(GEN e, long n0)
{
  pari_sp av;
  ulong p, m, SQRTn, n = (ulong)n0;
  GEN an, D;
  int CM;

  checkell_int(e);
  if (n0 <= 0) return cgetg(1,t_VEC);
  if (n >= LGBITS)
    pari_err_IMPL( stack_sprintf("ellan for n >= %lu", LGBITS) );
  SQRTn = (ulong)sqrt(n);
  D = ell_get_disc(e);
  CM = ell_get_CM(e);

  an = cgetg(n+1,t_VECSMALL); an[1] = 1;
  av = avma;
  for (p=2; p <= n; p++) an[p] = LONG_MAX; /* not computed yet */
  for (p=2; p<=n; p++)
  {
    long ap;
    if (an[p] != LONG_MAX) continue; /* p not prime */
    if (!umodiu(D,p)) /* p | D, bad reduction or non-minimal model */
    {
      int good_red;
      ap = is_minimal_ap_small(e, p, &good_red);
      if (good_red) goto GOOD_RED;
      switch (ap) /* (-c6/p) */
      {
        case -1: { /* non-split */
          ulong N = n/p;
          for (m=1; m<=N; m++)
            if (an[m] != LONG_MAX) an[m*p] = -an[m];
          break;
        }
        case 0: /* additive */
          for (m=p; m<=n; m+=p) an[m] = 0;
          break;
        case 1: { /* split */
          ulong N = n/p;
          for (m=1; m<=N; m++)
            if (an[m] != LONG_MAX) an[m*p] = an[m];
          break;
        }
      }
    }
    else /* good reduction */
    {
      ap = ellap_small_goodred(CM, e, p);
GOOD_RED:
      if (p <= SQRTn) {
        ulong pk, oldpk = 1;
        for (pk=p; pk <= n; oldpk=pk, pk *= p)
        {
          if (pk == p)
            an[pk] = ap;
          else
            an[pk] = ap * an[oldpk] - p * an[oldpk/p];
          for (m = n/pk; m > 1; m--)
            if (an[m] != LONG_MAX && m%p) an[m*pk] = an[m] * an[pk];
        }
      } else {
        an[p] = ap;
        for (m = n/p; m > 1; m--)
          if (an[m] != LONG_MAX) an[m*p] = ap * an[m];
      }
    }
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
  pari_sp av = avma, av1, lim;
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
  av1 = avma; lim = stack_lim(av1,1);
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
    if (low_stack(lim, stack_lim(av1,1)))
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

/* h' := h_oo(a) + 1/2 log(denom(a)) */
static GEN
hell(GEN e, GEN a, long prec)
{
  long n;
  pari_sp av = avma;
  GEN pi2 = Pi2n(1, prec);
  GEN om = ellR_omega(e,prec), w1 = gel(om,1), w2 = gel(om,2);
  GEN p1, y, z, q, pi2surw, qn, ps;

  pi2surw = gdiv(pi2, w1);
  z = gmul(real_i(zell(e,a,prec)), pi2surw);
  q = real_i( expIxy(mpneg(pi2surw), w2, prec) );
  y = mpsin(z); qn = gen_1; ps = gneg_i(q);
  for (n = 3; ; n += 2)
  {
    qn = gmul(qn, ps);
    ps = gmul(ps, q);
    y = gadd(y, gmul(qn, gsin(gmulsg(n,z),prec)));
    if (gexpo(qn) < -prec2nbits(prec)) break;
  }
  p1 = gmul(gsqr(gdiv(gmul2n(y,1), d_ellLHS(e,a))), pi2surw);
  p1 = gsqr(gsqr(gdiv(p1, gsqr(gsqr(denom(gel(a,1)))))));
  p1 = gdiv(gmul(p1,q), ell_get_disc(e));
  p1 = gmul2n(glog(gabs(p1,prec),prec), -5);
  return gerepileupto(av, gneg(p1));
}

static GEN
Q_numer(GEN x) { return typ(x) == t_INT? x: gel(x,1); }

/* h' := h_oo(x) + 1/2 log(denom(x)) */
static GEN
hells(GEN e, GEN Q, long prec)
{
  GEN b2 = ell_get_b2(e);
  GEN b4 = ell_get_b4(e);
  GEN b6 = ell_get_b6(e);
  GEN b8 = ell_get_b8(e);
  GEN x = gel(Q,1), w, z, t, mu, b42, b62;
  long n, lim;

  mu = gmul2n(glog(Q_numer(x),prec),-1);
  t = ginv(gtofp(x, prec));
  b42 = gmul2n(b4,1);
  b62 = gmul2n(b6,1);
  lim = 15 + prec2nbits(prec);
  for (n = 3; n < lim; n += 2)
  {
    /* 4 + b2 t + 2b4 t^2 + b6 t^3 */
    w = gmul(t, gaddsg(4, gmul(t, gadd(b2, gmul(t, gadd(b42, gmul(t, b6)))))));
    /* 1 - (b4 t^2 + 2b6 t^3 + b8 t^4) */
    z = gsubsg(1, gmul(gsqr(t), gadd(b4, gmul(t, gadd(b62, gmul(t, b8))))));
    mu = gadd(mu, gmul2n(glog(z,prec), -n));
    t = gdiv(w, z);
  }
  return mu;
}

static GEN
hell2(GEN e, GEN x, long prec)
{
  GEN e3, ro, r;
  pari_sp av = avma;

  if (ell_is_inf(x)) return gen_0;
  ro= ellR_roots(e, prec);
  e3 = (ellR_get_sign(e) < 0)? gel(ro,1): gel(ro,3);
  r = addis(gfloor(e3),-1);
  e = coordch_r(e, r);
  x = ellchangepoint_r(x, r);
  return gerepileupto(av, hells(e, x, prec));
}

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
  GEN x_a, a, b, e1, r, V = cgetg(1, t_VEC), x = gel(z,1);
  long n, ex = 5-prec2nbits(prec), p = prec+EXTRAPRECWORD;

  if (typ(x) == t_REAL && realprec(x) < p) x = gprec_w(x, p);
  e1 = ellR_root(e, p);
  {
    GEN ab = ellR_ab(e, p);
    a = gel(ab, 1);
    b = gel(ab, 2);
  }
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

/* exp( 4h_oo(z) ) */
static GEN
exp4hellagm(GEN E, GEN z, long prec)
{
  if (!ellR_on_neutral(E, z, prec))
  {
    GEN eh = exphellagm(E, elladd(E, z,z), 0, prec);
    /* h_oo(2P) = 4h_oo(P) - log |2y + a1x + a3| */
    return gmul(eh, gabs(d_ellLHS(E, z), prec));
  }
  return exphellagm(E, z, 1, prec);
}

GEN
ellheightoo(GEN E, GEN z, long prec)
{
  pari_sp av = avma;
  GEN h;
  checkell_Q(E);
  if (!ellR_on_neutral(E, z, prec))
  {
    GEN eh = exphellagm(E, elladd(E, z,z), 0, prec);
    /* h_oo(2P) = 4h_oo(P) - log |2y + a1x + a3| */
    h = gmul(eh, gabs(d_ellLHS(E, z), prec));
  }
  else
    h = exphellagm(E, z, 1, prec);
  return gerepileuptoleaf(av, gmul2n(mplog(h), -2));
}

GEN
ellheight0(GEN e, GEN a, long flag, long prec)
{
  long i, tx = typ(a), lx;
  pari_sp av = avma;
  GEN Lp, x, y, z, phi2, psi2, psi3;
  GEN v, S, b2, b4, b6, b8, a1, a2, a4, c4, D;

  if (flag > 2 || flag < 0) pari_err_FLAG("ellheight");
  checkell_Q(e); if (!is_matvec_t(tx)) pari_err_TYPE("ellheight",a);
  lx = lg(a); if (lx==1) return cgetg(1,tx);
  tx = typ(gel(a,1));
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
  if (is_matvec_t(tx))
  {
    z = cgetg(lx,tx);
    for (i=1; i<lx; i++) gel(z,i) = ellheight0(e,gel(a,i),flag,prec);
    return z;
  }
  if (ell_is_inf(a)) return gen_0;
  if (!oncurve(e,a))
    pari_err_DOMAIN("ellheight", "point", "not on", strtoGENstr("E"),a);
  psi2 = Q_numer(d_ellLHS(e,a));
  if (!signe(psi2)) { avma = av; return gen_0; }
  switch(flag)
  {
    case 0:  z = hell2(e,a,prec); break; /* Tate 4^n */
    case 1:  z = hell(e,a,prec);  break; /* Silverman's log(sigma) */
    default:
    {
      GEN d = denom(gel(a,1));
      z = exp4hellagm(e,a,prec); /* = exp(4h_oo(a)), Mestre's AGM */
      if (!is_pm1(d)) z = gmul(z, sqri(d));
      z = gmul2n(mplog(z), -2); break;
    }
  }
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
ghell(GEN e, GEN a, long prec) { return ellheight0(e,a,2,prec); }

GEN
mathell(GEN e, GEN x, long prec)
{
  GEN y, h, pdiag;
  long lx = lg(x),i,j,tx=typ(x);
  pari_sp av = avma;

  if (!is_vec_t(tx)) pari_err_TYPE("ellheightmatrix",x);
  y = cgetg(lx,t_MAT); pdiag = new_chunk(lx);
  for (i=1; i<lx; i++)
  {
    gel(pdiag,i) = ghell(e,gel(x,i),prec);
    gel(y,i) = cgetg(lx,t_COL);
  }
  for (i=1; i<lx; i++)
  {
    gcoeff(y,i,i) = gel(pdiag,i);
    for (j=i+1; j<lx; j++)
    {
      h = ghell(e, elladd(e,gel(x,i),gel(x,j)), prec);
      h = gsub(h, gadd(gel(pdiag,i),gel(pdiag,j)));
      gcoeff(y,j,i) = gcoeff(y,i,j) = gmul2n(h, -1);
    }
  }
  return gerepilecopy(av,y);
}

static GEN
bilhells(GEN e, GEN z1, GEN z2, GEN h2, long prec)
{
  long lz1=lg(z1), tx, i;
  pari_sp av = avma;
  GEN y,p1,p2;

  if (lz1==1) return cgetg(1,typ(z1));

  tx = typ(gel(z1,1));
  if (!is_matvec_t(tx))
  {
    p1 = ghell(e, elladd(e,z1,z2),prec);
    p2 = gadd(h2, ghell(e,z1,prec));
    return gerepileupto(av, gmul2n(gsub(p1,p2), -1));
  }
  y = cgetg(lz1, typ(z1));
  for (i=1; i<lz1; i++) gel(y,i) = bilhells(e,gel(z1,i),z2,h2,prec);
  return y;
}

GEN
bilhell(GEN e, GEN z1, GEN z2, long prec)
{
  GEN p1, h2;
  long tz1 = typ(z1), tz2 = typ(z2);
  pari_sp av = avma;

  if (!is_matvec_t(tz1)) pari_err_TYPE("ellbil",z1);
  if (!is_matvec_t(tz2)) pari_err_TYPE("ellbil",z2);
  if (lg(z1)==1) return cgetg(1,tz1);
  if (lg(z2)==1) return cgetg(1,tz2);

  tz1 = typ(gel(z1,1));
  tz2 = typ(gel(z2,1));
  if (is_matvec_t(tz2))
  {
    if (is_matvec_t(tz1)) pari_err_TYPE("bilhell",z1);
    p1 = z1; z1 = z2; z2 = p1;
  }
  h2 = ghell(e,z2,prec);
  return gerepileupto(av, bilhells(e,z1,z2,h2,prec));
}

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
  w = gsub(w, ellLHS0(e,x));
  c = cgetg(3,t_VEC);
  gel(c,1) = gcopy(x);
  gel(c,2) = gmul2n(w,-1); return gerepileupto(av, c);
}

/********************************************************************/
/**                                                                **/
/**                       TORSION POINTS (over Q)                  **/
/**                                                                **/
/********************************************************************/
static int
smaller_x(GEN p, GEN q)
{
  int s = absi_cmp(denom(p), denom(q));
  return (s<0 || (s==0 && absi_cmp(numer(p),numer(q)) < 0));
}

/* best generator in cycle of length k */
static GEN
best_in_cycle(GEN e, GEN p, long k)
{
  GEN p0 = p,q = p;
  long i;

  for (i=2; i+i<k; i++)
  {
    q = elladd(e,q,p0);
    if (ugcd(i,k)==1 && smaller_x(gel(q,1), gel(p,1))) p = q;
  }
  return (gsigne(d_ellLHS(e,p)) < 0)? ellneg_i(e,p): p;
}

/* <p,q> = E_tors, possibly NULL (= oo), p,q independent unless NULL
 * order p = k, order q = 2 unless NULL */
static GEN
tors(GEN e, long k, GEN p, GEN q, GEN v)
{
  GEN r;
  if (q)
  {
    long n = k>>1;
    GEN p1, best = q, np = ellmul_Z(e,p,utoipos(n));
    if (n % 2 && smaller_x(gel(np,1), gel(best,1))) best = np;
    p1 = elladd(e,q,np);
    if (smaller_x(gel(p1,1), gel(best,1))) q = p1;
    else if (best == np) { p = elladd(e,p,q); q = np; }
    p = best_in_cycle(e,p,k);
    if (v)
    {
      p = ellchangepointinv(p,v);
      q = ellchangepointinv(q,v);
    }
    r = cgetg(4,t_VEC);
    gel(r,1) = utoipos(2*k);
    gel(r,2) = mkvec2(utoipos(k), gen_2);
    gel(r,3) = mkvec2copy(p, q);
  }
  else
  {
    if (p)
    {
      p = best_in_cycle(e,p,k);
      if (v) p = ellchangepointinv(p,v);
      r = cgetg(4,t_VEC);
      gel(r,1) = utoipos(k);
      gel(r,2) = mkvec( gel(r,1) );
      gel(r,3) = mkvec( gcopy(p) );
    }
    else
    {
      r = cgetg(4,t_VEC);
      gel(r,1) = gen_1;
      gel(r,2) = cgetg(1,t_VEC);
      gel(r,3) = cgetg(1,t_VEC);
    }
  }
  return r;
}

static GEN
doellff_get_o(GEN E)
{
  GEN G = ellgroup(E, NULL), d1 = gel(G,1);
  return mkvec2(d1, Z_factor(d1));
}
GEN
ellff_get_o(GEN E)
{ return obj_checkbuild(E, FF_O, &doellff_get_o); };

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

/* assume e is defined over Q (use Mazur's theorem) */
static long
_orderell(GEN E, GEN P)
{
  pari_sp av = avma;
  GEN tmp, p, a4, dx, dy, d4, d6, D, Pp, Q;
  forprime_t T;
  ulong pp;
  long k;
  if (ell_is_inf(P)) return 1;

  dx = Q_denom(gel(P,1));
  dy = Q_denom(gel(P,2));
  if (ell_is_integral(E)) /* integral model, try Nagell Lutz */
    if (cmpiu(dx, 4) > 0 || cmpiu(dy, 8) > 0) return 0;

  d4 = Q_denom(ell_get_c4(E));
  d6 = Q_denom(ell_get_c6(E));
  D = ell_get_disc (E);
  /* choose not too small prime p dividing neither a coefficient of the
     short Weierstrass form nor of P and leading to good reduction      */

  u_forprime_init(&T, 100003, ULONG_MAX);
  while ( (pp = u_forprime_next(&T)) )
    if (Rg_to_Fl(d4, pp) && Rg_to_Fl(d6, pp) && Rg_to_Fl(D, pp)
     && Rg_to_Fl(dx, pp) && Rg_to_Fl(dy, pp)) break;

  /* transform E into short Weierstrass form Ep modulo p
     and P to Pp on Ep */
  p = utoipos(pp);
  tmp = ell_to_a4a6_bc(E, p);
  a4 = gel(tmp, 1);
  Pp = FpE_changepointinv(RgV_to_FpV(P, p), gel(tmp,3), p);

  /* check whether the order of Pp on Ep is <= 12 */
  for (Q = FpE_dbl(Pp, a4, p), k = 2;
       !ell_is_inf(Q) && k <= 12;
       Q = FpE_add(Q, Pp, a4, p), k++) /* empty */;

  if (k != 13)
    /* check over Q; one could also run more tests modulo primes */
    for (Q = elladd(E, P, P), k = 2;
        !ell_is_inf(Q) && k <= 12;
        Q = elladd(E, Q, P), k++) /* empty */;

  avma = av;
  return (k == 13 ? 0 : k);
}

GEN
ellorder(GEN E, GEN P, GEN o)
{
  pari_sp av = avma;
  GEN fg, r, E0 = E;
  checkell(E); checkellpt(P);
  if (ell_is_inf(P)) return gen_1;
  if (ell_get_type(E)==t_ELL_Q)
  {
    GEN p = NULL;
    if (is_rational_t(typ(gel(P,1))) && is_rational_t(typ(gel(P,2))))
      return utoi( _orderell(E, P) );
    if (RgV_is_FpV(P,&p) && p)
    {
      E = ellinit(E,p,0);
      if (lg(E)==1) pari_err_IMPL("ellorder for curve with singular reduction");
    }
  }
  checkell_Fq(E);
  fg = ellff_get_field(E);
  if (!o) o = ellff_get_o(E);
  if (typ(fg)==t_FFELT)
    r = FF_ellorder(E, P, o);
  else
  {
    GEN p = fg, e = ellff_get_a4a6(E);
    GEN Pp = FpE_changepointinv(RgE_to_FpE(P,p), gel(e,3), p);
    r = FpE_order(Pp, o, gel(e,1), p);
  }
  if (E != E0) obj_free(E);
  return gerepileuptoint(av, r);
}

GEN
orderell(GEN e, GEN z) { return ellorder(e,z,NULL); }

/* Using Lutz-Nagell */

/* p in Z[X] of degree 3. Return vector of x/4, x integral root of p */
static GEN
ratroot(GEN p)
{
  GEN L, a, ld;
  long i, t, v = ZX_valrem(p, &p);

  if (v == 3) return ellinf();
  if (v == 2) return mkvec2(gen_0, gmul2n(negi(gel(p,2)), -2));

  L = cgetg(4,t_VEC); t = 1;
  if (v == 1) gel(L,t++) = gen_0;
  ld = divisors(gel(p,2));
  for (i=1; i<lg(ld); i++)
  {
    a = gel(ld,i);
    if (!signe(poleval(p,a))) gel(L,t++) = gmul2n(a, -2);
    a = negi(a);
    if (!signe(poleval(p,a))) gel(L,t++) = gmul2n(a, -2);
  }
  setlg(L,t); return L;
}

static int
is_new_torsion(GEN e, GEN v, GEN p, long t2) {
  GEN pk = p, pkprec = NULL;
  long k,l;

  for (k=2; k<=6; k++)
  {
    pk = elladd(e,pk,p); /* = [k] p */
    if (ell_is_inf(pk)) return 1;

    for (l=2; l<=t2; l++)
      if (gequal(gel(pk,1),gmael(v,l,1))) return 1;

    if (pkprec && k<=5)
      if (gequal(gel(pk,1),gel(pkprec,1))) return 1;
    pkprec=pk;
  }
  return 0;
}

static GEN
nagelllutz(GEN e)
{
  GEN ld, pol, p1, lr, r, v, w2, w3;
  long i, j, nlr, t, t2, k, k2;
  pari_sp av=avma;

  e = ellintegralmodel(e, &v);
  pol = RgX_rescale(RHSpol(e,NULL), utoipos(4));
  r = cgetg(17, t_VEC);
  gel(r,1) = ellinf();
  lr = ratroot(pol); nlr=lg(lr)-1;
  for (t=1,i=1; i<=nlr; i++)
  {
    GEN x = gel(lr,i), y = gmul2n(gneg(ellLHS0(e,x)), -1);
    gel(r,++t) = mkvec2(x, y);
  }
  ld = absi_factor(gmul2n(ell_get_disc(e), 4));
  p1 = gel(ld,2); k = lg(p1);
  for (i=1; i<k; i++) gel(p1,i) = shifti(gel(p1,i), -1);
  ld = divisors(ld);
  for (t2=t,j=1; j<lg(ld); j++)
  {
    GEN d = gel(ld,j);
    lr = ratroot(ZX_Z_sub(pol, shifti(sqri(d), 6)));
    for (i=1; i<lg(lr); i++)
    {
      GEN x = gel(lr,i), y = gmul2n(gsub(d, ellLHS0(e,x)), -1);
      p1 = mkvec2(x, y);
      if (is_new_torsion(e,r,p1,t2))
      {
        gel(r,++t) = p1;
        gel(r,++t) = mkvec2(x, gsub(y, d));
      }
    }
  }
  if (t == 1) { avma = av; return tors(e,1,NULL,NULL,v); }

  if (nlr < 3)
  {
    w2 = mkvec( utoipos(t) );
    for (k=2; k<=t; k++)
      if (_orderell(e,gel(r,k)) == t) break;
    if (k>t) pari_err_BUG("elltors (bug1)");

    w3 = mkvec( gel(r,k) );
  }
  else
  {
    if (t&3) pari_err_BUG("elltors (bug2)");
    t2 = t>>1;
    w2 = mkvec2(utoipos(t2), gen_2);
    for (k=2; k<=t; k++)
      if (_orderell(e,gel(r,k)) == t2) break;
    if (k>t) pari_err_BUG("elltors (bug3)");

    p1 = ellmul_Z(e,gel(r,k),utoipos(t>>2));
    k2 = (!ell_is_inf(p1) && gequal(gel(r,2),p1))? 3: 2;
    w3 = mkvec2(gel(r,k), gel(r,k2));
  }
  if (v)
  {
    gel(v,1) = ginv(gel(v,1));
    w3 = ellchangepoint(w3,v);
  }
  return gerepilecopy(av, mkvec3(utoipos(t), w2,w3));
}

/* Using Doud's algorithm */

/* finds a bound for #E_tor */
static long
torsbound(GEN e)
{
  GEN D = ell_get_disc(e);
  pari_sp av = avma, av2;
  long m, b, bold, nb;
  forprime_t S;
  int CM = ell_get_CM(e);
  nb = expi(D) >> 3;
  /* nb = number of primes to try ~ 1 prime every 8 bits in D */
  b = bold = 5040; /* = 2^4 * 3^2 * 5 * 7 */
  m = 0;
  (void)u_forprime_init(&S, 3, ULONG_MAX);
  av2 = avma;
  while (m < nb || (b > 12 && b != 16))
  {
    ulong p = u_forprime_next(&S);
    if (!p) pari_err_BUG("torsbound [ran out of primes]");
    if (!umodiu(D, p)) continue;

    b = ugcd(b, p+1 - ellap_small_goodred(CM, e, p));
    avma = av2;
    if (b == 1) break;
    if (b == bold) m++; else { bold = b; m = 0; }
  }
  avma = av; return b;
}

static GEN
myround(GEN x, long *e)
{
  GEN y = grndtoi(x,e);
  if (*e > -5 && prec2nbits(gprecision(x)) < gexpo(y) - 10)
    pari_err_PREC("elltors");
  return y;
}

/* E the curve, w in C/Lambda ~ E of order n, returns q = pointell(w) as a
 * rational point on the curve, or NULL if q is not rational. */
static GEN
torspnt(GEN E, GEN w, long n, long prec)
{
  GEN p = cgetg(3,t_VEC), q = pointell(E, w, prec);
  long e;
  gel(p,1) = gmul2n(myround(gmul2n(gel(q,1),2), &e),-2);
  if (e > -5 || typ(gel(p,1)) == t_COMPLEX) return NULL;
  gel(p,2) = gmul2n(myround(gmul2n(gel(q,2),3), &e),-3);
  if (e > -5 || typ(gel(p,2)) == t_COMPLEX) return NULL;
  return (oncurve(E,p)
      && ell_is_inf(ellmul_Z(E,p,utoipos(n)))
      && _orderell(E,p) == n)? p: NULL;
}

static GEN
elltors_doud(GEN e)
{
  long B, i, ord, prec, k = 1;
  pari_sp av=avma;
  GEN v,w,w1,w22,w1j,w12,p,tor1,tor2;
  GEN om;

  e = ellintegralmodel(e, &v);
  B = torsbound(e); /* #E_tor | B */
  if (B == 1) { avma = av; return tors(e,1,NULL,NULL, v); }

  /* prec >= size of sqrt(D) */
  prec = DEFAULTPREC + ((lgefint(ell_get_disc(e))-2) >> 1);
  om = ellR_omega(e, prec);
  w1 = gel(om,1);
  w22 = gmul2n(gel(om,2),-1);
  if (B % 4)
  { /* cyclic of order 1, p, 2p, p <= 5 */
    p = NULL;
    for (i=10; i>1; i--)
    {
      if (B%i != 0) continue;
      w1j = gdivgs(w1,i);
      p = torspnt(e,w1j,i,prec);
      if (!p && i%2==0)
      {
        p = torspnt(e,gadd(w22,w1j),i,prec);
        if (!p) p = torspnt(e,gadd(w22,gmul2n(w1j,1)),i,prec);
      }
      if (p) { k = i; break; }
    }
    return gerepileupto(av, tors(e,k,p,NULL, v));
  }

  ord = 0; tor1 = tor2 = NULL;
  w12 = gmul2n(w1,-1);
  if ((p = torspnt(e,w12,2,prec))) { tor1 = p; ord++; }
  w = w22;
  if ((p = torspnt(e,w,2,prec))) { tor2 = p; ord += 2; }
  if (!ord)
  {
    w = gadd(w12,w22);
    if ((p = torspnt(e,w,2,prec))) { tor2 = p; ord += 2; }
  }
  p = NULL;
  switch(ord)
  {
    case 0: /* no point of order 2 */
      for (i=9; i>1; i-=2)
      {
        if (B%i != 0) continue;
        w1j = gdivgs(w1,i);
        p = torspnt(e,w1j,i,prec);
        if (p) { k = i; break; }
      }
      break;

    case 1: /* 1 point of order 2: w1 / 2 */
      for (i=12; i>2; i-=2)
      {
        if (B%i != 0) continue;
        w1j = gdivgs(w1,i);
        p = torspnt(e,w1j,i,prec);
        if (!p && i%4==0) p = torspnt(e,gadd(w22,w1j),i,prec);
        if (p) { k = i; break; }
      }
      if (!p) { p = tor1; k = 2; }
      break;

    case 2: /* 1 point of order 2: w = w2/2 or (w1+w2)/2 */
      for (i=5; i>1; i-=2)
      {
        if (B%i != 0) continue;
        w1j = gdivgs(w1,i);
        p = torspnt(e,gadd(w,w1j),2*i,prec);
        if (p) { k = 2*i; break; }
      }
      if (!p) { p = tor2; k = 2; }
      tor2 = NULL; break;

    case 3: /* 2 points of order 2: w1/2 and w2/2 */
      for (i=8; i>2; i-=2)
      {
        if (B%(2*i) != 0) continue;
        w1j = gdivgs(w1,i);
        p = torspnt(e,w1j,i,prec);
        if (p) { k = i; break; }
      }
      if (!p) { p = tor1; k = 2; }
      break;
  }
  return gerepileupto(av, tors(e,k,p,tor2, v));
}

/* return a rational point of order pk = p^k on E, or NULL if E(Q)[k] = O.
 * *fk is either NULL (pk = 4 or prime) or elldivpol(p^(k-1)).
 * Set *fk to elldivpol(p^k) */
static GEN
tpoint(GEN E, long pk, GEN *fk)
{
  GEN f = elldivpol(E,pk,0), g = *fk, v;
  long i, l;
  *fk = f;
  if (g) f = RgX_div(f, g);
  v = nfrootsQ(f); l = lg(v);
  for (i = 1; i < l; i++)
  {
    GEN x = gel(v,i);
    GEN y = ellordinate_i(E,x,0);
    if (lg(y) != 1) return mkvec2(x,gel(y,1));
  }
  return NULL;
}
/* return E(Q)[2] */
static GEN
t2points(GEN E, GEN *f2)
{
  long i, l;
  GEN v;
  *f2 = RHSpol(E,NULL);
  v = nfrootsQ(*f2); l = lg(v);
  for (i = 1; i < l; i++)
  {
    GEN x = gel(v,i);
    GEN y = ellordinate_i(E,x,0);
    if (lg(y) != 1) gel(v,i) = mkvec2(x,gel(y,1));
  }
  return v;
}

static GEN
elltors_divpol(GEN E)
{
  GEN T2 = NULL, p, P, Q, v;
  long v2, r2, B;

  E = ellintegralmodel(E, &v);
  B = torsbound(E); /* #E_tor | B */
  if (B == 1) return tors(E,1,NULL,NULL, v);
  v2 = vals(B); /* bound for v_2(point order) */
  B >>= v2;
  p = const_vec(9, NULL);
  r2 = 0;
  if (v2) {
    GEN f;
    T2 = t2points(E, &f);
    switch(lg(T2)-1)
    {
      case 0:  v2 = 0; break;
      case 1:  r2 = 1; if (v2 == 4) v2 = 3; break;
      default: r2 = 2; v2--; break; /* 3 */
    }
    if (v2) gel(p,2) = gel(T2,1);
    /* f = f_2 */
    if (v2 > 1) { gel(p,4) = tpoint(E,4, &f); if (!gel(p,4)) v2 = 1; }
    /* if (v2>1) now f = f4 */
    if (v2 > 2) { gel(p,8) = tpoint(E,8, &f); if (!gel(p,8)) v2 = 2; }
  }
  B <<= v2;
  if (B % 3 == 0) {
    GEN f3 = NULL;
    gel(p,3) = tpoint(E,3,&f3);
    if (!gel(p,3)) B /= (B%9)? 3: 9;
    if (gel(p,3) && B % 9 == 0)
    {
      gel(p,9) = tpoint(E,9,&f3);
      if (!gel(p,9)) B /= 3;
    }
  }
  if (B % 5 == 0) {
    GEN junk = NULL;
    gel(p,5) = tpoint(E,5,&junk);
    if (!gel(p,5)) B /= 5;
  }
  if (B % 7 == 0) {
    GEN junk = NULL;
    gel(p,7) = tpoint(E,7,&junk);
    if (!gel(p,7)) B /= 7;
  }
  /* B is the exponent of E_tors(Q), r2 is the rank of its 2-Sylow,
   * for i > 1, p[i] is a point of order i if one exists and i is a prime power
   * and NULL otherwise */
  if (r2 == 2) /* 2 cyclic factors */
  { /* C2 x C2 */
    if (B == 2) return tors(E,2, gel(T2,1), gel(T2,2), v);
    else if (B == 6)
    { /* C2 x C6 */
      P = elladd(E, gel(p,3), gel(T2,1));
      Q = gel(T2,2);
    }
    else
    { /* C2 x C4 or C2 x C8 */
      P = gel(p, B);
      Q = gel(T2,2);
      if (gequal(Q, ellmul(E, P, utoipos(B>>1)))) Q = gel(T2,1);
    }
  }
  else /* cyclic */
  {
    Q = NULL;
    if (v2)
    {
      if (B>>v2 == 1)
        P = gel(p, B);
      else
        P = elladd(E, gel(p, B>>v2), gel(p,1<<v2));
    }
    else P = gel(p, B);
  }
  return tors(E,B, P, Q, v);
}
GEN
elltors(GEN e)
{
  pari_sp av = avma;
  checkell_Q(e);
  return gerepileupto(av, elltors_divpol(e));
}

GEN
elltors0(GEN e, long flag)
{
  checkell_Q(e);
  switch(flag)
  {
    case 0: return elltors(e);
    case 1: return nagelllutz(e);
    case 2: return elltors_doud(e);
    default: pari_err_FLAG("elltors");
  }
  return NULL; /* not reached */
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

/* E/Q, return cardinal including the (possible) ramified point */
static GEN
ellcard_ram(GEN E, GEN p)
{
  GEN a4, a6, D = Rg_to_Fp(ell_get_disc(E), p);
  if (!signe(D))
  {
    pari_sp av = avma;
    int good_red;
    GEN ap = is_minimal_ap(E, p, &good_red);
    return gerepileuptoint(av, subii(addiu(p,1), ap));
  }
  if (equaliu(p,2)) return utoi(cardmod2(E));
  if (equaliu(p,3)) return utoi(cardmod3(E));
  ell_to_a4a6(E,p,&a4,&a6);
  return Fp_ellcard(a4, a6, p);
}

static GEN
checkellp(GEN E, GEN p, const char *s)
{
  GEN q;
  if (p)
  {
    if (typ(p)!=t_INT) pari_err_TYPE(s,p);
    if (cmpis(p, 2) < 0) pari_err_DOMAIN(s,"p", "<", gen_2, p);
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
    q = p; card = ellcard_ram(E, p);
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
      GEN N = ellcard_ram(E, p);
      GEN D = Rg_to_Fp(ell_get_disc(E), p);
      if (!signe(D)) N = subis(N, 1); /* remove singular point */
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
    res = mkpoln(7, N? modsi(2, N): gen_2,b2,gmulsg(5,b4),gmulsg(10,b6),gmulsg(10,b8),b10,b12);
  }
  setvarn(res, v); return res;
}

/* T = (2y + a1x + a3)^2 modulo the curve equation. Store elldivpol(e,n,v)
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
  GEN ret, D, N;
  checkell(e); D = ell_get_disc(e);
  if (v==-1) v = 0;
  if (varncmp(gvar(D), v) <= 0) pari_err_PRIORITY("elldivpol", e, "<=", v);
  N = characteristic(D);
  if (!signe(N)) N = NULL;
  if (n<0) n = -n;
  if (n==1 || n==3)
    ret = elldivpol4(e, N, n, v);
  else
  {
    GEN d2 = RHSpol(e, N); /* (2y + a1x + 3)^2 mod E */
    setvarn(d2,v);
    if (n <= 4)
      ret = elldivpol4(e, N, n, v);
    else
      ret = elldivpol0(e, const_vec(n,NULL), N,RgX_sqr(d2), n, v);
    if (n%2==0) ret = RgX_mul(ret, d2);
  }
  return gerepilecopy(av, ret);
}
