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

static int
check_ZV(GEN x, long l)
{
  long i;
  for (i=1; i<l; i++)
    if (typ(gel(x,i)) != t_INT) return 0;
  return 1;
}
void
RgV_check_ZV(GEN A, const char *s)
{
  if (!RgV_is_ZV(A)) pari_err_TYPE(stack_strcat(s," [integer vector]"), A);
}
void
RgM_check_ZM(GEN A, const char *s)
{
  long n = lg(A);
  if (n != 1)
  {
    long j, m = lgcols(A);
    for (j=1; j<n; j++)
      if (!check_ZV(gel(A,j), m))
        pari_err_TYPE(stack_strcat(s," [integer matrix]"), A);
  }
}

long
ZV_max_lg(GEN x)
{
  long i, prec = 2, m = lg(x);
  for (i=1; i<m; i++) { long l = lgefint(gel(x,i)); if (l > prec) prec = l; }
  return prec;
}
long
ZM_max_lg(GEN x)
{
  long i, prec = 2, n = lg(x);
  if (n != 1)
  {
    long j, m = lgcols(x);
    for (j=1; j<n; j++)
    {
      GEN c = gel(x,j);
      for (i=1; i<m; i++) { long l = lgefint(gel(c,i)); if (l > prec) prec = l; }
    }
  }
  return prec;
}

GEN
ZM_supnorm(GEN x)
{
  long i, j, h, lx = lg(x);
  GEN s = gen_0;
  if (lx == 1) return gen_1;
  h = lgcols(x);
  for (j=1; j<lx; j++)
  {
    GEN xj = gel(x,j);
    for (i=1; i<h; i++)
    {
      GEN c = gel(xj,i);
      if (absi_cmp(c, s) > 0) s = c;
    }
  }
  return absi(s);
}

/********************************************************************/
/**                                                                **/
/**                           MULTIPLICATION                       **/
/**                                                                **/
/********************************************************************/
/* x non-empty ZM, y a compatible nc (dimension > 0). */
static GEN
ZM_nc_mul_i(GEN x, GEN y, long c, long l)
{
  long i, j;
  pari_sp av;
  GEN z = cgetg(l,t_COL), s;

  for (i=1; i<l; i++)
  {
    av = avma; s = muliu(gcoeff(x,i,1),y[1]);
    for (j=2; j<c; j++)
      if (y[j]) s = addii(s, muliu(gcoeff(x,i,j),y[j]));
    gel(z,i) = gerepileuptoint(av,s);
  }
  return z;
}
/* x non-empty ZM, y a compatible zc (dimension > 0). */
static GEN
ZM_zc_mul_i(GEN x, GEN y, long c, long l)
{
  long i, j;
  pari_sp av;
  GEN z = cgetg(l,t_COL), s;

  for (i=1; i<l; i++)
  {
    av = avma; s = mulis(gcoeff(x,i,1),y[1]);
    for (j=2; j<c; j++)
      if (y[j]) s = addii(s, mulis(gcoeff(x,i,j),y[j]));
    gel(z,i) = gerepileuptoint(av,s);
  }
  return z;
}
GEN
ZM_zc_mul(GEN x, GEN y) {
  long l = lg(x);
  if (l == 1) return cgetg(1, t_COL);
  return ZM_zc_mul_i(x,y, l, lgcols(x));
}

/* x ZM, y a compatible zm (dimension > 0). */
GEN
ZM_zm_mul(GEN x, GEN y)
{
  long j, c, l = lg(x), ly = lg(y);
  GEN z = cgetg(ly, t_MAT);
  if (l == 1) return z;
  c = lgcols(x);
  for (j = 1; j < ly; j++) gel(z,j) = ZM_zc_mul_i(x, gel(y,j), l,c);
  return z;
}
/* x ZM, y a compatible zn (dimension > 0). */
GEN
ZM_nm_mul(GEN x, GEN y)
{
  long j, c, l = lg(x), ly = lg(y);
  GEN z = cgetg(ly, t_MAT);
  if (l == 1) return z;
  c = lgcols(x);
  for (j = 1; j < ly; j++) gel(z,j) = ZM_nc_mul_i(x, gel(y,j), l,c);
  return z;
}

/* x[i,]*y. Assume lg(x) > 1 and 0 < i < lgcols(x) */
static GEN
ZMrow_ZC_mul_i(GEN x, GEN y, long i, long lx)
{
  pari_sp av = avma;
  GEN c = mulii(gcoeff(x,i,1), gel(y,1)), ZERO = gen_0;
  long k;
  for (k = 2; k < lx; k++)
  {
    GEN t = mulii(gcoeff(x,i,k), gel(y,k));
    if (t != ZERO) c = addii(c, t);
  }
  return gerepileuptoint(av, c);
}
GEN
ZMrow_ZC_mul(GEN x, GEN y, long i)
{ return ZMrow_ZC_mul_i(x, y, i, lg(x)); }

/* return x * y, 1 < lx = lg(x), l = lgcols(x) */
static GEN
ZM_ZC_mul_i(GEN x, GEN y, long lx, long l)
{
  GEN z = cgetg(l,t_COL);
  long i;
  for (i=1; i<l; i++) gel(z,i) = ZMrow_ZC_mul_i(x,y,i,lx);
  return z;
}
GEN
ZM_mul(GEN x, GEN y)
{
  long j, l, lx=lg(x), ly=lg(y);
  GEN z;
  if (ly==1) return cgetg(1,t_MAT);
  if (lx==1) return zeromat(0, ly-1);
  l = lgcols(x); z = cgetg(ly,t_MAT);
  for (j=1; j<ly; j++) gel(z,j) = ZM_ZC_mul_i(x, gel(y,j), lx, l);
  return z;
}
/* assume result is symmetric */
GEN
ZM_multosym(GEN x, GEN y)
{
  long j, lx, ly = lg(y);
  GEN M;
  if (ly == 1) return cgetg(1,t_MAT);
  lx = lg(x); /* = lgcols(y) */
  if (lx == 1) return cgetg(1,t_MAT);
  /* ly = lgcols(x) */
  M = cgetg(ly, t_MAT);
  for (j=1; j<ly; j++)
  {
    GEN z = cgetg(ly,t_COL), yj = gel(y,j);
    long i;
    for (i=1; i<j; i++) gel(z,i) = gcoeff(M,j,i);
    for (i=j; i<ly; i++)gel(z,i) = ZMrow_ZC_mul_i(x,yj,i,lx);
    gel(M,j) = z;
  }
  return M;
}

/* assume lx > 1 is lg(x) = lg(y) */
static GEN
ZV_dotproduct_i(GEN x, GEN y, long lx)
{
  pari_sp av = avma;
  GEN c = mulii(gel(x,1), gel(y,1));
  long i;
  for (i = 2; i < lx; i++)
  {
    GEN t = mulii(gel(x,i), gel(y,i));
    if (t != gen_0) c = addii(c, t);
  }
  return gerepileuptoint(av, c);
}

/* x~ * y, assuming result is symmetric */
GEN
ZM_transmultosym(GEN x, GEN y)
{
  long i, j, l, ly = lg(y);
  GEN M;
  if (ly == 1) return cgetg(1,t_MAT);
  /* lg(x) = ly */
  l = lgcols(y); /* = lgcols(x) */
  M = cgetg(ly, t_MAT);
  for (i=1; i<ly; i++)
  {
    GEN xi = gel(x,i), c = cgetg(ly,t_COL);
    gel(M,i) = c;
    for (j=1; j<i; j++)
      gcoeff(M,i,j) = gel(c,j) = ZV_dotproduct_i(xi,gel(y,j),l);
    gel(c,i) = ZV_dotproduct_i(xi,gel(y,i),l);
  }
  return M;
}
GEN
ZM_ZC_mul(GEN x, GEN y)
{
  long lx = lg(x);
  return lx==1? cgetg(1,t_COL): ZM_ZC_mul_i(x, y, lx, lgcols(x));
}

long
zv_dotproduct(GEN x, GEN y)
{
  long i, lx = lg(x);
  ulong c;
  if (lx == 1) return 0;
  c = uel(x,1)*uel(y,1);
  for (i = 2; i < lx; i++)
    c += uel(x,i)*uel(y,i);
  return c;
}

GEN
ZV_ZM_mul(GEN x, GEN y)
{
  long i, lx = lg(x), ly = lg(y);
  GEN z;
  if (lx == 1) return zerovec(ly-1);
  z = cgetg(ly, t_VEC);
  for (i = 1; i < ly; i++) gel(z,i) = ZV_dotproduct_i(x, gel(y,i), lx);
  return z;
}

GEN
ZC_ZV_mul(GEN x, GEN y)
{
  long i,j, lx=lg(x), ly=lg(y);
  GEN z;
  if (ly==1) return cgetg(1,t_MAT);
  z = cgetg(ly,t_MAT);
  for (j=1; j < ly; j++)
  {
    gel(z,j) = cgetg(lx,t_COL);
    for (i=1; i<lx; i++) gcoeff(z,i,j) = mulii(gel(x,i),gel(y,j));
  }
  return z;
}

GEN
ZV_dotsquare(GEN x)
{
  long i, lx;
  pari_sp av;
  GEN z;
  lx = lg(x);
  if (lx == 1) return gen_0;
  av = avma; z = sqri(gel(x,1));
  for (i=2; i<lx; i++) z = addii(z, sqri(gel(x,i)));
  return gerepileuptoint(av,z);
}

GEN
ZV_dotproduct(GEN x,GEN y)
{
  long lx;
  if (x == y) return ZV_dotsquare(x);
  lx = lg(x);
  if (lx == 1) return gen_0;
  return ZV_dotproduct_i(x, y, lx);
}

static GEN
_ZM_mul(void *data /*ignored*/, GEN x, GEN y)
{ (void)data; return ZM_mul(x,y); }
static GEN
_ZM_sqr(void *data /*ignored*/, GEN x)
{ (void)data; return ZM_mul(x,x); }
GEN
ZM_pow(GEN x, GEN n)
{
  pari_sp av = avma;
  if (!signe(n)) return matid(lg(x)-1);
  return gerepileupto(av, gen_pow(x, n, NULL, &_ZM_sqr, &_ZM_mul));
}
GEN
ZM_powu(GEN x, ulong n)
{
  pari_sp av = avma;
  if (!n) return matid(lg(x)-1);
  return gerepileupto(av, gen_powu(x, n, NULL, &_ZM_sqr, &_ZM_mul));
}
/********************************************************************/
/**                                                                **/
/**                           ADD, SUB                             **/
/**                                                                **/
/********************************************************************/
static GEN
ZC_add_i(GEN x, GEN y, long lx)
{
  GEN A = cgetg(lx, t_COL);
  long i;
  for (i=1; i<lx; i++) gel(A,i) = addii(gel(x,i), gel(y,i));
  return A;
}
GEN
ZC_add(GEN x, GEN y) { return ZC_add_i(x, y, lg(x)); }
GEN
ZC_Z_add(GEN x, GEN y)
{
  long k, lx = lg(x);
  GEN z = cgetg(lx, t_COL);
  if (lx == 1) pari_err_TYPE2("+",x,y);
  gel(z,1) = addii(y,gel(x,1));
  for (k = 2; k < lx; k++) gel(z,k) = icopy(gel(x,k));
  return z;
}

static GEN
ZC_sub_i(GEN x, GEN y, long lx)
{
  long i;
  GEN A = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) gel(A,i) = subii(gel(x,i), gel(y,i));
  return A;
}
GEN
ZC_sub(GEN x, GEN y) { return ZC_sub_i(x, y, lg(x)); }
GEN
ZC_Z_sub(GEN x, GEN y)
{
  long k, lx = lg(x);
  GEN z = cgetg(lx, t_COL);
  if (lx == 1) pari_err_TYPE2("+",x,y);
  gel(z,1) = subii(gel(x,1), y);
  for (k = 2; k < lx; k++) gel(z,k) = icopy(gel(x,k));
  return z;
}

GEN
ZM_add(GEN x, GEN y)
{
  long lx = lg(x), l, j;
  GEN z;
  if (lx == 1) return cgetg(1, t_MAT);
  z = cgetg(lx, t_MAT); l = lgcols(x);
  for (j = 1; j < lx; j++) gel(z,j) = ZC_add_i(gel(x,j), gel(y,j), l);
  return z;
}
GEN
ZM_sub(GEN x, GEN y)
{
  long lx = lg(x), l, j;
  GEN z;
  if (lx == 1) return cgetg(1, t_MAT);
  z = cgetg(lx, t_MAT); l = lgcols(x);
  for (j = 1; j < lx; j++) gel(z,j) = ZC_sub_i(gel(x,j), gel(y,j), l);
  return z;
}
/********************************************************************/
/**                                                                **/
/**                         LINEAR COMBINATION                     **/
/**                                                                **/
/********************************************************************/
/* return X/c assuming division is exact */
GEN
ZC_Z_divexact(GEN X, GEN c)
{
  long i, l = lg(X);
  GEN A = cgetg(l, t_COL);
  for (i=1; i<l; i++) gel(A,i) = diviiexact(gel(X,i), c);
  return A;
}
GEN
ZM_Z_divexact(GEN X, GEN c)
{
  long i, l = lg(X);
  GEN A = cgetg(l, t_MAT);
  for (i = 1; i < l; i++) gel(A,i) = ZC_Z_divexact(gel(X,i), c);
  return A;
}
/* Return c * X */
GEN
ZC_Z_mul(GEN X, GEN c)
{
  long i, l;
  GEN A;
  if (!signe(c)) return zerocol(lg(X)-1);
  if (is_pm1(c)) return (signe(c) > 0)? ZC_copy(X): ZC_neg(X);
  l = lg(X); A = cgetg(l, t_COL);
  for (i=1; i<l; i++) gel(A,i) = mulii(c,gel(X,i));
  return A;
}
GEN
ZC_z_mul(GEN X, long c)
{
  long i, l;
  GEN A;
  if (!c) return zerocol(lg(X)-1);
  if (c == 1) return ZC_copy(X);
  if (c ==-1) return ZC_neg(X);
  l = lg(X); A = cgetg(l, t_COL);
  for (i=1; i<l; i++) gel(A,i) = mulsi(c,gel(X,i));
  return A;
}

GEN
zv_z_mul(GEN M, long n)
{
  long l;
  GEN N = cgetg_copy(M, &l);
  while (--l > 0) N[l] = M[l]*n;
  return N;
}

/* return a ZM */
GEN
nm_Z_mul(GEN X, GEN c)
{
  long i, j, h, l = lg(X), s = signe(c);
  GEN A;
  if (l == 1) return cgetg(1, t_MAT);
  h = lgcols(X);
  if (!s) return zeromat(h-1, l-1);
  if (is_pm1(c)) {
    if (s > 0) return Flm_to_ZM(X);
    X = Flm_to_ZM(X); ZM_togglesign(X); return X;
  }
  A = cgetg(l, t_MAT);
  for (j = 1; j < l; j++)
  {
    GEN a = cgetg(h, t_COL), x = gel(X, j);
    for (i = 1; i < h; i++) gel(a,i) = muliu(c, x[i]);
    gel(A,j) = a;
  }
  return A;
}
GEN
ZM_Z_mul(GEN X, GEN c)
{
  long i, j, h, l = lg(X);
  GEN A;
  if (l == 1) return cgetg(1, t_MAT);
  h = lgcols(X);
  if (!signe(c)) return zeromat(h-1, l-1);
  if (is_pm1(c)) return (signe(c) > 0)? ZM_copy(X): ZM_neg(X);
  A = cgetg(l, t_MAT);
  for (j = 1; j < l; j++)
  {
    GEN a = cgetg(h, t_COL), x = gel(X, j);
    for (i = 1; i < h; i++) gel(a,i) = mulii(c, gel(x,i));
    gel(A,j) = a;
  }
  return A;
}

/* X <- X + v Y (elementary col operation) */
void
ZC_lincomb1_inplace(GEN X, GEN Y, GEN v)
{
  long i, m = lgefint(v);
  if (m == 2) return; /* v = 0 */
  for (i = lg(X)-1; i; i--) gel(X,i) = addmulii_inplace(gel(X,i), gel(Y,i), v);
}
void
Flc_lincomb1_inplace(GEN X, GEN Y, ulong v, ulong q)
{
  long i;
  if (!v) return; /* v = 0 */
  for (i = lg(X)-1; i; i--) X[i] = Fl_add(X[i], Fl_mul(Y[i], v, q), q);
}

/* X + v Y, wasteful if (v = 0) */
static GEN
ZC_lincomb1(GEN v, GEN X, GEN Y)
{
  long i, lx = lg(X);
  GEN A = cgetg(lx,t_COL);
  for (i=1; i<lx; i++) gel(A,i) = addmulii(gel(X,i), gel(Y,i), v);
  return A;
}
/* -X + vY */
static GEN
ZC_lincomb_1(GEN v, GEN X, GEN Y)
{
  long i, lx = lg(X);
  GEN A = cgetg(lx,t_COL);
  for (i=1; i<lx; i++) gel(A,i) = mulsubii(gel(Y,i), v, gel(X,i));
  return A;
}
/* X,Y compatible ZV; u,v in Z. Returns A = u*X + v*Y */
GEN
ZC_lincomb(GEN u, GEN v, GEN X, GEN Y)
{
  long su, sv;
  GEN A;

  su = signe(u); if (!su) return ZC_Z_mul(Y, v);
  sv = signe(v); if (!sv) return ZC_Z_mul(X, u);
  if (is_pm1(v))
  {
    if (is_pm1(u))
    {
      if (su != sv) A = ZC_sub(X, Y);
      else          A = ZC_add(X, Y);
      if (su < 0) ZV_togglesign(A); /* in place but was created above */
    }
    else
    {
      if (sv > 0) A = ZC_lincomb1 (u, Y, X);
      else        A = ZC_lincomb_1(u, Y, X);
    }
  }
  else if (is_pm1(u))
  {
    if (su > 0) A = ZC_lincomb1 (v, X, Y);
    else        A = ZC_lincomb_1(v, X, Y);
  }
  else
  { /* not cgetg_copy: x may be a t_VEC */
    long i, lx = lg(X);
    A = cgetg(lx,t_COL);
    for (i=1; i<lx; i++) gel(A,i) = lincombii(u,v,gel(X,i),gel(Y,i));
  }
  return A;
}

/********************************************************************/
/**                                                                **/
/**                           CONVERSIONS                          **/
/**                                                                **/
/********************************************************************/
GEN
ZV_to_nv(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l, t_VECSMALL);
  for (i=1; i<l; i++) x[i] = itou(gel(z,i));
  return x;
}

GEN
zm_to_ZM(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = zc_to_ZC(gel(z,i));
  return x;
}

GEN
zmV_to_ZMV(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_VEC);
  for (i=1; i<l; i++) gel(x,i) = zm_to_ZM(gel(z,i));
  return x;
}

/* same as Flm_to_ZM but do not assume positivity */
GEN
ZM_to_zm(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = ZV_to_zv(gel(z,i));
  return x;
}

GEN
zv_to_Flv(GEN z, ulong p)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_VECSMALL);
  for (i=1; i<l; i++) x[i] = smodss(z[i],p);
  return x;
}

GEN
zm_to_Flm(GEN z, ulong p)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = zv_to_Flv(gel(z,i),p);
  return x;
}

GEN
ZMV_to_zmV(GEN z)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_VEC);
  for (i=1; i<l; i++) gel(x,i) = ZM_to_zm(gel(z,i));
  return x;
}

/********************************************************************/
/**                                                                **/
/**                         COPY, NEGATION                         **/
/**                                                                **/
/********************************************************************/
GEN
ZC_copy(GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx, t_COL);
  for (i=1; i<lx; i++)
  {
    GEN c = gel(x,i);
    gel(y,i) = lgefint(c) == 2? gen_0: icopy(c);
  }
  return y;
}

GEN
ZM_copy(GEN x)
{
  long l;
  GEN y = cgetg_copy(x, &l);
  while (--l > 0) gel(y,l) = ZC_copy(gel(x,l));
  return y;
}

void
ZV_neg_inplace(GEN M)
{
  long l = lg(M);
  while (--l > 0) gel(M,l) = negi(gel(M,l));
}
GEN
ZC_neg(GEN M)
{
  long l = lg(M);
  GEN N = cgetg(l, t_COL);
  while (--l > 0) gel(N,l) = negi(gel(M,l));
  return N;
}
GEN
zv_neg(GEN M)
{
  long l;
  GEN N = cgetg_copy(M, &l);
  while (--l > 0) N[l] = -M[l];
  return N;
}
GEN
zv_neg_inplace(GEN M)
{
  long l = lg(M);
  while (--l > 0) M[l] = -M[l];
  return M;
}
GEN
ZM_neg(GEN x)
{
  long l;
  GEN y = cgetg_copy(x, &l);
  while (--l > 0) gel(y,l) = ZC_neg(gel(x,l));
  return y;
}

void
ZV_togglesign(GEN M)
{
  long l = lg(M);
  while (--l > 0) togglesign_safe(&gel(M,l));
}
void
ZM_togglesign(GEN M)
{
  long l = lg(M);
  while (--l > 0) ZV_togglesign(gel(M,l));
}

/********************************************************************/
/**                                                                **/
/**                        "DIVISION" mod HNF                      **/
/**                                                                **/
/********************************************************************/
/* Reduce ZC x modulo ZM y in HNF, may return x itself (not a copy) */
GEN
ZC_hnfremdiv(GEN x, GEN y, GEN *Q)
{
  long i, l = lg(x);
  GEN q;

  if (Q) *Q = cgetg(l,t_COL);
  if (l == 1) return cgetg(1,t_COL);
  for (i = l-1; i>0; i--)
  {
    q = diviiround(gel(x,i), gcoeff(y,i,i));
    if (signe(q)) {
      togglesign(q);
      x = ZC_lincomb(gen_1, q, x, gel(y,i));
    }
    if (Q) gel(*Q, i) = q;
  }
  return x;
}

/* x = y Q + R, may return some columns of x (not copies) */
GEN
ZM_hnfdivrem(GEN x, GEN y, GEN *Q)
{
  long lx = lg(x), i;
  GEN R = cgetg(lx, t_MAT);
  if (Q)
  {
    GEN q = cgetg(lx, t_MAT); *Q = q;
    for (i=1; i<lx; i++) gel(R,i) = ZC_hnfremdiv(gel(x,i),y,(GEN*)(q+i));
  }
  else
    for (i=1; i<lx; i++)
    {
      pari_sp av = avma;
      GEN z = ZC_hnfrem(gel(x,i),y);
      gel(R,i) = (avma == av)? ZC_copy(z): gerepileupto(av, z);
    }
  return R;
}


/********************************************************************/
/**                                                                **/
/**                               TESTS                            **/
/**                                                                **/
/********************************************************************/
int
zv_equal0(GEN V)
{
  long l = lg(V);
  while (--l > 0)
    if (V[l]) return 0;
  return 1;
}

int
ZV_equal0(GEN V)
{
  long l = lg(V);
  while (--l > 0)
    if (signe(gel(V,l))) return 0;
  return 1;
}

static int
ZV_equal_lg(GEN V, GEN W, long l)
{
  while (--l > 0)
    if (!equalii(gel(V,l), gel(W,l))) return 0;
  return 1;
}
int
ZV_equal(GEN V, GEN W)
{
  long l = lg(V);
  if (lg(W) != l) return 0;
  return ZV_equal_lg(V, W, l);
}
int
ZM_equal(GEN A, GEN B)
{
  long i, m, l = lg(A);
  if (lg(B) != l) return 0;
  if (l == 1) return 1;
  m = lgcols(A);
  if (lgcols(B) != m) return 0;
  for (i = 1; i < l; i++)
    if (!ZV_equal_lg(gel(A,i), gel(B,i), m)) return 0;
  return 1;
}
int
zv_equal(GEN V, GEN W)
{
  long l = lg(V);
  if (lg(W) != l) return 0;
  while (--l > 0)
    if (V[l] != W[l]) return 0;
  return 1;
}

int
zvV_equal(GEN V, GEN W)
{
  long l = lg(V);
  if (lg(W) != l) return 0;
  while (--l > 0)
    if (!zv_equal(gel(V,l),gel(W,l))) return 0;
  return 1;
}

int
ZM_ishnf(GEN x)
{
  long i,j, lx = lg(x);
  for (i=1; i<lx; i++)
  {
    GEN xii = gcoeff(x,i,i);
    if (signe(xii) <= 0) return 0;
    for (j=1; j<i; j++)
      if (signe(gcoeff(x,i,j))) return 0;
    for (j=i+1; j<lx; j++)
    {
      GEN xij = gcoeff(x,i,j);
      if (signe(xij)<0 || cmpii(xij,xii)>=0) return 0;
    }
  }
  return 1;
}
int
ZM_isidentity(GEN x)
{
  long i,j, lx = lg(x);

  if (lx == 1) return 1;
  if (lx != lgcols(x)) return 0;
  for (j=1; j<lx; j++)
  {
    GEN c = gel(x,j), t;
    for (i=1; i<j; )
      if (signe(gel(c,i++))) return 0;
    /* i = j */
    t = gel(c,i++);
      if (!is_pm1(t) || signe(t) < 0) return 0;
    for (   ; i<lx; )
      if (signe(gel(c,i++))) return 0;
  }
  return 1;
}

/********************************************************************/
/**                                                                **/
/**                       MISCELLANEOUS                            **/
/**                                                                **/
/********************************************************************/
/* assume lg(x) = lg(y), x,y in Z^n */
int
ZV_cmp(GEN x, GEN y)
{
  long fl,i, lx = lg(x);
  for (i=1; i<lx; i++)
    if (( fl = cmpii(gel(x,i), gel(y,i)) )) return fl;
  return 0;
}
/* assume lg(x) = lg(y), x,y in Z^n */
int
ZV_abscmp(GEN x, GEN y)
{
  long fl,i, lx = lg(x);
  for (i=1; i<lx; i++)
    if (( fl = absi_cmp(gel(x,i), gel(y,i)) )) return fl;
  return 0;
}

long
zv_content(GEN x)
{
  long i, l = lg(x), s = labs(x[1]);
  for (i=2; i<l && s!=1; i++) s = cgcd(x[i],s);
  return s;
}
GEN
ZV_content(GEN x)
{
  long i, l = lg(x);
  pari_sp av = avma;
  GEN c;
  if (l == 1) return gen_1;
  if (l == 2) return absi(gel(x,1));
  c = gel(x,1);
  for (i = 2; i < l; i++)
  {
    c = gcdii(c, gel(x,i));
    if (is_pm1(c)) { avma = av; return gen_1; }
  }
  return gerepileuptoint(av, c);
}

GEN
ZM_det_triangular(GEN mat)
{
  pari_sp av;
  long i,l = lg(mat);
  GEN s;

  if (l<3) return l<2? gen_1: icopy(gcoeff(mat,1,1));
  av = avma; s = gcoeff(mat,1,1);
  for (i=2; i<l; i++) s = mulii(s,gcoeff(mat,i,i));
  return gerepileuptoint(av,s);
}

/* assumes no overflow */
long
zv_prod(GEN v)
{
  long n, i, l = lg(v);
  if (l == 1) return 1;
  n = v[1]; for (i = 2; i < l; i++) n *= v[i];
  return n;
}
/* product of ulongs */
GEN
zv_prod_Z(GEN v)
{
  pari_sp av = avma;
  long k, n = lg(v)-1, m;
  GEN x;
  if (n == 0) return gen_1;
  if (n == 1) return utoi(v[1]);
  if (n == 2) return muluu(v[1], v[2]);
  m = n >> 1;
  x = cgetg(m + (odd(n)? 2: 1), t_VEC);
  for (k = 1; k <= m; k++) gel(x,k) = muluu(v[k<<1], v[(k<<1)-1]);
  if (odd(n)) gel(x,k) = utoipos(v[n]);
  return gerepileuptoint(av, divide_conquer_prod(x, mulii));
}

GEN
ZV_prod(GEN v)
{
  pari_sp av = avma;
  long i, l = lg(v);
  GEN n;
  if (l == 1) return gen_1;
  if (l > 7) return gerepileuptoint(av, divide_conquer_prod(v, mulii));
  n = gel(v,1);
  if (l == 2) return icopy(n);
  for (i = 2; i < l; i++) n = mulii(n, gel(v,i));
  return gerepileuptoint(av, n);
}
/* assumes no overflow */
long
zv_sum(GEN v)
{
  long n, i, l = lg(v);
  if (l == 1) return 0;
  n = v[1]; for (i = 2; i < l; i++) n += v[i];
  return n;
}
GEN
ZV_sum(GEN v)
{
  pari_sp av = avma;
  long i, l = lg(v);
  GEN n;
  if (l == 1) return gen_0;
  n = gel(v,1);
  if (l == 2) return icopy(n);
  for (i = 2; i < l; i++) n = addii(n, gel(v,i));
  return gerepileuptoint(av, n);
}

/********************************************************************/
/**                                                                **/
/**         GRAM SCHMIDT REDUCTION (integer matrices)              **/
/**                                                                **/
/********************************************************************/

/* L[k,] += q * L[l,], l < k. Inefficient if q = 0 */
static void
Zupdate_row(long k, long l, GEN q, GEN L, GEN B)
{
  long i, qq = itos_or_0(q);
  if (!qq)
  {
    for(i=1;i<l;i++)  gcoeff(L,k,i) = addii(gcoeff(L,k,i),mulii(q,gcoeff(L,l,i)));
    gcoeff(L,k,l) = addii(gcoeff(L,k,l), mulii(q,B));
    return;
  }
  if (qq == 1) {
    for (i=1;i<l; i++) gcoeff(L,k,i) = addii(gcoeff(L,k,i),gcoeff(L,l,i));
    gcoeff(L,k,l) = addii(gcoeff(L,k,l), B);
  } else if (qq == -1) {
    for (i=1;i<l; i++) gcoeff(L,k,i) = subii(gcoeff(L,k,i),gcoeff(L,l,i));
    gcoeff(L,k,l) = addii(gcoeff(L,k,l), negi(B));
  } else {
    for(i=1;i<l;i++) gcoeff(L,k,i) = addii(gcoeff(L,k,i),mulsi(qq,gcoeff(L,l,i)));
    gcoeff(L,k,l) = addii(gcoeff(L,k,l), mulsi(qq,B));
  }
}

/* update L[k,] */
static void
ZRED(long k, long l, GEN x, GEN L, GEN B)
{
  GEN q = truedivii(addii(B,shifti(gcoeff(L,k,l),1)), shifti(B,1));
  if (!signe(q)) return;
  q = negi(q);
  Zupdate_row(k,l,q,L,B);
  gel(x,k) = ZC_lincomb(gen_1, q, gel(x,k), gel(x,l));
}

/* Gram-Schmidt reduction, x a ZM */
static void
ZincrementalGS(GEN x, GEN L, GEN B, long k)
{
  long i, j;
  for (j=1; j<=k; j++)
  {
    pari_sp av = avma;
    GEN u = ZV_dotproduct(gel(x,k), gel(x,j));
    for (i=1; i<j; i++)
    {
      u = subii(mulii(gel(B,i+1), u), mulii(gcoeff(L,k,i), gcoeff(L,j,i)));
      u = diviiexact(u, gel(B,i));
    }
    gcoeff(L,k,j) = gerepileuptoint(av, u);
  }
  gel(B,k+1) = gcoeff(L,k,k); gcoeff(L,k,k) = gen_1;
}

/* Variant reducemodinvertible(ZC v, ZM y), when y singular.
 * Very inefficient if y is not LLL-reduced of maximal rank */
static GEN
ZC_reducemodmatrix_i(GEN v, GEN y)
{
  GEN B, L, x = shallowconcat(y, v);
  long k, lx = lg(x), nx = lx-1;

  B = scalarcol_shallow(gen_1, lx);
  L = zeromatcopy(nx, nx);
  for (k=1; k <= nx; k++) ZincrementalGS(x, L, B, k);
  for (k = nx-1; k >= 1; k--) ZRED(nx,k, x,L,gel(B,k+1));
  return gel(x,nx);
}
GEN
ZC_reducemodmatrix(GEN v, GEN y) {
  pari_sp av = avma;
  return gerepilecopy(av, ZC_reducemodmatrix_i(v,y));
}

/* Variant reducemodinvertible(ZM v, ZM y), when y singular.
 * Very inefficient if y is not LLL-reduced of maximal rank */
static GEN
ZM_reducemodmatrix_i(GEN v, GEN y)
{
  GEN B, L, V;
  long j, k, lv = lg(v), nx = lg(y), lx = nx+1;

  V = cgetg(lv, t_MAT);
  B = scalarcol_shallow(gen_1, lx);
  L = zeromatcopy(nx, nx);
  for (k=1; k < nx; k++) ZincrementalGS(y, L, B, k);
  for (j = 1; j < lg(v); j++)
  {
    GEN x = shallowconcat(y, gel(v,j));
    ZincrementalGS(x, L, B, nx); /* overwrite last */
    for (k = nx-1; k >= 1; k--) ZRED(nx,k, x,L,gel(B,k+1));
    gel(V,j) = gel(x,nx);
  }
  return V;
}
GEN
ZM_reducemodmatrix(GEN v, GEN y) {
  pari_sp av = avma;
  return gerepilecopy(av, ZM_reducemodmatrix_i(v,y));
}

GEN
ZC_reducemodlll(GEN x,GEN y)
{
  pari_sp av = avma;
  GEN z = ZC_reducemodmatrix(x, ZM_lll(y, 0.75, LLL_INPLACE));
  return gerepilecopy(av, z);
}
GEN
ZM_reducemodlll(GEN x,GEN y)
{
  pari_sp av = avma;
  GEN z = ZM_reducemodmatrix(x, ZM_lll(y, 0.75, LLL_INPLACE));
  return gerepilecopy(av, z);
}
