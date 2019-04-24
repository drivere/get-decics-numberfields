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

/********************************************************************/
/**                                                                **/
/**                           REDUCTION                            **/
/**                                                                **/
/********************************************************************/
/* z in Z^n, return lift(Col(z) * Mod(1,p)) */
GEN
FpC_red(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_COL);
  for (i=1; i<l; i++) gel(x,i) = modii(gel(z,i),p);
  return x;
}

/* z in Z^n, return lift(Vec(z) * Mod(1,p)) */
GEN
FpV_red(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_VEC);
  for (i=1; i<l; i++) gel(x,i) = modii(gel(z,i),p);
  return x;
}
GEN
FpC_center(GEN z, GEN p, GEN pov2)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_COL);
  for (i=1; i<l; i++) gel(x,i) = Fp_center(gel(z,i),p, pov2);
  return x;
}

/* assume 0 <= u < p and ps2 = p>>1 */
INLINE void
Fp_center_inplace(GEN u, GEN p, GEN ps2)
{ if (absi_cmp(u,ps2) > 0) subiiz(u,p,u); }

void
FpC_center_inplace(GEN z, GEN p, GEN ps2)
{
  long i,l = lg(z);
  for (i=1; i<l; i++)
    Fp_center_inplace(gel(z,i), p, ps2);
}

GEN
Flv_center(GEN z, ulong p, ulong ps2)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_VECSMALL);
  for (i=1; i<l; i++) x[i] = Fl_center(z[i],p,ps2);
  return x;
}

/* z in Mat m,n(Z), return lift(z * Mod(1,p)) */
GEN
FpM_red(GEN z, GEN p)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = FpC_red(gel(z,i), p);
  return x;
}
GEN
FpM_center(GEN z, GEN p, GEN pov2)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = FpC_center(gel(z,i), p, pov2);
  return x;
}

void
FpM_center_inplace(GEN z, GEN p, GEN pov2)
{
  long i, l = lg(z);
  for (i=1; i<l; i++) FpC_center_inplace(gel(z,i), p, pov2);
}
GEN
Flm_center(GEN z, ulong p, ulong ps2)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = Flv_center(gel(z,i),p,ps2);
  return x;
}

/********************************************************************/
/**                                                                **/
/**                           ADD, SUB                             **/
/**                                                                **/
/********************************************************************/
GEN
FpC_add(GEN x, GEN y, GEN p)
{
  long i, lx = lg(x);
  GEN z = cgetg(lx, t_COL);
  for (i = 1; i < lx; i++) gel(z, i) = Fp_add(gel(x, i), gel(y, i), p);
  return z;
}
GEN
FpV_add(GEN x, GEN y, GEN p)
{
  long i, lx = lg(x);
  GEN z = cgetg(lx, t_VEC);
  for (i = 1; i < lx; i++) gel(z, i) = Fp_add(gel(x, i), gel(y, i), p);
  return z;
}
GEN
FpM_add(GEN x, GEN y, GEN p)
{
  long lx = lg(x), j;
  GEN z;
  if (lx == 1) return cgetg(1, t_MAT);
  z = cgetg(lx, t_MAT);
  for (j = 1; j < lx; j++) gel(z,j) = FpC_add(gel(x,j), gel(y,j), p);
  return z;
}

GEN
Flv_add(GEN x, GEN y, ulong p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_VECSMALL);
  if (p==2)
    for (i = 1; i < l; i++) z[i] = x[i]^y[i];
  else
    for (i = 1; i < l; i++) z[i] = Fl_add(x[i], y[i], p);
  return z;
}

void
Flv_add_inplace(GEN x, GEN y, ulong p)
{
  long i, l = lg(x);
  if (p==2)
    for (i = 1; i < l; i++) x[i] ^= y[i];
  else
    for (i = 1; i < l; i++) x[i] = Fl_add(x[i], y[i], p);
}

ulong
Flv_sum(GEN x, ulong p)
{
  long i, l = lg(x);
  ulong s = 0;
  if (p==2)
    for (i = 1; i < l; i++) s ^= x[i];
  else
    for (i = 1; i < l; i++) s = Fl_add(s, x[i], p);
  return s;
}

GEN
FpC_sub(GEN x, GEN y, GEN p)
{
  long i, lx = lg(x);
  GEN z = cgetg(lx, t_COL);
  for (i = 1; i < lx; i++) gel(z, i) = Fp_sub(gel(x, i), gel(y, i), p);
  return z;
}
GEN
FpV_sub(GEN x, GEN y, GEN p)
{
  long i, lx = lg(x);
  GEN z = cgetg(lx, t_VEC);
  for (i = 1; i < lx; i++) gel(z, i) = Fp_sub(gel(x, i), gel(y, i), p);
  return z;
}

GEN
Flv_sub(GEN x, GEN y, ulong p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++) z[i] = Fl_sub(x[i], y[i], p);
  return z;
}

void
Flv_sub_inplace(GEN x, GEN y, ulong p)
{
  long i, l = lg(x);
  for (i = 1; i < l; i++) x[i] = Fl_sub(x[i], y[i], p);
}

GEN
Flm_Fl_add(GEN x, ulong y, ulong p)
{
  long l = lg(x), i, j;
  GEN z = cgetg(l,t_MAT);

  if (l==1) return z;
  if (l != lgcols(x)) pari_err_OP( "+", x, utoi(y));
  for (i=1; i<l; i++)
  {
    GEN zi = cgetg(l,t_VECSMALL), xi = gel(x,i);
    gel(z,i) = zi;
    for (j=1; j<l; j++) zi[j] = xi[j];
    zi[i] = Fl_add(zi[i], y, p);
  }
  return z;
}

GEN
Flm_add(GEN x, GEN y, ulong p)
{
  long i, l = lg(x);
  GEN z = cgetg(l,t_MAT);
  for (i = 1; i < l; i++) gel(z,i) = Flv_add(gel(x,i),gel(y,i),p);
  return z;
}

/********************************************************************/
/**                                                                **/
/**                           MULTIPLICATION                       **/
/**                                                                **/
/********************************************************************/
GEN
FpC_Fp_mul(GEN x, GEN y, GEN p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_COL);
  for (i=1;i<l;i++) gel(z,i) = Fp_mul(gel(x,i),y,p);
  return z;
}
GEN
Flc_Fl_mul(GEN x, ulong y, ulong p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_VECSMALL);
  for (i=1;i<l;i++) z[i] = Fl_mul(x[i], y, p);
  return z;
}
GEN
Flc_Fl_div(GEN x, ulong y, ulong p)
{
  return Flc_Fl_mul(x, Fl_inv(y, p), p);
}
void
Flc_Fl_div_inplace(GEN x, ulong y, ulong p)
{
  Flc_Fl_mul_inplace(x, Fl_inv(y, p), p);
}
GEN
FpM_Fp_mul(GEN X, GEN c, GEN p) {
  long i, j, h, l = lg(X);
  GEN A = cgetg(l, t_MAT);
  if (l == 1) return A;
  h = lgcols(X);
  for (j=1; j<l; j++)
  {
    GEN a = cgetg(h, t_COL), x = gel(X, j);
    for (i = 1; i < h; i++) gel(a,i) = Fp_mul(gel(x,i), c, p);
    gel(A,j) = a;
  }
  return A;
}

/* x *= y */
void
Flc_Fl_mul_part_inplace(GEN x, ulong y, ulong p, long l)
{
  long i;
  for (i=1;i<=l;i++) x[i] = Fl_mul(x[i], y, p);
}
void
Flc_Fl_mul_inplace(GEN x, ulong y, ulong p)
{ Flc_Fl_mul_part_inplace(x, y, p, lg(x)-1); }

/* set y *= x */
void
Flm_Fl_mul_inplace(GEN y, ulong x, ulong p)
{
  long i, j, m = lgcols(y), l = lg(y);
  if (HIGHWORD(x | p))
    for(j=1; j<l; j++)
      for(i=1; i<m; i++) ucoeff(y,i,j) = Fl_mul(ucoeff(y,i,j), x, p);
  else
    for(j=1; j<l; j++)
      for(i=1; i<m; i++) ucoeff(y,i,j) = (ucoeff(y,i,j) * x) % p;
}
/* return x * y */
GEN
Flm_Fl_mul(GEN y, ulong x, ulong p)
{
  long i, j, m = lgcols(y), l = lg(y);
  GEN z = cgetg(l, t_MAT);
  if (HIGHWORD(x | p))
    for(j=1; j<l; j++) {
      GEN c = cgetg(m, t_VECSMALL); gel(z,j) = c;
      for(i=1; i<m; i++) c[i] = Fl_mul(ucoeff(y,i,j), x, p);
    }
  else
    for(j=1; j<l; j++) {
      GEN c = cgetg(m, t_VECSMALL); gel(z,j) = c;
      for(i=1; i<m; i++) c[i] = (ucoeff(y,i,j) * x) % p;
    }
  return z;
}

GEN
Flv_neg(GEN v, ulong p)
{
  long i, m = lg(v);
  GEN c = cgetg(m, t_VECSMALL);
  for(i=1; i<m; i++) uel(c,i) = Fl_neg(uel(v,i), p);
  return c;
}

void
Flv_neg_inplace(GEN v, ulong p)
{
  long i;
  for (i = 1; i < lg(v); ++i)
    v[i] = Fl_neg(v[i], p);
}

GEN
Flm_neg(GEN y, ulong p)
{
  long j, l = lg(y);
  GEN z = cgetg(l, t_MAT);
  for(j=1; j<l; j++)
    gel(z,j) = Flv_neg(gel(y,j), p);
  return z;
}

/* x[i,]*y. Assume lx > 1 and 0 < i < lgcols(x) */
static GEN
ZMrow_ZC_mul_i(GEN x, GEN y, long lx, long i)
{
  GEN c = mulii(gcoeff(x,i,1), gel(y,1));
  long k;
  for (k = 2; k < lx; k++)
  {
    GEN t = mulii(gcoeff(x,i,k), gel(y,k));
    if (signe(t)) c = addii(c, t);
  }
  return c;
}

static long
zmrow_zc_mul(GEN x, GEN y, long lx, long i)
{
  long k;
  long c = coeff(x,i,1) * y[1];
  for (k = 2; k < lx; k++)
    c += coeff(x,i,k) * y[k];
  return c;
}

GEN
zm_zc_mul(GEN x, GEN y)
{
  long lx = lg(x), l, i;
  GEN z;
  if (lx == 1) return cgetg(1, t_VECSMALL);
  l = lg(gel(x,1));
  z = cgetg(l,t_VECSMALL);
  for (i=1; i<l; i++) z[i] = zmrow_zc_mul(x, y, lx, i);
  return z;
}

GEN
zm_mul(GEN x, GEN y)
{
  long i,j,lx=lg(x), ly=lg(y);
  GEN z;
  if (ly==1) return cgetg(1,t_MAT);
  z = cgetg(ly,t_MAT);
  if (lx==1)
  {
    for (i=1; i<ly; i++) gel(z,i) = cgetg(1,t_VECSMALL);
    return z;
  }
  for (j=1; j<ly; j++)
    gel(z,j) = zm_zc_mul(x, gel(y,j));
  return z;
}

static ulong
Flmrow_Flc_mul_SMALL(GEN x, GEN y, ulong p, long lx, long i)
{
  ulong c = ucoeff(x,i,1) * uel(y,1);
  long k;
  for (k = 2; k < lx; k++) {
    c += ucoeff(x,i,k) * uel(y,k);
    if (c & HIGHBIT) c %= p;
  }
  return c % p;
}

static ulong
Flmrow_Flc_mul_i(GEN x, GEN y, ulong p, ulong pi, long lx, long i)
{
  ulong l0, l1, v1, h0, h1;
  long k = 1;
  LOCAL_OVERFLOW;
  LOCAL_HIREMAINDER;
  l1 = mulll(ucoeff(x,i,k), uel(y,k)); h1 = hiremainder; v1 = 0;
  while (++k < lx) {
    l0 = mulll(ucoeff(x,i,k), uel(y,k)); h0 = hiremainder;
    l1 = addll(l0, l1); h1 = addllx(h0, h1); v1 += overflow;
  }
  if (v1 == 0) return remll_pre(h1, l1, p, pi);
  else return remlll_pre(v1, h1, l1, p, pi);
}

static GEN
Flm_Flc_mul_i_2(GEN x, GEN y, long lx, long l)
{
  long i,j;
  GEN z = NULL;

  for (j=1; j<lx; j++)
  {
    if (!y[j]) continue;
    if (!z) z = Flv_copy(gel(x,j));
    else for (i = 1; i < l; i++) z[i] ^= coeff(x,i,j);
  }
  if (!z) z = zero_zv(l-1);
  return z;
}

static GEN
FpM_FpC_mul_i(GEN x, GEN y, long lx, long l, GEN p)
{
  GEN z = cgetg(l,t_COL);
  long i;
  for (i = 1; i < l; i++)
  {
    pari_sp av = avma;
    GEN c = ZMrow_ZC_mul_i(x, y, lx, i);
    gel(z,i) = gerepileuptoint(av, modii(c,p));
  }
  return z;
}
static GEN
Flm_Flc_mul_i_SMALL(GEN x, GEN y, long lx, long l, ulong p)
{
  GEN z = cgetg(l,t_VECSMALL);
  long i;
  for (i = 1; i < l; i++) z[i] = Flmrow_Flc_mul_SMALL(x, y, p, lx, i);
  return z;
}
static GEN
Flm_Flc_mul_i(GEN x, GEN y, long lx, long l, ulong p, ulong pi)
{
  GEN z = cgetg(l,t_VECSMALL);
  long i;
  for (i = 1; i < l; i++) z[i] = Flmrow_Flc_mul_i(x, y, p, pi, lx, i);
  return z;
}
INLINE GEN
F2m_F2c_mul_i(GEN x, GEN y, long lx, long l)
{
  long j;
  GEN z = NULL;

  for (j=1; j<lx; j++)
  {
    if (!F2v_coeff(y,j)) continue;
    if (!z) z = vecsmall_copy(gel(x,j));
    else F2v_add_inplace(z,gel(x,j));
  }
  if (!z) z = zero_F2v(l);
  return z;
}

GEN
FpM_mul(GEN x, GEN y, GEN p)
{
  long j, l, lx=lg(x), ly=lg(y);
  GEN z;
  if (ly==1) return cgetg(1,t_MAT);
  if (lx==1) return zeromat(0, ly-1);
  if (lgefint(p) == 3)
  {
    pari_sp av = avma;
    ulong pp = uel(p,2);
    if (pp == 2)
    {
      x = ZM_to_F2m(x);
      y = ZM_to_F2m(y);
      z = F2m_to_ZM(F2m_mul(x,y));
    }
    else
    {
      x = ZM_to_Flm(x, pp);
      y = ZM_to_Flm(y, pp);
      z = Flm_to_ZM(Flm_mul(x,y, pp));
    }
    return gerepileupto(av, z);
  }
  l = lgcols(x); z = cgetg(ly,t_MAT);
  for (j=1; j<ly; j++) gel(z,j) = FpM_FpC_mul_i(x, gel(y,j), lx, l, p);
  return z;
}
GEN
Flm_mul(GEN x, GEN y, ulong p)
{
  long i,j,l,lx=lg(x), ly=lg(y);
  GEN z;
  if (ly==1) return cgetg(1,t_MAT);
  z = cgetg(ly,t_MAT);
  if (lx==1)
  {
    for (i=1; i<ly; i++) gel(z,i) = cgetg(1,t_VECSMALL);
    return z;
  }
  l = lgcols(x);
  if (SMALL_ULONG(p)) {
    for (j=1; j<ly; j++)
      gel(z,j) = Flm_Flc_mul_i_SMALL(x, gel(y,j), lx, l, p);
  } else {
    ulong pi = get_Fl_red(p);
    for (j=1; j<ly; j++)
      gel(z,j) = Flm_Flc_mul_i(x, gel(y,j), lx, l, p, pi);
  }
  return z;
}
GEN
F2m_mul(GEN x, GEN y)
{
  long i,j,l,lx=lg(x), ly=lg(y);
  GEN z;
  if (ly==1) return cgetg(1,t_MAT);
  z = cgetg(ly,t_MAT);
  if (lx==1)
  {
    for (i=1; i<ly; i++) gel(z,i) = mkvecsmall(0);
    return z;
  }
  l = coeff(x,1,1);
  for (j=1; j<ly; j++) gel(z,j) = F2m_F2c_mul_i(x, gel(y,j), lx, l);
  return z;
}

static GEN
_Flm_mul(void *p , GEN x, GEN y)
{ return Flm_mul(x,y,*(ulong*)p); }
static GEN
_Flm_sqr(void *p, GEN x)
{ return Flm_mul(x,x,*(ulong*)p); }
GEN
Flm_powu(GEN x, ulong n, ulong p)
{
  pari_sp av = avma;
  if (!n) return matid(lg(x)-1);
  return gerepileupto(av, gen_powu(x, n, (void*)&p, &_Flm_sqr, &_Flm_mul));
}
static GEN
_F2m_mul(void *data, GEN x, GEN y)
{ (void) data; return F2m_mul(x,y); }
static GEN
_F2m_sqr(void *data, GEN x)
{ (void) data; return F2m_mul(x,x); }
GEN
F2m_powu(GEN x, ulong n)
{
  pari_sp av = avma;
  if (!n) return matid(lg(x)-1);
  return gerepileupto(av, gen_powu(x, n,NULL, &_F2m_sqr, &_F2m_mul));
}
static GEN
_FpM_mul(void *p , GEN x, GEN y)
{ return FpM_mul(x,y,(GEN)p); }
static GEN
_FpM_sqr(void *p, GEN x)
{ return FpM_mul(x,x,(GEN)p); }
GEN
FpM_powu(GEN x, ulong n, GEN p)
{
  pari_sp av = avma;
  if (!n) return matid(lg(x)-1);
  if (lgefint(p) == 3)
  {
    pari_sp av = avma;
    ulong pp = uel(p,2);
    GEN z;
    if (pp == 2)
      z = F2m_to_ZM(F2m_powu(ZM_to_F2m(x),n));
    else
      z = Flm_to_ZM(Flm_powu(ZM_to_Flm(x, pp), n, pp));
    return gerepileupto(av, z);
  }
  return gerepileupto(av, gen_powu(x, n, (void*)p, &_FpM_sqr, &_FpM_mul));
}

/*Multiple a column vector by a line vector to make a matrix*/
GEN
FpC_FpV_mul(GEN x, GEN y, GEN p)
{
  long i,j, lx=lg(x), ly=lg(y);
  GEN z;
  if (ly==1) return cgetg(1,t_MAT);
  z = cgetg(ly,t_MAT);
  for (j=1; j < ly; j++)
  {
    gel(z,j) = cgetg(lx,t_COL);
    for (i=1; i<lx; i++) gcoeff(z,i,j) = Fp_mul(gel(x,i),gel(y,j), p);
  }
  return z;
}

/* Multiply a line vector by a column and return a scalar (t_INT) */
GEN
FpV_dotproduct(GEN x, GEN y, GEN p)
{
  long i, lx = lg(x);
  pari_sp av;
  GEN c;
  if (lx == 1) return gen_0;
  av = avma; c = mulii(gel(x,1),gel(y,1));
  for (i=2; i<lx; i++) c = addii(c, mulii(gel(x,i),gel(y,i)));
  return gerepileuptoint(av, modii(c,p));
}
GEN
FpV_dotsquare(GEN x, GEN p)
{
  long i, lx = lg(x);
  pari_sp av;
  GEN c;
  if (lx == 1) return gen_0;
  av = avma; c = sqri(gel(x,1));
  for (i=2; i<lx; i++) c = addii(c, sqri(gel(x,i)));
  return gerepileuptoint(av, modii(c,p));
}

INLINE ulong
Flv_dotproduct_SMALL(GEN x, GEN y, ulong p, long lx)
{
  ulong c = uel(x,1) * uel(y,1);
  long k;
  for (k = 2; k < lx; k++) {
    c += uel(x,k) * uel(y,k);
    if (c & HIGHBIT) c %= p;
  }
  return c % p;
}

INLINE ulong
Flv_dotproduct_i(GEN x, GEN y, ulong p, ulong pi, long lx)
{
  ulong l0, l1, v1, h0, h1;
  long i = 1;
  LOCAL_OVERFLOW;
  LOCAL_HIREMAINDER;
  l1 = mulll(uel(x,i), uel(y,i)); h1 = hiremainder; v1 = 0;
  while (++i < lx) {
    l0 = mulll(uel(x,i), uel(y,i)); h0 = hiremainder;
    l1 = addll(l0, l1); h1 = addllx(h0, h1); v1 += overflow;
  }
  if (v1 == 0) return remll_pre(h1, l1, p, pi);
  else return remlll_pre(v1, h1, l1, p, pi);
}

ulong
Flv_dotproduct(GEN x, GEN y, ulong p)
{
  long lx = lg(x);
  if (lx == 1) return 0;
  if (SMALL_ULONG(p))
    return Flv_dotproduct_SMALL(x, y, p, lx);
  else
    return Flv_dotproduct_i(x, y, p, get_Fl_red(p), lx);
}

ulong
Flv_dotproduct_pre(GEN x, GEN y, ulong p, ulong pi)
{
  long lx = lg(x);
  if (lx == 1) return 0;
  if (SMALL_ULONG(p))
    return Flv_dotproduct_SMALL(x, y, p, lx);
  else
    return Flv_dotproduct_i(x, y, p, pi, lx);
}

ulong
F2v_dotproduct(GEN x, GEN y)
{
  long i, lx = lg(x);
  ulong c;
  if (lx == 2) return 0;
  c = uel(x,2) & uel(y,2);
  for (i=3; i<lx; i++) c ^= uel(x,i) & uel(y,i);
#ifdef LONG_IS_64BIT
  c ^= c >> 32;
#endif
  c ^= c >> 16;
  c ^= c >>  8;
  c ^= c >>  4;
  c ^= c >>  2;
  c ^= c >>  1;
  return c & 1;
}

GEN
FpM_FpC_mul(GEN x, GEN y, GEN p)
{
  long lx = lg(x);
  return lx==1? cgetg(1,t_COL): FpM_FpC_mul_i(x, y, lx, lgcols(x), p);
}
GEN
Flm_Flc_mul(GEN x, GEN y, ulong p)
{
  long l, lx = lg(x);
  if (lx==1) return cgetg(1,t_VECSMALL);
  l = lgcols(x);
  if (p==2)
    return Flm_Flc_mul_i_2(x, y, lx, l);
  else if (SMALL_ULONG(p))
    return Flm_Flc_mul_i_SMALL(x, y, lx, l, p);
  else
    return Flm_Flc_mul_i(x, y, lx, l, p, get_Fl_red(p));
}

GEN
Flm_Flc_mul_pre(GEN x, GEN y, ulong p, ulong pi)
{
  long l, lx = lg(x);
  if (lx==1) return cgetg(1,t_VECSMALL);
  l = lgcols(x);
  if (SMALL_ULONG(p))
    return Flm_Flc_mul_i_SMALL(x, y, lx, l, p);
  else
    return Flm_Flc_mul_i(x, y, lx, l, p, pi);
}

GEN
F2m_F2c_mul(GEN x, GEN y)
{
  long l, lx = lg(x);
  if (lx==1) return cgetg(1,t_VECSMALL);
  l = coeff(x,1,1);
  return F2m_F2c_mul_i(x, y, lx, l);
}
/* RgV_to_RgX(FpM_FpC_mul(x,y,p), v), p != NULL, memory clean */
GEN
FpM_FpC_mul_FpX(GEN x, GEN y, GEN p, long v)
{
  long i, l, lx = lg(x);
  GEN z;
  if (lx==1) return pol_0(v);
  l = lgcols(x);
  z = new_chunk(l+1);
  for (i=l-1; i; i--)
  {
    pari_sp av = avma;
    GEN p1 = ZMrow_ZC_mul_i(x,y,lx,i);
    p1 = modii(p1, p);
    if (signe(p1))
    {
      if (i != l-1) stackdummy((pari_sp)(z + l+1), (pari_sp)(z + i+2));
      gel(z,i+1) = gerepileuptoint(av, p1);
      break;
    }
    avma = av;
  }
  if (!i) { avma = (pari_sp)(z + l+1); return pol_0(v); }
  z[0] = evaltyp(t_POL) | evallg(i+2);
  z[1] = evalsigne(1) | evalvarn(v);
  for (; i; i--)
  {
    pari_sp av = avma;
    GEN p1 = ZMrow_ZC_mul_i(x,y,lx,i);
    gel(z,i+1) = gerepileuptoint(av, modii(p1,p));
  }
  return z;
}

/********************************************************************/
/**                                                                **/
/**                           TRANSPOSITION                        **/
/**                                                                **/
/********************************************************************/

/* == zm_transpose */
GEN
Flm_transpose(GEN x)
{
  long i, dx, lx = lg(x);
  GEN y;
  if (lx == 1) return cgetg(1,t_MAT);
  dx = lgcols(x); y = cgetg(dx,t_MAT);
  for (i=1; i<dx; i++) gel(y,i) = Flm_row(x,i);
  return y;
}

/********************************************************************/
/**                                                                **/
/**                           SCALAR MATRICES                      **/
/**                                                                **/
/********************************************************************/

GEN
gen_matid(long n, void *E, const struct bb_field *S)
{
  GEN y = cgetg(n+1,t_MAT), _0, _1;
  long i;
  if (n < 0) pari_err_DOMAIN("gen_matid", "dimension","<",gen_0,stoi(n));
  _0 = S->s(E,0);
  _1 = S->s(E,1);
  for (i=1; i<=n; i++)
  {
    GEN z = const_col(n, _0); gel(z,i) = _1;
    gel(y, i) = z;
  }
  return y;
}

GEN
matid_F2m(long n)
{
  GEN y = cgetg(n+1,t_MAT);
  long i;
  if (n < 0) pari_err_DOMAIN("matid_F2m", "dimension","<",gen_0,stoi(n));
  for (i=1; i<=n; i++) { gel(y,i) = zero_F2v(n); F2v_set(gel(y,i),i); }
  return y;
}

GEN
matid_F2xqM(long n, GEN T)
{
  void *E;
  const struct bb_field *S = get_F2xq_field(&E, T);
  return gen_matid(n, E, S);
}
GEN
matid_FlxqM(long n, GEN T, ulong p)
{
  void *E;
  const struct bb_field *S = get_Flxq_field(&E, T, p);
  return gen_matid(n, E, S);
}

GEN
matid_Flm(long n)
{
  GEN y = cgetg(n+1,t_MAT);
  long i;
  if (n < 0) pari_err_DOMAIN("matid_Flm", "dimension","<",gen_0,stoi(n));
  for (i=1; i<=n; i++) { gel(y,i) = zero_zv(n); ucoeff(y, i,i) = 1; }
  return y;
}

GEN
scalar_Flm(long s, long n)
{
  long i;
  GEN y = cgetg(n+1,t_MAT);
  for (i=1; i<=n; i++) { gel(y,i) = zero_Flv(n); coeff(y, i,i) = s; }
  return y;
}

/********************************************************************/
/**                                                                **/
/**                           CONVERSIONS                          **/
/**                                                                **/
/********************************************************************/
GEN
ZV_to_Flv(GEN x, ulong p)
{
  long i, n = lg(x);
  GEN y = cgetg(n,t_VECSMALL);
  for (i=1; i<n; i++) y[i] = umodiu(gel(x,i), p);
  return y;
}
GEN
ZM_to_Flm(GEN x, ulong p)
{
  long j,n = lg(x);
  GEN y = cgetg(n,t_MAT);
  if (n == 1) return y;
  for (j=1; j<n; j++) gel(y,j) = ZV_to_Flv(gel(x,j), p);
  return y;
}
GEN
ZMV_to_FlmV(GEN z, ulong m)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_VEC);
  for (i=1; i<l; i++) gel(x,i) = ZM_to_Flm(gel(z,i), m);
  return x;
}

/*                          TO INTMOD                        */
static GEN
to_intmod(GEN x, GEN p) { retmkintmod(modii(x, p), p); }
static GEN
Fl_to_intmod(ulong x, GEN p) { retmkintmod(utoi(x), p); }

GEN
Fp_to_mod(GEN z, GEN p)
{
  retmkintmod(modii(z, p), icopy(p));
}

/* z in Z[X], return z * Mod(1,p), normalized*/
GEN
FpX_to_mod(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l,t_POL);
  if (l >2) p = icopy(p);
  for (i=2; i<l; i++) gel(x,i) = to_intmod(gel(z,i), p);
  x[1] = z[1]; return normalizepol_lg(x,l);
}

/* z in Z^n, return z * Mod(1,p), normalized*/
GEN
FpV_to_mod(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_VEC);
  if (l == 1) return x;
  p = icopy(p);
  for (i=1; i<l; i++) gel(x,i) = to_intmod(gel(z,i), p);
  return x;
}
/* z in Z^n, return z * Mod(1,p), normalized*/
GEN
FpC_to_mod(GEN z, GEN p)
{
  long i, l = lg(z);
  GEN x = cgetg(l, t_COL);
  if (l == 1) return x;
  p = icopy(p);
  for (i=1; i<l; i++) gel(x,i) = to_intmod(gel(z,i), p);
  return x;
}
/* z in Mat m,n(Z), return z * Mod(1,p), normalized*/
GEN
FpM_to_mod(GEN z, GEN p)
{
  long i, j, m, l = lg(z);
  GEN  x = cgetg(l,t_MAT), y, zi;
  if (l == 1) return x;
  m = lgcols(z);
  p = icopy(p);
  for (i=1; i<l; i++)
  {
    gel(x,i) = cgetg(m,t_COL);
    y = gel(x,i); zi= gel(z,i);
    for (j=1; j<m; j++) gel(y,j) = to_intmod(gel(zi,j), p);
  }
  return x;
}
GEN
Flc_to_mod(GEN z, ulong pp)
{
  long i, l = lg(z);
  GEN p, x = cgetg(l, t_COL);
  if (l == 1) return x;
  p = utoipos(pp);
  for (i=1; i<l; i++) gel(x,i) = Fl_to_intmod(z[i], p);
  return x;
}
GEN
Flm_to_mod(GEN z, ulong pp)
{
  long i, j, m, l = lg(z);
  GEN p, x = cgetg(l,t_MAT), y, zi;
  if (l == 1) return x;
  m = lgcols(z);
  p = utoipos(pp);
  for (i=1; i<l; i++)
  {
    gel(x,i) = cgetg(m,t_COL);
    y = gel(x,i); zi= gel(z,i);
    for (j=1; j<m; j++) gel(y,j) = Fl_to_intmod(zi[j], p);
  }
  return x;
}

GEN
FpVV_to_mod(GEN z, GEN p)
{
  long i, j, m, l = lg(z);
  GEN  x = cgetg(l,t_VEC), y, zi;
  if (l == 1) return x;
  m = lgcols(z);
  p = icopy(p);
  for (i=1; i<l; i++)
  {
    gel(x,i) = cgetg(m,t_VEC);
    y = gel(x,i); zi= gel(z,i);
    for (j=1; j<m; j++) gel(y,j) = to_intmod(gel(zi,j), p);
  }
  return x;
}

/* z in Z^n, return z * Mod(1,p), normalized*/
GEN
FpXQC_to_mod(GEN z, GEN T, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_COL); T = FpX_to_mod(T, p);
  for (i=1; i<l; i++)
    gel(x,i) = mkpolmod(FpX_to_mod(gel(z,i), p), T);
  return x;
}

/********************************************************************/
/*                                                                  */
/*                     Blackbox linear algebra                      */
/*                                                                  */
/********************************************************************/

/* A sparse column (zCs) v is a t_COL with two components C and E which are
 * t_VECSMALL of the same length, representing sum_i E[i]*e_{C[i]}, where
 * (e_j) is the canonical basis.
 * A sparse matrix (zMs) is a t_VEC of zCs */

/* FpCs and FpMs are identical but E[i] is interpreted as a _signed_ C long
 * integer representing an element of Fp. This is important since p can be
 * large and p+E[i] would not fit in a C long.  */

/* RgCs and RgMs are similar, except that the type of the component is
 * unspecified. Functions handling RgCs/RgMs must be independent of the type
 * of E. */

/* Most functions take an argument nbrow which is the number of lines of the
 * column/matrix, which cannot be derived from the data. */

GEN
zCs_to_ZC(GEN R, long nbrow)
{
  GEN C = gel(R,1), E = gel(R,2), c = zerocol(nbrow);
  long j, l = lg(C);
  for (j = 1; j < l; ++j) gel(c, C[j]) = stoi(E[j]);
  return c;
}

GEN
zMs_to_ZM(GEN M, long nbrow)
{
  long i, l = lg(M);
  GEN m = cgetg(l, t_MAT);
  for (i = 1; i < l; ++i) gel(m,i) = zCs_to_ZC(gel(M,i), nbrow);
  return m;
}

/* Solve equation f(X) = B (mod p) where B is a FpV, and f is an endomorphism.
 * Return either a solution as a t_COL, or a kernel vector as a t_VEC. */
GEN
gen_FpM_Wiedemann(void *E, GEN (*f)(void*, GEN), GEN B, GEN p)
{
  pari_sp ltop = avma;
  long col = 0, n = lg(B)-1, m = 2*n+1;
  if (ZV_equal0(B)) return zerocol(n);
  while (++col <= n)
  {
    pari_sp btop = avma, av;
    long i, lQ;
    GEN V, Q, M, W = B;
    GEN b = cgetg(m+2, t_POL);
    b[1] = evalsigne(1)|evalvarn(0);
    gel(b, 2) = gel(W, col);
    for (i = 3; i<m+2; i++)
      gel(b, i) = cgeti(lgefint(p));
    av = avma;
    for (i = 3; i<m+2; i++)
    {
      W = f(E, W);
      affii(gel(W, col),gel(b, i));
      if (gc_needed(av,1))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"Wiedemann: first loop, %ld",i);
        W = gerepileupto(av, W);
      }
    }
    b = FpX_renormalize(b, m+2);
    if (lgpol(b)==0) {avma = btop; continue; }
    M = FpX_halfgcd(b, monomial(gen_1, m, 0), p);
    Q = FpX_neg(FpX_normalize(gcoeff(M, 2, 1),p),p);
    W = B; lQ =lg(Q);
    if (DEBUGLEVEL) err_printf("Wiedemann: deg. minpoly: %ld\n",lQ-3);
    V = FpC_Fp_mul(W, gel(Q, lQ-2), p);
    av = avma;
    for (i = lQ-3; i > 1; i--)
    {
      W = f(E, W);
      V = ZC_lincomb(gen_1, gel(Q,i), V, W);
      if (gc_needed(av,1))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"Wiedemann: second loop, %ld",i);
        gerepileall(av, 2, &V, &W);
      }
    }
    V = FpC_red(V, p);
    W = FpC_sub(f(E,V), B, p);
    if (ZV_equal0(W)) return gerepilecopy(ltop, V);
    av = avma;
    for (i = 1; i <= n; ++i)
    {
      V = W;
      W = f(E, V);
      if (ZV_equal0(W))
        return gerepilecopy(ltop, shallowtrans(V));
      gerepileall(av, 2, &V, &W);
    }
    avma = btop;
  }
  return NULL;
}

GEN
zMs_ZC_mul(GEN M, GEN B)
{
  long i, j;
  long n = lg(B)-1;
  GEN V = zerocol(n);
  for (i = 1; i <= n; ++i)
    if (signe(gel(B, i)))
    {
      GEN R = gel(M, i), C = gel(R, 1), E = gel(R, 2);
      long l = lg(C);
      for (j = 1; j < l; ++j)
      {
        long k = C[j];
        switch(E[j])
        {
        case 1:
          gel(V, k) = gel(V,k)==gen_0 ? gel(B,i) : addii(gel(V, k), gel(B,i));
          break;
        case -1:
          gel(V, k) = gel(V,k)==gen_0 ? negi(gel(B,i)) : subii(gel(V, k), gel(B,i));
          break;
        default:
          gel(V, k) = gel(V,k)==gen_0 ? mulis(gel(B, i), E[j]) : addii(gel(V, k), mulis(gel(B, i), E[j]));
          break;
        }
      }
    }
  return V;
}

GEN
FpMs_FpC_mul(GEN M, GEN B, GEN p) { return FpC_red(zMs_ZC_mul(M, B), p); }

GEN
ZV_zMs_mul(GEN B, GEN M)
{
  long i, j;
  long m = lg(M)-1;
  GEN V = cgetg(m+1,t_VEC);
  for (i = 1; i <= m; ++i)
  {
    GEN R = gel(M, i), C = gel(R, 1), E = gel(R, 2);
    long l = lg(C);
    GEN z = mulis(gel(B, C[1]), E[1]);
    for (j = 2; j < l; ++j)
    {
      long k = C[j];
      switch(E[j])
      {
      case 1:
        z = addii(z, gel(B,k));
        break;
      case -1:
        z = subii(z, gel(B,k));
        break;
      default:
        z = addii(z, mulis(gel(B,k), E[j]));
        break;
      }
    }
    gel(V,i) = z;
  }
  return V;
}

GEN
FpV_FpMs_mul(GEN B, GEN M, GEN p) { return FpV_red(ZV_zMs_mul(B, M), p); }

GEN
ZlM_gauss(GEN a, GEN b, ulong p, long e, GEN C)
{
  pari_sp av = avma, av2;
  GEN xi, xb, pi = gen_1, P;
  long i;
  if (!C) {
    C = Flm_inv(ZM_to_Flm(a, p), p);
    if (!C) pari_err_INV("ZlM_gauss", a);
  }
  P = utoipos(p);
  av2 = avma;
  xi = Flm_mul(C, ZM_to_Flm(b, p), p);
  xb = Flm_to_ZM(xi);
  for (i = 2; i <= e; i++)
  {
    pi = muliu(pi, p); /* = p^(i-1) */
    b = ZM_Z_divexact(ZM_sub(b, ZM_nm_mul(a, xi)), P);
    if (gc_needed(av,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ZlM_gauss. i=%ld",i);
      gerepileall(av2,3, &pi,&b,&xb);
    }
    xi = Flm_mul(C, ZM_to_Flm(b, p), p);
    xb = ZM_add(xb, nm_Z_mul(xi, pi));
  }
  return gerepileupto(av, xb);
}

struct wrapper_modp_s {
  GEN (*f)(void*, GEN);
  void *E;
  GEN p;
};

/* compute f(x) mod p */
static GEN
wrap_relcomb_modp(void *E, GEN x)
{
  struct wrapper_modp_s *W = (struct wrapper_modp_s*)E;
  return FpC_red(W->f(W->E, x), W->p);
}
static GEN
wrap_relcomb(void*E, GEN x) { return zMs_ZC_mul((GEN)E, x); }

static GEN
wrap_relker(void*E, GEN x) { return ZV_zMs_mul(x, (GEN)E); }

/* Solve f(X) = B (mod p^e); blackbox version of ZlM_gauss */
GEN
gen_ZpM_Dixon(void *E, GEN (*f)(void*, GEN), GEN B, GEN p, long e)
{
  struct wrapper_modp_s W;
  pari_sp av = avma;
  GEN xb, xi, pi = gen_1;
  long i;
  W.E = E;
  W.f = f;
  W.p = p;
  xi = gen_FpM_Wiedemann((void*)&W, wrap_relcomb_modp, FpC_red(B, p), p); /* f^(-1) B */
  if (!xi || e == 1 || typ(xi) == t_VEC) return xi;
  xb = xi;
  for (i = 2; i <= e; i++)
  {
    pi = mulii(pi, p); /* = p^(i-1) */
    B = ZC_Z_divexact(ZC_sub(B, f(E, xi)), p);
    if (gc_needed(av,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"gen_ZpM_Dixon. i=%ld",i);
      gerepileall(av,3, &pi,&B,&xb);
    }
    xi = gen_FpM_Wiedemann((void*)&W, wrap_relcomb_modp, FpC_red(B, p), p);
    if (!xi) return NULL;
    if (typ(xi) == t_VEC) return gerepileupto(av, xi);
    xb = ZC_add(xb, ZC_Z_mul(xi, pi));
  }
  return gerepileupto(av, xb);
}

static GEN
vecprow(GEN A, GEN prow)
{
  return mkvec2(vecsmallpermute(prow,gel(A,1)), gel(A,2));
}

/* Solve the equation MX = A. Return either a solution as a t_COL,
 * or the index of a column which is linearly dependent from the others as a
 * t_VECSMALL with a single component. */
GEN
ZpMs_ZpCs_solve(GEN M, GEN A, long nbrow, GEN p, long e)
{
  pari_sp av = avma;
  GEN pcol, prow;
  long nbi=lg(M)-1, lR;
  long i, n;
  GEN Mp, Ap, Rp;
  pari_timer ti;
  if (DEBUGLEVEL) timer_start(&ti);
  RgMs_structelim(M, nbrow, gel(A, 1), &pcol, &prow);
  if (!pcol) { avma = av; return NULL; }
  if (DEBUGLEVEL)
    timer_printf(&ti,"structured elimination (%ld -> %ld)",nbi,lg(pcol)-1);
  n = lg(pcol)-1;
  Mp = cgetg(n+1, t_MAT);
  for(i=1; i<=n; i++)
    gel(Mp, i) = vecprow(gel(M,pcol[i]), prow);
  Ap = zCs_to_ZC(vecprow(A, prow), n);
  if (DEBUGLEVEL) timer_start(&ti);
  Rp = gen_ZpM_Dixon((void*)Mp,wrap_relcomb, Ap, p, e);
  if (DEBUGLEVEL) timer_printf(&ti,"linear algebra");
  if (!Rp) { avma = av; return NULL; }
  lR = lg(Rp)-1;
  if (typ(Rp) == t_COL)
  {
    GEN R = zerocol(nbi+1);
    for (i=1; i<=lR; i++)
       gel(R,pcol[i]) = gel(Rp,i);
    return gerepilecopy(av, R);
  }
  for (i = 1; i <= lR; ++i)
    if (signe(gel(Rp, i)))
      return gerepileuptoleaf(av, mkvecsmall(pcol[i]));
  return NULL; /* NOT REACHED */
}

GEN
FpMs_FpCs_solve(GEN M, GEN A, long nbrow, GEN p)
{
  return ZpMs_ZpCs_solve(M, A, nbrow, p, 1);
}

GEN
FpMs_FpCs_solve_safe(GEN M, GEN A, long nbrow, GEN p)
{
  GEN res;
  pari_CATCH(e_INV)
  {
    GEN E = pari_err_last();
    GEN x = err_get_compo(E,2);
    if (typ(x) != t_INTMOD) pari_err(0,E);
    if (DEBUGLEVEL)
      pari_warn(warner,"FpMs_FpCs_solve_safe, impossible inverse %Ps", x);
    res = NULL;
  } pari_TRY {
    res = ZpMs_ZpCs_solve(M, A, nbrow, p, 1);
  } pari_ENDCATCH
  return res;
}

static GEN
FpMs_structelim_back(GEN M, GEN V, GEN prow, GEN p)
{
  long i, j, oldf = 0, f = 0;
  long lrow = lg(prow), lM = lg(M);
  GEN W = const_vecsmall(lM-1,1);
  GEN R = cgetg(lrow, t_VEC);
  for (i=1; i<lrow; i++)
    gel(R,i) = prow[i]==0 ? NULL: gel(V,prow[i]);
  do
  {
    oldf = f;
    for(i=1; i<lM; i++)
      if (W[i])
      {
        GEN C = gel(M,i), F = gel(C,1), E = gel(C,2);
        long c=0, cj=0, lF = lg(F);
        for(j=1; j<lF; j++)
          if (!gel(R,F[j]))
          { c++; cj=j; }
        if (c>=2) continue;
        if (c==1)
        {
          pari_sp av = avma;
          GEN s = gen_0;
          for(j=1; j<lF; j++)
            if (j!=cj) s = Fp_add(s, mulis(gel(R,F[j]), E[j]), p);
          gel(R,F[cj]) = gerepileupto(av, Fp_div(Fp_neg(s, p), stoi(E[cj]), p));
          f++;
        }
        W[i]=0;
      }
  } while(oldf!=f);
  for (i=1; i<lrow; i++)
    if (!gel(R,i)) gel(R,i) = gen_0;
  return R;
}

/* Return a linear form Y such that YM is essentially 0 */
GEN
FpMs_leftkernel_elt(GEN M, long nbrow, GEN p)
{
  pari_sp av = avma, av2;
  GEN pcol, prow;
  long nbi=lg(M)-1;
  long i, n;
  GEN Mp, B, MB, R, Rp;
  pari_timer ti;
  struct wrapper_modp_s W;
  if (DEBUGLEVEL) timer_start(&ti);
  RgMs_structelim(M, nbrow, cgetg(1,t_VECSMALL), &pcol, &prow);
  if (!pcol) { avma = av; return NULL; }
  if (DEBUGLEVEL)
    timer_printf(&ti,"structured elimination (%ld -> %ld)",nbi,lg(pcol)-1);
  n = lg(pcol)-1;
  Mp = cgetg(n+1, t_MAT);
  for(i=1; i<=n; i++)
    gel(Mp, i) = vecprow(gel(M,pcol[i]), prow);
  W.E = (void*) Mp;
  W.f = wrap_relker;
  W.p = p;
  av2 = avma;
  for(;;)
  {
    avma = av2;
    B = cgetg(n+1,t_VEC);
    for(i=1; i<=n; i++)
      gel(B,i) = randomi(p);
    MB = FpV_FpMs_mul(B, Mp, p);
    if (DEBUGLEVEL) timer_start(&ti);
    pari_CATCH(e_INV)
    {
      GEN E = pari_err_last();
      GEN x = err_get_compo(E,2);
      if (typ(x) != t_INTMOD) pari_err(0,E);
      if (DEBUGLEVEL)
        pari_warn(warner,"FpMs_leftkernel_elt, impossible inverse %Ps", x);
      Rp = NULL;
    } pari_TRY {
      Rp = gen_FpM_Wiedemann((void*)&W, wrap_relcomb_modp, MB, p);
    } pari_ENDCATCH
    if (!Rp) continue;
    if (typ(Rp)==t_COL)
    {
      Rp = FpC_sub(Rp,B,p);
      if (ZV_equal0(Rp)) continue;
    }
    R = FpMs_structelim_back(M, Rp, prow, p);
    if (DEBUGLEVEL) timer_printf(&ti,"Wiedemann left kernel");
    return gerepilecopy(av, R);
  }
}
