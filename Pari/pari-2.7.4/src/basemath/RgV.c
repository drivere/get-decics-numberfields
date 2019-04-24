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

int
RgM_is_ZM(GEN x)
{
  long i, j, h, l = lg(x);
  if (l == 1) return 1;
  h = lgcols(x);
  if (h == 1) return 1;
  for (j = l-1; j > 0; j--)
    for (i = h-1; i > 0; i--)
      if (typ(gcoeff(x,i,j)) != t_INT) return 0;
  return 1;
}

int
RgV_is_ZMV(GEN V)
{
  long i, l = lg(V);
  for (i=1; i<l; i++)
    if (typ(gel(V,i))!=t_MAT || !RgM_is_ZM(gel(V,i)))
      return 0;
  return 1;
}

/********************************************************************/
/**                                                                **/
/**                   GENERIC LINEAR ALGEBRA                       **/
/**                                                                **/
/********************************************************************/
/*           GENERIC  MULTIPLICATION involving zc/zm                */
/* x non-empty t_MAT, y a compatible zc (dimension > 0). */
static GEN
RgM_zc_mul_i(GEN x, GEN y, long c, long l)
{
  long i, j;
  pari_sp av;
  GEN z = cgetg(l,t_COL), s;

  for (i=1; i<l; i++)
  {
    av = avma; s = gmulgs(gcoeff(x,i,1),y[1]);
    for (j=2; j<c; j++)
    {
      long t = y[j];
      switch(t)
      {
        case  0: break;
        case  1: s = gadd(s, gcoeff(x,i,j)); break;
        case -1: s = gsub(s, gcoeff(x,i,j)); break;
        default: s = gadd(s, gmulgs(gcoeff(x,i,j), t)); break;
      }
    }
    gel(z,i) = gerepileupto(av,s);
  }
  return z;
}
GEN
RgM_zc_mul(GEN x, GEN y) { return RgM_zc_mul_i(x,y, lg(x), lgcols(x)); }
/* x t_MAT, y a compatible zm (dimension > 0). */
GEN
RgM_zm_mul(GEN x, GEN y)
{
  long j, c, l = lg(x), ly = lg(y);
  GEN z = cgetg(ly, t_MAT);
  if (l == 1) return z;
  c = lgcols(x);
  for (j = 1; j < ly; j++) gel(z,j) = RgM_zc_mul_i(x, gel(y,j), l,c);
  return z;
}

static GEN
RgV_zc_mul_i(GEN x, GEN y, long l)
{
  long i;
  GEN z = gen_0;
  pari_sp av = avma;
  for (i = 1; i < l; i++) z = gadd(z, gmulgs(gel(x,i), y[i]));
  return gerepileupto(av, z);
}
GEN
RgV_zc_mul(GEN x, GEN y) { return RgV_zc_mul_i(x, y, lg(x)); }

GEN
RgV_zm_mul(GEN x, GEN y)
{
  long j, l = lg(x), ly = lg(y);
  GEN z = cgetg(ly, t_VEC);
  for (j = 1; j < ly; j++) gel(z,j) = RgV_zc_mul_i(x, gel(y,j), l);
  return z;
}

/* scalar product x.x */
GEN
RgV_dotsquare(GEN x)
{
  long i, lx = lg(x);
  pari_sp av = avma, lim = stack_lim(av,3);
  GEN z;
  if (lx == 1) return gen_0;
  z = gsqr(gel(x,1));
  for (i=2; i<lx; i++)
  {
    z = gadd(z, gsqr(gel(x,i)));
    if (low_stack(lim,stack_lim(av,3)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgV_dotsquare, i = %ld",i);
      z = gerepileupto(av, z);
    }
  }
  return gerepileupto(av,z);
}

/* scalar product x.y, lx = lg(x) = lg(y) */
static GEN
RgV_dotproduct_i(GEN x, GEN y, long lx)
{
  pari_sp av = avma, lim = stack_lim(av,3);
  long i;
  GEN z;
  if (lx == 1) return gen_0;
  z = gmul(gel(x,1),gel(y,1));
  for (i=2; i<lx; i++)
  {
    z = gadd(z, gmul(gel(x,i), gel(y,i)));
    if (low_stack(lim,stack_lim(av,3)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgV_dotproduct, i = %ld",i);
      z = gerepileupto(av, z);
    }
  }
  return gerepileupto(av,z);
}
GEN
RgV_dotproduct(GEN x,GEN y)
{
  if (x == y) return RgV_dotsquare(x);
  return RgV_dotproduct_i(x, y, lg(x));
}
/* v[1] + ... + v[lg(v)-1] */
GEN
RgV_sum(GEN v)
{
  GEN p;
  long i, l = lg(v);
  if (l == 1) return gen_0;
  p = gel(v,1); for (i=2; i<l; i++) p = gadd(p, gel(v,i));
  return p;
}
/* v[1] + ... + v[n]. Assume lg(v) > n. */
GEN
RgV_sumpart(GEN v, long n)
{
  GEN p;
  long i;
  if (!n) return gen_0;
  p = gel(v,1); for (i=2; i<=n; i++) p = gadd(p, gel(v,i));
  return p;
}
/* v[m] + ... + v[n]. Assume lg(v) > n, m > 0. */
GEN
RgV_sumpart2(GEN v, long m, long n)
{
  GEN p;
  long i;
  if (n < m) return gen_0;
  p = gel(v,m); for (i=m+1; i<=n; i++) p = gadd(p, gel(v,i));
  return p;
}

/*                    ADDITION SCALAR + MATRIX                     */
/* x square matrix, y scalar; create the square matrix x + y*Id */
GEN
RgM_Rg_add(GEN x, GEN y)
{
  long l = lg(x), i, j;
  GEN z = cgetg(l,t_MAT);

  if (l==1) return z;
  if (l != lgcols(x)) pari_err_OP( "+", x, y);
  z = cgetg(l,t_MAT);
  for (i=1; i<l; i++)
  {
    GEN zi = cgetg(l,t_COL), xi = gel(x,i);
    gel(z,i) = zi;
    for (j=1; j<l; j++)
      gel(zi,j) = i==j? gadd(y,gel(xi,j)): gcopy(gel(xi,j));
  }
  return z;
}
GEN
RgM_Rg_sub(GEN x, GEN y)
{
  long l = lg(x), i, j;
  GEN z = cgetg(l,t_MAT);

  if (l==1) return z;
  if (l != lgcols(x)) pari_err_OP( "-", x, y);
  z = cgetg(l,t_MAT);
  for (i=1; i<l; i++)
  {
    GEN zi = cgetg(l,t_COL), xi = gel(x,i);
    gel(z,i) = zi;
    for (j=1; j<l; j++)
      gel(zi,j) = i==j? gsub(y,gel(xi,j)): gcopy(gel(xi,j));
  }
  return z;
}
GEN
RgM_Rg_add_shallow(GEN x, GEN y)
{
  long l = lg(x), i, j;
  GEN z = cgetg(l,t_MAT);

  if (l==1) return z;
  if (l != lgcols(x)) pari_err_OP( "+", x, y);
  for (i=1; i<l; i++)
  {
    GEN zi = cgetg(l,t_COL), xi = gel(x,i);
    gel(z,i) = zi;
    for (j=1; j<l; j++) gel(zi,j) = gel(xi,j);
    gel(zi,i) = gadd(gel(zi,i), y);
  }
  return z;
}
GEN
RgM_Rg_sub_shallow(GEN x, GEN y)
{
  long l = lg(x), i, j;
  GEN z = cgetg(l,t_MAT);

  if (l==1) return z;
  if (l != lgcols(x)) pari_err_OP( "-", x, y);
  for (i=1; i<l; i++)
  {
    GEN zi = cgetg(l,t_COL), xi = gel(x,i);
    gel(z,i) = zi;
    for (j=1; j<l; j++) gel(zi,j) = gel(xi,j);
    gel(zi,i) = gsub(gel(zi,i), y);
  }
  return z;
}

GEN
RgC_Rg_add(GEN x, GEN y)
{
  long k, lx = lg(x);
  GEN z = cgetg(lx, t_COL);
  if (lx == 1)
  {
    if (isintzero(y)) return z;
    pari_err_TYPE2("+",x,y);
  }
  gel(z,1) = gadd(y,gel(x,1));
  for (k = 2; k < lx; k++) gel(z,k) = gcopy(gel(x,k));
  return z;
}

static GEN
RgC_add_i(GEN x, GEN y, long lx)
{
  GEN A = cgetg(lx, t_COL);
  long i;
  for (i=1; i<lx; i++) gel(A,i) = gadd(gel(x,i), gel(y,i));
  return A;
}
GEN
RgC_add(GEN x, GEN y) { return RgC_add_i(x, y, lg(x)); }
GEN
RgV_add(GEN x, GEN y)
{
  long i, lx = lg(x);
  GEN A = cgetg(lx, t_VEC);
  for (i=1; i<lx; i++) gel(A,i) = gadd(gel(x,i), gel(y,i));
  return A;
}

static GEN
RgC_sub_i(GEN x, GEN y, long lx)
{
  long i;
  GEN A = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) gel(A,i) = gsub(gel(x,i), gel(y,i));
  return A;
}
GEN
RgC_sub(GEN x, GEN y) { return RgC_sub_i(x, y, lg(x)); }
GEN
RgV_sub(GEN x, GEN y)
{
  long i, lx = lg(x);
  GEN A = cgetg(lx, t_VEC);
  for (i=1; i<lx; i++) gel(A,i) = gsub(gel(x,i), gel(y,i));
  return A;
}

GEN
RgM_add(GEN x, GEN y)
{
  long lx = lg(x), l, j;
  GEN z;
  if (lx == 1) return cgetg(1, t_MAT);
  z = cgetg(lx, t_MAT); l = lgcols(x);
  for (j = 1; j < lx; j++) gel(z,j) = RgC_add_i(gel(x,j), gel(y,j), l);
  return z;
}
GEN
RgM_sub(GEN x, GEN y)
{
  long lx = lg(x), l, j;
  GEN z;
  if (lx == 1) return cgetg(1, t_MAT);
  z = cgetg(lx, t_MAT); l = lgcols(x);
  for (j = 1; j < lx; j++) gel(z,j) = RgC_sub_i(gel(x,j), gel(y,j), l);
  return z;
}

static GEN
RgC_neg_i(GEN x, long lx)
{
  long i;
  GEN y = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) gel(y,i) = gneg(gel(x,i));
  return y;
}
GEN
RgC_neg(GEN x) { return RgC_neg_i(x, lg(x)); }
GEN
RgV_neg(GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx, t_VEC);
  for (i=1; i<lx; i++) gel(y,i) = gneg(gel(x,i));
  return y;
}
GEN
RgM_neg(GEN x)
{
  long i, hx, lx = lg(x);
  GEN y = cgetg(lx, t_MAT);
  if (lx == 1) return y;
  hx = lgcols(x);
  for (i=1; i<lx; i++) gel(y,i) = RgC_neg_i(gel(x,i), hx);
  return y;
}

GEN
RgV_RgC_mul(GEN x, GEN y)
{
  long lx = lg(x);
  if (lx != lg(y)) pari_err_OP("operation 'RgV_RgC_mul'", x, y);
  return RgV_dotproduct_i(x, y, lx);
}
GEN
RgC_RgV_mul(GEN x, GEN y)
{
  long i, ly = lg(y);
  GEN z = cgetg(ly,t_MAT);
  for (i=1; i<ly; i++) gel(z,i) = RgC_Rg_mul(x, gel(y,i));
  return z;
}
GEN
RgC_RgM_mul(GEN x, GEN y)
{
  long i, ly = lg(y);
  GEN z = cgetg(ly,t_MAT);
  if (ly != 1 && lgcols(y) != 2) pari_err_OP("operation 'RgC_RgM_mul'",x,y);
  for (i=1; i<ly; i++) gel(z,i) = RgC_Rg_mul(x, gcoeff(y,1,i));
  return z;
}
GEN
RgM_RgV_mul(GEN x, GEN y)
{
  if (lg(x) != 2) pari_err_OP("operation 'RgM_RgV_mul'", x,y);
  return RgC_RgV_mul(gel(x,1), y);
}

/* x[i,]*y, l = lg(y) > 1 */
static GEN
RgMrow_RgC_mul_i(GEN x, GEN y, long i, long l)
{
  pari_sp av = avma;
  GEN t = gmul(gcoeff(x,i,1), gel(y,1)); /* l > 1 ! */
  long j;
  for (j=2; j<l; j++) t = gadd(t, gmul(gcoeff(x,i,j), gel(y,j)));
  return gerepileupto(av,t);
}
GEN
RgMrow_RgC_mul(GEN x, GEN y, long i)
{ return RgMrow_RgC_mul_i(x, y, i, lg(x)); }

/* compatible t_MAT * t_COL, lx = lg(x) = lg(y) > 1, l = lgcols(x) */
static GEN
RgM_RgC_mul_i(GEN x, GEN y, long lx, long l)
{
  GEN z = cgetg(l,t_COL);
  long i;
  for (i=1; i<l; i++) gel(z,i) = RgMrow_RgC_mul_i(x,y,i,lx);
  return z;
}

GEN
RgM_RgC_mul(GEN x, GEN y)
{
  long lx = lg(x);
  GEN ffx = NULL, ffy = NULL;
  if (lx != lg(y)) pari_err_OP("operation 'RgM_RgC_mul'", x,y);
  if (lx == 1) return cgetg(1,t_COL);
  if (RgM_is_FFM(x, &ffx) && RgC_is_FFC(y, &ffy)) {
    if (!FF_samefield(ffx, ffy))
      pari_err_OP("*", ffx, ffy);
    return FFM_FFC_mul(x, y, ffx);
  }
  return RgM_RgC_mul_i(x, y, lx, lgcols(x));
}

GEN
RgV_RgM_mul(GEN x, GEN y)
{
  long i, lx, ly = lg(y);
  GEN z;
  if (ly == 1) return cgetg(1,t_VEC);
  lx = lg(x);
  if (lx != lgcols(y)) pari_err_OP("operation 'RgV_RgM_mul'", x,y);
  z = cgetg(ly, t_VEC);
  for (i=1; i<ly; i++) gel(z,i) = RgV_dotproduct_i(x, gel(y,i), lx);
  return z;
}

static int
is_modular_mul(GEN a, GEN b, GEN *z)
{
  GEN p1 = NULL, p2 = NULL, p;
  ulong pp;
  if (!RgM_is_FpM(a, &p1) || !p1) return 0;
  if (!RgM_is_FpM(b, &p2) || !p2) return 0;
  p = gcdii(p1, p2);
  a = RgM_Fp_init(a, p, &pp);
  switch(pp)
  {
  case 0:
    b = RgM_to_FpM(b,p);
    b = FpM_mul(a,b,p);
    *z = FpM_to_mod(b,p);
    break;
  case 2:
    b = RgM_to_F2m(b);
    b = F2m_mul(a,b);
    *z = F2m_to_mod(b);
    break;
  default:
    b = RgM_to_Flm(b,pp);
    b = Flm_mul(a,b,pp);
    *z = Flm_to_mod(b,pp);
  }
  return 1;
}
static int
is_modular_sqr(GEN a, GEN *z)
{
  GEN p = NULL;
  ulong pp;
  if (!RgM_is_FpM(a, &p) || !p) return 0;
  a = RgM_Fp_init(a, p, &pp);
  switch(pp)
  {
    case 0: *z = FpM_to_mod(FpM_mul(a,a, p), p); break;
    case 2: *z = F2m_to_mod(F2m_mul(a,a)); break;
    default:*z = Flm_to_mod(Flm_mul(a,a, pp), pp); break;
  }
  return 1;
}

GEN
RgM_mul(GEN x, GEN y)
{
  pari_sp av = avma;
  long j, l, lx, ly = lg(y);
  GEN z, ffx = NULL, ffy = NULL;
  if (ly == 1) return cgetg(1,t_MAT);
  lx = lg(x);
  if (lx != lgcols(y)) pari_err_OP("operation 'RgM_mul'", x,y);
  if (lx == 1) return zeromat(0,ly-1);
  if (is_modular_mul(x,y,&z)) return gerepileupto(av, z);
  if (RgM_is_FFM(x, &ffx) && RgM_is_FFM(y, &ffy)) {
    if (!FF_samefield(ffx, ffy))
      pari_err_OP("*", ffx, ffy);
    return FFM_mul(x, y, ffx);
  }
  z = cgetg(ly, t_MAT);
  l = lgcols(x);
  for (j=1; j<ly; j++) gel(z,j) = RgM_RgC_mul_i(x, gel(y,j), lx, l);
  return z;
}
/* assume result is symmetric */
GEN
RgM_multosym(GEN x, GEN y)
{
  long j, lx, ly = lg(y);
  GEN M;
  if (ly == 1) return cgetg(1,t_MAT);
  lx = lg(x);
  if (lx != lgcols(y)) pari_err_OP("operation 'RgM_multosym'", x,y);
  if (lx == 1) return cgetg(1,t_MAT);
  if (ly != lgcols(x)) pari_err_OP("operation 'RgM_multosym'", x,y);
  M = cgetg(ly, t_MAT);
  for (j=1; j<ly; j++)
  {
    GEN z = cgetg(ly,t_COL), yj = gel(y,j);
    long i;
    for (i=1; i<j; i++) gel(z,i) = gcoeff(M,j,i);
    for (i=j; i<ly; i++)gel(z,i) = RgMrow_RgC_mul_i(x,yj,i,lx);
    gel(M,j) = z;
  }
  return M;
}
/* x~ * y, assuming result is symmetric */
GEN
RgM_transmultosym(GEN x, GEN y)
{
  long i, j, l, ly = lg(y);
  GEN M;
  if (ly == 1) return cgetg(1,t_MAT);
  if (lg(x) != ly) pari_err_OP("operation 'RgM_transmultosym'", x,y);
  l = lgcols(y);
  if (lgcols(x) != l) pari_err_OP("operation 'RgM_transmultosym'", x,y);
  M = cgetg(ly, t_MAT);
  for (i=1; i<ly; i++)
  {
    GEN xi = gel(x,i), c = cgetg(ly,t_COL);
    gel(M,i) = c;
    for (j=1; j<i; j++)
      gcoeff(M,i,j) = gel(c,j) = RgV_dotproduct_i(xi,gel(y,j),l);
    gel(c,i) = RgV_dotproduct_i(xi,gel(y,i),l);
  }
  return M;
}
/* x~ * y */
GEN
RgM_transmul(GEN x, GEN y)
{
  long i, j, l, lx, ly = lg(y);
  GEN M;
  if (ly == 1) return cgetg(1,t_MAT);
  lx = lg(x);
  l = lgcols(y);
  if (lgcols(x) != l) pari_err_OP("operation 'RgM_transmul'", x,y);
  M = cgetg(ly, t_MAT);
  for (i=1; i<ly; i++)
  {
    GEN yi = gel(y,i), c = cgetg(lx,t_COL);
    gel(M,i) = c;
    for (j=1; j<lx; j++) gel(c,j) = RgV_dotproduct_i(yi,gel(x,j),l);
  }
  return M;
}

GEN
gram_matrix(GEN x)
{
  long i,j, l, lx = lg(x);
  GEN M;
  if (!is_matvec_t(typ(x))) pari_err_TYPE("gram",x);
  if (lx == 1) return cgetg(1,t_MAT);
  l = lgcols(x);
  M = cgetg(lx,t_MAT);
  for (i=1; i<lx; i++)
  {
    GEN xi = gel(x,i), c = cgetg(lx,t_COL);
    gel(M,i) = c;
    for (j=1; j<i; j++)
      gcoeff(M,i,j) = gel(c,j) = RgV_dotproduct_i(xi,gel(x,j),l);
    gel(c,i) = RgV_dotsquare(xi);
  }
  return M;
}

GEN
RgM_sqr(GEN x)
{
  pari_sp av = avma;
  long j, lx = lg(x);
  GEN z;
  if (lx == 1) return cgetg(1, t_MAT);
  if (lx != lgcols(x)) pari_err_OP("operation 'RgM_mul'", x,x);
  if (is_modular_sqr(x,&z)) return gerepileupto(av, z);
  z = cgetg(lx, t_MAT);
  for (j=1; j<lx; j++) gel(z,j) = RgM_RgC_mul_i(x, gel(x,j), lx, lx);
  return z;
}

static GEN
_RgM_add(void *E, GEN x, GEN y) { (void)E; return RgM_add(x, y); }

static GEN
_RgM_cmul(void *E, GEN P, long a, GEN x) { (void)E; return RgM_Rg_mul(x,gel(P,a+2)); }

static GEN
_RgM_sqr(void *E, GEN x) { (void) E; return RgM_sqr(x); }

static GEN
_RgM_mul(void *E, GEN x, GEN y) { (void) E; return RgM_mul(x, y); }

static GEN
_RgM_one(void *E) { long *n = (long*) E; return matid(*n); }

static GEN
_RgM_zero(void *E) { long *n = (long*) E; return zeromat(*n,*n); }

static GEN
_RgM_red(void *E, GEN x) { (void)E; return x; }

static struct bb_algebra RgM_algebra = { _RgM_red,_RgM_add,_RgM_mul,_RgM_sqr,_RgM_one,_RgM_zero };

/* generates the list of powers of x of degree 0,1,2,...,l*/
GEN
RgM_powers(GEN x, long l)
{
  long n = lg(x)-1;
  return gen_powers(x,l,1,(void *) &n, &_RgM_sqr, &_RgM_mul, &_RgM_one);
}

GEN
RgX_RgMV_eval(GEN Q, GEN x)
{
  long n = lg(x)>1 ? lg(gel(x,1))-1:0;
  return gen_bkeval_powers(Q,degpol(Q),x,(void*)&n,&RgM_algebra,&_RgM_cmul);
}

GEN
RgX_RgM_eval(GEN Q, GEN x)
{
  long n = lg(x)-1;
  return gen_bkeval(Q,degpol(Q),x,1,(void*)&n,&RgM_algebra,&_RgM_cmul);
}

GEN
RgC_Rg_div(GEN x, GEN y) {
  long i, lx = lg(x);
  GEN z = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) gel(z,i) = gdiv(gel(x,i),y);
  return z;
}
GEN
RgC_Rg_mul(GEN x, GEN y) {
  long i, lx = lg(x);
  GEN z = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) gel(z,i) = gmul(gel(x,i),y);
  return z;
}
GEN
RgV_Rg_mul(GEN x, GEN y) {
  long i, lx = lg(x);
  GEN z = cgetg(lx, t_VEC);
  for (i=1; i<lx; i++) gel(z,i) = gmul(gel(x,i),y);
  return z;
}
GEN
RgM_Rg_div(GEN X, GEN c) {
  long i, j, h, l = lg(X);
  GEN A = cgetg(l, t_MAT);
  if (l == 1) return A;
  h = lgcols(X);
  for (j=1; j<l; j++)
  {
    GEN a = cgetg(h, t_COL), x = gel(X, j);
    for (i = 1; i < h; i++) gel(a,i) = gdiv(gel(x,i), c);
    gel(A,j) = a;
  }
  return A;
}
GEN
RgM_Rg_mul(GEN X, GEN c) {
  long i, j, h, l = lg(X);
  GEN A = cgetg(l, t_MAT);
  if (l == 1) return A;
  h = lgcols(X);
  for (j=1; j<l; j++)
  {
    GEN a = cgetg(h, t_COL), x = gel(X, j);
    for (i = 1; i < h; i++) gel(a,i) = gmul(gel(x,i), c);
    gel(A,j) = a;
  }
  return A;
}

/********************************************************************/
/*                                                                  */
/*                    SCALAR TO MATRIX/VECTOR                       */
/*                                                                  */
/********************************************************************/
/* fill the square nxn matrix equal to t*Id */
static void
fill_scalmat(GEN y, GEN t, long n)
{
  long i;
  for (i = 1; i <= n; i++)
  {
    gel(y,i) = zerocol(n);
    gcoeff(y,i,i) = t;
  }
}

GEN
scalarmat(GEN x, long n) {
  GEN y = cgetg(n+1, t_MAT);
  if (!n) return y;
  fill_scalmat(y, gcopy(x), n); return y;
}
GEN
scalarmat_shallow(GEN x, long n) {
  GEN y = cgetg(n+1, t_MAT);
  fill_scalmat(y, x, n); return y;
}
GEN
scalarmat_s(long x, long n) {
  GEN y = cgetg(n+1, t_MAT);
  if (!n) return y;
  fill_scalmat(y, stoi(x), n); return y;
}
GEN
matid(long n) {
  GEN y;
  if (n < 0) pari_err_DOMAIN("matid", "size", "<", gen_0, stoi(n));
  y = cgetg(n+1, t_MAT);
  fill_scalmat(y, gen_1, n); return y;
}

INLINE GEN
scalarcol_i(GEN x, long n, long c)
{
  long i;
  GEN y = cgetg(n+1,t_COL);
  if (!n) return y;
  gel(y,1) = c? gcopy(x): x;
  for (i=2; i<=n; i++) gel(y,i) = gen_0;
  return y;
}

GEN
scalarcol(GEN x, long n) { return scalarcol_i(x,n,1); }

GEN
scalarcol_shallow(GEN x, long n) { return scalarcol_i(x,n,0); }

int
RgM_isscalar(GEN x, GEN s)
{
  long i, j, lx = lg(x);

  if (lx == 1) return 1;
  if (lx != lgcols(x)) return 0;
  if (!s) s = gcoeff(x,1,1);

  for (j=1; j<lx; j++)
  {
    GEN c = gel(x,j);
    for (i=1; i<j; )
      if (!gequal0(gel(c,i++))) return 0;
    /* i = j */
      if (!gequal(gel(c,i++),s)) return 0;
    for (   ; i<lx; )
      if (!gequal0(gel(c,i++))) return 0;
  }
  return 1;
}

int
RgM_isidentity(GEN x)
{
  long i,j, lx = lg(x);

  if (lx == 1) return 1;
  if (lx != lgcols(x)) return 0;
  for (j=1; j<lx; j++)
  {
    GEN c = gel(x,j);
    for (i=1; i<j; )
      if (!gequal0(gel(c,i++))) return 0;
    /* i = j */
      if (!gequal1(gel(c,i++))) return 0;
    for (   ; i<lx; )
      if (!gequal0(gel(c,i++))) return 0;
  }
  return 1;
}

int
RgM_isdiagonal(GEN x)
{
  long i,j, lx = lg(x);
  if (lx == 1) return 1;
  if (lx != lgcols(x)) return 0;

  for (j=1; j<lx; j++)
  {
    GEN c = gel(x,j);
    for (i=1; i<j; i++)
      if (!gequal0(gel(c,i))) return 0;
    for (i++; i<lx; i++)
      if (!gequal0(gel(c,i))) return 0;
  }
  return 1;
}
int
isdiagonal(GEN x)
{
  return (typ(x)==t_MAT) && RgM_isdiagonal(x);
}

/* returns the first index i<=n such that x=v[i] if it exists, 0 otherwise */
long
RgV_isin(GEN v, GEN x)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++)
    if (gequal(gel(v,i), x)) return i;
  return 0;
}

GEN
RgM_det_triangular(GEN mat)
{
  long i,l = lg(mat);
  pari_sp av;
  GEN s;

  if (l<3) return l<2? gen_1: gcopy(gcoeff(mat,1,1));
  av = avma; s = gcoeff(mat,1,1);
  for (i=2; i<l; i++) s = gmul(s,gcoeff(mat,i,i));
  return av==avma? gcopy(s): gerepileupto(av,s);
}

