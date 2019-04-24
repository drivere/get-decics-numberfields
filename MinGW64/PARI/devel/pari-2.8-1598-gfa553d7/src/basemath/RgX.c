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

/*******************************************************************/
/*                                                                 */
/*                         GENERIC                                 */
/*                                                                 */
/*******************************************************************/

/* Return optimal parameter l for the evaluation of n/m polynomials of degree d
   Fractional values can be used if the evaluations are done with different
   accuracies, and thus have different weights.
 */
long
brent_kung_optpow(long d, long n, long m)
{
  long p, r;
  long pold=1, rold=n*(d-1);
  for(p=2; p<=d; p++)
  {
    r = m*(p-1) + n*((d-1)/p);
    if (r<rold) { pold=p; rold=r; }
  }
  return pold;
}

static GEN
gen_RgXQ_eval_powers(GEN P, GEN V, long a, long n, void *E, const struct bb_algebra *ff,
                                           GEN cmul(void *E, GEN P, long a, GEN x))
{
  pari_sp av = avma;
  long i;
  GEN z = cmul(E,P,a,ff->one(E));
  for (i=1; i<=n; i++)
  {
    z = ff->add(E, z, cmul(E,P,a+i,gel(V,i+1)));
    if (gc_needed(av,2))
      z = gerepileupto(av, z);
  }
  return ff->red(E,z);
}

/* Brent & Kung
 * (Fast algorithms for manipulating formal power series, JACM 25:581-595, 1978)
 *
 * V as output by FpXQ_powers(x,l,T,p). For optimal performance, l is as given
 * by brent_kung_optpow */
GEN
gen_bkeval_powers(GEN P, long d, GEN V, void *E, const struct bb_algebra *ff,
                                     GEN cmul(void *E, GEN P, long a, GEN x))
{
  pari_sp av = avma;
  long l = lg(V)-1;
  GEN z, u;

  if (d < 0) return ff->zero(E);
  if (d < l) return gerepileupto(av, gen_RgXQ_eval_powers(P,V,0,d,E,ff,cmul));
  if (l<2) pari_err_DOMAIN("gen_RgX_bkeval_powers", "#powers", "<",gen_2,V);
  d -= l;
  z = gen_RgXQ_eval_powers(P,V,d+1,l-1,E,ff,cmul);
  while (d >= l-1)
  {
    d -= l-1;
    u = gen_RgXQ_eval_powers(P,V,d+1,l-2,E,ff,cmul);
    z = ff->add(E,u, ff->mul(E,z,gel(V,l)));
    if (gc_needed(av,2))
      z = gerepileupto(av, z);
  }
  u = gen_RgXQ_eval_powers(P,V,0,d,E,ff,cmul);
  z = ff->add(E,u, ff->mul(E,z,gel(V,d+2)));
  if (DEBUGLEVEL>=8)
  {
    long cnt = 1 + (d - l) / (l-1);
    err_printf("RgX_RgXQV_eval: %ld RgXQ_mul [%ld]\n", cnt, l-1);
  }
  return gerepileupto(av, ff->red(E,z));
}

GEN
gen_bkeval(GEN Q, long d, GEN x, int use_sqr, void *E, const struct bb_algebra *ff,
                                      GEN cmul(void *E, GEN P, long a, GEN x))
{
  pari_sp av = avma;
  GEN z, V;
  long rtd;
  if (d < 0) return ff->zero(E);
  rtd = (long) sqrt((double)d);
  V = gen_powers(x,rtd,use_sqr,E,ff->sqr,ff->mul,ff->one);
  z = gen_bkeval_powers(Q, d, V, E, ff, cmul);
  return gerepileupto(av, z);
}

static GEN
_gen_nored(void *E, GEN x) { (void)E; return x; }
static GEN
_gen_add(void *E, GEN x, GEN y) { (void)E; return gadd(x, y); }
static GEN
_gen_mul(void *E, GEN x, GEN y) { (void)E; return gmul(x, y); }
static GEN
_gen_sqr(void *E, GEN x) { (void)E; return gsqr(x); }
static GEN
_gen_one(void *E) { (void)E; return gen_1; }
static GEN
_gen_zero(void *E) { (void)E; return gen_0; }

static struct bb_algebra Rg_algebra = { _gen_nored,_gen_add,_gen_mul,_gen_sqr,
                                        _gen_one,_gen_zero };

static GEN
_gen_cmul(void *E, GEN P, long a, GEN x)
{(void)E; return gmul(gel(P,a+2), x);}

GEN
RgX_RgV_eval(GEN Q, GEN x)
{
  return gen_bkeval_powers(Q, degpol(Q), x, NULL, &Rg_algebra, _gen_cmul);
}

GEN
RgX_Rg_eval_bk(GEN Q, GEN x)
{
  return gen_bkeval(Q, degpol(Q), x, 1, NULL, &Rg_algebra, _gen_cmul);
}

/*******************************************************************/
/*                                                                 */
/*                         RgX                                     */
/*                                                                 */
/*******************************************************************/

long
RgX_equal(GEN x, GEN y)
{
  long i = lg(x);

  if (i != lg(y)) return 0;
  for (i--; i > 1; i--)
    if (!gequal(gel(x,i),gel(y,i))) return 0;
  return 1;
}

/* Returns 1 in the base ring over which x is defined */
/* HACK: this also works for t_SER */
GEN
RgX_get_1(GEN x)
{
  GEN p, T;
  long i, lx, tx = RgX_type(x, &p, &T, &lx);
  if (RgX_type_is_composite(tx))
    RgX_type_decode(tx, &i /*junk*/, &tx);
  switch(tx)
  {
    case t_INTMOD: retmkintmod(gen_1, icopy(p));
    case t_PADIC: return cvtop(gen_1, p, lx);
    case t_FFELT: return FF_1(T);
    default: return gen_1;
  }
}
/* Returns 0 in the base ring over which x is defined */
/* HACK: this also works for t_SER */
GEN
RgX_get_0(GEN x)
{
  GEN p, T;
  long i, lx, tx = RgX_type(x, &p, &T, &lx);
  if (RgX_type_is_composite(tx))
    RgX_type_decode(tx, &i /*junk*/, &tx);
  switch(tx)
  {
    case t_INTMOD: retmkintmod(gen_0, icopy(p));
    case t_PADIC: return cvtop(gen_0, p, lx);
    case t_FFELT: return FF_zero(T);
    default: return gen_0;
  }
}

GEN
QX_ZXQV_eval(GEN P, GEN V, GEN dV)
{
  long i, n = degpol(P);
  GEN z, dz, dP;
  if (n < 0) return gen_0;
  P = Q_remove_denom(P, &dP);
  z = gel(P,2); if (n == 0) return icopy(z);
  if (dV) z = mulii(dV, z); /* V[1] = dV */
  z = ZX_Z_add_shallow(ZX_Z_mul(gel(V,2),gel(P,3)), z);
  for (i=2; i<=n; i++) z = ZX_add(ZX_Z_mul(gel(V,i+1),gel(P,2+i)), z);
  dz = mul_denom(dP, dV);
  return dz? RgX_Rg_div(z, dz): z;
}

/* Return P(h * x), not memory clean */
GEN
RgX_unscale(GEN P, GEN h)
{
  long i, l = lg(P);
  GEN hi = gen_1, Q = cgetg(l, t_POL);
  Q[1] = P[1];
  if (l == 2) return Q;
  gel(Q,2) = gcopy(gel(P,2));
  for (i=3; i<l; i++)
  {
    hi = gmul(hi,h);
    gel(Q,i) = gmul(gel(P,i), hi);
  }
  return Q;
}
/* P a ZX, h a t_INT. Return P(h * x), not memory clean; optimize for h = -1 */
GEN
ZX_unscale(GEN P, GEN h)
{
  long i, l = lg(P);
  GEN Q = cgetg(l, t_POL);
  Q[1] = P[1];
  if (l == 2) return Q;
  gel(Q,2) = gel(P,2);
  if (l == 3) return Q;
  if (equalim1(h))
    for (i=3; i<l; i++)
    {
      gel(Q,i) = negi(gel(P,i));
      if (++i == l) break;
      gel(Q,i) = gel(P,i);
    }
  else
  {
    GEN hi = h;
    gel(Q,3) = mulii(gel(P,3), hi);
    for (i=4; i<l; i++)
    {
      hi = mulii(hi,h);
      gel(Q,i) = mulii(gel(P,i), hi);
    }
  }
  return Q;
}
/* P a ZX. Return P(x << n), not memory clean */
GEN
ZX_unscale2n(GEN P, long n)
{
  long i, ni = n, l = lg(P);
  GEN Q = cgetg(l, t_POL);
  Q[1] = P[1];
  if (l == 2) return Q;
  gel(Q,2) = gel(P,2);
  if (l == 3) return Q;
  gel(Q,3) = shifti(gel(P,3), ni);
  for (i=4; i<l; i++)
  {
    ni += n;
    gel(Q,i) = shifti(gel(P,i), ni);
  }
  return Q;
}
/* P(h*X) / h, assuming h | P(0), i.e. the result is a ZX */
GEN
ZX_unscale_div(GEN P, GEN h)
{
  long i, l = lg(P);
  GEN hi, Q = cgetg(l, t_POL);
  Q[1] = P[1];
  if (l == 2) return Q;
  gel(Q,2) = diviiexact(gel(P,2), h);
  if (l == 3) return Q;
  gel(Q,3) = gel(P,3);
  if (l == 4) return Q;
  hi = h;
  gel(Q,4) = mulii(gel(P,4), hi);
  for (i=5; i<l; i++)
  {
    hi = mulii(hi,h);
    gel(Q,i) = mulii(gel(P,i), hi);
  }
  return Q;
}

GEN
RgXV_unscale(GEN v, GEN h)
{
  long i, l;
  GEN w;
  if (!h || isint1(h)) return v;
  w = cgetg_copy(v, &l);
  for (i=1; i<l; i++) gel(w,i) = RgX_unscale(gel(v,i), h);
  return w;
}

/* Return h^degpol(P) P(x / h), not memory clean */
GEN
RgX_rescale(GEN P, GEN h)
{
  long i, l = lg(P);
  GEN Q = cgetg(l,t_POL), hi = h;
  Q[l-1] = P[l-1];
  for (i=l-2; i>=2; i--)
  {
    gel(Q,i) = gmul(gel(P,i), hi);
    if (i == 2) break;
    hi = gmul(hi,h);
  }
  Q[1] = P[1]; return Q;
}

/* A(X^d) --> A(X) */
GEN
RgX_deflate(GEN x0, long d)
{
  GEN z, y, x;
  long i,id, dy, dx = degpol(x0);
  if (d == 1 || dx <= 0) return leafcopy(x0);
  dy = dx/d;
  y = cgetg(dy+3, t_POL); y[1] = x0[1];
  z = y + 2;
  x = x0+ 2;
  for (i=id=0; i<=dy; i++,id+=d) gel(z,i) = gel(x,id);
  return y;
}

/* return x0(X^d) */
GEN
RgX_inflate(GEN x0, long d)
{
  long i, id, dy, dx = degpol(x0);
  GEN x = x0 + 2, z, y;
  if (dx <= 0) return leafcopy(x0);
  dy = dx*d;
  y = cgetg(dy+3, t_POL); y[1] = x0[1];
  z = y + 2;
  for (i=0; i<=dy; i++) gel(z,i) = gen_0;
  for (i=id=0; i<=dx; i++,id+=d) gel(z,id) = gel(x,i);
  return y;
}

/* return P(X + c) using destructive Horner, optimize for c = 1,-1 */
GEN
RgX_translate(GEN P, GEN c)
{
  pari_sp av = avma;
  GEN Q, *R;
  long i, k, n;

  if (!signe(P) || gequal0(c)) return RgX_copy(P);
  Q = leafcopy(P);
  R = (GEN*)(Q+2); n = degpol(P);
  if (gequal1(c))
  {
    for (i=1; i<=n; i++)
    {
      for (k=n-i; k<n; k++) R[k] = gadd(R[k], R[k+1]);
      if (gc_needed(av,2))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"TR_POL(1), i = %ld/%ld", i,n);
        Q = gerepilecopy(av, Q); R = (GEN*)Q+2;
      }
    }
  }
  else if (gequalm1(c))
  {
    for (i=1; i<=n; i++)
    {
      for (k=n-i; k<n; k++) R[k] = gsub(R[k], R[k+1]);
      if (gc_needed(av,2))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"TR_POL(-1), i = %ld/%ld", i,n);
        Q = gerepilecopy(av, Q); R = (GEN*)Q+2;
      }
    }
  }
  else
  {
    for (i=1; i<=n; i++)
    {
      for (k=n-i; k<n; k++) R[k] = gadd(R[k], gmul(c, R[k+1]));
      if (gc_needed(av,2))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"TR_POL, i = %ld/%ld", i,n);
        Q = gerepilecopy(av, Q); R = (GEN*)Q+2;
      }
    }
  }
  return gerepilecopy(av, Q);
}

/* return P(X + c) using destructive Horner, optimize for c = 1,-1 */
GEN
ZX_translate(GEN P, GEN c)
{
  pari_sp av = avma;
  GEN Q, *R;
  long i, k, n;

  if (!signe(P) || !signe(c)) return ZX_copy(P);
  Q = leafcopy(P);
  R = (GEN*)(Q+2); n = degpol(P);
  if (equali1(c))
  {
    for (i=1; i<=n; i++)
    {
      for (k=n-i; k<n; k++) R[k] = addii(R[k], R[k+1]);
      if (gc_needed(av,2))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"ZX_translate(1), i = %ld/%ld", i,n);
        Q = gerepilecopy(av, Q); R = (GEN*)Q+2;
      }
    }
  }
  else if (equalim1(c))
  {
    for (i=1; i<=n; i++)
    {
      for (k=n-i; k<n; k++) R[k] = subii(R[k], R[k+1]);
      if (gc_needed(av,2))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"ZX_translate(-1), i = %ld/%ld", i,n);
        Q = gerepilecopy(av, Q); R = (GEN*)Q+2;
      }
    }
  }
  else
  {
    for (i=1; i<=n; i++)
    {
      for (k=n-i; k<n; k++) R[k] = addii(R[k], mulii(c, R[k+1]));
      if (gc_needed(av,2))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"ZX_translate, i = %ld/%ld", i,n);
        Q = gerepilecopy(av, Q); R = (GEN*)Q+2;
      }
    }
  }
  return gerepilecopy(av, Q);
}
/* return lift( P(X + c) ) using Horner, c in R[y]/(T) */
GEN
RgXQX_translate(GEN P, GEN c, GEN T)
{
  pari_sp av = avma;
  GEN Q, *R;
  long i, k, n;

  if (!signe(P) || gequal0(c)) return RgX_copy(P);
  Q = leafcopy(P);
  R = (GEN*)(Q+2); n = degpol(P);
  for (i=1; i<=n; i++)
  {
    for (k=n-i; k<n; k++)
    {
      pari_sp av2 = avma;
      R[k] = gerepileupto(av2, RgX_rem(gadd(R[k], gmul(c, R[k+1])), T));
    }
    if (gc_needed(av,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgXQX_translate, i = %ld/%ld", i,n);
      Q = gerepilecopy(av, Q); R = (GEN*)Q+2;
    }
  }
  return gerepilecopy(av, Q);
}

/********************************************************************/
/**                                                                **/
/**                          CONVERSIONS                           **/
/**                       (not memory clean)                       **/
/**                                                                **/
/********************************************************************/
/* to INT / FRAC / (POLMOD mod T), not memory clean because T not copied,
 * but everything else is */
static GEN
QXQ_to_mod_copy(GEN x, GEN T)
{
  long d;
  switch(typ(x))
  {
    case t_INT:  return icopy(x);
    case t_FRAC: return gcopy(x);
    case t_POL:
      d = degpol(x);
      if (d < 0) return gen_0;
      if (d == 0) return gcopy(gel(x,2));
      return mkpolmod(RgX_copy(x), T);
    default: pari_err_TYPE("QXQ_to_mod",x);
             return NULL;/* not reached */
  }
}
/* pure shallow version */
static GEN
QXQ_to_mod(GEN x, GEN T)
{
  long d;
  switch(typ(x))
  {
    case t_INT:
    case t_FRAC: return x;
    case t_POL:
      d = degpol(x);
      if (d < 0) return gen_0;
      if (d == 0) return gel(x,2);
      return mkpolmod(x, T);
    default: pari_err_TYPE("QXQ_to_mod",x);
             return NULL;/* not reached */
  }
}
/* T a ZX, z lifted from (Q[Y]/(T(Y)))[X], apply QXQ_to_mod_copy to all coeffs.
 * Not memory clean because T not copied, but everything else is */
static GEN
QXQX_to_mod(GEN z, GEN T)
{
  long i,l = lg(z);
  GEN x = cgetg(l,t_POL);
  for (i=2; i<l; i++) gel(x,i) = QXQ_to_mod_copy(gel(z,i), T);
  x[1] = z[1]; return normalizepol_lg(x,l);
}
/* pure shallow version */
GEN
QXQX_to_mod_shallow(GEN z, GEN T)
{
  long i,l = lg(z);
  GEN x = cgetg(l,t_POL);
  for (i=2; i<l; i++) gel(x,i) = QXQ_to_mod(gel(z,i), T);
  x[1] = z[1]; return normalizepol_lg(x,l);
}
/* Apply QXQX_to_mod to all entries. Memory-clean ! */
GEN
QXQXV_to_mod(GEN V, GEN T)
{
  long i, l = lg(V);
  GEN z = cgetg(l, t_VEC); T = ZX_copy(T);
  for (i=1;i<l; i++) gel(z,i) = QXQX_to_mod(gel(V,i), T);
  return z;
}
/* Apply QXQ_to_mod_copy to all entries. Memory-clean ! */
GEN
QXQV_to_mod(GEN V, GEN T)
{
  long i, l = lg(V);
  GEN z = cgetg(l, t_VEC); T = ZX_copy(T);
  for (i=1;i<l; i++) gel(z,i) = QXQ_to_mod_copy(gel(V,i), T);
  return z;
}

GEN
RgX_renormalize_lg(GEN x, long lx)
{
  long i;
  for (i = lx-1; i>1; i--)
    if (! gequal0(gel(x,i))) break; /* _not_ isexactzero */
  stackdummy((pari_sp)(x + lg(x)), (pari_sp)(x + i+1));
  setlg(x, i+1); setsigne(x, i != 1); return x;
}

GEN
RgV_to_RgX(GEN x, long v)
{
  long i, k = lg(x);
  GEN p;

  while (--k && gequal0(gel(x,k)));
  if (!k) return pol_0(v);
  i = k+2; p = cgetg(i,t_POL);
  p[1] = evalsigne(1) | evalvarn(v);
  x--; for (k=2; k<i; k++) gel(p,k) = gel(x,k);
  return p;
}
GEN
RgV_to_RgX_reverse(GEN x, long v)
{
  long j, k, l = lg(x);
  GEN p;

  for (k = 2; k < l; k++)
    if (!gequal0(gel(x,k))) break;
  if (k == l) return pol_0(v);
  k -= 2;
  l -= k;
  x += k;
  p = cgetg(l+1,t_POL);
  p[1] = evalsigne(1) | evalvarn(v);
  for (j=2, k=l; j<=l; j++) gel(p,j) = gel(x,--k);
  return p;
}

/* return the (N-dimensional) vector of coeffs of p */
GEN
RgX_to_RgC(GEN x, long N)
{
  long i, l;
  GEN z;
  l = lg(x)-1; x++;
  if (l > N+1) l = N+1; /* truncate higher degree terms */
  z = cgetg(N+1,t_COL);
  for (i=1; i<l ; i++) gel(z,i) = gel(x,i);
  for (   ; i<=N; i++) gel(z,i) = gen_0;
  return z;
}
GEN
Rg_to_RgC(GEN x, long N)
{
  return (typ(x) == t_POL)? RgX_to_RgC(x,N): scalarcol_shallow(x, N);
}

/* vector of polynomials (in v) whose coeffs are given by the columns of x */
GEN
RgM_to_RgXV(GEN x, long v)
{
  long j, lx = lg(x);
  GEN y = cgetg(lx, t_VEC);
  for (j=1; j<lx; j++) gel(y,j) = RgV_to_RgX(gel(x,j), v);
  return y;
}

/* matrix whose entries are given by the coeffs of the polynomials in
 * vector v (considered as degree n-1 polynomials) */
GEN
RgV_to_RgM(GEN v, long n)
{
  long j, N = lg(v);
  GEN y = cgetg(N, t_MAT);
  for (j=1; j<N; j++) gel(y,j) = Rg_to_RgC(gel(v,j), n);
  return y;
}
GEN
RgXV_to_RgM(GEN v, long n)
{
  long j, N = lg(v);
  GEN y = cgetg(N, t_MAT);
  for (j=1; j<N; j++) gel(y,j) = RgX_to_RgC(gel(v,j), n);
  return y;
}

/* polynomial (in v) of polynomials (in w) whose coeffs are given by the columns of x */
GEN
RgM_to_RgXX(GEN x, long v,long w)
{
  long j, lx = lg(x);
  GEN y = cgetg(lx+1, t_POL);
  y[1] = evalsigne(1) | evalvarn(v);
  y++;
  for (j=1; j<lx; j++) gel(y,j) = RgV_to_RgX(gel(x,j), w);
  return normalizepol_lg(--y, lx+1);
}

/* matrix whose entries are given by the coeffs of the polynomial v in
 * two variables (considered as degree n-1 polynomials) */
GEN
RgXX_to_RgM(GEN v, long n)
{
  long j, N = lg(v)-1;
  GEN y = cgetg(N, t_MAT);
  for (j=1; j<N; j++) gel(y,j) = Rg_to_RgC(gel(v,j+1), n);
  return y;
}

/* P(X,Y) --> P(Y,X), n is an upper bound for deg_Y(P) */
GEN
RgXY_swapspec(GEN x, long n, long w, long nx)
{
  long j, ly = n+3;
  GEN y = cgetg(ly, t_POL);
  y[1] = evalsigne(1);
  for (j=2; j<ly; j++)
  {
    long k;
    GEN a = cgetg(nx+2,t_POL);
    a[1] = evalsigne(1) | evalvarn(w);
    for (k=0; k<nx; k++)
    {
      GEN xk = gel(x,k);
      if (typ(xk)==t_POL)
        gel(a,k+2) = j<lg(xk)? gel(xk,j): gen_0;
      else
        gel(a,k+2) = j==2 ? xk: gen_0;
    }
    gel(y,j) = normalizepol_lg(a, nx+2);
  }
  return normalizepol_lg(y,ly);
}

/* P(X,Y) --> P(Y,X), n is an upper bound for deg_Y(P) */
GEN
RgXY_swap(GEN x, long n, long w)
{
  GEN z = RgXY_swapspec(x+2, n, w, lgpol(x));
  setvarn(z, varn(x)); return z;
}

long
RgXY_degreex(GEN bpol)
{
  long deg = 0, i;
  if (!signe(bpol)) return -1;
  for (i = 2; i < lg(bpol); ++i)
    deg = maxss(deg, degpol(gel(bpol, i)));
  return deg;
}

/* return (x % X^n). Shallow */
GEN
RgXn_red_shallow(GEN a, long n)
{
  long i, L, l = lg(a);
  GEN  b;
  if (l == 2 || !n) return pol_0(varn(a));
  L = n+2; if (L > l) L = l;
  b = cgetg(L, t_POL); b[1] = a[1];
  for (i=2; i<L; i++) gel(b,i) = gel(a,i);
  return normalizepol_lg(b,L);
}

GEN
RgXnV_red_shallow(GEN P, long n)
{
  long i, l = lg(P);
  GEN Q = cgetg(l, t_VEC);
  for (i=1; i<l; i++) gel(Q,i) = RgXn_red_shallow(gel(P,i), n);
  return Q;
}

/* return (x * X^n). Shallow */
GEN
RgX_shift_shallow(GEN a, long n)
{
  long i, l = lg(a);
  GEN  b;
  if (l == 2 || !n) return a;
  l += n;
  if (n < 0)
  {
    if (l <= 2) return pol_0(varn(a));
    b = cgetg(l, t_POL); b[1] = a[1];
    a -= n;
    for (i=2; i<l; i++) gel(b,i) = gel(a,i);
  } else {
    b = cgetg(l, t_POL); b[1] = a[1];
    a -= n; n += 2;
    for (i=2; i<n; i++) gel(b,i) = gen_0;
    for (   ; i<l; i++) gel(b,i) = gel(a,i);
  }
  return b;
}
/* return (x * X^n). */
GEN
RgX_shift(GEN a, long n)
{
  long i, l = lg(a);
  GEN  b;
  if (l == 2 || !n) return RgX_copy(a);
  l += n;
  if (n < 0)
  {
    if (l <= 2) return pol_0(varn(a));
    b = cgetg(l, t_POL); b[1] = a[1];
    a -= n;
    for (i=2; i<l; i++) gel(b,i) = gcopy(gel(a,i));
  } else {
    b = cgetg(l, t_POL); b[1] = a[1];
    a -= n; n += 2;
    for (i=2; i<n; i++) gel(b,i) = gen_0;
    for (   ; i<l; i++) gel(b,i) = gcopy(gel(a,i));
  }
  return b;
}

GEN
RgX_rotate_shallow(GEN P, long k, long p)
{
  long i, l = lgpol(P);
  GEN r;
  if (signe(P)==0)
    return pol_0(varn(P));
  r = cgetg(p+2,t_POL); r[1] = P[1];
  for(i=0; i<p; i++)
  {
    long s = 2+(i+k)%p;
    gel(r,s) = i<l? gel(P,2+i): gen_0;
  }
  return RgX_renormalize(r);
}

GEN
RgX_mulXn(GEN x, long d)
{
  pari_sp av;
  GEN z;
  long v;
  if (d >= 0) return RgX_shift(x, d);
  d = -d;
  v = RgX_val(x);
  if (v >= d) return RgX_shift(x, -d);
  av = avma;
  z = gred_rfrac_simple( RgX_shift_shallow(x, -v),
                         monomial(gen_1, d - v, varn(x)));
  return gerepileupto(av, z);
}

long
RgX_val(GEN x)
{
  long i, lx = lg(x);
  if (lx == 2) return LONG_MAX;
  for (i = 2; i < lx; i++)
    if (!isexactzero(gel(x,i))) break;
  if (i == lx) i--; /* possible with non-rational zeros */
  return i - 2;
}
long
RgX_valrem(GEN x, GEN *Z)
{
  long v, i, lx = lg(x);
  if (lx == 2) { *Z = pol_0(varn(x)); return LONG_MAX; }
  for (i = 2; i < lx; i++)
    if (!isexactzero(gel(x,i))) break;
  if (i == lx) i--; /* possible with non-rational zeros */
  v = i - 2;
  *Z = RgX_shift_shallow(x, -v);
  return v;
}
long
RgX_valrem_inexact(GEN x, GEN *Z)
{
  long v;
  if (!signe(x)) { if (Z) *Z = pol_0(varn(x)); return LONG_MAX; }
  for (v = 0;; v++)
    if (!gequal0(gel(x,2+v))) break;
  if (Z) *Z = RgX_shift_shallow(x, -v);
  return v;
}

GEN
RgXQC_red(GEN P, GEN T)
{
  long i, l = lg(P);
  GEN Q = cgetg(l, t_COL);
  for (i=1; i<l; i++) gel(Q,i) = grem(gel(P,i), T);
  return Q;
}

GEN
RgXQV_red(GEN P, GEN T)
{
  long i, l = lg(P);
  GEN Q = cgetg(l, t_VEC);
  for (i=1; i<l; i++) gel(Q,i) = grem(gel(P,i), T);
  return Q;
}

GEN
RgXQX_red(GEN P, GEN T)
{
  long i, l = lg(P);
  GEN Q = cgetg(l, t_POL);
  Q[1] = P[1];
  for (i=2; i<l; i++) gel(Q,i) = grem(gel(P,i), T);
  return normalizepol_lg(Q, l);
}

GEN
RgX_deriv(GEN x)
{
  long i,lx = lg(x)-1;
  GEN y;

  if (lx<3) return pol_0(varn(x));
  y = cgetg(lx,t_POL); gel(y,2) = gcopy(gel(x,3));
  for (i=3; i<lx ; i++) gel(y,i) = gmulsg(i-1,gel(x,i+1));
  y[1] = x[1]; return normalizepol_lg(y,i);
}

GEN
RgX_recipspec_shallow(GEN x, long l, long n)
{
  long i;
  GEN z=cgetg(n+2,t_POL)+2;
  for(i=0; i<l; i++)
    gel(z,n-i-1) = gel(x,i);
  for(   ; i<n; i++)
    gel(z, n-i-1) = gen_0;
  return normalizepol_lg(z-2,n+2);
}

/* return coefficients s.t x = x_0 X^n + ... + x_n */
GEN
RgX_recip(GEN x)
{
  long lx, i, j;
  GEN y = cgetg_copy(x, &lx);
  y[1] = x[1]; for (i=2,j=lx-1; i<lx; i++,j--) gel(y,i) = gcopy(gel(x,j));
  return normalizepol_lg(y,lx);
}
/* shallow version */
GEN
RgX_recip_shallow(GEN x)
{
  long lx, i, j;
  GEN y = cgetg_copy(x, &lx);
  y[1] = x[1]; for (i=2,j=lx-1; i<lx; i++,j--) gel(y,i) = gel(x,j);
  return y;
}
/*******************************************************************/
/*                                                                 */
/*                      ADDITION / SUBTRACTION                     */
/*                                                                 */
/*******************************************************************/
/* same variable */
GEN
RgX_add(GEN x, GEN y)
{
  long i, lx = lg(x), ly = lg(y);
  GEN z;
  if (ly <= lx) {
    z = cgetg(lx,t_POL); z[1] = x[1];
    for (i=2; i < ly; i++) gel(z,i) = gadd(gel(x,i),gel(y,i));
    for (   ; i < lx; i++) gel(z,i) = gcopy(gel(x,i));
    z = normalizepol_lg(z, lx);
  } else {
    z = cgetg(ly,t_POL); z[1] = y[1];
    for (i=2; i < lx; i++) gel(z,i) = gadd(gel(x,i),gel(y,i));
    for (   ; i < ly; i++) gel(z,i) = gcopy(gel(y,i));
    z = normalizepol_lg(z, ly);
  }
  return z;
}
GEN
RgX_sub(GEN x, GEN y)
{
  long i, lx = lg(x), ly = lg(y);
  GEN z;
  if (ly <= lx) {
    z = cgetg(lx,t_POL); z[1] = x[1];
    for (i=2; i < ly; i++) gel(z,i) = gsub(gel(x,i),gel(y,i));
    for (   ; i < lx; i++) gel(z,i) = gcopy(gel(x,i));
    z = normalizepol_lg(z, lx);
  } else {
    z = cgetg(ly,t_POL); z[1] = y[1];
    for (i=2; i < lx; i++) gel(z,i) = gsub(gel(x,i),gel(y,i));
    for (   ; i < ly; i++) gel(z,i) = gneg(gel(y,i));
    z = normalizepol_lg(z, ly);
  }
  return z;
}
GEN
RgX_neg(GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx, t_POL); y[1] = x[1];
  for (i=2; i<lx; i++) gel(y,i) = gneg(gel(x,i));
  return y;
}

GEN
RgX_Rg_add(GEN y, GEN x)
{
  GEN z;
  long lz = lg(y), i;
  if (lz == 2) return scalarpol(x,varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = gadd(gel(y,2),x);
  for(i=3; i<lz; i++) gel(z,i) = gcopy(gel(y,i));
  /* probably useless unless lz = 3, but cannot be skipped if y is
   * an inexact 0 */
  return normalizepol_lg(z,lz);
}
GEN
RgX_Rg_add_shallow(GEN y, GEN x)
{
  GEN z;
  long lz = lg(y), i;
  if (lz == 2) return scalarpol(x,varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = gadd(gel(y,2),x);
  for(i=3; i<lz; i++) gel(z,i) = gel(y,i);
  return z = normalizepol_lg(z,lz);
}
GEN
RgX_Rg_sub(GEN y, GEN x)
{
  GEN z;
  long lz = lg(y), i;
  if (lz == 2)
  { /* scalarpol(gneg(x),varn(y)) optimized */
    long v = varn(y);
    if (isrationalzero(x)) return pol_0(v);
    z = cgetg(3,t_POL);
    z[1] = gequal0(x)? evalvarn(v)
                   : evalvarn(v) | evalsigne(1);
    gel(z,2) = gneg(x); return z;
  }
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = gsub(gel(y,2),x);
  for(i=3; i<lz; i++) gel(z,i) = gcopy(gel(y,i));
  return z = normalizepol_lg(z,lz);
}
GEN
Rg_RgX_sub(GEN x, GEN y)
{
  GEN z;
  long lz = lg(y), i;
  if (lz == 2) return scalarpol(x,varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = gsub(x, gel(y,2));
  for(i=3; i<lz; i++) gel(z,i) = gneg(gel(y,i));
  return z = normalizepol_lg(z,lz);
}
/*******************************************************************/
/*                                                                 */
/*                  KARATSUBA MULTIPLICATION                       */
/*                                                                 */
/*******************************************************************/
#if 0
/* to debug Karatsuba-like routines */
GEN
zx_debug_spec(GEN x, long nx)
{
  GEN z = cgetg(nx+2,t_POL);
  long i;
  for (i=0; i<nx; i++) gel(z,i+2) = stoi(x[i]);
  z[1] = evalsigne(1); return z;
}

GEN
RgX_debug_spec(GEN x, long nx)
{
  GEN z = cgetg(nx+2,t_POL);
  long i;
  for (i=0; i<nx; i++) z[i+2] = x[i];
  z[1] = evalsigne(1); return z;
}
#endif

/* generic multiplication */

static GEN
addpol(GEN x, GEN y, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx+2; z = cgetg(lz,t_POL) + 2;
  for (i=0; i<ly; i++) gel(z,i) = gadd(gel(x,i),gel(y,i));
  for (   ; i<lx; i++) gel(z,i) = gel(x,i);
  z -= 2; z[1]=0; return normalizepol_lg(z, lz);
}

static GEN
addpolcopy(GEN x, GEN y, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx+2; z = cgetg(lz,t_POL) + 2;
  for (i=0; i<ly; i++) gel(z,i) = gadd(gel(x,i),gel(y,i));
  for (   ; i<lx; i++) gel(z,i) = gcopy(gel(x,i));
  z -= 2; z[1]=0; return normalizepol_lg(z, lz);
}

/* Return the vector of coefficients of x, where we replace rational 0s by NULL
 * [ to speed up basic operation s += x[i]*y[j] ]. We create a proper
 * t_VECSMALL, to hold this, which can be left on stack: gerepile
 * will not crash on it. The returned vector itself is not a proper GEN,
 * we access the coefficients as x[i], i = 0..deg(x) */
static GEN
RgXspec_kill0(GEN x, long lx)
{
  GEN z = cgetg(lx+1, t_VECSMALL) + 1; /* inhibit gerepile-wise */
  long i;
  for (i=0; i <lx; i++)
  {
    GEN c = gel(x,i);
    z[i] = (long)(isrationalzero(c)? NULL: c);
  }
  return z;
}

INLINE GEN
RgX_mulspec_basecase_limb(GEN x, GEN y, long a, long b)
{
  pari_sp av = avma;
  GEN s = NULL;
  long i;

  for (i=a; i<b; i++)
    if (gel(y,i) && gel(x,-i))
    {
      GEN t = gmul(gel(y,i), gel(x,-i));
      s = s? gadd(s, t): t;
    }
  return s? gerepileupto(av, s): gen_0;
}

/* assume nx >= ny > 0, return x * y * t^v */
static GEN
RgX_mulspec_basecase(GEN x, GEN y, long nx, long ny, long v)
{
  long i, lz, nz;
  GEN z;

  x = RgXspec_kill0(x,nx);
  y = RgXspec_kill0(y,ny);
  lz = nx + ny + 1; nz = lz-2;
  lz += v;
  z = cgetg(lz, t_POL) + 2; /* x:y:z [i] = term of degree i */
  for (i=0; i<v; i++) gel(z++, 0) = gen_0;
  for (i=0; i<ny; i++)gel(z,i) = RgX_mulspec_basecase_limb(x+i,y, 0, i+1);
  for (  ; i<nx; i++) gel(z,i) = RgX_mulspec_basecase_limb(x+i,y, 0,ny);
  for (  ; i<nz; i++) gel(z,i) = RgX_mulspec_basecase_limb(x+i,y, i-nx+1,ny);
  z -= v+2; z[1] = 0; return normalizepol_lg(z, lz);
}

/* return (x * X^d) + y. Assume d > 0 */
GEN
addmulXn(GEN x, GEN y, long d)
{
  GEN xd, yd, zd;
  long a, lz, nx, ny;

  if (!signe(x)) return y;
  ny = lgpol(y);
  nx = lgpol(x);
  zd = (GEN)avma;
  x += 2; y += 2; a = ny-d;
  if (a <= 0)
  {
    lz = nx+d+2;
    (void)new_chunk(lz); xd = x+nx; yd = y+ny;
    while (xd > x) gel(--zd,0) = gel(--xd,0);
    x = zd + a;
    while (zd > x) gel(--zd,0) = gen_0;
  }
  else
  {
    xd = new_chunk(d); yd = y+d;
    x = addpol(x,yd, nx,a);
    lz = (a>nx)? ny+2: lg(x)+d;
    x += 2; while (xd > x) *--zd = *--xd;
  }
  while (yd > y) *--zd = *--yd;
  *--zd = evalsigne(1);
  *--zd = evaltyp(t_POL) | evallg(lz); return zd;
}

GEN
addshiftpol(GEN x, GEN y, long d)
{
  long v = varn(x);
  x = addmulXn(x,y,d);
  setvarn(x,v); return x;
}

/* as above, producing a clean malloc */
static GEN
addmulXncopy(GEN x, GEN y, long d)
{
  GEN xd, yd, zd;
  long a, lz, nx, ny;

  if (!signe(x)) return RgX_copy(y);
  nx = lgpol(x);
  ny = lgpol(y);
  zd = (GEN)avma;
  x += 2; y += 2; a = ny-d;
  if (a <= 0)
  {
    lz = nx+d+2;
    (void)new_chunk(lz); xd = x+nx; yd = y+ny;
    while (xd > x) gel(--zd,0) = gcopy(gel(--xd,0));
    x = zd + a;
    while (zd > x) gel(--zd,0) = gen_0;
  }
  else
  {
    xd = new_chunk(d); yd = y+d;
    x = addpolcopy(x,yd, nx,a);
    lz = (a>nx)? ny+2: lg(x)+d;
    x += 2; while (xd > x) *--zd = *--xd;
  }
  while (yd > y) gel(--zd,0) = gcopy(gel(--yd,0));
  *--zd = evalsigne(1);
  *--zd = evaltyp(t_POL) | evallg(lz); return zd;
}

/* return x * y mod t^n */
static GEN
RgXn_mul_basecase(GEN x, GEN y, long n)
{
  long i, lz = n+2, lx = lgpol(x), ly = lgpol(y);
  GEN z;
  if (lx < 0) return pol_0(varn(x));
  if (ly < 0) return pol_0(varn(x));
  z = cgetg(lz, t_POL) + 2;
  x+=2; if (lx > n) lx = n;
  y+=2; if (ly > n) ly = n;
  z[-1] = x[-1];
  if (ly > lx) { swap(x,y); lswap(lx,ly); }
  x = RgXspec_kill0(x, lx);
  y = RgXspec_kill0(y, ly);
  /* x:y:z [i] = term of degree i */
  for (i=0;i<ly; i++) gel(z,i) = RgX_mulspec_basecase_limb(x+i,y, 0,i+1);
  for (  ; i<lx; i++) gel(z,i) = RgX_mulspec_basecase_limb(x+i,y, 0,ly);
  for (  ; i<n; i++)  gel(z,i) = RgX_mulspec_basecase_limb(x+i,y, i-lx+1,ly);
  return normalizepol_lg(z - 2, lz);
}
/* Mulders / Karatsuba product f*g mod t^n (Hanrot-Zimmermann variant) */
GEN
RgXn_mul(GEN f, GEN g, long n)
{
  pari_sp av = avma;
  GEN fe,fo, ge,go, l,h,m;
  long n0, n1;
  if (degpol(f) + degpol(g) < n) return RgX_mul(f,g);
  if (n < 80) return RgXn_mul_basecase(f,g,n);
  n0 = n>>1; n1 = n-n0;
  RgX_even_odd(f, &fe, &fo);
  RgX_even_odd(g, &ge, &go);
  l = RgXn_mul(fe,ge,n1);
  h = RgXn_mul(fo,go,n0);
  m = RgX_sub(RgXn_mul(RgX_add(fe,fo),RgX_add(ge,go),n0), RgX_add(l,h));
  /* n1-1 <= n0 <= n1, deg l,m <= n1-1, deg h <= n0-1
   * result is t^2 h(t^2) + t m(t^2) + l(t^2) */
  l = RgX_inflate(l,2); /* deg l <= 2n1 - 2 <= n-1 */
  /* deg(t m(t^2)) <= 2n1 - 1 <= n, truncate to < n */
  if (2*degpol(m)+1 == n) m = normalizepol_lg(m, lg(m)-1);
  m = RgX_inflate(m,2);
  /* deg(t^2 h(t^2)) <= 2n0 <= n, truncate to < n */
  if (2*degpol(h)+2 == n) h = normalizepol_lg(h, lg(h)-1);
  h = RgX_inflate(h,2);
  h = addmulXncopy(addmulXn(h,m,1), l,1);
  setvarn(h, varn(f)); return gerepileupto(av, h);
}

/* fast product (Karatsuba) of polynomials a,b. These are not real GENs, a+2,
 * b+2 were sent instead. na, nb = number of terms of a, b.
 * Only c, c0, c1, c2 are genuine GEN.
 */
GEN
RgX_mulspec(GEN a, GEN b, long na, long nb)
{
  GEN a0, c, c0;
  long n0, n0a, i, v = 0;
  pari_sp av;

  while (na && isrationalzero(gel(a,0))) { a++; na--; v++; }
  while (nb && isrationalzero(gel(b,0))) { b++; nb--; v++; }
  if (na < nb) swapspec(a,b, na,nb);
  if (!nb) return pol_0(0);

  if (nb < RgX_MUL_LIMIT) return RgX_mulspec_basecase(a,b,na,nb, v);
  RgX_shift_inplace_init(v);
  i = (na>>1); n0 = na-i; na = i;
  av = avma; a0 = a+n0; n0a = n0;
  while (n0a && isrationalzero(gel(a,n0a-1))) n0a--;

  if (nb > n0)
  {
    GEN b0,c1,c2;
    long n0b;

    nb -= n0; b0 = b+n0; n0b = n0;
    while (n0b && isrationalzero(gel(b,n0b-1))) n0b--;
    c = RgX_mulspec(a,b,n0a,n0b);
    c0 = RgX_mulspec(a0,b0, na,nb);

    c2 = addpol(a0,a, na,n0a);
    c1 = addpol(b0,b, nb,n0b);

    c1 = RgX_mulspec(c1+2,c2+2, lgpol(c1),lgpol(c2));
    c2 = RgX_sub(c1, RgX_add(c0,c));
    c0 = addmulXn(c0, c2, n0);
  }
  else
  {
    c = RgX_mulspec(a,b,n0a,nb);
    c0 = RgX_mulspec(a0,b,na,nb);
  }
  c0 = addmulXncopy(c0,c,n0);
  return RgX_shift_inplace(gerepileupto(av,c0), v);
}

INLINE GEN
RgX_sqrspec_basecase_limb(GEN x, long a, long i)
{
  pari_sp av = avma;
  GEN s = NULL;
  long j, l = (i+1)>>1;
  for (j=a; j<l; j++)
  {
    GEN xj = gel(x,j), xx = gel(x,i-j);
    if (xj && xx)
    {
      GEN t = gmul(xj, xx);
      s = s? gadd(s, t): t;
    }
  }
  if (s) s = gshift(s,1);
  if ((i&1) == 0)
  {
    GEN t = gel(x, i>>1);
    if (t) {
      t = gsqr(t);
      s = s? gadd(s, t): t;
    }
  }
  return s? gerepileupto(av,s): gen_0;
}
static GEN
RgX_sqrspec_basecase(GEN x, long nx, long v)
{
  long i, lz, nz;
  GEN z;

  if (!nx) return pol_0(0);
  x = RgXspec_kill0(x,nx);
  lz = (nx << 1) + 1, nz = lz-2;
  lz += v;
  z = cgetg(lz,t_POL) + 2;
  for (i=0; i<v; i++) gel(z++, 0) = gen_0;
  for (i=0; i<nx; i++)gel(z,i) = RgX_sqrspec_basecase_limb(x, 0, i);
  for (  ; i<nz; i++) gel(z,i) = RgX_sqrspec_basecase_limb(x, i-nx+1, i);
  z -= v+2; z[1] = 0; return normalizepol_lg(z, lz);
}
/* return x^2 mod t^n */
static GEN
RgXn_sqr_basecase(GEN x, long n)
{
  long i, lz = n+2, lx = lgpol(x);
  GEN z;
  if (lx < 0) return pol_0(varn(x));
  z = cgetg(lz, t_POL);
  z[1] = x[1];
  x+=2; if (lx > n) lx = n;
  x = RgXspec_kill0(x,lx);
  z+=2;/* x:z [i] = term of degree i */
  for (i=0;i<lx; i++) gel(z,i) = RgX_sqrspec_basecase_limb(x, 0, i);
  for (  ; i<n; i++)  gel(z,i) = RgX_sqrspec_basecase_limb(x, i-lx+1, i);
  z -= 2; return normalizepol_lg(z, lz);
}
/* Mulders / Karatsuba product f^2 mod t^n (Hanrot-Zimmermann variant) */
GEN
RgXn_sqr(GEN f, long n)
{
  pari_sp av = avma;
  GEN fe,fo, l,h,m;
  long n0, n1;
  if (2*degpol(f) < n) return RgX_sqr(f);
  if (n < 80) return RgXn_sqr_basecase(f,n);
  n0 = n>>1; n1 = n-n0;
  RgX_even_odd(f, &fe, &fo);
  l = RgXn_sqr(fe,n1);
  h = RgXn_sqr(fo,n0);
  m = RgX_sub(RgXn_sqr(RgX_add(fe,fo),n0), RgX_add(l,h));
  /* n1-1 <= n0 <= n1, deg l,m <= n1-1, deg h <= n0-1
   * result is t^2 h(t^2) + t m(t^2) + l(t^2) */
  l = RgX_inflate(l,2); /* deg l <= 2n1 - 2 <= n-1 */
  /* deg(t m(t^2)) <= 2n1 - 1 <= n, truncate to < n */
  if (2*degpol(m)+1 == n) m = normalizepol_lg(m, lg(m)-1);
  m = RgX_inflate(m,2);
  /* deg(t^2 h(t^2)) <= 2n0 <= n, truncate to < n */
  if (2*degpol(h)+2 == n) h = normalizepol_lg(h, lg(h)-1);
  h = RgX_inflate(h,2);
  h = addmulXncopy(addmulXn(h,m,1), l,1);
  setvarn(h, varn(f)); return gerepileupto(av, h);
}

GEN
RgX_sqrspec(GEN a, long na)
{
  GEN a0, c, c0, c1;
  long n0, n0a, i, v = 0;
  pari_sp av;

  while (na && isrationalzero(gel(a,0))) { a++; na--; v += 2; }
  if (na<RgX_SQR_LIMIT) return RgX_sqrspec_basecase(a, na, v);
  RgX_shift_inplace_init(v);
  i = (na>>1); n0 = na-i; na = i;
  av = avma; a0 = a+n0; n0a = n0;
  while (n0a && isrationalzero(gel(a,n0a-1))) n0a--;

  c = RgX_sqrspec(a,n0a);
  c0 = RgX_sqrspec(a0,na);
  c1 = gmul2n(RgX_mulspec(a0,a, na,n0a), 1);
  c0 = addmulXn(c0,c1, n0);
  c0 = addmulXncopy(c0,c,n0);
  return RgX_shift_inplace(gerepileupto(av,c0), v);
}

/* (X^a + A)(X^b + B) - X^(a+b), where deg A < a, deg B < b */
GEN
RgX_mul_normalized(GEN A, long a, GEN B, long b)
{
  GEN z = RgX_mul(A, B);
  if (a < b)
    z = addmulXn(addmulXn(A, B, b-a), z, a);
  else if (a > b)
    z = addmulXn(addmulXn(B, A, a-b), z, b);
  else
    z = addmulXn(RgX_add(A, B), z, a);
  setvarn(z,varn(A)); return z;
}

GEN
RgX_mul(GEN x, GEN y)
{
  GEN z = RgX_mulspec(y+2, x+2, lgpol(y), lgpol(x));
  setvarn(z,varn(x)); return z;
}

GEN
RgX_sqr(GEN x)
{
  GEN z = RgX_sqrspec(x+2, lgpol(x));
  setvarn(z,varn(x)); return z;
}

/*******************************************************************/
/*                                                                 */
/*                               DIVISION                          */
/*                                                                 */
/*******************************************************************/
GEN
RgX_Rg_divexact(GEN x, GEN y) {
  long i, lx;
  GEN z;
  if (typ(y) == t_INT && is_pm1(y))
    return signe(y) < 0 ? RgX_neg(x): RgX_copy(x);
  z = cgetg_copy(x, &lx); z[1] = x[1];
  for (i=2; i<lx; i++) gel(z,i) = gdivexact(gel(x,i),y);
  return z;
}
GEN
RgX_Rg_div(GEN x, GEN y) {
  long i, lx;
  GEN z = cgetg_copy(x, &lx); z[1] = x[1];
  for (i=2; i<lx; i++) gel(z,i) = gdiv(gel(x,i),y);
  return normalizepol_lg(z, lx);
}
GEN
RgX_normalize(GEN x)
{
  GEN d = NULL;
  long i, n = lg(x)-1;
  for (i = n; i > 1; i--)
  {
    d = gel(x,i);
    if (!gequal0(d)) break;
  }
  if (i == 1) return pol_0(varn(x));
  if (i == n && isint1(d)) return x;
  return normalizepol_lg(RgX_Rg_div(x, d), i+1);
}
GEN
RgX_divs(GEN x, long y) {
  long i, lx;
  GEN z = cgetg_copy(x, &lx); z[1] = x[1];
  for (i=2; i<lx; i++) gel(z,i) = gdivgs(gel(x,i),y);
  return normalizepol_lg(z, lx);
}
GEN
RgX_div_by_X_x(GEN a, GEN x, GEN *r)
{
  long l = lg(a), i;
  GEN a0, z0, z = cgetg(l-1, t_POL);
  z[1] = a[1];
  a0 = a + l-1;
  z0 = z + l-2; *z0 = *a0--;
  for (i=l-3; i>1; i--) /* z[i] = a[i+1] + x*z[i+1] */
  {
    GEN t = gadd(gel(a0--,0), gmul(x, gel(z0--,0)));
    gel(z0,0) = t;
  }
  if (r) *r = gadd(gel(a0,0), gmul(x, gel(z0,0)));
  return z;
}
/* Polynomial division x / y:
 *   if z = ONLY_REM  return remainder, otherwise return quotient
 *   if z != NULL set *z to remainder
 *   *z is the last object on stack (and thus can be disposed of with cgiv
 *   instead of gerepile) */
/* assume, typ(x) = typ(y) = t_POL, same variable */
GEN
RgX_divrem(GEN x, GEN y, GEN *pr)
{
  pari_sp avy, av, av1;
  long dx,dy,dz,i,j,sx,lr;
  GEN z,p1,p2,rem,y_lead,mod;
  GEN (*f)(GEN,GEN);

  if (!signe(y)) pari_err_INV("RgX_divrem",y);

  dy = degpol(y);
  y_lead = gel(y,dy+2);
  if (gequal0(y_lead)) /* normalize denominator if leading term is 0 */
  {
    pari_warn(warner,"normalizing a polynomial with 0 leading term");
    for (dy--; dy>=0; dy--)
    {
      y_lead = gel(y,dy+2);
      if (!gequal0(y_lead)) break;
    }
  }
  if (!dy) /* y is constant */
  {
    if (pr == ONLY_REM) return pol_0(varn(x));
    z = RgX_Rg_div(x, y_lead);
    if (pr == ONLY_DIVIDES) return z;
    if (pr) *pr = pol_0(varn(x));
    return z;
  }
  dx = degpol(x);
  if (dx < dy)
  {
    if (pr == ONLY_REM) return RgX_copy(x);
    if (pr == ONLY_DIVIDES) return signe(x)? NULL: pol_0(varn(x));
    z = pol_0(varn(x));
    if (pr) *pr = RgX_copy(x);
    return z;
  }

  /* x,y in R[X], y non constant */
  av = avma;
  switch(typ(y_lead))
  {
    case t_REAL:
      y_lead = ginv(y_lead);
      f = gmul; mod = NULL;
      break;
    case t_INTMOD:
    case t_POLMOD: y_lead = ginv(y_lead);
      f = gmul; mod = gmodulo(gen_1, gel(y_lead,1));
      break;
    default: if (gequal1(y_lead)) y_lead = NULL;
      f = gdiv; mod = NULL;
  }

  if (y_lead == NULL)
    p2 = gel(x,dx+2);
  else {
    for(;;) {
      p2 = f(gel(x,dx+2),y_lead);
      p2 = simplify_shallow(p2);
      if (!isexactzero(p2) || (--dx < 0)) break;
    }
    if (dx < dy) /* leading coeff of x was in fact zero */
    {
      if (pr == ONLY_DIVIDES) {
        avma = av;
        return (dx < 0)? pol_0(varn(x)) : NULL;
      }
      if (pr == ONLY_REM)
      {
        if (dx < 0)
          return gerepilecopy(av, scalarpol(p2, varn(x)));
        else
        {
          GEN t;
          avma = av;
          t = cgetg(dx + 3, t_POL); t[1] = x[1];
          for (i = 2; i < dx + 3; i++) gel(t,i) = gcopy(gel(x,i));
          return t;
        }
      }
      if (pr) /* cf ONLY_REM above */
      {
        if (dx < 0)
        {
          p2 = gclone(p2);
          avma = av;
          z = pol_0(varn(x));
          x = scalarpol(p2, varn(x));
          gunclone(p2);
        }
        else
        {
          GEN t;
          avma = av;
          z = pol_0(varn(x));
          t = cgetg(dx + 3, t_POL); t[1] = x[1];
          for (i = 2; i < dx + 3; i++) gel(t,i) = gcopy(gel(x,i));
          x = t;
        }
        *pr = x;
      }
      else
      {
        avma = av;
        z = pol_0(varn(x));
      }
      return z;
    }
  }
  /* dx >= dy */
  avy = avma;
  dz = dx-dy;
  z = cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2;
  z += 2;
  y += 2;
  gel(z,dz) = gcopy(p2);

  for (i=dx-1; i>=dy; i--)
  {
    av1=avma; p1=gel(x,i);
    for (j=i-dy+1; j<=i && j<=dz; j++) p1 = gsub(p1, gmul(gel(z,j),gel(y,i-j)));
    if (y_lead) p1 = simplify(f(p1,y_lead));

    if (isrationalzero(p1)) { avma=av1; p1 = gen_0; }
    else
      p1 = avma==av1? gcopy(p1): gerepileupto(av1,p1);
    gel(z,i-dy) = p1;
  }
  if (!pr) return gerepileupto(av,z-2);

  rem = (GEN)avma; av1 = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = gel(x,i);
    /* we always enter this loop at least once */
    for (j=0; j<=i && j<=dz; j++) p1 = gsub(p1, gmul(gel(z,j),gel(y,i-j)));
    if (mod && avma==av1) p1 = gmul(p1,mod);
    if (!gequal0(p1)) { sx = 1; break; } /* remainder is non-zero */
    if (!isexactzero(p1)) break;
    if (!i) break;
    avma=av1;
  }
  if (pr == ONLY_DIVIDES)
  {
    if (sx) { avma=av; return NULL; }
    avma = (pari_sp)rem;
    return gerepileupto(av,z-2);
  }
  lr=i+3; rem -= lr;
  if (avma==av1) { avma = (pari_sp)rem; p1 = gcopy(p1); }
  else p1 = gerepileupto((pari_sp)rem,p1);
  rem[0] = evaltyp(t_POL) | evallg(lr);
  rem[1] = z[-1];
  rem += 2;
  gel(rem,i) = p1;
  for (i--; i>=0; i--)
  {
    av1=avma; p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++) p1 = gsub(p1, gmul(gel(z,j),gel(y,i-j)));
    if (mod && avma==av1) p1 = gmul(p1,mod);
    gel(rem,i) = avma==av1? gcopy(p1):gerepileupto(av1,p1);
  }
  rem -= 2;
  if (!sx) (void)normalizepol_lg(rem, lr);
  if (pr == ONLY_REM) return gerepileupto(av,rem);
  z -= 2;
  {
    GEN *gptr[2]; gptr[0]=&z; gptr[1]=&rem;
    gerepilemanysp(av,avy,gptr,2); *pr = rem; return z;
  }
}

/* x and y in (R[Y]/T)[X]  (lifted), T in R[Y]. y preferably monic */
GEN
RgXQX_divrem(GEN x, GEN y, GEN T, GEN *pr)
{
  long vx, dx, dy, dz, i, j, sx, lr;
  pari_sp av0, av, tetpil;
  GEN z,p1,rem,lead;

  if (!signe(y)) pari_err_INV("RgXQX_divrem",y);
  vx = varn(x);
  dx = degpol(x);
  dy = degpol(y);
  if (dx < dy)
  {
    if (pr)
    {
      av0 = avma; x = RgXQX_red(x, T);
      if (pr == ONLY_DIVIDES) { avma=av0; return signe(x)? NULL: gen_0; }
      if (pr == ONLY_REM) return x;
      *pr = x;
    }
    return pol_0(vx);
  }
  lead = leading_term(y);
  if (!dy) /* y is constant */
  {
    if (pr && pr != ONLY_DIVIDES)
    {
      if (pr == ONLY_REM) return pol_0(vx);
      *pr = pol_0(vx);
    }
    if (gequal1(lead)) return RgX_copy(x);
    av0 = avma; x = gmul(x, ginvmod(lead,T)); tetpil = avma;
    return gerepile(av0,tetpil,RgXQX_red(x,T));
  }
  av0 = avma; dz = dx-dy;
  lead = gequal1(lead)? NULL: gclone(ginvmod(lead,T));
  avma = av0;
  z = cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2; y += 2; z += 2;

  p1 = gel(x,dx); av = avma;
  gel(z,dz) = lead? gerepileupto(av, grem(gmul(p1,lead), T)): gcopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=gel(x,i);
    for (j=i-dy+1; j<=i && j<=dz; j++) p1 = gsub(p1, gmul(gel(z,j),gel(y,i-j)));
    if (lead) p1 = gmul(grem(p1, T), lead);
    tetpil=avma; gel(z,i-dy) = gerepile(av,tetpil, grem(p1, T));
  }
  if (!pr) { if (lead) gunclone(lead); return z-2; }

  rem = (GEN)avma; av = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++) p1 = gsub(p1, gmul(gel(z,j),gel(y,i-j)));
    tetpil=avma; p1 = grem(p1, T); if (!gequal0(p1)) { sx = 1; break; }
    if (!i) break;
    avma=av;
  }
  if (pr == ONLY_DIVIDES)
  {
    if (lead) gunclone(lead);
    if (sx) { avma=av0; return NULL; }
    avma = (pari_sp)rem; return z-2;
  }
  lr=i+3; rem -= lr;
  rem[0] = evaltyp(t_POL) | evallg(lr);
  rem[1] = z[-1];
  p1 = gerepile((pari_sp)rem,tetpil,p1);
  rem += 2; gel(rem,i) = p1;
  for (i--; i>=0; i--)
  {
    av=avma; p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = gsub(p1, gmul(gel(z,j),gel(y,i-j)));
    tetpil=avma; gel(rem,i) = gerepile(av,tetpil, grem(p1, T));
  }
  rem -= 2;
  if (lead) gunclone(lead);
  if (!sx) (void)normalizepol_lg(rem, lr);
  if (pr == ONLY_REM) return gerepileupto(av0,rem);
  *pr = rem; return z-2;
}

/*******************************************************************/
/*                                                                 */
/*                        PSEUDO-DIVISION                          */
/*                                                                 */
/*******************************************************************/
INLINE GEN
rem(GEN c, GEN T)
{
  if (T && typ(c) == t_POL && varn(c) == varn(T)) c = RgX_rem(c, T);
  return c;
}

/* x, y, are ZYX, lc(y) is an integer, T is a ZY */
int
ZXQX_dvd(GEN x, GEN y, GEN T)
{
  long dx, dy, dz, i, p, T_ismonic;
  pari_sp av = avma, av2;
  GEN y_lead;

  if (!signe(y)) pari_err_INV("ZXQX_dvd",y);
  dy = degpol(y); y_lead = gel(y,dy+2);
  if (typ(y_lead) == t_POL) y_lead = gel(y_lead, 2); /* t_INT */
  /* if monic, no point in using pseudo-division */
  if (gequal1(y_lead)) return signe(RgXQX_rem(x, y, T)) == 0;
  T_ismonic = gequal1(leading_term(T));
  dx = degpol(x);
  if (dx < dy) return !signe(x);
  (void)new_chunk(2);
  x = RgX_recip_shallow(x)+2;
  y = RgX_recip_shallow(y)+2;
  /* pay attention to sparse divisors */
  for (i = 1; i <= dy; i++)
    if (!signe(gel(y,i))) gel(y,i) = NULL;
  dz = dx-dy; p = dz+1;
  av2 = avma;
  for (;;)
  {
    GEN m, x0 = gel(x,0), y0 = y_lead, cx = content(x0);
    x0 = gneg(x0); p--;
    m = gcdii(cx, y0);
    if (!equali1(m))
    {
      x0 = gdiv(x0, m);
      y0 = diviiexact(y0, m);
      if (equali1(y0)) y0 = NULL;
    }
    for (i=1; i<=dy; i++)
    {
      GEN c = gel(x,i); if (y0) c = gmul(y0, c);
      if (gel(y,i)) c = gadd(c, gmul(x0,gel(y,i)));
      if (typ(c) == t_POL) c = T_ismonic ? ZX_rem(c, T): RgX_rem(c, T);
      gel(x,i) = c;
    }
    for (   ; i<=dx; i++)
    {
      GEN c = gel(x,i); if (y0) c = gmul(y0, c);
      if (typ(c) == t_POL) c = T_ismonic ? ZX_rem(c, T): RgX_rem(c, T);
      gel(x,i) = c;
    }
    do { x++; dx--; } while (dx >= 0 && !signe(gel(x,0)));
    if (dx < dy) break;
    if (gc_needed(av2,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ZXQX_dvd dx = %ld >= %ld",dx,dy);
      gerepilecoeffs(av2,x,dx+1);
    }
  }
  avma = av; return (dx < 0);
}

/* T either NULL or a t_POL. */
GEN
RgXQX_pseudorem(GEN x, GEN y, GEN T)
{
  long vx = varn(x), dx, dy, dz, i, lx, p;
  pari_sp av = avma, av2;
  GEN y_lead;

  if (!signe(y)) pari_err_INV("RgXQX_pseudorem",y);
  dy = degpol(y); y_lead = gel(y,dy+2);
  /* if monic, no point in using pseudo-division */
  if (gequal1(y_lead)) return T? RgXQX_rem(x, y, T): RgX_rem(x, y);
  dx = degpol(x);
  if (dx < dy) return RgX_copy(x);
  (void)new_chunk(2);
  x = RgX_recip_shallow(x)+2;
  y = RgX_recip_shallow(y)+2;
  /* pay attention to sparse divisors */
  for (i = 1; i <= dy; i++)
    if (isexactzero(gel(y,i))) gel(y,i) = NULL;
  dz = dx-dy; p = dz+1;
  av2 = avma;
  for (;;)
  {
    gel(x,0) = gneg(gel(x,0)); p--;
    for (i=1; i<=dy; i++)
    {
      GEN c = gmul(y_lead, gel(x,i));
      if (gel(y,i)) c = gadd(c, gmul(gel(x,0),gel(y,i)));
      gel(x,i) = rem(c, T);
    }
    for (   ; i<=dx; i++)
    {
      GEN c = gmul(y_lead, gel(x,i));
      gel(x,i) = rem(c, T);
    }
    do { x++; dx--; } while (dx >= 0 && gequal0(gel(x,0)));
    if (dx < dy) break;
    if (gc_needed(av2,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgX_pseudorem dx = %ld >= %ld",dx,dy);
      gerepilecoeffs(av2,x,dx+1);
    }
  }
  if (dx < 0) return pol_0(vx);
  lx = dx+3; x -= 2;
  x[0] = evaltyp(t_POL) | evallg(lx);
  x[1] = evalsigne(1) | evalvarn(vx);
  x = RgX_recip_shallow(x);
  if (p)
  { /* multiply by y[0]^p   [beware dummy vars from FpX_FpXY_resultant] */
    GEN t = y_lead;
    if (T && typ(t) == t_POL && varn(t) == varn(T))
      t = RgXQ_powu(t, p, T);
    else
      t = gpowgs(t, p);
    for (i=2; i<lx; i++)
    {
      GEN c = gmul(gel(x,i), t);
      gel(x,i) = rem(c,T);
    }
    if (!T) return gerepileupto(av, x);
  }
  return gerepilecopy(av, x);
}

GEN
RgX_pseudorem(GEN x, GEN y) { return RgXQX_pseudorem(x,y, NULL); }

/* Compute z,r s.t lc(y)^(dx-dy+1) x = z y + r */
GEN
RgXQX_pseudodivrem(GEN x, GEN y, GEN T, GEN *ptr)
{
  long vx = varn(x), dx, dy, dz, i, iz, lx, lz, p;
  pari_sp av = avma, av2;
  GEN z, r, ypow, y_lead;

  if (!signe(y)) pari_err_INV("RgXQX_pseudodivrem",y);
  dy = degpol(y); y_lead = gel(y,dy+2);
  if (gequal1(y_lead)) return T? RgXQX_divrem(x,y, T, ptr): RgX_divrem(x,y, ptr);
  dx = degpol(x);
  if (dx < dy) { *ptr = RgX_copy(x); return pol_0(vx); }
  if (dx == dy)
  {
    GEN x_lead = gel(x,lg(x)-1);
    x = RgX_renormalize_lg(leafcopy(x), lg(x)-1);
    y = RgX_renormalize_lg(leafcopy(y), lg(y)-1);
    r = RgX_sub(RgX_Rg_mul(x, y_lead), RgX_Rg_mul(y, x_lead));
    *ptr = gerepileupto(av, r); return scalarpol(x_lead, vx);
  }
  (void)new_chunk(2);
  x = RgX_recip_shallow(x)+2;
  y = RgX_recip_shallow(y)+2;
  /* pay attention to sparse divisors */
  for (i = 1; i <= dy; i++)
    if (isexactzero(gel(y,i))) gel(y,i) = NULL;
  dz = dx-dy; p = dz+1;
  lz = dz+3;
  z = cgetg(lz, t_POL);
  z[1] = evalsigne(1) | evalvarn(vx);
  for (i = 2; i < lz; i++) gel(z,i) = gen_0;
  ypow = new_chunk(dz+1);
  gel(ypow,0) = gen_1;
  gel(ypow,1) = y_lead;
  for (i=2; i<=dz; i++)
  {
    GEN c = gmul(gel(ypow,i-1), y_lead);
    gel(ypow,i) = rem(c,T);
  }
  av2 = avma;
  for (iz=2;;)
  {
    p--;
    gel(z,iz++) = rem(gmul(gel(x,0), gel(ypow,p)), T);
    for (i=1; i<=dy; i++)
    {
      GEN c = gmul(y_lead, gel(x,i));
      if (gel(y,i)) c = gsub(c, gmul(gel(x,0),gel(y,i)));
      gel(x,i) = rem(c, T);
    }
    for (   ; i<=dx; i++)
    {
      GEN c = gmul(y_lead, gel(x,i));
      gel(x,i) = rem(c,T);
    }
    x++; dx--;
    while (dx >= dy && gequal0(gel(x,0))) { x++; dx--; iz++; }
    if (dx < dy) break;
    if (gc_needed(av2,1))
    {
      GEN X = x-2;
      if(DEBUGMEM>1) pari_warn(warnmem,"RgX_pseudodivrem dx=%ld >= %ld",dx,dy);
      X[0] = evaltyp(t_POL)|evallg(dx+3); X[1] = z[1]; /* hack */
      gerepileall(av2,2, &X, &z); x = X+2;
    }
  }
  while (dx >= 0 && gequal0(gel(x,0))) { x++; dx--; }
  if (dx < 0)
    x = pol_0(vx);
  else
  {
    lx = dx+3; x -= 2;
    x[0] = evaltyp(t_POL) | evallg(lx);
    x[1] = evalsigne(1) | evalvarn(vx);
    x = RgX_recip_shallow(x);
  }
  z = RgX_recip_shallow(z);
  r = x;
  if (p)
  {
    GEN c = gel(ypow,p); r = RgX_Rg_mul(r, c);
    if (T && typ(c) == t_POL && varn(c) == varn(T)) r = RgXQX_red(r, T);
  }
  gerepileall(av, 2, &z, &r);
  *ptr = r; return z;
}
GEN
RgX_pseudodivrem(GEN x, GEN y, GEN *ptr)
{ return RgXQX_pseudodivrem(x,y,NULL,ptr); }

GEN
RgXQX_mul(GEN x, GEN y, GEN T)
{
  return RgXQX_red(RgX_mul(x,y), T);
}
GEN
RgX_Rg_mul(GEN y, GEN x) {
  long i, ly;
  GEN z = cgetg_copy(y, &ly); z[1] = y[1];
  if (ly == 2) return z;
  for (i = 2; i < ly; i++) gel(z,i) = gmul(x,gel(y,i));
  return normalizepol_lg(z,ly);
}
GEN
RgX_muls(GEN y, long x) {
  long i, ly;
  GEN z = cgetg_copy(y, &ly); z[1] = y[1];
  if (ly == 2) return z;
  for (i = 2; i < ly; i++) gel(z,i) = gmulsg(x,gel(y,i));
  return normalizepol_lg(z,ly);
}
GEN
RgXQX_RgXQ_mul(GEN x, GEN y, GEN T)
{
  return RgXQX_red(RgX_Rg_mul(x,y), T);
}
GEN
RgXQV_RgXQ_mul(GEN v, GEN x, GEN T)
{
  return RgXQV_red(RgV_Rg_mul(v,x), T);
}

GEN
RgXQX_sqr(GEN x, GEN T)
{
  return RgXQX_red(RgX_sqr(x), T);
}

static GEN
_add(void *data, GEN x, GEN y) { (void)data; return RgX_add(x, y); }
static GEN
_sqr(void *data, GEN x) { return RgXQ_sqr(x, (GEN)data); }
static GEN
_mul(void *data, GEN x, GEN y) { return RgXQ_mul(x,y, (GEN)data); }
static GEN
_cmul(void *data, GEN P, long a, GEN x) { (void)data; return RgX_Rg_mul(x,gel(P,a+2)); }
static GEN
_one(void *data) { return pol_1(varn((GEN)data)); }
static GEN
_zero(void *data) { return pol_0(varn((GEN)data)); }
static GEN
_red(void *data, GEN x) { (void)data; return gcopy(x); }

static struct bb_algebra RgXQ_algebra = { _red,_add,_mul,_sqr,_one,_zero };

GEN
RgX_RgXQV_eval(GEN Q, GEN x, GEN T)
{
  return gen_bkeval_powers(Q,degpol(Q),x,(void*)T,&RgXQ_algebra,_cmul);
}

GEN
RgX_RgXQ_eval(GEN Q, GEN x, GEN T)
{
  int use_sqr = (degpol(x)<<1) >= degpol(T);
  return gen_bkeval(Q,degpol(Q),x,use_sqr,(void*)T,&RgXQ_algebra,_cmul);
}

/* mod X^n */
struct modXn {
  long v; /* varn(X) */
  long n;
} ;
static GEN
_sqrXn(void *data, GEN x) {
  struct modXn *S = (struct modXn*)data;
  return RgXn_sqr(x, S->n);
}
static GEN
_mulXn(void *data, GEN x, GEN y) {
  struct modXn *S = (struct modXn*)data;
  return RgXn_mul(x,y, S->n);
}
static GEN
_oneXn(void *data) {
  struct modXn *S = (struct modXn*)data;
  return pol_1(S->v);
}
static GEN
_zeroXn(void *data) {
  struct modXn *S = (struct modXn*)data;
  return pol_0(S->v);
}
static struct bb_algebra RgXn_algebra = { _red,_add, _mulXn,_sqrXn, _oneXn,_zeroXn };

GEN
RgXn_powers(GEN x, long m, long n)
{
  long d = degpol(x);
  int use_sqr = (d<<1) >= n;
  struct modXn S;
  S.v = varn(x); S.n = n;
  return gen_powers(x,m,use_sqr,(void*)&S,_sqrXn,_mulXn,_oneXn);
}

GEN
RgX_RgXnV_eval(GEN Q, GEN x, long n)
{
  struct modXn S;
  S.v = varn(gel(x,2)); S.n = n;
  return gen_bkeval_powers(Q,degpol(Q),x,(void*)&S,&RgXn_algebra,_cmul);
}

GEN
RgX_RgXn_eval(GEN Q, GEN x, long n)
{
  int use_sqr = (degpol(x)<<1) >= n;
  struct modXn S;
  S.v = varn(x); S.n = n;
  return gen_bkeval(Q,degpol(Q),x,use_sqr,(void*)&S,&RgXn_algebra,_cmul);
}

/* Q(x) mod t^n, x in R[t], n >= 1 */
GEN
RgXn_eval(GEN Q, GEN x, long n)
{
  long d = degpol(x);
  int use_sqr;
  struct modXn S;
  if (d == 1 && isrationalzero(gel(x,2)))
  {
    GEN y = RgX_unscale(Q, gel(x,3));
    setvarn(y, varn(x)); return y;
  }
  S.v = varn(x);
  S.n = n;
  use_sqr = (d<<1) >= n;
  return gen_bkeval(Q,degpol(Q),x,use_sqr,(void*)&S,&RgXn_algebra,_cmul);
}

GEN
RgXn_inv(GEN f, long e)
{
  pari_sp av = avma, av2;
  ulong mask;
  GEN W;
  long v = varn(f), n=1;
  if (signe(f)==0)
    pari_err_INV("RgXn_inv",f);
  W = scalarpol(ginv(gel(f,2)),v);
  mask = quadratic_prec_mask(e);
  av2 = avma;
  for (;mask>1;)
  {
    GEN u, fr;
    long n2 = n;
    n<<=1; if (mask & 1) n--;
    mask >>= 1;
    fr = RgXn_red_shallow(f, n);
    u = RgX_shift_shallow(RgXn_mul(W, fr, n), -n2);
    W = RgX_sub(W, RgX_shift_shallow(RgXn_mul(u, W, n-n2), n2));
    if (gc_needed(av2,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgXn_inv, e = %ld", n);
      W = gerepileupto(av2, W);
    }
  }
  return gerepileupto(av, W);
}

GEN
RgXn_exp(GEN h, long e)
{
  pari_sp av = avma, av2;
  long v = varn(h), n=1;
  GEN f = pol_1(v), g = pol_1(v);
  ulong mask = quadratic_prec_mask(e);
  av2 = avma;
  if (signe(h)==0 || degpol(h)<1 || !gequal0(gel(h,2)))
    pari_err_DOMAIN("RgXn_exp","valuation", "<", gen_1, h);
  for (;mask>1;)
  {
    GEN q, w;
    long n2 = n;
    n<<=1; if (mask & 1) n--;
    mask >>= 1;
    g = RgX_sub(RgX_muls(g,2),RgXn_mul(f,RgXn_sqr(g,n2),n2));
    q = RgX_deriv(RgXn_red_shallow(h,n2));
    w = RgX_add(q, RgXn_mul(g, RgX_sub(RgX_deriv(f), RgXn_mul(f,q,n-1)),n-1));
    f = RgX_add(f, RgXn_mul(f, RgX_sub(RgXn_red_shallow(h, n), RgX_integ(w)), n));
    if (gc_needed(av2,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgXn_exp, e = %ld", n);
      gerepileall(av2, 2, &f, &g);
    }
  }
  return gerepileupto(av, f);
}

GEN
RgXn_reverse(GEN f, long e)
{
  pari_sp av = avma, av2;
  ulong mask;
  GEN fi, a, df, W, an;
  long v = varn(f), n=1;
  if (degpol(f)<1 || !gequal0(gel(f,2)))
    pari_err_INV("serreverse",f);
  fi = ginv(gel(f,3));
  a = deg1pol_shallow(fi,gen_0,v);
  if (e <= 2) return gerepilecopy(av, a);
  W = scalarpol(fi,v);
  df = RgX_deriv(f);
  mask = quadratic_prec_mask(e);
  av2 = avma;
  for (;mask>1;)
  {
    GEN u, fa, fr;
    long n2 = n, rt;
    n<<=1; if (mask & 1) n--;
    mask >>= 1;
    fr = RgXn_red_shallow(f, n);
    rt = brent_kung_optpow(degpol(fr), 4, 3);
    an = RgXn_powers(a, rt, n);
    if (n>1)
    {
      long n4 = (n2+1)>>1;
      GEN dfr = RgXn_red_shallow(df, n2);
      dfr = RgX_RgXnV_eval(dfr, RgXnV_red_shallow(an, n2), n2);
      u = RgX_shift(RgX_Rg_sub(RgXn_mul(W, dfr, n2), gen_1), -n4);
      W = RgX_sub(W, RgX_shift(RgXn_mul(u, W, n2-n4), n4));
    }
    fa = RgX_sub(RgX_RgXnV_eval(fr, an, n), pol_x(v));
    fa = RgX_shift(fa, -n2);
    a = RgX_sub(a, RgX_shift(RgXn_mul(W, fa, n-n2), n2));
    if (gc_needed(av2,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgXn_reverse, e = %ld", n);
      gerepileall(av2, 2, &a, &W);
    }
  }
  return gerepileupto(av, a);
}

/* x,T in Rg[X], n in N, compute lift(x^n mod T)) */
GEN
RgXQ_powu(GEN x, ulong n, GEN T)
{
  pari_sp av;
  GEN y;

  if (!n) return pol_1(varn(x));
  if (n == 1) return RgX_copy(x);
  av = avma;
  y = gen_powu(x, n, (void*)T, &_sqr, &_mul);
  return gerepileupto(av, y);
}
/* x,T in Rg[X], n in N, compute lift(x^n mod T)) */
GEN
RgXQ_pow(GEN x, GEN n, GEN T)
{
  pari_sp av;
  long s = signe(n);
  GEN y;

  if (!s) return pol_1(varn(x));
  if (is_pm1(n) == 1)
    return (s < 0)? RgXQ_inv(x, T): RgX_copy(x);
  av = avma;
  if (s < 0) x = RgXQ_inv(x, T);
  y = gen_pow(x, n, (void*)T, &_sqr, &_mul);
  return gerepileupto(av, y);
}

/* generates the list of powers of x of degree 0,1,2,...,l*/
GEN
RgXQ_powers(GEN x, long l, GEN T)
{
  int use_sqr = (degpol(x)<<1) >= degpol(T);
  return gen_powers(x, l, use_sqr, (void *)T,_sqr,_mul,_one);
}

/* a in K = Q[X]/(T), returns [a^0, ..., a^n] */
GEN
QXQ_powers(GEN a, long n, GEN T)
{
  GEN den, v = RgXQ_powers(Q_remove_denom(a, &den), n, T);
  /* den*a integral; v[i+1] = (den*a)^i in K */
  if (den)
  { /* restore denominators */
    GEN d = den;
    long i;
    gel(v,2) = a;
    for (i=3; i<=n+1; i++) {
      d = mulii(d,den);
      gel(v,i) = RgX_Rg_div(gel(v,i), d);
    }
  }
  return v;
}

static GEN
do_QXQ_eval(GEN v, long imin, GEN a, GEN T)
{
  long l, i, m = degpol(T);
  GEN dz, z = Q_remove_denom(QXQ_powers(a, m-1, T), &dz);
  GEN V = cgetg_copy(v, &l);
  for (i = 1; i < imin; i++) V[i] = v[i];
  for (i = imin; i < l; i++)
  {
    GEN c = gel(v,i);
    if (typ(c) == t_POL) c = QX_ZXQV_eval(c, z, dz);
    gel(V,i) = c;
  }
  return V;
}
/* [ s(a mod T) | s <- lift(v) ], a,T are QX, v a QXV */
GEN
QXV_QXQ_eval(GEN v, GEN a, GEN T)
{ return do_QXQ_eval(v, 1, a, T); }
GEN
QXX_QXQ_eval(GEN v, GEN a, GEN T)
{ return normalizepol(do_QXQ_eval(v, 2, a, T)); }

GEN
RgXQ_matrix_pow(GEN y, long n, long m, GEN P)
{
  return RgXV_to_RgM(RgXQ_powers(y,m-1,P),n);
}

GEN
RgXQ_minpoly_naive(GEN y, GEN P)
{
  pari_sp ltop=avma;
  long n=lgpol(P);
  GEN M=ker(RgXQ_matrix_pow(y,n,n,P));
  M=content(RgM_to_RgXV(M,varn(P)));
  return gerepileupto(ltop,M);
}

GEN
RgXQ_norm(GEN x, GEN T)
{
  pari_sp av;
  long dx = degpol(x);
  GEN L, y;

  av = avma; y = resultant(T, x);
  L = leading_term(T);
  if (gequal1(L) || !signe(x)) return y;
  return gerepileupto(av, gdiv(y, gpowgs(L, dx)));
}

GEN
RgX_blocks(GEN P, long n, long m)
{
  GEN z = cgetg(m+1,t_VEC);
  long i,j, k=2, l = lg(P);
  for(i=1; i<=m; i++)
  {
    GEN zi = cgetg(n+2,t_POL);
    zi[1] = P[1];
    gel(z,i) = zi;
    for(j=2; j<n+2; j++)
      gel(zi, j) = k==l ? gen_0 : gel(P,k++);
    zi = ZX_renormalize(zi, n+2);
  }
  return z;
}

/* write p(X) = e(X^2) + Xo(X^2), shallow function */
void
RgX_even_odd(GEN p, GEN *pe, GEN *po)
{
  long n = degpol(p), v = varn(p), n0, n1, i;
  GEN p0, p1;

  if (n <= 0) { *pe = RgX_copy(p); *po = zeropol(v); return; }

  n0 = (n>>1)+1; n1 = n+1 - n0; /* n1 <= n0 <= n1+1 */
  p0 = cgetg(n0+2, t_POL); p0[1] = evalvarn(v)|evalsigne(1);
  p1 = cgetg(n1+2, t_POL); p1[1] = evalvarn(v)|evalsigne(1);
  for (i=0; i<n1; i++)
  {
    p0[2+i] = p[2+(i<<1)];
    p1[2+i] = p[3+(i<<1)];
  }
  if (n1 != n0)
    p0[2+i] = p[2+(i<<1)];
  *pe = normalizepol(p0);
  *po = normalizepol(p1);
}

/* write p(X) = a_0(X^k) + Xa_1(X^k) + ... + X^(k-1)a_{k-1}(X^k), shallow function */
GEN
RgX_splitting(GEN p, long k)
{
  long n = degpol(p), v = varn(p), m, i, j, l;
  GEN r;

  m = n/k;
  r = cgetg(k+1,t_VEC);
  for(i=1; i<=k; i++)
  {
    gel(r,i) = cgetg(m+3, t_POL);
    mael(r,i,1) = evalvarn(v)|evalsigne(1);
  }
  for (j=1, i=0, l=2; i<=n; i++)
  {
    gmael(r,j,l) = gel(p,2+i);
    if (j==k) { j=1; l++; } else j++;
  }
  for(i=1; i<=k; i++)
    gel(r,i) = normalizepol_lg(gel(r,i),i<j?l+1:l);
  return r;
}

/*******************************************************************/
/*                                                                 */
/*                        Kronecker form                           */
/*                                                                 */
/*******************************************************************/

/* z in R[Y] representing an elt in R[X,Y] mod T(Y) in Kronecker form,
 * i.e subst(lift(z), x, y^(2deg(z)-1)). Recover the "real" z, with
 * normalized coefficients */
GEN
Kronecker_to_mod(GEN z, GEN T)
{
  long i,j,lx,l = lg(z), N = (degpol(T)<<1) + 1;
  GEN x, t = cgetg(N,t_POL);
  t[1] = T[1];
  lx = (l-2) / (N-2); x = cgetg(lx+3,t_POL);
  x[1] = z[1];
  T = RgX_copy(T);
  for (i=2; i<lx+2; i++, z+= N-2)
  {
    for (j=2; j<N; j++) gel(t,j) = gel(z,j);
    gel(x,i) = mkpolmod(RgX_rem(normalizepol_lg(t,N), T), T);
  }
  N = (l-2) % (N-2) + 2;
  for (j=2; j<N; j++) t[j] = z[j];
  gel(x,i) = mkpolmod(RgX_rem(normalizepol_lg(t,N), T), T);
  return normalizepol_lg(x, i+1);
}
