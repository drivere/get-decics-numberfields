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
/*                       BASIC NF OPERATIONS                       */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

/*******************************************************************/
/*                                                                 */
/*                OPERATIONS OVER NUMBER FIELD ELEMENTS.           */
/*     represented as column vectors over the integral basis       */
/*                                                                 */
/*******************************************************************/
static GEN
get_tab(GEN nf, long *N)
{
  GEN tab = (typ(nf) == t_MAT)? nf: gel(nf,9);
  *N = nbrows(tab); return tab;
}

/* x != 0, y t_INT. Return x * y (not memory clean if x = 1) */
static GEN
_mulii(GEN x, GEN y) {
  return is_pm1(x)? (signe(x) < 0)? negi(y): y
                  : mulii(x, y);
}

GEN
tablemul_ei_ej(GEN M, long i, long j)
{
  long N;
  GEN tab = get_tab(M, &N);
  tab += (i-1)*N; return gel(tab,j);
}

/* Outputs x.ei, where ei is the i-th elt of the algebra basis.
 * x an RgV of correct length and arbitrary content (polynomials, scalars...).
 * M is the multiplication table ei ej = sum_k M_k^(i,j) ek */
GEN
tablemul_ei(GEN M, GEN x, long i)
{
  long j, k, N;
  GEN v, tab;

  if (i==1) return gcopy(x);
  tab = get_tab(M, &N);
  if (typ(x) != t_COL) { v = zerocol(N); gel(v,i) = gcopy(x); return v; }
  tab += (i-1)*N; v = cgetg(N+1,t_COL);
  /* wi . x = [ sum_j tab[k,j] x[j] ]_k */
  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    GEN s = gen_0;
    for (j=1; j<=N; j++)
    {
      GEN c = gcoeff(tab,k,j);
      if (!gequal0(c)) s = gadd(s, gmul(c, gel(x,j)));
    }
    gel(v,k) = gerepileupto(av,s);
  }
  return v;
}
/* as tablemul_ei, assume x a ZV of correct length */
GEN
zk_ei_mul(GEN nf, GEN x, long i)
{
  long j, k, N;
  GEN v, tab;

  if (i==1) return ZC_copy(x);
  tab = get_tab(nf, &N); tab += (i-1)*N;
  v = cgetg(N+1,t_COL);
  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    GEN s = gen_0;
    for (j=1; j<=N; j++)
    {
      GEN c = gcoeff(tab,k,j);
      if (signe(c)) s = addii(s, _mulii(c, gel(x,j)));
    }
    gel(v,k) = gerepileuptoint(av, s);
  }
  return v;
}

/* table of multiplication by wi in R[w1,..., wN] */
GEN
ei_multable(GEN TAB, long i)
{
  long k,N;
  GEN m, tab = get_tab(TAB, &N);
  tab += (i-1)*N;
  m = cgetg(N+1,t_MAT);
  for (k=1; k<=N; k++) gel(m,k) = gel(tab,k);
  return m;
}

GEN
zk_multable(GEN nf, GEN x)
{
  long i, l = lg(x);
  GEN mul = cgetg(l,t_MAT);
  gel(mul,1) = x; /* assume w_1 = 1 */
  for (i=2; i<l; i++) gel(mul,i) = zk_ei_mul(nf,x,i);
  return mul;
}
GEN
multable(GEN M, GEN x)
{
  long i, N;
  GEN mul;
  if (typ(x) == t_MAT) return x;
  M = get_tab(M, &N);
  if (typ(x) != t_COL) return scalarmat(x, N);
  mul = cgetg(N+1,t_MAT);
  gel(mul,1) = x; /* assume w_1 = 1 */
  for (i=2; i<=N; i++) gel(mul,i) = tablemul_ei(M,x,i);
  return mul;
}

/* x integral in nf; table of multiplication by x in ZK = Z[w1,..., wN].
 * Return a t_INT if x is scalar, and a ZM otherwise */
GEN
zk_scalar_or_multable(GEN nf, GEN x)
{
  long tx = typ(x);
  if (tx == t_MAT || tx == t_INT) return x;
  x = nf_to_scalar_or_basis(nf, x);
  return (typ(x) == t_COL)? zk_multable(nf, x): x;
}

GEN
nftrace(GEN nf, GEN x)
{
  pari_sp av = avma;
  nf = checknf(nf);
  x = nf_to_scalar_or_basis(nf, x);
  x = (typ(x) == t_COL)? RgV_dotproduct(x, gel(nf_get_Tr(nf),1))
                       : gmulgs(x, nf_get_degree(nf));
  return gerepileupto(av, x);
}
GEN
rnfelttrace(GEN rnf, GEN x)
{
  pari_sp av = avma;
  checkrnf(rnf);
  x = rnfeltabstorel(rnf, x);
  x = (typ(x) == t_POLMOD)? rnfeltdown(rnf, gtrace(x))
                          : gmulgs(x, rnf_get_degree(rnf));
  return gerepileupto(av, x);
}

/* assume nf is a genuine nf, fa a famat */
static GEN
famat_norm(GEN nf, GEN fa)
{
  pari_sp av = avma;
  GEN g = gel(fa,1), e = gel(fa,2), N = gen_1;
  long i, l = lg(g);
  for (i = 1; i < l; i++)
    N = gmul(N, powgi(nfnorm(nf, gel(g,i)), gel(e,i)));
  return gerepileupto(av, N);
}
GEN
nfnorm(GEN nf, GEN x)
{
  pari_sp av = avma;
  nf = checknf(nf);
  if (typ(x) == t_MAT) return famat_norm(nf, x);
  x = nf_to_scalar_or_alg(nf, x);
  x = (typ(x) == t_POL)? RgXQ_norm(x, nf_get_pol(nf))
                       : gpowgs(x, nf_get_degree(nf));
  return gerepileupto(av, x);
}

GEN
rnfeltnorm(GEN rnf, GEN x)
{
  pari_sp av = avma;
  checkrnf(rnf);
  x = rnfeltabstorel(rnf, x);
  x = (typ(x) == t_POLMOD)? rnfeltdown(rnf, gnorm(x))
                          : gpowgs(x, rnf_get_degree(rnf));
  return gerepileupto(av, x);
}

/* sum of x and y in nf */
GEN
nfadd(GEN nf, GEN x, GEN y)
{
  GEN z;
  pari_sp av = avma;

  nf = checknf(nf);
  x = nf_to_scalar_or_basis(nf, x);
  y = nf_to_scalar_or_basis(nf, y);
  if (typ(x) != t_COL) {
    if (typ(y) == t_COL) z = RgC_Rg_add(y, x);
    else {
      long N = nf_get_degree(nf);
      z = zerocol(N); gel(z,1) = gadd(x,y);
    }
  } else {
    if (typ(y) != t_COL) z = RgC_Rg_add(x, y);
    else z = RgC_add(x, y);
  }
  return gerepileupto(av, z);
}

/* product of x and y in nf */
GEN
nfmul(GEN nf, GEN x, GEN y)
{
  GEN z;
  pari_sp av = avma;

  if (x == y) return nfsqr(nf,x);

  nf = checknf(nf);
  x = nf_to_scalar_or_basis(nf, x);
  y = nf_to_scalar_or_basis(nf, y);
  if (typ(x) != t_COL)
  {
    if (typ(y) == t_COL) z = RgC_Rg_mul(y, x);
    else {
      long N = nf_get_degree(nf);
      z = zerocol(N); gel(z,1) = gmul(x,y);
    }
  }
  else
  {
    if (typ(y) != t_COL) z = RgC_Rg_mul(x, y);
    else {
      GEN dx, dy;
      x = Q_remove_denom(x, &dx);
      y = Q_remove_denom(y, &dy);
      z = nfmuli(nf,x,y);
      dx = mul_denom(dx,dy);
      if (dx) z = RgC_Rg_div(z, dx);
    }
  }
  return gerepileupto(av, z);
}
/* square of x in nf */
GEN
nfsqr(GEN nf, GEN x)
{
  pari_sp av = avma;
  GEN z;

  nf = checknf(nf);
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) != t_COL)
  {
    long N = nf_get_degree(nf);
    z = zerocol(N); gel(z,1) = gsqr(x);
  }
  else
  {
    GEN dx;
    x = Q_remove_denom(x, &dx);
    z = nfsqri(nf,x);
    if (dx) z = RgC_Rg_div(z, sqri(dx));
  }
  return gerepileupto(av, z);
}

GEN
nfC_nf_mul(GEN nf, GEN v, GEN x)
{
  long tx, l, i;
  GEN y, dx = NULL;

  x = nf_to_scalar_or_basis(nf, x);
  tx = typ(x);
  if (tx != t_COL) {
    if (tx == t_INT)
    {
      long s = signe(x);
      if (!s) return zerocol(lg(v)-1);
      if (is_pm1(x)) return s > 0? leafcopy(v): RgC_neg(v);
    }
    l = lg(v); y = cgetg(l, t_COL);
    for (i=1; i < l; i++)
    {
      GEN c = gel(v,i);
      if (typ(c) != t_COL) c = gmul(c, x); else c = RgC_Rg_mul(c, x);
      gel(y,i) = c;
    }
  }
  else
  {
    x = Q_remove_denom(x, &dx);
    x = zk_multable(nf, x);
    l = lg(v); y = cgetg(l, t_COL);
    for (i=1; i < l; i++)
    {
      GEN c = gel(v,i);
      if (typ(c)!=t_COL) {
        if (!isintzero(c)) c = RgC_Rg_mul(gel(x,1), c);
      } else {
        c = RgM_RgC_mul(x,c);
        if (QV_isscalar(c)) c = gel(c,1);
      }
      gel(y,i) = c;
    }
  }
  return dx? RgC_Rg_div(y, dx): y;
}
static GEN
mulbytab(GEN M, GEN c)
{ return typ(c) == t_COL? RgM_RgC_mul(M,c): RgC_Rg_mul(gel(M,1), c); }
GEN
tablemulvec(GEN M, GEN x, GEN v)
{
  long l, i;
  GEN y;

  if (typ(x) == t_COL && RgV_isscalar(x))
  {
    x = gel(x,1);
    return typ(v) == t_POL? RgX_Rg_mul(v,x): RgV_Rg_mul(v,x);
  }
  x = multable(M, x); /* multiplication table by x */
  y = cgetg_copy(v, &l);
  if (typ(v) == t_POL)
  {
    y[1] = v[1];
    for (i=2; i < l; i++) gel(y,i) = mulbytab(x, gel(v,i));
    y = normalizepol(y);
  }
  else
  {
    for (i=1; i < l; i++) gel(y,i) = mulbytab(x, gel(v,i));
  }
  return y;
}

/* inverse of x in nf */
GEN
nfinv(GEN nf, GEN x)
{
  pari_sp av = avma;
  GEN T, z;

  nf = checknf(nf); T = nf_get_pol(nf);
  x = nf_to_scalar_or_alg(nf, x);
  if (typ(x) == t_POL)
    z = poltobasis(nf, QXQ_inv(x, T));
  else {
    z = zerocol(degpol(T)); gel(z,1) = ginv(x);
  }
  return gerepileupto(av, z);
}

/* quotient of x and y in nf */
GEN
nfdiv(GEN nf, GEN x, GEN y)
{
  pari_sp av = avma;
  GEN T, z;

  nf = checknf(nf); T = nf_get_pol(nf);
  y = nf_to_scalar_or_alg(nf, y);
  if (typ(y) != t_POL) {
    x = nf_to_scalar_or_basis(nf, x);
    if (typ(x) == t_COL) z = RgC_Rg_div(x, y);
    else {
      z = zerocol(degpol(T)); gel(z,1) = gdiv(x,y);
    }
  }
  else
  {
    x = nf_to_scalar_or_alg(nf, x);
    z = QXQ_inv(y, T);
    z = (typ(x) == t_POL)? RgXQ_mul(z, x, T): RgX_Rg_mul(z, x);
    z = poltobasis(nf, z);
  }
  return gerepileupto(av, z);
}

/* product of INTEGERS (t_INT or ZC) x and y in nf
 * compute xy as ( sum_i x_i sum_j y_j m^{i,j}_k )_k */
GEN
nfmuli(GEN nf, GEN x, GEN y)
{
  long i, j, k, N;
  GEN s, v, TAB = get_tab(nf, &N);

  if (typ(x) == t_INT)
  {
    if (typ(y) == t_INT) return scalarcol(mulii(x,y), N);
    return ZC_Z_mul(y, x);
  }
  if (typ(y) == t_INT) return ZC_Z_mul(x, y);
  /* both x and y are ZV */
  v = cgetg(N+1,t_COL);
  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    GEN TABi = TAB;
    if (k == 1)
      s = mulii(gel(x,1),gel(y,1));
    else
      s = addii(mulii(gel(x,1),gel(y,k)),
                mulii(gel(x,k),gel(y,1)));
    for (i=2; i<=N; i++)
    {
      GEN t, xi = gel(x,i);
      TABi += N;
      if (!signe(xi)) continue;

      t = NULL;
      for (j=2; j<=N; j++)
      {
        GEN p1, c = gcoeff(TABi, k, j); /* m^{i,j}_k */
        if (!signe(c)) continue;
        p1 = _mulii(c, gel(y,j));
        t = t? addii(t, p1): p1;
      }
      if (t) s = addii(s, mulii(xi, t));
    }
    gel(v,k) = gerepileuptoint(av,s);
  }
  return v;
}
/* square of INTEGER (t_INT or ZC) x in nf */
GEN
nfsqri(GEN nf, GEN x)
{
  long i, j, k, N;
  GEN s, v, TAB = get_tab(nf, &N);

  if (typ(x) == t_INT) return scalarcol(sqri(x), N);
  v = cgetg(N+1,t_COL);
  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    GEN TABi = TAB;
    if (k == 1)
      s = sqri(gel(x,1));
    else
      s = shifti(mulii(gel(x,1),gel(x,k)), 1);
    for (i=2; i<=N; i++)
    {
      GEN p1, c, t, xi = gel(x,i);
      TABi += N;
      if (!signe(xi)) continue;

      c = gcoeff(TABi, k, i);
      t = signe(c)? _mulii(c,xi): NULL;
      for (j=i+1; j<=N; j++)
      {
        c = gcoeff(TABi, k, j);
        if (!signe(c)) continue;
        p1 = _mulii(c, shifti(gel(x,j),1));
        t = t? addii(t, p1): p1;
      }
      if (t) s = addii(s, mulii(xi, t));
    }
    gel(v,k) = gerepileuptoint(av,s);
  }
  return v;
}

/* both x and y are RgV */
GEN
tablemul(GEN TAB, GEN x, GEN y)
{
  long i, j, k, N;
  GEN s, v;
  if (typ(x) != t_COL) return gmul(x, y);
  if (typ(y) != t_COL) return gmul(y, x);
  N = lg(x)-1;
  v = cgetg(N+1,t_COL);
  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    GEN TABi = TAB;
    if (k == 1)
      s = gmul(gel(x,1),gel(y,1));
    else
      s = gadd(gmul(gel(x,1),gel(y,k)),
               gmul(gel(x,k),gel(y,1)));
    for (i=2; i<=N; i++)
    {
      GEN t, xi = gel(x,i);
      TABi += N;
      if (gequal0(xi)) continue;

      t = NULL;
      for (j=2; j<=N; j++)
      {
        GEN p1, c = gcoeff(TABi, k, j); /* m^{i,j}_k */
        if (gequal0(c)) continue;
        p1 = gmul(c, gel(y,j));
        t = t? gadd(t, p1): p1;
      }
      if (t) s = gadd(s, gmul(xi, t));
    }
    gel(v,k) = gerepileupto(av,s);
  }
  return v;
}
GEN
tablesqr(GEN TAB, GEN x)
{
  long i, j, k, N;
  GEN s, v;

  if (typ(x) != t_COL) return gsqr(x);
  N = lg(x)-1;
  v = cgetg(N+1,t_COL);

  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    GEN TABi = TAB;
    if (k == 1)
      s = gsqr(gel(x,1));
    else
      s = gmul2n(gmul(gel(x,1),gel(x,k)), 1);
    for (i=2; i<=N; i++)
    {
      GEN p1, c, t, xi = gel(x,i);
      TABi += N;
      if (gequal0(xi)) continue;

      c = gcoeff(TABi, k, i);
      t = !gequal0(c)? gmul(c,xi): NULL;
      for (j=i+1; j<=N; j++)
      {
        c = gcoeff(TABi, k, j);
        if (gequal0(c)) continue;
        p1 = gmul(gmul2n(c,1), gel(x,j));
        t = t? gadd(t, p1): p1;
      }
      if (t) s = gadd(s, gmul(xi, t));
    }
    gel(v,k) = gerepileupto(av,s);
  }
  return v;
}

static GEN
_mul(void *data, GEN x, GEN y) { return nfmuli((GEN)data,x,y); }
static GEN
_sqr(void *data, GEN x) { return nfsqri((GEN)data,x); }

/* Compute z^n in nf, left-shift binary powering */
GEN
nfpow(GEN nf, GEN z, GEN n)
{
  pari_sp av = avma;
  long s, N;
  GEN x, cx, T;

  if (typ(n)!=t_INT) pari_err_TYPE("nfpow",n);
  nf = checknf(nf); T = nf_get_pol(nf); N = degpol(T);
  s = signe(n); if (!s) return scalarcol_shallow(gen_1,N);
  x = nf_to_scalar_or_basis(nf, z);
  if (typ(x) != t_COL) { GEN y = zerocol(N); gel(y,1) = powgi(x,n); return y; }
  if (s < 0) { /* simplified nfinv */
    x = nf_to_scalar_or_alg(nf, z);
    x = poltobasis(nf, QXQ_inv(x, T));
    n = absi(n);
  }
  x = primitive_part(x, &cx);
  x = gen_pow(x, n, (void*)nf, _sqr, _mul);
  if (cx) x = RgC_Rg_mul(x, powgi(cx, n));
  return av==avma? gcopy(x): gerepileupto(av,x);
}
/* Compute z^n in nf, left-shift binary powering */
GEN
nfpow_u(GEN nf, GEN z, ulong n)
{
  pari_sp av = avma;
  long N;
  GEN x, cx, T;

  nf = checknf(nf); T = nf_get_pol(nf); N = degpol(T);
  if (!n) return scalarcol_shallow(gen_1,N);
  x = nf_to_scalar_or_basis(nf, z);
  if (typ(x) != t_COL) { GEN y = zerocol(N); gel(y,1) = gpowgs(x,n); return y; }
  x = primitive_part(x, &cx);
  x = gen_powu(x, n, (void*)nf, _sqr, _mul);
  if (cx) x = RgC_Rg_mul(x, powgi(cx, utoipos(n)));
  return av==avma? gcopy(x): gerepileupto(av,x);
}

typedef struct {
  GEN nf, p;
  long I;
} eltmod_muldata;

static GEN
sqr_mod(void *data, GEN x)
{
  eltmod_muldata *D = (eltmod_muldata*)data;
  return FpC_red(nfsqri(D->nf, x), D->p);
}
static GEN
ei_msqr_mod(void *data, GEN x)
{
  GEN x2 = sqr_mod(data, x);
  eltmod_muldata *D = (eltmod_muldata*)data;
  return FpC_red(zk_ei_mul(D->nf, x2, D->I), D->p);
}

/* x = I-th vector of the Z-basis of Z_K, in Z^n, compute lift(x^n mod p) */
GEN
pow_ei_mod_p(GEN nf, long I, GEN n, GEN p)
{
  pari_sp av = avma;
  eltmod_muldata D;
  long s,N;
  GEN y;

  if (typ(n) != t_INT) pari_err_TYPE("nfpow",n);
  nf = checknf(nf); N = nf_get_degree(nf);
  s = signe(n);
  if (s < 0) pari_err_IMPL("negative power in pow_ei_mod_p");
  if (!s || I == 1) return scalarcol_shallow(gen_1,N);
  D.nf = nf;
  D.p = p;
  D.I = I;
  y = gen_pow_fold(col_ei(N, I), n, (void*)&D, &sqr_mod, &ei_msqr_mod);
  return gerepileupto(av,y);
}

/* valuation of integral x (ZV), with resp. to prime ideal pr */
long
ZC_nfvalrem(GEN nf, GEN x, GEN pr, GEN *newx)
{
  long i, v, l;
  GEN r, y, p = pr_get_p(pr), mul = zk_scalar_or_multable(nf, pr_get_tau(pr));

  /* p inert */
  if (typ(mul) == t_INT) return newx? ZV_pvalrem(x, p, newx):ZV_pval(x, p);
  y = cgetg_copy(x, &l); /* will hold the new x */
  x = leafcopy(x);
  for(v=0;; v++)
  {
    for (i=1; i<l; i++)
    { /* is (x.b)[i] divisible by p ? */
      gel(y,i) = dvmdii(ZMrow_ZC_mul(mul,x,i),p,&r);
      if (r != gen_0) { if (newx) *newx = x; return v; }
    }
    swap(x, y);
  }
}
long
ZC_nfval(GEN nf, GEN x, GEN P)
{ return ZC_nfvalrem(nf, x, P, NULL); }

/* v_P(x) != 0, x a ZV. Simpler version of ZC_nfvalrem */
int
ZC_prdvd(GEN nf, GEN x, GEN P)
{
  pari_sp av = avma;
  long i, l;
  GEN p = pr_get_p(P), mul = zk_scalar_or_multable(nf, pr_get_tau(P));
  if (typ(mul) == t_INT) return ZV_Z_dvd(x, p);
  l = lg(x);
  for (i=1; i<l; i++)
    if (remii(ZMrow_ZC_mul(mul,x,i), p) != gen_0) { avma = av; return 0; }
  avma = av; return 1;
}

int
pr_equal(GEN nf, GEN P, GEN Q)
{
  GEN gQ, p = pr_get_p(P);
  long e = pr_get_e(P), f = pr_get_f(P), n;
  if (!equalii(p, pr_get_p(Q)) || e != pr_get_e(Q) || f != pr_get_f(Q))
    return 0;
  gQ = pr_get_gen(Q); n = lg(gQ)-1;
  if (2*e*f > n) return 1; /* room for only one such pr */
  return ZV_equal(pr_get_gen(P), gQ) || ZC_prdvd(nf, gQ, P);
}

long
nfval(GEN nf, GEN x, GEN pr)
{
  pari_sp av = avma;
  long w, e;
  GEN cx, p;

  if (gequal0(x)) return LONG_MAX;
  nf = checknf(nf);
  checkprid(pr);
  p = pr_get_p(pr);
  e = pr_get_e(pr);
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) != t_COL) return e*Q_pval(x,p);
  x = Q_primitive_part(x, &cx);
  w = ZC_nfval(nf,x,pr);
  if (cx) w += e*Q_pval(cx,p);
  avma = av; return w;
}

/* want to write p^v = uniformizer^(e*v) * z^v, z coprime to pr */
/* z := tau^e / p^(e-1), algebraic integer coprime to pr; return z^v */
static GEN
powp(GEN nf, GEN pr, long v)
{
  GEN b, z;
  long e;
  if (!v) return gen_1;
  b = pr_get_tau(pr);
  if (typ(b) == t_INT) return gen_1;
  e = pr_get_e(pr);
  z = gel(b,1);
  if (e != 1) z = gdiv(nfpow_u(nf, z, e), powiu(pr_get_p(pr),e-1));
  return nfpow_u(nf, z, v);
}
long
nfvalrem(GEN nf, GEN x, GEN pr, GEN *py)
{
  pari_sp av = avma;
  long w, e;
  GEN cx, p, t;

  if (!py) return nfval(nf,x,pr);
  if (gequal0(x)) { *py = gcopy(x); return LONG_MAX; }
  nf = checknf(nf);
  checkprid(pr);
  p = pr_get_p(pr);
  e = pr_get_e(pr);
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) != t_COL) {
    w = Q_pvalrem(x,p, py);
    if (!w) { *py = gerepilecopy(av, x); return 0; }
    *py = gerepileupto(av, gmul(powp(nf, pr, w), *py));
    return e*w;
  }
  x = Q_primitive_part(x, &cx);
  w = ZC_nfvalrem(nf,x,pr, py);
  if (cx)
  {
    long v = Q_pvalrem(cx,p, &t);
    *py = nfmul(nf, *py, gmul(powp(nf,pr,v), t));
    *py = gerepileupto(av, *py);
    w += e*v;
  }
  else
    *py = gerepilecopy(av, *py);
  return w;
}
GEN
gpnfvalrem(GEN nf, GEN x, GEN pr, GEN *py)
{
  long v = nfvalrem(nf,x,pr,py);
  return v == LONG_MAX? mkoo(): stoi(v);
}

GEN
coltoalg(GEN nf, GEN x)
{
  return mkpolmod( coltoliftalg(nf, x), nf_get_pol(nf) );
}

GEN
basistoalg(GEN nf, GEN x)
{
  GEN z, T;

  nf = checknf(nf);
  switch(typ(x))
  {
    case t_COL: {
      pari_sp av = avma;
      return gerepilecopy(av, coltoalg(nf, x));
    }
    case t_POLMOD:
      T = nf_get_pol(nf);
      if (!RgX_equal_var(T,gel(x,1)))
        pari_err_MODULUS("basistoalg", T,gel(x,1));
      return gcopy(x);
    case t_POL:
      T = nf_get_pol(nf);
      if (varn(T) != varn(x)) pari_err_VAR("basistoalg",x,T);
      z = cgetg(3,t_POLMOD);
      gel(z,1) = ZX_copy(T);
      gel(z,2) = RgX_rem(x, T); return z;
    case t_INT:
    case t_FRAC:
      T = nf_get_pol(nf);
      z = cgetg(3,t_POLMOD);
      gel(z,1) = ZX_copy(T);
      gel(z,2) = gcopy(x); return z;
    default:
      pari_err_TYPE("basistoalg",x);
      return NULL; /* not reached */
  }
}

/* Assume nf is a genuine nf. */
GEN
nf_to_scalar_or_basis(GEN nf, GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_FRAC:
      return x;
    case t_POLMOD:
      x = checknfelt_mod(nf,x,"nf_to_scalar_or_basis");
      if (typ(x) != t_POL) return x;
      /* fall through */
    case t_POL:
    {
      GEN T = nf_get_pol(nf);
      long l = lg(x);
      if (varn(x) != varn(T)) pari_err_VAR("nf_to_scalar_or_basis", x,T);
      if (l >= lg(T)) { x = RgX_rem(x, T); l = lg(x); }
      if (l == 2) return gen_0;
      if (l == 3) return gel(x,2);
      return poltobasis(nf,x);
    }
    case t_COL:
      if (lg(x) != lg(nf_get_zk(nf))) break;
      return QV_isscalar(x)? gel(x,1): x;
  }
  pari_err_TYPE("nf_to_scalar_or_basis",x);
  return NULL; /* not reached */
}
/* Let x be a polynomial with coefficients in Q or nf. Return the same
 * polynomial with coefficients expressed as vectors (on the integral basis).
 * No consistency checks, not memory-clean. */
GEN
RgX_to_nfX(GEN nf, GEN x)
{
  long i, l;
  GEN y = cgetg_copy(x, &l); y[1] = x[1];
  for (i=2; i<l; i++) gel(y,i) = nf_to_scalar_or_basis(nf, gel(x,i));
  return y;
}

/* Assume nf is a genuine nf. */
GEN
nf_to_scalar_or_alg(GEN nf, GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_FRAC:
      return x;
    case t_POLMOD:
      x = checknfelt_mod(nf,x,"nf_to_scalar_or_alg");
      if (typ(x) != t_POL) return x;
      /* fall through */
    case t_POL:
    {
      GEN T = nf_get_pol(nf);
      long l = lg(x);
      if (varn(x) != varn(T)) pari_err_VAR("nf_to_scalar_or_alg", x,T);
      if (l >= lg(T)) { x = RgX_rem(x, T); l = lg(x); }
      if (l == 2) return gen_0;
      if (l == 3) return gel(x,2);
      return x;
    }
    case t_COL:
      if (lg(x) != lg(nf_get_zk(nf))) break;
      return QV_isscalar(x)? gel(x,1): coltoliftalg(nf, x);
  }
  pari_err_TYPE("nf_to_scalar_or_alg",x);
  return NULL; /* not reached */
}

/* gmul(A, RgX_to_RgC(x)), A t_MAT (or t_VEC) of compatible dimensions */
GEN
mulmat_pol(GEN A, GEN x)
{
  long i,l;
  GEN z;
  if (typ(x) != t_POL) return gmul(x,gel(A,1)); /* scalar */
  l=lg(x)-1; if (l == 1) return typ(A)==t_VEC? gen_0: zerocol(nbrows(A));
  x++; z = gmul(gel(x,1), gel(A,1));
  for (i=2; i<l ; i++)
    if (!gequal0(gel(x,i))) z = gadd(z, gmul(gel(x,i), gel(A,i)));
  return z;
}

/* x a t_POL, nf a genuine nf. No garbage collecting. No check.  */
GEN
poltobasis(GEN nf, GEN x)
{
  GEN P = nf_get_pol(nf);
  if (varn(x) != varn(P)) pari_err_VAR( "poltobasis", x,P);
  if (degpol(x) >= degpol(P)) x = RgX_rem(x,P);
  return mulmat_pol(nf_get_invzk(nf), x);
}

GEN
algtobasis(GEN nf, GEN x)
{
  pari_sp av;

  nf = checknf(nf);
  switch(typ(x))
  {
    case t_POLMOD:
      if (!RgX_equal_var(nf_get_pol(nf),gel(x,1)))
        pari_err_MODULUS("algtobasis", nf_get_pol(nf),gel(x,1));
      x = gel(x,2);
      switch(typ(x))
      {
        case t_INT:
        case t_FRAC: return scalarcol(x, nf_get_degree(nf));
        case t_POL:
          av = avma;
          return gerepileupto(av,poltobasis(nf,x));
      }
      break;

    case t_POL:
      av = avma;
      return gerepileupto(av,poltobasis(nf,x));

    case t_COL:
      if (lg(x)-1 != nf_get_degree(nf)) pari_err_DIM("nfalgtobasis");
      return gcopy(x);

    case t_INT:
    case t_FRAC: return scalarcol(x, nf_get_degree(nf));
  }
  pari_err_TYPE("algtobasis",x);
  return NULL; /* not reached */
}

GEN
rnfbasistoalg(GEN rnf,GEN x)
{
  const char *f = "rnfbasistoalg";
  long lx, i;
  pari_sp av = avma;
  GEN z, nf, relpol, T;

  checkrnf(rnf);
  nf = rnf_get_nf(rnf);
  T = nf_get_pol(nf);
  relpol = QXQX_to_mod_shallow(rnf_get_pol(rnf), T);
  switch(typ(x))
  {
    case t_COL:
      z = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++)
      {
        GEN c = nf_to_scalar_or_alg(nf, gel(x,i));
        if (typ(c) == t_POL) c = mkpolmod(c,T);
        gel(z,i) = c;
      }
      z = RgV_RgC_mul(gel(rnf_get_zk(rnf),1), z);
      return gerepileupto(av, gmodulo(z,relpol));

    case t_POLMOD:
      x = polmod_nffix(f, rnf, x, 0);
      if (typ(x) != t_POL) break;
      retmkpolmod(RgX_copy(x), RgX_copy(relpol));
    case t_POL:
      if (varn(x) == varn(T))
      {
        if (!RgX_is_QX(x)) pari_err_TYPE(f,x);
        x = gmodulo(x,T); break;
      }
      if (varn(x) == varn(relpol))
      {
        x = RgX_nffix(f,nf_get_pol(nf),x,0);
        return gmodulo(x, relpol);
      }
      pari_err_VAR(f, x,relpol);
  }
  retmkpolmod(scalarpol(x, varn(relpol)), RgX_copy(relpol));
}

GEN
matbasistoalg(GEN nf,GEN x)
{
  long i, j, li, lx;
  GEN z = cgetg_copy(x, &lx);

  if (lx == 1) return z;
  switch(typ(x))
  {
    case t_VEC: case t_COL:
      for (i=1; i<lx; i++) gel(z,i) = basistoalg(nf, gel(x,i));
      return z;
    case t_MAT: break;
    default: pari_err_TYPE("matbasistoalg",x);
  }
  li = lgcols(x);
  for (j=1; j<lx; j++)
  {
    GEN c = cgetg(li,t_COL), xj = gel(x,j);
    gel(z,j) = c;
    for (i=1; i<li; i++) gel(c,i) = basistoalg(nf, gel(xj,i));
  }
  return z;
}

GEN
matalgtobasis(GEN nf,GEN x)
{
  long i, j, li, lx;
  GEN z = cgetg_copy(x, &lx);

  if (lx == 1) return z;
  switch(typ(x))
  {
    case t_VEC: case t_COL:
      for (i=1; i<lx; i++) gel(z,i) = algtobasis(nf, gel(x,i));
      return z;
    case t_MAT: break;
    default: pari_err_TYPE("matalgtobasis",x);
  }
  li = lgcols(x);
  for (j=1; j<lx; j++)
  {
    GEN c = cgetg(li,t_COL), xj = gel(x,j);
    gel(z,j) = c;
    for (i=1; i<li; i++) gel(c,i) = algtobasis(nf, gel(xj,i));
  }
  return z;
}
GEN
RgM_to_nfM(GEN nf,GEN x)
{
  long i, j, li, lx;
  GEN z = cgetg_copy(x, &lx);

  if (lx == 1) return z;
  li = lgcols(x);
  for (j=1; j<lx; j++)
  {
    GEN c = cgetg(li,t_COL), xj = gel(x,j);
    gel(z,j) = c;
    for (i=1; i<li; i++) gel(c,i) = nf_to_scalar_or_basis(nf, gel(xj,i));
  }
  return z;
}
GEN
RgC_to_nfC(GEN nf,GEN x)
{
  long i, lx = lg(x);
  GEN z = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) gel(z,i) = nf_to_scalar_or_basis(nf, gel(x,i));
  return z;
}

/* x a t_POLMOD, supposedly in rnf = K[z]/(T), K = Q[y]/(Tnf) */
GEN
polmod_nffix(const char *f, GEN rnf, GEN x, int lift)
{ return polmod_nffix2(f, rnf_get_nfpol(rnf), rnf_get_pol(rnf), x,lift); }
GEN
polmod_nffix2(const char *f, GEN T, GEN relpol, GEN x, int lift)
{
  if (RgX_equal_var(gel(x,1),relpol))
  {
    x = gel(x,2);
    if (typ(x) == t_POL && varn(x) == varn(relpol))
    {
      x = RgX_nffix(f, T, x, lift);
      switch(lg(x))
      {
        case 2: return gen_0;
        case 3: return gel(x,2);
      }
      return x;
    }
  }
  return Rg_nffix(f, T, x, lift);
}
GEN
rnfalgtobasis(GEN rnf,GEN x)
{
  const char *f = "rnfalgtobasis";
  pari_sp av = avma;
  GEN T, relpol;

  checkrnf(rnf);
  relpol = rnf_get_pol(rnf);
  T = rnf_get_nfpol(rnf);
  switch(typ(x))
  {
    case t_COL:
      if (lg(x)-1 != rnf_get_degree(rnf)) pari_err_DIM(f);
      x = RgV_nffix(f, T, x, 0);
      return gerepilecopy(av, x);

    case t_POLMOD:
      x = polmod_nffix(f, rnf, x, 0);
      if (typ(x) != t_POL) break;
      return gerepileupto(av, mulmat_pol(rnf_get_invzk(rnf), x));
    case t_POL:
      if (varn(x) == varn(T))
      {
        if (!RgX_is_QX(x)) pari_err_TYPE(f,x);
        x = mkpolmod(x,T); break;
      }
      x = RgX_nffix(f, T, x, 0);
      if (degpol(x) >= degpol(relpol)) x = RgX_rem(x,relpol);
      return gerepileupto(av, mulmat_pol(rnf_get_invzk(rnf), x));
  }
  return gerepileupto(av, scalarcol(x, rnf_get_degree(rnf)));
}

/* Given a and b in nf, gives an algebraic integer y in nf such that a-b.y
 * is "small" */
GEN
nfdiveuc(GEN nf, GEN a, GEN b)
{
  pari_sp av = avma;
  a = nfdiv(nf,a,b);
  return gerepileupto(av, ground(a));
}

/* Given a and b in nf, gives a "small" algebraic integer r in nf
 * of the form a-b.y */
GEN
nfmod(GEN nf, GEN a, GEN b)
{
  pari_sp av = avma;
  GEN p1 = gneg_i(nfmul(nf,b,ground(nfdiv(nf,a,b))));
  return gerepileupto(av, nfadd(nf,a,p1));
}

/* Given a and b in nf, gives a two-component vector [y,r] in nf such
 * that r=a-b.y is "small". */
GEN
nfdivrem(GEN nf, GEN a, GEN b)
{
  pari_sp av = avma;
  GEN p1,z, y = ground(nfdiv(nf,a,b));

  p1 = gneg_i(nfmul(nf,b,y));
  z = cgetg(3,t_VEC);
  gel(z,1) = gcopy(y);
  gel(z,2) = nfadd(nf,a,p1); return gerepileupto(av, z);
}

/*************************************************************************/
/**                                                                     **/
/**                           (Z_K/I)^*                                 **/
/**                                                                     **/
/*************************************************************************/
/* return sign(sigma_k(x)), x t_COL (integral, primitive) */
static long
eval_sign(GEN M, GEN x, long k)
{
  long i, l = lg(x);
  GEN z = gel(x,1); /* times M[k,1], which is 1 */
  for (i = 2; i < l; i++) z = mpadd(z, mpmul(gcoeff(M,k,i), gel(x,i)));
  if (realprec(z) < DEFAULTPREC) pari_err_PREC("nfsign_arch");
  return signe(z);
}

/* sigma_k(x) */
GEN
nfembed(GEN nf, GEN x, long k)
{
  pari_sp av = avma;
  long i, l;
  GEN z, M;
  nf = checknf(nf);
  x = nf_to_scalar_or_basis(nf,x);
  if (typ(x) != t_COL) return gerepilecopy(av, x);
  M = nf_get_M(nf); l = lg(M); /* > 2 */
  z = gel(x,1);
  for (i=2; i<l; i++) z = gadd(z, gmul(gcoeff(M,k,i), gel(x,i)));
  return gerepileupto(av, z);
}

GEN
vecsmall01_to_indices(GEN v)
{
  long i, k, l = lg(v);
  GEN p = new_chunk(l) + l;
  for (k=1, i=l-1; i; i--)
    if (v[i]) { *--p = i; k++; }
  *--p = evallg(k) | evaltyp(t_VECSMALL);
  avma = (pari_sp)p; return p;
}
GEN
vec01_to_indices(GEN v)
{
  long i, k, l;
  GEN p;

  switch (typ(v))
  {
   case t_VECSMALL: return v;
   case t_VEC: break;
   default: pari_err_TYPE("vec01_to_indices",v);
  }
  l = lg(v);
  p = new_chunk(l) + l;
  for (k=1, i=l-1; i; i--)
    if (signe(gel(v,i))) { *--p = i; k++; }
  *--p = evallg(k) | evaltyp(t_VECSMALL);
  avma = (pari_sp)p; return p;
}
GEN
indices_to_vec01(GEN p, long r)
{
  long i, l = lg(p);
  GEN v = zerovec(r);
  for (i = 1; i < l; i++) gel(v, p[i]) = gen_1;
  return v;
}

/* return (column) vector of R1 signatures of x (0 or 1) */
GEN
nfsign_arch(GEN nf, GEN x, GEN arch)
{
  GEN M, V, archp = vec01_to_indices(arch);
  long i, s, n = lg(archp)-1;
  pari_sp av;

  if (!n) return cgetg(1,t_VECSMALL);
  nf = checknf(nf);
  if (typ(x) == t_MAT)
  { /* factorisation */
    GEN g = gel(x,1), e = gel(x,2);
    V = zero_zv(n);
    for (i=1; i<lg(g); i++)
      if (mpodd(gel(e,i)))
        Flv_add_inplace(V, nfsign_arch(nf,gel(g,i),archp), 2);
    avma = (pari_sp)V; return V;
  }
  av = avma; V = cgetg(n+1,t_VECSMALL);
  x = nf_to_scalar_or_basis(nf, x);
  switch(typ(x))
  {
    case t_INT:
      s = signe(x);
      if (!s) pari_err_DOMAIN("nfsign_arch","element","=",gen_0,x);
      avma = av; return const_vecsmall(n, (s < 0)? 1: 0);
    case t_FRAC:
      s = signe(gel(x,1));
      avma = av; return const_vecsmall(n, (s < 0)? 1: 0);
  }
  x = Q_primpart(x); M = nf_get_M(nf);
  for (i = 1; i <= n; i++) V[i] = (eval_sign(M, x, archp[i]) < 0)? 1: 0;
  avma = (pari_sp)V; return V;
}

/* return the vector of signs of x; the matrix of such if x is a vector
 * of nf elements */
GEN
nfsign(GEN nf, GEN x)
{
  long i, l;
  GEN arch, S;

  nf = checknf(nf);
  arch = identity_perm( nf_get_r1(nf) );
  if (typ(x) != t_VEC) return nfsign_arch(nf, x, arch);
  l = lg(x); S = cgetg(l, t_MAT);
  for (i=1; i<l; i++) gel(S,i) = nfsign_arch(nf, gel(x,i), arch);
  return S;
}

/* multiply y by t = 1 mod^* f such that sign(x) = sign(y) at arch = divisor[2].
 * If x == NULL, make y >> 0 at sarch */
GEN
set_sign_mod_divisor(GEN nf, GEN x, GEN y, GEN divisor, GEN sarch)
{
  GEN s, archp, gen;
  long nba,i;
  if (!sarch) return y;
  gen = gel(sarch,2); nba = lg(gen);
  if (nba == 1) return y;

  archp = vec01_to_indices(gel(divisor,2));
  s = nfsign_arch(nf, y, archp);
  if (x) Flv_add_inplace(s, nfsign_arch(nf, x, archp), 2);
  s = Flm_Flc_mul(gel(sarch,3), s, 2);
  for (i=1; i<nba; i++)
    if (s[i]) y = nfmul(nf,y,gel(gen,i));
  return y;
}

/* given an element x in Z_K and an integral ideal y in HNF, coprime with x,
   outputs an element inverse of x modulo y */
GEN
nfinvmodideal(GEN nf, GEN x, GEN y)
{
  pari_sp av = avma;
  GEN a, yZ = gcoeff(y,1,1);

  if (is_pm1(yZ)) return zerocol( nf_get_degree(nf) );
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) == t_INT) return gerepileupto(av, Fp_inv(x, yZ));

  a = hnfmerge_get_1(idealhnf_principal(nf,x), y);
  if (!a) pari_err_INV("nfinvmodideal", x);
  return gerepileupto(av, ZC_hnfrem(nfdiv(nf,a,x), y));
}

static GEN
nfsqrmodideal(GEN nf, GEN x, GEN id) {
  return ZC_hnfrem(nfsqri(nf,x), id);
}
static GEN
nfmulmodideal(GEN nf, GEN x, GEN y, GEN id) {
  return x? ZC_hnfrem(nfmuli(nf,x,y), id): y;
}
/* assume x integral, k integer, A in HNF */
GEN
nfpowmodideal(GEN nf,GEN x,GEN k,GEN A)
{
  long s = signe(k);
  pari_sp av;
  GEN y;

  if (!s) return gen_1;
  av = avma;
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) != t_COL) return Fp_pow(x, k, gcoeff(A,1,1));
  if (s < 0) { x = nfinvmodideal(nf, x,A); k = absi(k); }
  for(y = NULL;;)
  {
    if (mpodd(k)) y = nfmulmodideal(nf,y,x,A);
    k = shifti(k,-1); if (!signe(k)) break;
    x = nfsqrmodideal(nf,x,A);
  }
  return gerepileupto(av, y);
}

/* a * g^n mod id */
static GEN
elt_mulpow_modideal(GEN nf, GEN a, GEN g, GEN n, GEN id)
{
  return nfmulmodideal(nf, a, nfpowmodideal(nf,g,n,id), id);
}

/* assume (num(g[i]), id) = 1 for all i. Return prod g[i]^e[i] mod id.
 * EX = multiple of exponent of (O_K/id)^* */
GEN
famat_to_nf_modideal_coprime(GEN nf, GEN g, GEN e, GEN id, GEN EX)
{
  GEN plus = NULL, minus = NULL, idZ = gcoeff(id,1,1);
  pari_sp av = avma;
  long i, lx = lg(g);
  GEN EXo2 = (expi(EX) > 10)? shifti(EX,-1): NULL;

  if (is_pm1(idZ)) lx = 1; /* id = Z_K */
  for (i=1; i<lx; i++)
  {
    GEN h, n = centermodii(gel(e,i), EX, EXo2);
    long sn = signe(n);
    if (!sn) continue;

    h = nf_to_scalar_or_basis(nf, gel(g,i));
    switch(typ(h))
    {
      case t_INT: break;
      case t_FRAC:
        h = Fp_div(gel(h,1), gel(h,2), idZ); break;
      default:
      {
        GEN dh;
        h = Q_remove_denom(h, &dh);
        if (dh) h = FpC_Fp_mul(h, Fp_inv(dh,idZ), idZ);
      }
    }
    if (sn > 0)
      plus = elt_mulpow_modideal(nf, plus, h, n, id);
    else /* sn < 0 */
      minus = elt_mulpow_modideal(nf, minus, h, absi(n), id);

    if (gc_needed(av, 2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"famat_to_nf_modideal_coprime");
      if (!plus) plus = gen_0;
      if (!minus) minus = gen_0;
      gerepileall(av,2, &plus, &minus);
      if (isintzero(plus)) plus = NULL;
      if (isintzero(minus)) minus = NULL;
    }
  }
  if (minus)
    plus = nfmulmodideal(nf, plus, nfinvmodideal(nf,minus,id), id);
  return plus? plus: scalarcol_shallow(gen_1, lg(id)-1);
}

/* given 2 integral ideals x, y in HNF s.t x | y | x^2, compute the quotient
   (1+x)/(1+y) in the form [[cyc],[gen]], if U != NULL, set *U := ux^-1 */
static GEN
zidealij(GEN x, GEN y, GEN *U)
{
  GEN G, cyc;
  long j, N;

  /* x^(-1) y = relations between the 1 + x_i (HNF) */
  cyc = ZM_snf_group(hnf_solve(x, y), U, &G);
  N = lg(cyc); G = ZM_mul(x,G); settyp(G, t_VEC); /* new generators */
  for (j=1; j<N; j++)
  {
    GEN c = gel(G,j);
    gel(c,1) = addiu(gel(c,1), 1); /* 1 + g_j */
    if (ZV_isscalar(c)) gel(G,j) = gel(c,1);
  }
  if (U) *U = RgM_mul(*U, RgM_inv(x));
  return mkvec2(cyc, G);
}

static GEN
Fq_FpXQ_log(GEN a, GEN g, GEN ord, GEN T, GEN p)
{
  if (!T) return Fp_log(a,g,ord,p);
  if (typ(a)==t_INT) return Fp_FpXQ_log(a,g,ord,T,p);
  return FpXQ_log(a,g,ord,T,p);
}
/* same in nf.zk / pr */
static GEN
nf_log(GEN nf, GEN a, GEN g, GEN ord, GEN pr)
{
  pari_sp av = avma;
  GEN T,p, modpr = nf_to_Fq_init(nf, &pr, &T, &p);
  GEN A = nf_to_Fq(nf,a,modpr);
  GEN G = nf_to_Fq(nf,g,modpr);
  return gerepileuptoint(av, Fq_FpXQ_log(A,G,ord,T,p));
}

/* Product of cyc entries, with cyc = diagonal(Smith Normal Form), assumed != 0.
 * Set L to the index of the last non-trivial (!= 1) entry */
GEN
detcyc(GEN cyc, long *L)
{
  pari_sp av = avma;
  long i, l = lg(cyc);
  GEN s = gel(cyc,1);

  if (l == 1) { *L = 1; return gen_1; }
  for (i=2; i<l; i++)
  {
    GEN t = gel(cyc,i);
    if (is_pm1(t)) break;
    s = mulii(s, t);
  }
  *L = i; return i <= 2? icopy(s): gerepileuptoint(av,s);
}

/* (U,V) = 1. Return y = x mod U, = 1 mod V (uv: u + v = 1, u in U, v in V),
 * namely u + x*v.
 * Either (u,mv) are both t_INT, or
 * u is a t_COL, mv is a t_MAT, multiplication table by v */
static GEN
makeprimetoideal(GEN UV, GEN u,GEN mv, GEN x)
{
  GEN t;
  if (typ(mv) == t_INT) /* u t_INT */
  {
    if (typ(x) == t_INT) return addii(mulii(x,mv), u);
    t = ZC_Z_add(ZC_Z_mul(x,mv), u);
  }
  else
  {
    t = typ(x) == t_INT? ZC_Z_mul(gel(mv,1),x): ZM_ZC_mul(mv,x);
    t = ZC_add(t, u);
  }
  return ZC_hnfrem(t, UV);
}

static GEN
makeprimetoidealvec(GEN UV, GEN u,GEN mv, GEN gen)
{
  long i, ly;
  GEN y = cgetg_copy(gen, &ly);
  for (i=1; i<ly; i++) gel(y,i) = makeprimetoideal(UV,u,mv, gel(gen,i));
  return y;
}

/* Given an ideal pr^ep, and an integral ideal x (in HNF form) compute a list
 * of vectors,corresponding to the abelian groups (O_K/pr)^*, and
 * 1 + pr^i/ 1 + pr^min(2i, ep), i = 1,...
 * Each vector has 5 components as follows :
 * [[cyc],[g],[g'],[sign],U.X^-1].
 * cyc   = type as abelian group
 * g, g' = generators. (g',x) = 1, not necessarily so for g
 * sign  = vector of the sign(g') at arch.
 * If x = NULL, the original ideal was a prime power */
static GEN
zprimestar(GEN nf, GEN pr, GEN ep, GEN x, GEN arch)
{
  pari_sp av = avma;
  long a, e = itos(ep), f = pr_get_f(pr);
  GEN p = pr_get_p(pr), list, g, g0, y, u,v, prb, pre;
  ulong mask;

  if(DEBUGLEVEL>3) err_printf("treating pr^%ld, pr = %Ps\n",e,pr);
  if (f == 1)
    g = pgener_Fp(p);
  else
  {
    GEN T, modpr = zk_to_Fq_init(nf, &pr, &T, &p);
    g = Fq_to_nf(gener_FpXQ(T,p,NULL), modpr);
    g = poltobasis(nf, g);
  }
  /* g generates  (Z_K / pr)^* */
  prb = idealhnf_two(nf,pr);
  pre = (e==1)? prb: idealpow(nf,pr,ep);
  if (x)
  {
    GEN mv;
    v = idealaddtoone_i(nf,idealdivpowprime(nf,x,pr,ep), pre);
    mv = zk_scalar_or_multable(nf, v);
    u = typ(mv) == t_INT? subui(1,mv): unnf_minus_x(v);
    v = mv;
    g0 = makeprimetoideal(x,u,mv,g);
  }
  else
  {
    u = v = NULL; /* gcc -Wall */
    g0 = g;
  }

  y = mkvec5(mkvec(subiu(powiu(p,f), 1)),
             mkvec(g),
             mkvec(g0),
             mkvec(nfsign_arch(nf,g0,arch)),
             gen_1);
  if (e == 1) return gerepilecopy(av, mkvec(y));
  list = vectrunc_init(e+1);
  vectrunc_append(list, y);
  mask = quadratic_prec_mask(e);
  a = 1;
  while (mask > 1)
  {
    GEN pra = prb, gen, z, s, U;
    long i, l, b = a << 1;

    if (mask & 1) b--;
    mask >>= 1;
    /* compute 1 + pr^a / 1 + pr^b, 2a <= b */
    if(DEBUGLEVEL>3) err_printf("  treating a = %ld, b = %ld\n",a,b);
    prb = (b >= e)? pre: idealpows(nf,pr,b);
    z = zidealij(pra, prb, &U);
    gen = leafcopy(gel(z,2));
    s = cgetg_copy(gen, &l);
    for (i = 1; i < l; i++)
    {
      if (x) gel(gen,i) = makeprimetoideal(x,u,v,gel(gen,i));
      gel(s,i) = nfsign_arch(nf,gel(gen,i),arch);
    }
    y = mkvec5(gel(z,1), gel(z,2), gen, s, U);
    vectrunc_append(list, y);
    a = b;
  }
  return gerepilecopy(av, list);
}

/* increment y, which runs through [-d,d]^k. Return 0 when done. */
static int
increment(GEN y, long k, long d)
{
  long i = 0, j;
  do
  {
    if (++i > k) return 0;
    y[i]++;
  } while (y[i] > d);
  for (j = 1; j < i; j++) y[j] = -d;
  return 1;
}

GEN
archstar_full_rk(GEN x, GEN bas, GEN v, GEN gen)
{
  long i, r, lgmat, N = lg(bas)-1, nba = nbrows(v);
  GEN lambda = cgetg(N+1, t_VECSMALL), mat = cgetg(nba+1,t_MAT);

  lgmat = lg(v); setlg(mat, lgmat+1);
  for (i = 1; i < lgmat; i++) gel(mat,i) = gel(v,i);
  for (     ; i <= nba; i++)  gel(mat,i) = cgetg(nba+1, t_VECSMALL);

  if (x) { x = ZM_lll(x, 0.75, LLL_INPLACE); bas = RgV_RgM_mul(bas, x); }

  for (r=1;; r++)
  { /* reset */
    (void)vec_setconst(lambda, (GEN)0);
    if (!x) lambda[1] = r;
    while (increment(lambda, N, r))
    {
      pari_sp av1 = avma;
      GEN a = RgM_zc_mul(bas, lambda), c = gel(mat,lgmat);
      for (i = 1; i <= nba; i++)
      {
        GEN t = x? gadd(gel(a,i), gen_1): gel(a,i);
        c[i] = (gsigne(t) < 0)? 1: 0;
      }
      avma = av1; if (Flm_deplin(mat, 2)) continue;

      /* c independent of previous sign vectors */
      if (!x) a = zc_to_ZC(lambda);
      else
      {
        a = ZM_zc_mul(x, lambda);
        gel(a,1) = addis(gel(a,1), 1);
      }
      gel(gen,lgmat) = a;
      if (lgmat++ == nba) {
        mat = Flm_inv(mat,2); /* full rank */
        settyp(mat, t_VEC); return mat;
      }
      setlg(mat,lgmat+1);
    }
  }
}

/* x non-0 integral ideal in HNF, compute elements in 1+x (in x, if x = zk)
 * whose sign matrix is invertible. archp in 'indices' format */
GEN
nfarchstar(GEN nf, GEN x, GEN archp)
{
  long nba = lg(archp) - 1;
  GEN cyc, gen, mat;

  if (!nba)
    cyc = gen = mat = cgetg(1, t_VEC);
  else
  {
    GEN xZ = gcoeff(x,1,1), gZ;
    pari_sp av = avma;
    if (is_pm1(xZ)) x = NULL; /* x = O_K */
    gZ = x? subsi(1, xZ): gen_m1; /* gZ << 0, gZ = 1 mod x */
    if (nba == 1)
    {
      gen = mkvec(gZ);
      mat = mkvec( mkvecsmall(1) );
    }
    else
    {
      GEN bas = nf_get_M(nf);
      if (lgcols(bas) > lg(archp)) bas = rowpermute(bas, archp);
      gen = cgetg(nba+1,t_VEC);
      gel(gen,1) = gZ;
      mat = archstar_full_rk(x, bas, mkmat(const_vecsmall(nba,1)), gen);
      gerepileall(av,2,&gen,&mat);
    }
    cyc = const_vec(nba, gen_2);
  }
  return mkvec3(cyc,gen,mat);
}

static GEN
apply_U(GEN U, GEN a)
{
  GEN e;
  if (typ(a) == t_INT)
    e = RgC_Rg_mul(gel(U,1), subis(a, 1));
  else
  { /* t_COL */
    GEN t = gel(a,1);
    gel(a,1) = addsi(-1, gel(a,1)); /* a -= 1 */
    e = RgM_RgC_mul(U, a);
    gel(a,1) = t; /* restore */
  }
  return e;
}
/* a in Z_K (t_COL or t_INT), pr prime ideal, prk = pr^k,
 * list = zprimestar(nf, pr, k, ...)  */
static GEN
zlog_pk(GEN nf, GEN a, GEN y, GEN pr, GEN prk, GEN list, GEN *psigne)
{
  long i,j, llist = lg(list)-1;
  for (j = 1; j <= llist; j++)
  {
    GEN L = gel(list,j), e;
    GEN cyc = gel(L,1), gen = gel(L,2), s = gel(L,4), U = gel(L,5);
    if (j == 1)
      e = mkcol( nf_log(nf, a, gel(gen,1), gel(cyc,1), pr) );
    else
      e = apply_U(U, a);
    /* here lg(e) == lg(cyc) */
    for (i = 1; i < lg(cyc); i++)
    {
      GEN t;
      if (typ(gel(e,i)) != t_INT) pari_err_COPRIME("zlog_pk", a, pr);
      t = modii(negi(gel(e,i)), gel(cyc,i));
      gel(++y,0) = negi(t); if (!signe(t)) continue;

      if (mod2(t)) Flv_add_inplace(*psigne, gel(s,i), 2);
      if (j != llist) a = elt_mulpow_modideal(nf, a, gel(gen,i), t, prk);
    }
  }
  return y;
}

static void
zlog_add_sign(GEN y0, GEN sgn, GEN lists)
{
  GEN y, s;
  long i;
  if (!sgn) return;
  y = y0 + lg(y0);
  s = Flm_Flc_mul(gmael(lists, lg(lists)-1, 3), sgn, 2);
  for (i = lg(s)-1; i > 0; i--) gel(--y,0) = s[i]? gen_1: gen_0;
}

static GEN
famat_zlog(GEN nf, GEN fa, GEN sgn, GEN bid)
{
  GEN g = gel(fa,1), e = gel(fa,2);
  GEN vp = gmael(bid, 3,1), ep = gmael(bid, 3,2);
  GEN arch = bid_get_arch(bid);
  GEN cyc = bid_get_cyc(bid), lists = gel(bid,4), U = gel(bid,5);
  GEN y0, x, y, EX = gel(cyc,1);
  long i, l;

  y0 = y = cgetg(lg(U), t_COL);
  if (!sgn) sgn = nfsign_arch(nf, mkmat2(g,e), arch);
  l = lg(vp);
  for (i=1; i < l; i++)
  {
    GEN pr = gel(vp,i), prk, ex;
    if (l == 2) {
      prk = bid_get_ideal(bid);
      ex = EX;
    } else { /* try to improve EX: should be group exponent mod prf, not f */
      GEN k = gel(ep,i);
      prk = idealpow(nf, pr, k);
      /* upper bound: gcd(EX, (Nv-1)p^(k-1)) = (Nv-1) p^min(k-1,v_p(EX)) */
      ex = subis(pr_norm(pr),1);
      if (!is_pm1(k)) {
        GEN p = pr_get_p(pr), k_1 = subis(k,1);
        long v = Z_pval(EX, p);
        if (cmpui(v, k_1) > 0) v = itos(k_1);
        if (v) ex = mulii(ex, powiu(p, v));
      }
    }
    x = famat_makecoprime(nf, g, e, pr, prk, ex);
    y = zlog_pk(nf, x, y, pr, prk, gel(lists,i), &sgn);
  }
  zlog_add_sign(y0, sgn, lists);
  return y0;
}

static GEN
get_index(GEN lists)
{
  long t = 0, j, k, l = lg(lists)-1;
  GEN L, ind = cgetg(l+1, t_VECSMALL);

  for (k = 1; k < l; k++)
  {
    L = gel(lists,k);
    ind[k] = t;
    for (j=1; j<lg(L); j++) t += lg(gmael(L,j,1)) - 1;
  }
  /* for arch. components */
  ind[k] = t; return ind;
}

static void
init_zlog(zlog_S *S, long n, GEN P, GEN e, GEN arch, GEN lists, GEN U)
{
  S->n = n;
  S->U = U;
  S->P = P;
  S->e = e;
  S->archp = vec01_to_indices(arch);
  S->lists = lists;
  S->ind = get_index(lists);
}
void
init_zlog_bid(zlog_S *S, GEN bid)
{
  GEN fa = gel(bid,3), lists = gel(bid,4), U = gel(bid,5);
  GEN arch = gel(bid_get_mod(bid), 2);
  init_zlog(S, lg(U)-1, gel(fa,1), gel(fa,2), arch, lists, U);
}

/* Return decomposition of a on the S->n successive generators contained in
 * S->lists. If index !=0, do the computation for the corresponding prime
 * ideal and set to 0 the other components. */
static GEN
zlog_ind(GEN nf, GEN a, zlog_S *S, GEN sgn, long index)
{
  GEN y0 = zerocol(S->n), y;
  pari_sp av = avma;
  long k, kmin, kmax;

  a = nf_to_scalar_or_basis(nf,a);
  if (index)
  {
    kmin = kmax = index;
    y = y0 + S->ind[index];
  }
  else
  {
    kmin = 1; kmax = lg(S->P)-1;
    y = y0;
  }
  if (!sgn) sgn = nfsign_arch(nf, a, S->archp);
  for (k = kmin; k <= kmax; k++)
  {
    GEN list= gel(S->lists,k);
    GEN pr  = gel(S->P,k);
    GEN prk = idealpow(nf, pr, gel(S->e,k));
    y = zlog_pk(nf, a, y, pr, prk, list, &sgn);
  }
  zlog_add_sign(y0, sgn, S->lists);
  return gerepilecopy(av, y0);
}
/* sgn = sign(a, S->arch) or NULL if unknown */
GEN
zlog(GEN nf, GEN a, GEN sgn, zlog_S *S) { return zlog_ind(nf, a, S, sgn, 0); }

/* Log on bid.gen of generators of P_{1,I pr^{e-1}} / P_{1,I pr^e} (I,pr) = 1,
 * defined implicitly via CRT. 'index' is the index of pr in modulus
 * factorization */
GEN
log_gen_pr(zlog_S *S, long index, GEN nf, long e)
{
  long i, l, yind = S->ind[index];
  GEN y, A, L, L2 = gel(S->lists,index);

  if (e == 1)
  {
    L = gel(L2,1);
    y = col_ei(S->n, yind+1);
    zlog_add_sign(y, gmael(L,4,1), S->lists);
    retmkmat( ZM_ZC_mul(S->U, y) );
  }
  else
  {
    GEN prk, g, pr = gel(S->P,index);
    long narchp = lg(S->archp)-1;

    if (e == 2)
      L = gel(L2,2);
    else
      L = zidealij(idealpows(nf,pr,e-1), idealpows(nf,pr,e), NULL);
    g = gel(L,2);
    l = lg(g); A = cgetg(l, t_MAT);
    prk = idealpow(nf, pr, gel(S->e,index));
    for (i = 1; i < l; i++)
    {
      GEN G = gel(g,i), sgn = zero_zv(narchp); /*positive at f_oo*/
      y = zerocol(S->n);
      (void)zlog_pk(nf, G, y + yind, pr, prk, L2, &sgn);
      zlog_add_sign(y, sgn, S->lists);
      gel(A,i) = y;
    }
    return ZM_mul(S->U, A);
  }
}
/* Log on bid.gen of generator of P_{1,f} / P_{1,f v[index]}
 * v = vector of r1 real places */
GEN
log_gen_arch(zlog_S *S, long index)
{
  GEN y = zerocol(S->n);
  zlog_add_sign(y, vecsmall_ei(lg(S->archp)-1, index), S->lists);
  return ZM_ZC_mul(S->U, y);
}

/* add [h,cyc] or [h,cyc,gen] to bid */
static void
add_grp(GEN nf, GEN u1, GEN cyc, GEN gen, GEN bid)
{
  GEN h = ZV_prod(cyc);
  if (u1)
  {
    GEN G = mkvec3(h,cyc,NULL/*dummy, bid[2] needed below*/);
    gel(bid,2) = G;
    if (u1 != gen_1)
    {
      long i, c = lg(u1);
      GEN g = cgetg(c,t_VEC);
      for (i=1; i<c; i++)
        gel(g,i) = famat_to_nf_moddivisor(nf, gen, gel(u1,i), bid);
      gen = g;
    }
    gel(G,3) = gen; /* replace dummy */
  }
  else
    gel(bid,2) = mkvec2(h,cyc);
}

static int
RgV_is_prV(GEN v)
{
  long l = lg(v), i;
  for (i = 1; i < l; i++)
    if (!get_prid(gel(v,i))) return 0;
  return 1;
}

static int
is_nf_factor(GEN F)
{
  return typ(F) == t_MAT && lg(F) == 3
    && RgV_is_prV(gel(F,1)) && RgV_is_ZV(gel(F,2));
}

/* Compute [[ideal,arch], [h,[cyc],[gen]], idealfact, [liste], U]
   flag may include nf_GEN | nf_INIT */
GEN
Idealstar(GEN nf, GEN ideal, long flag)
{
  pari_sp av = avma;
  long i, j, k, nbp, R1, nbgen;
  GEN t, y, cyc, U, u1 = NULL, fa, lists, x, arch, archp, E, P, sarch, gen;

  nf = checknf(nf);
  R1 = nf_get_r1(nf);
  if (typ(ideal) == t_VEC && lg(ideal) == 3)
  {
    arch = gel(ideal,2);
    ideal= gel(ideal,1);
    switch(typ(arch))
    {
      case t_VEC:
        if (lg(arch) != R1+1)
          pari_err_TYPE("Idealstar [incorrect archimedean component]",arch);
        archp = vec01_to_indices(arch);
        break;
      case t_VECSMALL:
        archp = arch;
        arch = vec01_to_indices(archp);
        break;
      default:
        pari_err_TYPE("Idealstar [incorrect archimedean component]",arch);
        return NULL;
    }
  }
  else
  {
    arch = zerovec(R1);
    archp = cgetg(1, t_VECSMALL);
  }
  if (is_nf_factor(ideal))
  {
    fa = ideal;
    x = idealfactorback(nf, gel(fa,1), gel(fa,2), 0);
  }
  else
  {
    fa = NULL;
    x = idealhnf_shallow(nf, ideal);
  }
  if (lg(x) == 1) pari_err_DOMAIN("Idealstar", "ideal","=",gen_0,x);
  if (typ(gcoeff(x,1,1)) != t_INT)
    pari_err_DOMAIN("Idealstar","denominator(ideal)", "!=",gen_1,x);
  sarch = nfarchstar(nf, x, archp);
  if (!fa) fa = idealfactor(nf, ideal);
  P = gel(fa,1);
  E = gel(fa,2); nbp = lg(P)-1;
  if (nbp)
  {
    GEN h;
    long cp = 0;
    zlog_S S;

    lists = cgetg(nbp+2,t_VEC);
    /* rough upper bound */
    nbgen = nbp + 1; for (i=1; i<=nbp; i++) nbgen += itos(gel(E,i));
    gen = cgetg(nbgen+1,t_VEC);
    nbgen = 1;
    t = (nbp==1)? NULL: x;
    for (i=1; i<=nbp; i++)
    {
      GEN L = zprimestar(nf, gel(P,i), gel(E,i), t, archp);
      gel(lists,i) = L;
      for (j = 1; j < lg(L); j++) gel(gen, nbgen++) = gmael(L,j,3);
    }
    gel(lists,i) = sarch;
    gel(gen, nbgen++) = gel(sarch,2); setlg(gen, nbgen);
    gen = shallowconcat1(gen); nbgen = lg(gen)-1;

    h = cgetg(nbgen+1,t_MAT);
    init_zlog(&S, nbgen, P, E, archp, lists, NULL);
    for (i=1; i<=nbp; i++)
    {
      GEN L2 = gel(lists,i);
      for (j=1; j < lg(L2); j++)
      {
        GEN L = gel(L2,j), F = gel(L,1), G = gel(L,3);
        for (k=1; k<lg(G); k++)
        { /* log(g^f) mod divisor */
          GEN g = gel(G,k), f = gel(F,k), a = nfpowmodideal(nf,g,f,x);
          GEN sgn = mpodd(f)? nfsign_arch(nf, g, S.archp)
                            : zero_zv(lg(S.archp)-1);
          gel(h,++cp) = ZC_neg(zlog_ind(nf, a, &S, sgn, i));
          gcoeff(h,cp,cp) = f;
        }
      }
    }
    for (j=1; j<lg(archp); j++)
    {
      gel(h,++cp) = zerocol(nbgen);
      gcoeff(h,cp,cp) = gen_2;
    }
    /* assert(cp == nbgen) */
    h = ZM_hnfall(h,NULL,0);
    cyc = ZM_snf_group(h, &U, (flag & nf_GEN)? &u1: NULL);
  }
  else
  {
    lists = mkvec(sarch);
    gen = gel(sarch,2); nbgen = lg(gen)-1;
    cyc = const_vec(nbgen, gen_2);
    U = matid(nbgen);
    if (flag & nf_GEN) u1 = gen_1;
  }

  y = cgetg(6,t_VEC);
  gel(y,1) = mkvec2(x, arch);
  gel(y,3) = fa;
  gel(y,4) = lists;
  gel(y,5) = U;
  add_grp(nf, u1, cyc, gen, y);
  if (!(flag & nf_INIT)) y = gel(y,2);
  return gerepilecopy(av, y);
}

/* vectors of [[cyc],[g],U.X^-1] */
static GEN
principal_units(GEN nf, GEN pr, long e)
{
  pari_sp av = avma;
  long a;
  GEN list, y, prb, pre;
  ulong mask;

  if(DEBUGLEVEL>3) err_printf("treating pr^%ld, pr = %Ps\n",e,pr);
  if (e == 1) return cgetg(1, t_VEC);
  prb = idealhnf_two(nf,pr);
  pre = idealpows(nf,pr,e);
  list = vectrunc_init(e);
  mask = quadratic_prec_mask(e);
  a = 1;
  while (mask > 1)
  {
    GEN pra = prb, z, U;
    long b = a << 1;

    if (mask & 1) b--;
    mask >>= 1;
    /* compute 1 + pr^a / 1 + pr^b, 2a <= b */
    if(DEBUGLEVEL>3) err_printf("  treating a = %ld, b = %ld\n",a,b);
    prb = (b >= e)? pre: idealpows(nf,pr,b);
    z = zidealij(pra, prb, &U);
    y = mkvec3(gel(z,1), gel(z,2), U);
    vectrunc_append(list, y);
    a = b;
  }
  return gerepilecopy(av, list);
}

static GEN
log_prk(GEN nf, GEN a, long nbgen, GEN list, GEN prk)
{
  GEN y = zerocol(nbgen);
  long i,j, iy = 1, llist = lg(list)-1;

  for (j = 1; j <= llist; j++)
  {
    GEN L = gel(list,j);
    GEN cyc = gel(L,1), gen = gel(L,2), U = gel(L,3);
    GEN e = apply_U(U, a);
    /* here lg(e) == lg(cyc) */
    for (i = 1; i < lg(cyc); i++)
    {
      GEN t = modii(negi(gel(e,i)), gel(cyc,i));
      gel(y, iy++) = negi(t); if (!signe(t)) continue;
      if (j != llist) a = elt_mulpow_modideal(nf, a, gel(gen,i), t, prk);
    }
  }
  return y;
}

/* multiplicative group (1 + pr) / (1 + pr^e) */
GEN
idealprincipalunits(GEN nf, GEN pr, long e)
{
  pari_sp av = avma;
  long c, i, j, k, nbgen;
  GEN cyc, u1 = NULL, pre, gen;
  GEN g, EX, h, L2;
  long cp = 0;

  nf = checknf(nf); pre = idealpows(nf, pr, e);
  L2 = principal_units(nf, pr, e);
  c = lg(L2); gen = cgetg(c, t_VEC);
  for (j = 1; j < c; j++) gel(gen, j) = gmael(L2,j,2);
  gen = shallowconcat1(gen); nbgen = lg(gen)-1;

  h = cgetg(nbgen+1,t_MAT);
  for (j=1; j < lg(L2); j++)
  {
    GEN L = gel(L2,j), F = gel(L,1), G = gel(L,2);
    for (k=1; k<lg(G); k++)
    { /* log(g^f) mod pr^e */
      GEN g = gel(G,k), f = gel(F,k), a = nfpowmodideal(nf,g,f,pre);
      gel(h,++cp) = ZC_neg(log_prk(nf, a, nbgen, L2, pre));
      gcoeff(h,cp,cp) = f;
    }
  }
  /* assert(cp == nbgen) */
  h = ZM_hnfall(h,NULL,0);
  cyc = ZM_snf_group(h, NULL, &u1);
  c = lg(u1); g = cgetg(c, t_VEC); EX = gel(cyc,1);
  for (i=1; i<c; i++)
    gel(g,i) = famat_to_nf_modideal_coprime(nf, gen, gel(u1,i), pre, EX);
  return gerepilecopy(av, mkvec3(powiu(pr_norm(pr), e-1), cyc, g));
}

/* FIXME: obsolete */
GEN
zidealstarinitgen(GEN nf, GEN ideal)
{ return Idealstar(nf,ideal, nf_INIT|nf_GEN); }
GEN
zidealstarinit(GEN nf, GEN ideal)
{ return Idealstar(nf,ideal, nf_INIT); }
GEN
zidealstar(GEN nf, GEN ideal)
{ return Idealstar(nf,ideal, nf_GEN); }

GEN
idealstar0(GEN nf, GEN ideal,long flag)
{
  switch(flag)
  {
    case 0: return Idealstar(nf,ideal, nf_GEN);
    case 1: return Idealstar(nf,ideal, nf_INIT);
    case 2: return Idealstar(nf,ideal, nf_INIT|nf_GEN);
    default: pari_err_FLAG("idealstar");
  }
  return NULL; /* not reached */
}

void
check_nfelt(GEN x, GEN *den)
{
  long l = lg(x), i;
  GEN t, d = NULL;
  if (typ(x) != t_COL) pari_err_TYPE("check_nfelt", x);
  for (i=1; i<l; i++)
  {
    t = gel(x,i);
    switch (typ(t))
    {
      case t_INT: break;
      case t_FRAC:
        if (!d) d = gel(t,2); else d = lcmii(d, gel(t,2));
        break;
      default: pari_err_TYPE("check_nfelt", x);
    }
  }
  *den = d;
}

GEN
vecmodii(GEN a, GEN b)
{
  long i, l;
  GEN c = cgetg_copy(a, &l);
  for (i = 1; i < l; i++) gel(c,i) = modii(gel(a,i), gel(b,i));
  return c;
}

/* Given x (not necessarily integral), and bid as output by zidealstarinit,
 * compute the vector of components on the generators bid[2].
 * Assume (x,bid) = 1 and sgn is either NULL or nfsign_arch(x, bid) */
GEN
ideallog_sgn(GEN nf, GEN x, GEN sgn, GEN bid)
{
  pari_sp av;
  long lcyc;
  GEN den, cyc, y;

  nf = checknf(nf); checkbid(bid);
  cyc = bid_get_cyc(bid);
  lcyc = lg(cyc); if (lcyc == 1) return cgetg(1, t_COL);
  av = avma;
  if (typ(x) == t_MAT) {
    if (lg(x) == 1) return zerocol(lcyc-1); /* x = 1 */
    y = famat_zlog(nf, x, sgn, bid);
    goto END;
  }
  x = nf_to_scalar_or_basis(nf, x);
  switch(typ(x))
  {
    case t_INT:
      den = NULL;
      break;
    case t_FRAC:
      den = gel(x,2);
      x = gel(x,1);
      break;
    default: /* case t_COL: */
      check_nfelt(x, &den);
      if (den) x = Q_muli_to_int(x, den);
  }
  if (den)
  {
    x = mkmat2(mkcol2(x, den), mkcol2(gen_1, gen_m1));
    y = famat_zlog(nf, x, sgn, bid);
  }
  else
  {
    zlog_S S; init_zlog_bid(&S, bid);
    y = zlog(nf, x, sgn, &S);
  }
END:
  y = ZM_ZC_mul(gel(bid,5), y);
  return gerepileupto(av, vecmodii(y, cyc));
}
GEN
ideallog(GEN nf, GEN x, GEN bid) { return ideallog_sgn(nf, x, NULL, bid); }

/*************************************************************************/
/**                                                                     **/
/**               JOIN BID STRUCTURES, IDEAL LISTS                      **/
/**                                                                     **/
/*************************************************************************/

/* bid1, bid2: for coprime modules m1 and m2 (without arch. part).
 * Output: bid [[m1 m2,arch],[h,[cyc],[gen]],idealfact,[liste],U] for m1 m2 */
static GEN
join_bid(GEN nf, GEN bid1, GEN bid2)
{
  pari_sp av = avma;
  long i, nbgen, lx, lx1,lx2, l1,l2;
  GEN I1,I2, G1,G2, fa1,fa2, lists1,lists2, cyc1,cyc2;
  GEN lists, fa, U, cyc, y, u1 = NULL, x, gen;

  I1 = bid_get_ideal(bid1);
  I2 = bid_get_ideal(bid2);
  if (gequal1(gcoeff(I1,1,1))) return bid2; /* frequent trivial case */
  G1 = bid_get_grp(bid1);
  G2 = bid_get_grp(bid2);
  fa1= gel(bid1,3);
  fa2= gel(bid2,3); x = idealmul(nf, I1,I2);
  fa = famat_mul_shallow(fa1, fa2);
  lists1 = gel(bid1,4); lx1 = lg(lists1);
  lists2 = gel(bid2,4); lx2 = lg(lists2);
  /* concat (lists1 - last elt [nfarchstar]) + lists2 */
  lx = lx1+lx2-2; lists = cgetg(lx,t_VEC);
  for (i=1; i<lx1-1; i++) gel(lists,i) = gel(lists1,i);
  for (   ; i<lx; i++)    gel(lists,i) = gel(lists2,i-lx1+2);

  cyc1 = abgrp_get_cyc(G1); l1 = lg(cyc1);
  cyc2 = abgrp_get_cyc(G2); l2 = lg(cyc2);
  gen = (lg(G1)>3 && lg(G2)>3)? gen_1: NULL;
  nbgen = l1+l2-2;
  cyc = ZM_snf_group(diagonal_shallow(shallowconcat(cyc1,cyc2)),
                     &U, gen? &u1: NULL);
  if (nbgen) {
    GEN U1 = gel(bid1,5), U2 = gel(bid2,5);
    U1 = l1 == 1? zeromat(nbgen,lg(U1)-1): ZM_mul(vecslice(U, 1, l1-1),   U1);
    U2 = l2 == 1? zeromat(nbgen,lg(U2)-1): ZM_mul(vecslice(U, l1, nbgen), U2);
    U = shallowconcat(U1, U2);
  }
  else
    U = zeromat(0, lx-2);

  if (gen)
  {
    GEN mu,mv, u,v = idealaddtoone_i(nf,I2,I1);
    mv = zk_scalar_or_multable(nf, v);
    if (typ(mv) == t_INT)
    {
      mu = u = subui(1,mv);
      v = mv;
    }
    else
    {
      u = unnf_minus_x(v);
      mu = RgM_Rg_add(ZM_neg(mv), gen_1); /* mult by u = 1-v */
    }
    gen = shallowconcat(makeprimetoidealvec(x,u,mv, abgrp_get_gen(G1)),
                        makeprimetoidealvec(x,v,mu, abgrp_get_gen(G2)));
  }
  y = cgetg(6,t_VEC);
  gel(y,1) = mkvec2(x, bid_get_arch(bid1));
  gel(y,3) = fa;
  gel(y,4) = lists;
  gel(y,5) = U;
  add_grp(nf, u1, cyc, gen, y);
  return gerepilecopy(av,y);
}

typedef struct _ideal_data {
  GEN nf, emb, L, pr, prL, arch, sgnU;
} ideal_data;

/* z <- ( z | f(v[i])_{i=1..#v} ) */
static void
concat_join(GEN *pz, GEN v, GEN (*f)(ideal_data*,GEN), ideal_data *data)
{
  long i, nz, lv = lg(v);
  GEN z, Z;
  if (lv == 1) return;
  z = *pz; nz = lg(z)-1;
  *pz = Z = cgetg(lv + nz, typ(z));
  for (i = 1; i <=nz; i++) gel(Z,i) = gel(z,i);
  Z += nz;
  for (i = 1; i < lv; i++) gel(Z,i) = f(data, gel(v,i));
}
static GEN
join_idealinit(ideal_data *D, GEN x) {
  return join_bid(D->nf, x, D->prL);
}
static GEN
join_ideal(ideal_data *D, GEN x) {
  return idealmulpowprime(D->nf, x, D->pr, D->L);
}
static GEN
join_unit(ideal_data *D, GEN x) {
  return mkvec2(join_idealinit(D, gel(x,1)), vconcat(gel(x,2), D->emb));
}

/* compute matrix of zlogs of units */
GEN
zlog_units(GEN nf, GEN U, GEN sgnU, GEN bid)
{
  long j, l = lg(U);
  GEN m = cgetg(l, t_MAT);
  zlog_S S; init_zlog_bid(&S, bid);
  for (j = 1; j < l; j++)
    gel(m,j) = zlog(nf, gel(U,j), vecsmallpermute(gel(sgnU,j), S.archp), &S);
  return m;
}
/* compute matrix of zlogs of units, assuming S.archp = [] */
GEN
zlog_units_noarch(GEN nf, GEN U, GEN bid)
{
  long j, l = lg(U);
  GEN m = cgetg(l, t_MAT), empty = cgetg(1, t_COL);
  zlog_S S; init_zlog_bid(&S, bid);
  for (j = 1; j < l; j++) gel(m,j) = zlog(nf, gel(U,j), empty, &S);
  return m;
}

/* calcule la matrice des zlog des unites */
static GEN
zlog_unitsarch(GEN sgnU, GEN bid)
{
  GEN lists = gel(bid,4), arch = gmael(bid,1,2);
  GEN listslast = gel(lists,lg(lists)-1);
  GEN m = rowpermute(sgnU, vec01_to_indices(arch));
  return Flm_mul(gel(listslast,3), m, 2);
}

/*  flag & nf_GEN : generators, otherwise no
 *  flag &2 : units, otherwise no
 *  flag &4 : ideals in HNF, otherwise bid */
static GEN
Ideallist(GEN bnf, ulong bound, long flag)
{
  const long do_units = flag & 2, big_id = !(flag & 4);
  const long istar_flag = (flag & nf_GEN) | nf_INIT;
  pari_sp av, av0 = avma;
  long i, j, l;
  GEN nf, z, p, fa, id, BOUND, U, empty = cgetg(1,t_VEC);
  forprime_t S;
  ideal_data ID;
  GEN (*join_z)(ideal_data*, GEN) =
    do_units? &join_unit
              : (big_id? &join_idealinit: &join_ideal);

  nf = checknf(bnf);
  if ((long)bound <= 0) return empty;
  id = matid(nf_get_degree(nf));
  if (big_id) id = Idealstar(nf,id, istar_flag);

  /* z[i] will contain all "objects" of norm i. Depending on flag, this means
   * an ideal, a bid, or a couple [bid, log(units)]. Such objects are stored
   * in vectors, computed one primary component at a time; join_z
   * reconstructs the global object */
  BOUND = utoipos(bound);
  z = cgetg(bound+1,t_VEC);
  if (do_units) {
    U = init_units(bnf);
    gel(z,1) = mkvec( mkvec2(id, zlog_units_noarch(nf, U, id)) );
  } else {
    U = NULL; /* -Wall */
    gel(z,1) = mkvec(id);
  }
  for (i=2; i<=(long)bound; i++) gel(z,i) = empty;
  ID.nf = nf;

  p = cgetipos(3);
  u_forprime_init(&S, 2, bound);
  av = avma;
  while ((p[2] = u_forprime_next(&S)))
  {
    if (DEBUGLEVEL>1) { err_printf("%ld ",p[2]); err_flush(); }
    fa = idealprimedec_limit_norm(nf, p, BOUND);
    for (j=1; j<lg(fa); j++)
    {
      GEN pr = gel(fa,j), z2;
      ulong q, Q = upowuu(p[2], pr_get_f(pr));

      z2 = leafcopy(z);
      q = Q;
      ID.pr = ID.prL = pr;
      for (l=1; Q <= bound; l++, Q *= q) /* add pr^l */
      {
        ulong iQ;
        ID.L = utoipos(l);
        if (big_id) {
          if (l > 1) ID.prL = idealpow(nf,pr,ID.L);
          ID.prL = Idealstar(nf,ID.prL, istar_flag);
          if (do_units) ID.emb = zlog_units_noarch(nf, U, ID.prL);
        }
        for (iQ = Q,i = 1; iQ <= bound; iQ += Q,i++)
          concat_join(&gel(z,iQ), gel(z2,i), join_z, &ID);
      }
    }
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"Ideallist");
      z = gerepilecopy(av, z);
    }
  }
  if (do_units) for (i = 1; i < lg(z); i++)
  {
    GEN s = gel(z,i);
    long l = lg(s);
    for (j = 1; j < l; j++) {
      GEN v = gel(s,j), bid = gel(v,1);
      gel(v,2) = ZM_mul(gel(bid,5), gel(v,2));
    }
  }
  return gerepilecopy(av0, z);
}
GEN
ideallist0(GEN bnf,long bound, long flag) {
  if (flag<0 || flag>4) pari_err_FLAG("ideallist");
  return Ideallist(bnf,bound,flag);
}
GEN
ideallist(GEN bnf,long bound) { return Ideallist(bnf,bound,4); }

/* bid1 = for module m1 (without arch. part), arch = archimedean part.
 * Output: bid [[m1,arch],[h,[cyc],[gen]],idealfact,[liste],U] for m1.arch */
static GEN
join_bid_arch(GEN nf, GEN bid1, GEN arch)
{
  pari_sp av = avma;
  GEN f1, G1, fa1, U;
  GEN lists, cyc, y, u1 = NULL, x, sarch, gen;

  checkbid(bid1);
  f1 = gel(bid1,1); G1 = gel(bid1,2); fa1 = gel(bid1,3);
  x = gel(f1,1);
  sarch = nfarchstar(nf, x, arch);
  lists = leafcopy(gel(bid1,4));
  gel(lists,lg(lists)-1) = sarch;

  gen = (lg(G1)>3)? gen_1: NULL;
  cyc = diagonal_shallow(shallowconcat(gel(G1,2), gel(sarch,1)));
  cyc = ZM_snf_group(cyc, &U, gen? &u1: NULL);
  if (gen) gen = shallowconcat(gel(G1,3), gel(sarch,2));
  y = cgetg(6,t_VEC);
  gel(y,1) = mkvec2(x, arch);
  gel(y,3) = fa1;
  gel(y,4) = lists;
  gel(y,5) = U;
  add_grp(nf, u1, cyc, gen, y);
  return gerepilecopy(av,y);
}
static GEN
join_arch(ideal_data *D, GEN x) {
  return join_bid_arch(D->nf, x, D->arch);
}
static GEN
join_archunit(ideal_data *D, GEN x) {
  GEN bid = join_arch(D, gel(x,1)), U = gel(x,2);
  U = ZM_mul(gel(bid,5), vconcat(U, zm_to_ZM(zlog_unitsarch(D->sgnU, bid))));
  return mkvec2(bid, U);
}

/* L from ideallist, add archimedean part */
GEN
ideallistarch(GEN bnf, GEN L, GEN arch)
{
  pari_sp av;
  long i, j, l = lg(L), lz;
  GEN v, z, V;
  ideal_data ID;
  GEN (*join_z)(ideal_data*, GEN);

  if (typ(L) != t_VEC) pari_err_TYPE("ideallistarch",L);
  if (l == 1) return cgetg(1,t_VEC);
  z = gel(L,1);
  if (typ(z) != t_VEC) pari_err_TYPE("ideallistarch",z);
  z = gel(z,1); /* either a bid or [bid,U] */
  if (lg(z) == 3) { /* the latter: do units */
    if (typ(z) != t_VEC) pari_err_TYPE("ideallistarch",z);
    ID.sgnU = nfsign_units(bnf, NULL, 1);
    join_z = &join_archunit;
  } else
    join_z = &join_arch;
  ID.nf = checknf(bnf);
  ID.arch = vec01_to_indices(arch);
  av = avma; V = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    z = gel(L,i); lz = lg(z);
    gel(V,i) = v = cgetg(lz,t_VEC);
    for (j=1; j<lz; j++) gel(v,j) = join_z(&ID, gel(z,j));
  }
  return gerepilecopy(av,V);
}
