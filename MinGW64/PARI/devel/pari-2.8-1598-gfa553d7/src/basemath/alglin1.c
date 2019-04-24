/* Copyright (C) 2000, 2012  The PARI group.

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
/**                         LINEAR ALGEBRA                         **/
/**                          (first part)                          **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

/*******************************************************************/
/*                                                                 */
/*                         GEREPILE                                */
/*                                                                 */
/*******************************************************************/

static void
gerepile_mat(pari_sp av, pari_sp tetpil, GEN x, long k, long m, long n, long t)
{
  pari_sp A, bot = pari_mainstack->bot;
  long u, i;
  size_t dec;

  (void)gerepile(av,tetpil,NULL); dec = av-tetpil;

  for (u=t+1; u<=m; u++)
  {
    A = (pari_sp)coeff(x,u,k);
    if (A < av && A >= bot) coeff(x,u,k) += dec;
  }
  for (i=k+1; i<=n; i++)
    for (u=1; u<=m; u++)
    {
      A = (pari_sp)coeff(x,u,i);
      if (A < av && A >= bot) coeff(x,u,i) += dec;
    }
}

static void
gen_gerepile_gauss_ker(GEN x, long k, long t, pari_sp av, void *E, GEN (*copy)(void*, GEN))
{
  pari_sp tetpil = avma;
  long u,i, n = lg(x)-1, m = n? nbrows(x): 0;

  if (DEBUGMEM > 1) pari_warn(warnmem,"gauss_pivot_ker. k=%ld, n=%ld",k,n);
  for (u=t+1; u<=m; u++) gcoeff(x,u,k) = copy(E,gcoeff(x,u,k));
  for (i=k+1; i<=n; i++)
    for (u=1; u<=m; u++) gcoeff(x,u,i) = copy(E,gcoeff(x,u,i));
  gerepile_mat(av,tetpil,x,k,m,n,t);
}

/* special gerepile for huge matrices */

#define COPY(x) {\
  GEN _t = (x); if (!is_universal_constant(_t)) x = gcopy(_t); \
}

INLINE GEN
_copy(void *E, GEN x)
{
  (void) E; COPY(x);
  return x;
}

static void
gerepile_gauss_ker(GEN x, long k, long t, pari_sp av)
{
  gen_gerepile_gauss_ker(x, k, t, av, NULL, &_copy);
}

static void
gerepile_gauss(GEN x,long k,long t,pari_sp av, long j, GEN c)
{
  pari_sp tetpil = avma, A, bot;
  long u,i, n = lg(x)-1, m = n? nbrows(x): 0;
  size_t dec;

  if (DEBUGMEM > 1) pari_warn(warnmem,"gauss_pivot. k=%ld, n=%ld",k,n);
  for (u=t+1; u<=m; u++)
    if (u==j || !c[u]) COPY(gcoeff(x,u,k));
  for (u=1; u<=m; u++)
    if (u==j || !c[u])
      for (i=k+1; i<=n; i++) COPY(gcoeff(x,u,i));

  (void)gerepile(av,tetpil,NULL); dec = av-tetpil;
  bot = pari_mainstack->bot;
  for (u=t+1; u<=m; u++)
    if (u==j || !c[u])
    {
      A=(pari_sp)coeff(x,u,k);
      if (A<av && A>=bot) coeff(x,u,k)+=dec;
    }
  for (u=1; u<=m; u++)
    if (u==j || !c[u])
      for (i=k+1; i<=n; i++)
      {
        A=(pari_sp)coeff(x,u,i);
        if (A<av && A>=bot) coeff(x,u,i)+=dec;
      }
}

/*******************************************************************/
/*                                                                 */
/*                         GENERIC                                 */
/*                                                                 */
/*******************************************************************/
GEN
gen_ker(GEN x, long deplin, void *E, const struct bb_field *ff)
{
  pari_sp av0 = avma, av, tetpil;
  GEN y, c, d;
  long i, j, k, r, t, n, m;

  n=lg(x)-1; if (!n) return cgetg(1,t_MAT);
  m=nbrows(x); r=0;
  x = RgM_shallowcopy(x);
  c = zero_zv(m);
  d=new_chunk(n+1);
  av=avma;
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        gcoeff(x,j,k) = ff->red(E, gcoeff(x,j,k));
        if (!ff->equal0(gcoeff(x,j,k))) break;
      }
    if (j>m)
    {
      if (deplin)
      {
        GEN c = cgetg(n+1, t_COL), g0 = ff->s(E,0), g1=ff->s(E,1);
        for (i=1; i<k; i++) gel(c,i) = ff->red(E, gcoeff(x,d[i],k));
        gel(c,k) = g1; for (i=k+1; i<=n; i++) gel(c,i) = g0;
        return gerepileupto(av0, c);
      }
      r++; d[k]=0;
      for(j=1; j<k; j++)
        if (d[j]) gcoeff(x,d[j],k) = gclone(gcoeff(x,d[j],k));
    }
    else
    {
      GEN piv = ff->neg(E,ff->inv(E,gcoeff(x,j,k)));
      c[j] = k; d[k] = j;
      gcoeff(x,j,k) = ff->s(E,-1);
      for (i=k+1; i<=n; i++) gcoeff(x,j,i) = ff->red(E,ff->mul(E,piv,gcoeff(x,j,i)));
      for (t=1; t<=m; t++)
      {
        if (t==j) continue;

        piv = ff->red(E,gcoeff(x,t,k));
        if (ff->equal0(piv)) continue;

        gcoeff(x,t,k) = ff->s(E,0);
        for (i=k+1; i<=n; i++)
           gcoeff(x,t,i) = ff->add(E, gcoeff(x,t,i), ff->mul(E,piv,gcoeff(x,j,i)));
        if (gc_needed(av,1))
          gen_gerepile_gauss_ker(x,k,t,av,E,ff->red);
      }
    }
  }
  if (deplin) { avma = av0; return NULL; }

  tetpil=avma; y=cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN C = cgetg(n+1,t_COL);
    GEN g0 = ff->s(E,0), g1 = ff->s(E,1);
    gel(y,j) = C; while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i])
      {
        GEN p1=gcoeff(x,d[i],k);
        gel(C,i) = ff->red(E,p1); gunclone(p1);
      }
      else
        gel(C,i) = g0;
    gel(C,k) = g1; for (i=k+1; i<=n; i++) gel(C,i) = g0;
  }
  return gerepile(av0,tetpil,y);
}

GEN
gen_Gauss_pivot(GEN x, long *rr, void *E, const struct bb_field *ff)
{
  pari_sp av;
  GEN c, d;
  long i, j, k, r, t, m, n = lg(x)-1;

  if (!n) { *rr = 0; return NULL; }

  m=nbrows(x); r=0;
  d = cgetg(n+1, t_VECSMALL);
  x = RgM_shallowcopy(x);
  c = zero_zv(m);
  av=avma;
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        gcoeff(x,j,k) = ff->red(E,gcoeff(x,j,k));
        if (!ff->equal0(gcoeff(x,j,k))) break;
      }
    if (j>m) { r++; d[k]=0; }
    else
    {
      GEN piv = ff->neg(E,ff->inv(E,gcoeff(x,j,k)));
      GEN g0 = ff->s(E,0);
      c[j] = k; d[k] = j;
      for (i=k+1; i<=n; i++) gcoeff(x,j,i) = ff->red(E,ff->mul(E,piv,gcoeff(x,j,i)));
      for (t=1; t<=m; t++)
      {
        if (c[t]) continue; /* already a pivot on that line */

        piv = ff->red(E,gcoeff(x,t,k));
        if (ff->equal0(piv)) continue;
        gcoeff(x,t,k) = g0;
        for (i=k+1; i<=n; i++)
          gcoeff(x,t,i) = ff->add(E,gcoeff(x,t,i), ff->mul(E,piv,gcoeff(x,j,i)));
        if (gc_needed(av,1))
          gerepile_gauss(x,k,t,av,j,c);
      }
      for (i=k; i<=n; i++) gcoeff(x,j,i) = g0; /* dummy */
    }
  }
  *rr = r; avma = (pari_sp)d; return d;
}

GEN
gen_det(GEN a, void *E, const struct bb_field *ff)
{
  pari_sp av = avma;
  long i,j,k, s = 1, nbco = lg(a)-1;
  GEN q, x = ff->s(E,1);
  a = RgM_shallowcopy(a);
  for (i=1; i<nbco; i++)
  {
    for(k=i; k<=nbco; k++)
    {
      gcoeff(a,k,i) = ff->red(E,gcoeff(a,k,i));
      if (!ff->equal0(gcoeff(a,k,i))) break;
    }
    if (k > nbco) return gerepileupto(av, gcoeff(a,i,i));
    if (k != i)
    { /* exchange the lines s.t. k = i */
      for (j=i; j<=nbco; j++) swap(gcoeff(a,i,j), gcoeff(a,k,j));
      s = -s;
    }
    q = gcoeff(a,i,i);

    x = ff->red(E,ff->mul(E,x,q));
    q = ff->inv(E,q);
    for (k=i+1; k<=nbco; k++)
    {
      GEN m = ff->red(E,gcoeff(a,i,k));
      if (ff->equal0(m)) continue;

      m = ff->neg(E, ff->mul(E,m, q));
      for (j=i+1; j<=nbco; j++)
      {
        gcoeff(a,j,k) = ff->add(E, gcoeff(a,j,k), ff->mul(E,m,gcoeff(a,j,i)));
        if (gc_needed(av,1))
        {
          if(DEBUGMEM>1) pari_warn(warnmem,"det. col = %ld",i);
          gerepileall(av,4, &a,&x,&q,&m);
        }
      }
    }
  }
  if (s < 0) x = ff->neg(E,x);
  return gerepileupto(av, ff->red(E,ff->mul(E, x, gcoeff(a,nbco,nbco))));
}

INLINE void
_gen_addmul(GEN b, long k, long i, GEN m, void *E, const struct bb_field *ff)
{
  gel(b,i) = ff->red(E,gel(b,i));
  gel(b,k) = ff->add(E,gel(b,k), ff->mul(E,m, gel(b,i)));
}

static GEN
_gen_get_col(GEN a, GEN b, long li, void *E, const struct bb_field *ff)
{
  GEN u = cgetg(li+1,t_COL);
  pari_sp av = avma;
  long i, j;

  gel(u,li) = gerepileupto(av, ff->red(E,ff->mul(E,gel(b,li), gcoeff(a,li,li))));
  for (i=li-1; i>0; i--)
  {
    pari_sp av = avma;
    GEN m = gel(b,i);
    for (j=i+1; j<=li; j++) m = ff->add(E,m, ff->neg(E,ff->mul(E,gcoeff(a,i,j), gel(u,j))));
    m = ff->red(E, m);
    gel(u,i) = gerepileupto(av, ff->red(E,ff->mul(E,m, gcoeff(a,i,i))));
  }
  return u;
}

GEN
gen_Gauss(GEN a, GEN b, void *E, const struct bb_field *ff)
{
  long i, j, k, li, bco, aco;
  GEN u, g0 = ff->s(E,0);
  pari_sp av = avma;
  a = RgM_shallowcopy(a);
  b = RgM_shallowcopy(b);
  aco = lg(a)-1; bco = lg(b)-1; li = nbrows(a);
  for (i=1; i<=aco; i++)
  {
    GEN invpiv;
    for (k = i; k <= li; k++)
    {
      GEN piv = ff->red(E,gcoeff(a,k,i));
      if (!ff->equal0(piv)) { gcoeff(a,k,i) = ff->inv(E,piv); break; }
      gcoeff(a,k,i) = g0;
    }
    /* found a pivot on line k */
    if (k > li) return NULL;
    if (k != i)
    { /* swap lines so that k = i */
      for (j=i; j<=aco; j++) swap(gcoeff(a,i,j), gcoeff(a,k,j));
      for (j=1; j<=bco; j++) swap(gcoeff(b,i,j), gcoeff(b,k,j));
    }
    if (i == aco) break;

    invpiv = gcoeff(a,i,i); /* 1/piv mod p */
    for (k=i+1; k<=li; k++)
    {
      GEN m = ff->red(E,gcoeff(a,k,i)); gcoeff(a,k,i) = g0;
      if (ff->equal0(m)) continue;

      m = ff->red(E,ff->neg(E,ff->mul(E,m, invpiv)));
      for (j=i+1; j<=aco; j++) _gen_addmul(gel(a,j),k,i,m,E,ff);
      for (j=1  ; j<=bco; j++) _gen_addmul(gel(b,j),k,i,m,E,ff);
    }
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"gen_Gauss. i=%ld",i);
      gerepileall(av,2, &a,&b);
    }
  }

  if(DEBUGLEVEL>4) err_printf("Solving the triangular system\n");
  u = cgetg(bco+1,t_MAT);
  for (j=1; j<=bco; j++) gel(u,j) = _gen_get_col(a, gel(b,j), aco, E, ff);
  return u;
}

/* compatible t_MAT * t_COL, lgA = lg(A) = lg(B) > 1, l = lgcols(A) */
static GEN
gen_matcolmul_i(GEN A, GEN B, ulong lgA, ulong l,
                void *E, const struct bb_field *ff)
{
  GEN C = cgetg(l, t_COL);
  ulong i;
  for (i = 1; i < l; i++) {
    pari_sp av = avma;
    GEN e = ff->mul(E, gcoeff(A, i, 1), gel(B, 1));
    ulong k;
    for(k = 2; k < lgA; k++)
      e = ff->add(E, e, ff->mul(E, gcoeff(A, i, k), gel(B, k)));
    gel(C, i) = gerepileupto(av, ff->red(E, e));
  }
  return C;
}

GEN
gen_matcolmul(GEN A, GEN B, void *E, const struct bb_field *ff)
{
  ulong lgA = lg(A);
  if (lgA != (ulong)lg(B))
    pari_err_OP("operation 'gen_matcolmul'", A, B);
  if (lgA == 1)
    return cgetg(1, t_COL);
  return gen_matcolmul_i(A, B, lgA, lgcols(A), E, ff);
}

GEN
gen_matmul(GEN A, GEN B, void *E, const struct bb_field *ff)
{
  ulong j, l, lgA, lgB = lg(B);
  GEN C;
  if (lgB == 1)
    return cgetg(1, t_MAT);
  lgA = lg(A);
  if (lgA != (ulong)lgcols(B))
    pari_err_OP("operation 'gen_matmul'", A, B);
  if (lgA == 1)
    return zeromat(0, lgB - 1);
  l = lgcols(A);
  C = cgetg(lgB, t_MAT);
  for(j = 1; j < lgB; j++)
    gel(C, j) = gen_matcolmul_i(A, gel(B, j), lgA, l, E, ff);
  return C;
}

static GEN
image_from_pivot(GEN x, GEN d, long r)
{
  GEN y;
  long j, k;

  if (!d) return gcopy(x);
  /* d left on stack for efficiency */
  r = lg(x)-1 - r; /* = dim Im(x) */
  y = cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; k++)
    if (d[k]) gel(y,j++) = gcopy(gel(x,k));
  return y;
}

/*******************************************************************/
/*                                                                 */
/*                    LINEAR ALGEBRA MODULO P                      */
/*                                                                 */
/*******************************************************************/

static long
F2v_find_nonzero(GEN x0, GEN mask0, long l, long m)
{
  ulong *x = (ulong *)x0+2, *mask = (ulong *)mask0+2, e;
  long i, j;
  for (i = 0; i < l; i++)
  {
    e = *x++ & *mask++;
    if (e)
      for (j = 1; ; j++, e >>= 1) if (e & 1uL) return i*BITS_IN_LONG+j;
  }
  return m+1;
}

/* in place, destroy x */
GEN
F2m_ker_sp(GEN x, long deplin)
{
  GEN y, c, d;
  long i, j, k, l, r, m, n;

  n = lg(x)-1;
  m = mael(x,1,1); r=0;

  d = cgetg(n+1, t_VECSMALL);
  c = zero_F2v(m);
  l = lg(c)-1;
  for (i = 2; i <= l; i++) c[i] = -1;
  if (remsBIL(m)) c[l] = (1uL<<remsBIL(m))-1uL;
  for (k=1; k<=n; k++)
  {
    GEN xk = gel(x,k);
    j = F2v_find_nonzero(xk, c, l, m);
    if (j>m)
    {
      if (deplin) {
        GEN c = zero_F2v(n);
        for (i=1; i<k; i++)
          if (F2v_coeff(xk, d[i]))
            F2v_set(c, i);
        F2v_set(c, k);
        return c;
      }
      r++; d[k] = 0;
    }
    else
    {
      F2v_clear(c,j); d[k] = j;
      F2v_clear(xk, j);
      for (i=k+1; i<=n; i++)
      {
        GEN xi = gel(x,i);
        if (F2v_coeff(xi,j)) F2v_add_inplace(xi, xk);
      }
      F2v_set(xk, j);
    }
  }
  if (deplin) return NULL;

  y = zero_F2m_copy(n,r);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN C = gel(y,j); while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i] && F2m_coeff(x,d[i],k))
        F2v_set(C,i);
    F2v_set(C, k);
  }
  return y;
}

static void /* assume m < p */
_Fl_submul(GEN b, long k, long i, ulong m, ulong p)
{
  uel(b,k) = Fl_sub(uel(b,k), Fl_mul(m, uel(b,i), p), p);
}
static void /* same m = 1 */
_Fl_sub(GEN b, long k, long i, ulong p)
{
  uel(b,k) = Fl_sub(uel(b,k), uel(b,i), p);
}
static void /* assume m < p && SMALL_ULONG(p) && (! (b[i] & b[k] & HIGHMASK)) */
_Fl_addmul_OK(GEN b, long k, long i, ulong m, ulong p)
{
  uel(b,k) += m * uel(b,i);
  if (uel(b,k) & HIGHMASK) uel(b,k) %= p;
}
static void /* assume SMALL_ULONG(p) && (! (b[i] & b[k] & HIGHMASK)) */
_Fl_add_OK(GEN b, long k, long i, ulong p)
{
  uel(b,k) += uel(b,i);
  if (uel(b,k) & HIGHMASK) uel(b,k) %= p;
}
static void /* assume m < p */
_Fl_addmul(GEN b, long k, long i, ulong m, ulong p)
{
  uel(b,i) %= p;
  uel(b,k) = Fl_add(uel(b,k), Fl_mul(m, uel(b,i), p), p);
}
static void /* same m = 1 */
_Fl_add(GEN b, long k, long i, ulong p)
{
  uel(b,k) = Fl_add(uel(b,k), uel(b,i), p);
}

/* in place, destroy x */
GEN
Flm_ker_sp(GEN x, ulong p, long deplin)
{
  GEN y, c, d;
  long i, j, k, r, t, m, n;
  ulong a;
  const int OK_ulong = SMALL_ULONG(p);

  n = lg(x)-1;
  m=nbrows(x); r=0;

  c = zero_zv(m);
  d = new_chunk(n+1);
  a = 0; /* for gcc -Wall */
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        a = ucoeff(x,j,k) % p;
        if (a) break;
      }
    if (j > m)
    {
      if (deplin) {
        c = cgetg(n+1, t_VECSMALL);
        for (i=1; i<k; i++) c[i] = ucoeff(x,d[i],k) % p;
        c[k] = 1; for (i=k+1; i<=n; i++) c[i] = 0;
        return c;
      }
      r++; d[k] = 0;
    }
    else
    {
      ulong piv = p - Fl_inv(a, p); /* -1/a */
      c[j] = k; d[k] = j;
      ucoeff(x,j,k) = p-1;
      if (piv == 1) { /* nothing */ }
      else if (OK_ulong)
        for (i=k+1; i<=n; i++) ucoeff(x,j,i) = (piv * ucoeff(x,j,i)) % p;
      else
        for (i=k+1; i<=n; i++) ucoeff(x,j,i) = Fl_mul(piv, ucoeff(x,j,i), p);
      for (t=1; t<=m; t++)
      {
        if (t == j) continue;

        piv = ( ucoeff(x,t,k) %= p );
        if (!piv) continue;

        if (OK_ulong)
        {
          if (piv == 1)
            for (i=k+1; i<=n; i++) _Fl_add_OK(gel(x,i),t,j, p);
          else
            for (i=k+1; i<=n; i++) _Fl_addmul_OK(gel(x,i),t,j,piv, p);
        } else {
          if (piv == 1)
            for (i=k+1; i<=n; i++) _Fl_add(gel(x,i),t,j,p);
          else
            for (i=k+1; i<=n; i++) _Fl_addmul(gel(x,i),t,j,piv,p);
        }
      }
    }
  }
  if (deplin) return NULL;

  y = cgetg(r+1, t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN C = cgetg(n+1, t_VECSMALL);

    gel(y,j) = C; while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i])
        uel(C,i) = ucoeff(x,d[i],k) % p;
      else
        uel(C,i) = 0UL;
    uel(C,k) = 1UL; for (i=k+1; i<=n; i++) uel(C,i) = 0UL;
  }
  return y;
}

GEN
FpM_intersect(GEN x, GEN y, GEN p)
{
  pari_sp av = avma;
  long j, lx = lg(x);
  GEN z;

  if (lx==1 || lg(y)==1) return cgetg(1,t_MAT);
  z = FpM_ker(shallowconcat(x,y), p);
  for (j=lg(z)-1; j; j--) setlg(gel(z,j),lx);
  return gerepileupto(av, FpM_mul(x,z,p));
}

/* not memory clean */
GEN
F2m_ker(GEN x) { return F2m_ker_sp(F2m_copy(x), 0); }
GEN
F2m_deplin(GEN x) { return F2m_ker_sp(F2m_copy(x), 1); }
GEN
Flm_ker(GEN x, ulong p) { return Flm_ker_sp(Flm_copy(x), p, 0); }
GEN
Flm_deplin(GEN x, ulong p) { return Flm_ker_sp(Flm_copy(x), p, 1); }

ulong
F2m_det_sp(GEN x) { return !F2m_ker_sp(x, 1); }

ulong
F2m_det(GEN x)
{
  pari_sp av = avma;
  ulong d = F2m_det_sp(F2m_copy(x));
  avma = av; return d;
}

/* in place, destroy a, SMALL_ULONG(p) is TRUE */
static ulong
Flm_det_sp_OK(GEN a, long nbco, ulong p)
{
  long i,j,k, s = 1;
  ulong q, x = 1;

  for (i=1; i<nbco; i++)
  {
    for(k=i; k<=nbco; k++)
    {
      ulong c = ucoeff(a,k,i) % p;
      ucoeff(a,k,i) = c;
      if (c) break;
    }
    for(j=k+1; j<=nbco; j++) ucoeff(a,j,i) %= p;
    if (k > nbco) return ucoeff(a,i,i);
    if (k != i)
    { /* exchange the lines s.t. k = i */
      for (j=i; j<=nbco; j++) lswap(ucoeff(a,i,j), ucoeff(a,k,j));
      s = -s;
    }
    q = ucoeff(a,i,i);

    if (x & HIGHMASK) x %= p;
    x *= q;
    q = Fl_inv(q,p);
    for (k=i+1; k<=nbco; k++)
    {
      ulong m = ucoeff(a,i,k) % p;
      if (!m) continue;

      m = p - ((m*q)%p);
      for (j=i+1; j<=nbco; j++)
      {
        ulong c = ucoeff(a,j,k);
        if (c & HIGHMASK) c %= p;
        ucoeff(a,j,k) = c  + m*ucoeff(a,j,i);
      }
    }
  }
  if (x & HIGHMASK) x %= p;
  q = ucoeff(a,nbco,nbco);
  if (q & HIGHMASK) q %= p;
  x = (x*q) % p;
  if (s < 0 && x) x = p - x;
  return x;
}
/* in place, destroy a */
ulong
Flm_det_sp(GEN a, ulong p)
{
  long i,j,k, s = 1, nbco = lg(a)-1;
  ulong q, x = 1;

  if (SMALL_ULONG(p)) return Flm_det_sp_OK(a, nbco, p);
  for (i=1; i<nbco; i++)
  {
    for(k=i; k<=nbco; k++)
      if (ucoeff(a,k,i)) break;
    if (k > nbco) return ucoeff(a,i,i);
    if (k != i)
    { /* exchange the lines s.t. k = i */
      for (j=i; j<=nbco; j++) lswap(ucoeff(a,i,j), ucoeff(a,k,j));
      s = -s;
    }
    q = ucoeff(a,i,i);

    x = Fl_mul(x,q,p);
    q = Fl_inv(q,p);
    for (k=i+1; k<=nbco; k++)
    {
      ulong m = ucoeff(a,i,k);
      if (!m) continue;

      m = Fl_mul(m, q, p);
      for (j=i+1; j<=nbco; j++)
        ucoeff(a,j,k) = Fl_sub(ucoeff(a,j,k), Fl_mul(m,ucoeff(a,j,i), p), p);
    }
  }
  if (s < 0) x = Fl_neg(x, p);
  return Fl_mul(x, ucoeff(a,nbco,nbco), p);
}

ulong
Flm_det(GEN x, ulong p)
{
  pari_sp av = avma;
  ulong d = Flm_det_sp(Flm_copy(x), p);
  avma = av; return d;
}

static GEN
FpM_init(GEN a, GEN p, ulong *pp)
{
  if (lgefint(p) == 3)
  {
    *pp = uel(p,2);
    return (*pp==2)? ZM_to_F2m(a): ZM_to_Flm(a, *pp);
  }
  *pp = 0; return a;
}
GEN
RgM_Fp_init(GEN a, GEN p, ulong *pp)
{
  if (lgefint(p) == 3)
  {
    *pp = uel(p,2);
    return (*pp==2)? RgM_to_F2m(a): RgM_to_Flm(a, *pp);
  }
  *pp = 0; return RgM_to_FpM(a,p);
}

static GEN
FpM_det_gen(GEN a, GEN p)
{
  void *E;
  const struct bb_field *S = get_Fp_field(&E,p);
  return gen_det(a, E, S);
}
GEN
FpM_det(GEN a, GEN p)
{
  pari_sp av = avma;
  ulong pp, d;
  a = FpM_init(a, p, &pp);
  switch(pp)
  {
  case 0: return FpM_det_gen(a, p);
  case 2: d = F2m_det_sp(a); break;
  default:d = Flm_det_sp(a,pp); break;
  }
  avma = av; return utoi(d);
}

/* Destroy x */
static GEN
F2m_gauss_pivot(GEN x, long *rr)
{
  GEN c, d;
  long i, j, k, l, r, m, n;

  n = lg(x)-1; if (!n) { *rr=0; return NULL; }
  m = mael(x,1,1); r=0;

  d = cgetg(n+1, t_VECSMALL);
  c = zero_F2v(m);
  l = lg(c)-1;
  for (i = 2; i <= l; i++) c[i] = -1;
  if (remsBIL(m)) c[l] = (1uL<<remsBIL(m))-1uL;
  for (k=1; k<=n; k++)
  {
    GEN xk = gel(x,k);
    j = F2v_find_nonzero(xk, c, l, m);
    if (j>m) { r++; d[k] = 0; }
    else
    {
      F2v_clear(c,j); d[k] = j;
      for (i=k+1; i<=n; i++)
      {
        GEN xi = gel(x,i);
        if (F2v_coeff(xi,j)) F2v_add_inplace(xi, xk);
      }
    }
  }

  *rr = r; avma = (pari_sp)d; return d;
}

/* Destroy x */
static GEN
Flm_gauss_pivot(GEN x, ulong p, long *rr)
{
  GEN c,d;
  long i,j,k,r,t,n,m;

  n=lg(x)-1; if (!n) { *rr=0; return NULL; }

  m=nbrows(x); r=0;
  d=cgetg(n+1,t_VECSMALL);
  c = zero_zv(m);
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        ucoeff(x,j,k) %= p;
        if (ucoeff(x,j,k)) break;
      }
    if (j>m) { r++; d[k]=0; }
    else
    {
      ulong piv = p - Fl_inv(ucoeff(x,j,k), p);
      c[j]=k; d[k]=j;
      for (i=k+1; i<=n; i++)
        ucoeff(x,j,i) = Fl_mul(piv, ucoeff(x,j,i), p);
      for (t=1; t<=m; t++)
        if (!c[t]) /* no pivot on that line yet */
        {
          piv = ucoeff(x,t,k);
          if (piv)
          {
            ucoeff(x,t,k) = 0;
            for (i=k+1; i<=n; i++)
              ucoeff(x,t,i) = Fl_add(ucoeff(x,t,i),
                                     Fl_mul(piv,ucoeff(x,j,i),p),p);
          }
        }
      for (i=k; i<=n; i++) ucoeff(x,j,i) = 0; /* dummy */
    }
  }
  *rr = r; avma = (pari_sp)d; return d;
}

static GEN
FpM_gauss_pivot_gen(GEN x, GEN p, long *rr)
{
  void *E;
  const struct bb_field *S = get_Fp_field(&E,p);
  return gen_Gauss_pivot(x, rr, E, S);
}
static GEN
FpM_gauss_pivot(GEN x, GEN p, long *rr)
{
  ulong pp;
  if (lg(x)==1) { *rr = 0; return NULL; }
  x = FpM_init(x, p, &pp);
  switch(pp)
  {
  case 0: return FpM_gauss_pivot_gen(x, p, rr);
  case 2: return F2m_gauss_pivot(x, rr);
  default:return Flm_gauss_pivot(x, pp, rr);
  }
}

GEN
FpM_image(GEN x, GEN p)
{
  long r;
  GEN d = FpM_gauss_pivot(x,p,&r); /* d left on stack for efficiency */
  return image_from_pivot(x,d,r);
}
GEN
Flm_image(GEN x, ulong p)
{
  long r;
  GEN d = Flm_gauss_pivot(Flm_copy(x),p,&r); /* d left on stack for efficiency */
  return image_from_pivot(x,d,r);
}
GEN
F2m_image(GEN x)
{
  long r;
  GEN d = F2m_gauss_pivot(F2m_copy(x),&r); /* d left on stack for efficiency */
  return image_from_pivot(x,d,r);
}

long
FpM_rank(GEN x, GEN p)
{
  pari_sp av = avma;
  long r;
  (void)FpM_gauss_pivot(x,p,&r);
  avma = av; return lg(x)-1 - r;
}
long
Flm_rank(GEN x, ulong p)
{
  pari_sp av = avma;
  long r;
  (void)Flm_gauss_pivot(Flm_copy(x),p,&r);
  avma = av; return lg(x)-1 - r;
}
long
F2m_rank(GEN x)
{
  pari_sp av = avma;
  long r;
  (void)F2m_gauss_pivot(F2m_copy(x),&r);
  avma = av; return lg(x)-1 - r;
}


static GEN
FlxqM_gauss_pivot(GEN x, GEN T, ulong p, long *rr)
{
  void *E;
  const struct bb_field *S = get_Flxq_field(&E, T, p);
  return gen_Gauss_pivot(x, rr, E, S);
}

GEN
FlxqM_image(GEN x, GEN T, ulong p)
{
  long r;
  GEN d = FlxqM_gauss_pivot(x,T,p,&r); /* d left on stack for efficiency */
  return image_from_pivot(x,d,r);
}

long
FlxqM_rank(GEN x, GEN T, ulong p)
{
  pari_sp av = avma;
  long r;
  (void)FlxqM_gauss_pivot(x,T,p,&r);
  avma = av; return lg(x)-1 - r;
}
GEN
FlxqM_det(GEN a, GEN T, ulong p)
{
  void *E;
  const struct bb_field *S = get_Flxq_field(&E, T, p);
  return gen_det(a, E, S);
}

GEN
FlxqM_FlxqC_mul(GEN A, GEN B, GEN T, ulong p) {
  void *E;
  const struct bb_field *ff = get_Flxq_field(&E, T, p);
  return gen_matcolmul(A, B, E, ff);
}

GEN
FlxqM_mul(GEN A, GEN B, GEN T, ulong p) {
  void *E;
  const struct bb_field *ff;
  long n = lg(A) - 1;

  if (n == 0)
    return cgetg(1, t_MAT);
  if (n > 1) {
    GEN C = FlxqM_mul_Kronecker(A, B, T, p);
    if (C != NULL)
      return C;
  }
  ff = get_Flxq_field(&E, T, p);
  return gen_matmul(A, B, E, ff);
}

GEN
F2xqM_det(GEN a, GEN T)
{
  void *E;
  const struct bb_field *S = get_F2xq_field(&E, T);
  return gen_det(a, E, S);
}

static GEN
F2xqM_gauss_gen(GEN a, GEN b, GEN T)
{
  void *E;
  const struct bb_field *S = get_F2xq_field(&E, T);
  return gen_Gauss(a, b, E, S);
}
GEN
F2xqM_inv(GEN a, GEN T)
{
  pari_sp av = avma;
  GEN u;
  if (lg(a) == 1) { avma = av; return cgetg(1, t_MAT); }
  u = F2xqM_gauss_gen(a, matid_F2xqM(nbrows(a),T), T);
  if (!u) { avma = av; return NULL; }
  return gerepilecopy(av, u);
}

GEN
F2xqM_F2xqC_mul(GEN A, GEN B, GEN T) {
  void *E;
  const struct bb_field *ff = get_F2xq_field(&E, T);
  return gen_matcolmul(A, B, E, ff);
}

GEN
F2xqM_mul(GEN A, GEN B, GEN T) {
  void *E;
  const struct bb_field *ff = get_F2xq_field(&E, T);
  return gen_matmul(A, B, E, ff);
}

static GEN
FqM_gauss_pivot_gen(GEN x, GEN T, GEN p, long *rr)
{
  void *E;
  const struct bb_field *S = get_Fq_field(&E,T,p);
  return gen_Gauss_pivot(x, rr, E, S);
}
static GEN
FqM_gauss_pivot(GEN x, GEN T, GEN p, long *rr)
{
  if (lg(x)==1) { *rr = 0; return NULL; }
  if (!T) return FpM_gauss_pivot(x, p, rr);
  if (lgefint(p) == 3)
  {
    pari_sp av = avma;
    ulong pp = uel(p,2);
    GEN Tp = ZXT_to_FlxT(T, pp);
    GEN d = FlxqM_gauss_pivot(FqM_to_FlxM(x, T, p), Tp, pp, rr);
    return d ? gerepileuptoleaf(av, d): d;
  }
  return FqM_gauss_pivot_gen(x, T, p, rr);
}

GEN
FqM_image(GEN x, GEN T, GEN p)
{
  long r;
  GEN d = FqM_gauss_pivot(x,T,p,&r); /* d left on stack for efficiency */
  return image_from_pivot(x,d,r);
}

long
FqM_rank(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  long r;
  (void)FqM_gauss_pivot(x,T,p,&r);
  avma = av; return lg(x)-1 - r;
}

GEN
FqM_det(GEN x, GEN T, GEN p)
{
  void *E;
  const struct bb_field *S = get_Fq_field(&E,T,p);
  return gen_det(x, E, S);
}

GEN
FqM_FqC_mul(GEN A, GEN B, GEN T, GEN p) {
  void *E;
  const struct bb_field *ff = get_Fq_field(&E, T, p);
  return gen_matcolmul(A, B, E, ff);
}

GEN
FqM_mul(GEN A, GEN B, GEN T, GEN p) {
  void *E;
  const struct bb_field *ff = get_Fq_field(&E, T, p);
  return gen_matmul(A, B, E, ff);
}

static GEN
FpM_ker_gen(GEN x, GEN p, long deplin)
{
  void *E;
  const struct bb_field *S = get_Fp_field(&E,p);
  return gen_ker(x, deplin, E, S);
}
static GEN
FpM_ker_i(GEN x, GEN p, long deplin)
{
  pari_sp av = avma;
  ulong pp;
  GEN y;

  if (lg(x)==1) return cgetg(1,t_MAT);
  x = FpM_init(x, p, &pp);
  switch(pp)
  {
  case 0: return FpM_ker_gen(x,p,deplin);
  case 2:
    y = F2m_ker_sp(x, deplin);
    if (!y) return y;
    y = deplin? F2c_to_ZC(y): F2m_to_ZM(y);
    return gerepileupto(av, y);
  default:
    y = Flm_ker_sp(x, pp, deplin);
    if (!y) return y;
    y = deplin? Flc_to_ZC(y): Flm_to_ZM(y);
    return gerepileupto(av, y);
  }
}

GEN
FpM_ker(GEN x, GEN p) { return FpM_ker_i(x,p,0); }

GEN
FpM_deplin(GEN x, GEN p) { return FpM_ker_i(x,p,1); }

static GEN
FqM_ker_gen(GEN x, GEN T, GEN p, long deplin)
{
  void *E;
  const struct bb_field *S = get_Fq_field(&E,T,p);
  return gen_ker(x,deplin,E,S);
}
static GEN
FqM_ker_i(GEN x, GEN T, GEN p, long deplin)
{
  if (!T) return FpM_ker_i(x,p,deplin);
  if (lg(x)==1) return cgetg(1,t_MAT);

  if (lgefint(p)==3)
  {
    pari_sp ltop=avma;
    ulong l= p[2];
    GEN Ml = FqM_to_FlxM(x, T, p);
    GEN Tl = ZXT_to_FlxT(T,l);
    GEN p1 = FlxM_to_ZXM(FlxqM_ker(Ml,Tl,l));
    return gerepileupto(ltop,p1);
  }
  return FqM_ker_gen(x, T, p, deplin);
}

GEN
FqM_ker(GEN x, GEN T, GEN p) { return FqM_ker_i(x,T,p,0); }

GEN
FqM_deplin(GEN x, GEN T, GEN p) { return FqM_ker_i(x,T,p,1); }

static GEN
FlxqM_ker_i(GEN x, GEN T, ulong p, long deplin)
{
  const struct bb_field *ff;
  void *E;

  if (lg(x)==1) return cgetg(1,t_MAT);
  ff=get_Flxq_field(&E,T,p);
  return gen_ker(x,deplin, E, ff);
}

GEN
FlxqM_ker(GEN x, GEN T, ulong p)
{
  return FlxqM_ker_i(x, T, p, 0);
}

static GEN
F2xqM_ker_i(GEN x, GEN T, long deplin)
{
  const struct bb_field *ff;
  void *E;

  if (lg(x)==1) return cgetg(1,t_MAT);
  ff = get_F2xq_field(&E,T);
  return gen_ker(x,deplin, E, ff);
}

GEN
F2xqM_ker(GEN x, GEN T)
{
  return F2xqM_ker_i(x, T, 0);
}
static GEN
F2xqM_gauss_pivot(GEN x, GEN T, long *rr)
{
  void *E;
  const struct bb_field *S = get_F2xq_field(&E,T);
  return gen_Gauss_pivot(x, rr, E, S);
}
GEN
F2xqM_image(GEN x, GEN T)
{
  long r;
  GEN d = F2xqM_gauss_pivot(x,T,&r); /* d left on stack for efficiency */
  return image_from_pivot(x,d,r);
}
long
F2xqM_rank(GEN x, GEN T)
{
  pari_sp av = avma;
  long r;
  (void)F2xqM_gauss_pivot(x,T,&r);
  avma = av; return lg(x)-1 - r;
}
/*******************************************************************/
/*                                                                 */
/*                       Solve A*X=B (Gauss pivot)                 */
/*                                                                 */
/*******************************************************************/
/* x ~ 0 compared to reference y */
int
approx_0(GEN x, GEN y)
{
  long tx = typ(x);
  if (tx == t_COMPLEX)
    return approx_0(gel(x,1), y) && approx_0(gel(x,2), y);
  return gequal0(x) ||
         (tx == t_REAL && gexpo(y) - gexpo(x) > bit_prec(x));
}
/* x a column, x0 same column in the original input matrix (for reference),
 * c list of pivots so far */
static long
gauss_get_pivot_max(GEN X, GEN X0, long ix, GEN c)
{
  GEN p, r, x = gel(X,ix), x0 = gel(X0,ix);
  long i, k = 0, ex = - (long)HIGHEXPOBIT, lx = lg(x);
  if (c)
  {
    for (i=1; i<lx; i++)
      if (!c[i])
      {
        long e = gexpo(gel(x,i));
        if (e > ex) { ex = e; k = i; }
      }
  }
  else
  {
    for (i=ix; i<lx; i++)
    {
      long e = gexpo(gel(x,i));
      if (e > ex) { ex = e; k = i; }
    }
  }
  if (!k) return lx;
  p = gel(x,k);
  r = gel(x0,k); if (isrationalzero(r)) r = x0;
  return approx_0(p, r)? lx: k;
}
static long
gauss_get_pivot_padic(GEN X, GEN p, long ix, GEN c)
{
  GEN x = gel(X, ix);
  long i, k = 0, ex = (long)HIGHVALPBIT, lx = lg(x);
  if (c)
  {
    for (i=1; i<lx; i++)
      if (!c[i] && !gequal0(gel(x,i)))
      {
        long e = gvaluation(gel(x,i), p);
        if (e < ex) { ex = e; k = i; }
      }
  }
  else
  {
    for (i=ix; i<lx; i++)
      if (!gequal0(gel(x,i)))
      {
        long e = gvaluation(gel(x,i), p);
        if (e < ex) { ex = e; k = i; }
      }
  }
  return k? k: lx;
}
static long
gauss_get_pivot_NZ(GEN X, GEN x0/*unused*/, long ix, GEN c)
{
  GEN x = gel(X, ix);
  long i, lx = lg(x);
  (void)x0;
  if (c)
  {
    for (i=1; i<lx; i++)
      if (!c[i] && !gequal0(gel(x,i))) return i;
  }
  else
  {
    for (i=ix; i<lx; i++)
      if (!gequal0(gel(x,i))) return i;
  }
  return lx;
}

/* Return pivot seeking function appropriate for the domain of the RgM x
 * (first non zero pivot, maximal pivot...)
 * x0 is a reference point used when guessing whether x[i,j] ~ 0
 * (iff x[i,j] << x0[i,j]); typical case: mateigen, Gauss pivot on x - vp.Id,
 * but use original x when deciding whether a prospective pivot is non-0 */
static pivot_fun
get_pivot_fun(GEN x, GEN x0, GEN *data)
{
  long i, j, hx, lx = lg(x);
  int res = t_INT;
  GEN p = NULL;

  *data = NULL;
  if (lx == 1) return &gauss_get_pivot_NZ;
  hx = lgcols(x);
  for (j=1; j<lx; j++)
  {
    GEN xj = gel(x,j);
    for (i=1; i<hx; i++)
    {
      GEN c = gel(xj,i);
      switch(typ(c))
      {
        case t_REAL:
          res = t_REAL;
          break;
        case t_COMPLEX:
          if (typ(gel(c,1)) == t_REAL || typ(gel(c,2)) == t_REAL) res = t_REAL;
          break;
        case t_INT: case t_INTMOD: case t_FRAC: case t_FFELT: case t_QUAD:
        case t_POLMOD: /* exact types */
          break;
        case t_PADIC:
          p = gel(c,2);
          res = t_PADIC;
          break;
        default: return &gauss_get_pivot_NZ;
      }
    }
  }
  switch(res)
  {
    case t_REAL: *data = x0; return &gauss_get_pivot_max;
    case t_PADIC: *data = p; return &gauss_get_pivot_padic;
    default: return &gauss_get_pivot_NZ;
  }
}

static GEN
get_col(GEN a, GEN b, GEN p, long li)
{
  GEN u = cgetg(li+1,t_COL);
  long i, j;

  gel(u,li) = gdiv(gel(b,li), p);
  for (i=li-1; i>0; i--)
  {
    pari_sp av = avma;
    GEN m = gel(b,i);
    for (j=i+1; j<=li; j++) m = gsub(m, gmul(gcoeff(a,i,j), gel(u,j)));
    gel(u,i) = gerepileupto(av, gdiv(m, gcoeff(a,i,i)));
  }
  return u;
}
/* assume 0 <= a[i,j] < p */
static GEN
Fl_get_col_OK(GEN a, GEN b, long li, ulong p)
{
  GEN u = cgetg(li+1,t_VECSMALL);
  ulong m = uel(b,li) % p;
  long i,j;

  uel(u,li) = (m * ucoeff(a,li,li)) % p;
  for (i = li-1; i > 0; i--)
  {
    m = p - uel(b,i)%p;
    for (j = i+1; j <= li; j++) {
      if (m & HIGHBIT) m %= p;
      m += ucoeff(a,i,j) * uel(u,j); /* 0 <= u[j] < p */
    }
    m %= p;
    if (m) m = ((p-m) * ucoeff(a,i,i)) % p;
    uel(u,i) = m;
  }
  return u;
}
static GEN
Fl_get_col(GEN a, GEN b, long li, ulong p)
{
  GEN u = cgetg(li+1,t_VECSMALL);
  ulong m = uel(b,li) % p;
  long i,j;

  uel(u,li) = Fl_mul(m, ucoeff(a,li,li), p);
  for (i=li-1; i>0; i--)
  {
    m = b[i]%p;
    for (j = i+1; j <= li; j++)
      m = Fl_sub(m, Fl_mul(ucoeff(a,i,j), uel(u,j), p), p);
    if (m) m = Fl_mul(m, ucoeff(a,i,i), p);
    uel(u,i) = m;
  }
  return u;
}

/* bk -= m * bi */
static void
_submul(GEN b, long k, long i, GEN m)
{
  gel(b,k) = gsub(gel(b,k), gmul(m, gel(b,i)));
}
static int
init_gauss(GEN a, GEN *b, long *aco, long *li, int *iscol)
{
  *iscol = *b ? (typ(*b) == t_COL): 0;
  *aco = lg(a) - 1;
  if (!*aco) /* a empty */
  {
    if (*b && lg(*b) != 1) pari_err_DIM("gauss");
    *li = 0; return 0;
  }
  *li = nbrows(a);
  if (*li < *aco) pari_err_INV("gauss [no left inverse]", a);
  if (*b)
  {
    if (*li != *aco) pari_err_DIM("gauss");
    switch(typ(*b))
    {
      case t_MAT:
        if (lg(*b) == 1) return 0;
        *b = RgM_shallowcopy(*b);
        break;
      case t_COL:
        *b = mkmat( leafcopy(*b) );
        break;
      default: pari_err_TYPE("gauss",*b);
    }
    if (nbrows(*b) != *li) pari_err_DIM("gauss");
  }
  else
    *b = matid(*li);
  return 1;
}

static int
is_modular_solve(GEN a, GEN b, GEN *u)
{
  GEN p = NULL;
  ulong pp;
  if (!RgM_is_FpM(a, &p) || !p) return 0;
  if (!b)
  {
    a = RgM_Fp_init(a, p, &pp);
    switch(pp)
    {
    case 0:
      a = FpM_inv(a,p);
      if (a) a = FpM_to_mod(a, p);
      break;
    case 2:
      a = F2m_inv(a);
      if (a) a = F2m_to_mod(a);
      break;
    default:
      a = Flm_inv(a,pp);
      if (a) a = Flm_to_mod(a, pp);
    }
  }
  else switch(typ(b))
  {
    case t_COL:
      if (!RgV_is_FpV(b, &p)) return 0;
      a = RgM_Fp_init(a, p, &pp);
      switch(pp)
      {
      case 0:
        b = RgC_to_FpC(b, p);
        a = FpM_FpC_gauss(a,b,p);
        if (a) a = FpC_to_mod(a, p);
        break;
      case 2:
        b = RgV_to_F2v(b);
        a = F2m_F2c_gauss(a,b);
        if (a) a = F2c_to_mod(a);
        break;
      default:
        b = RgC_to_Flc(b, pp);
        a = Flm_Flc_gauss(a,b,pp);
        if (a) a = Flc_to_mod(a, pp);
        break;
      }
      break;
    case t_MAT:
      if (!RgM_is_FpM(b, &p)) return 0;
      a = RgM_Fp_init(a, p, &pp);
      switch(pp)
      {
      case 0:
        b = RgM_to_FpM(b, p);
        a = FpM_gauss(a,b,p);
        if (a) a = FpM_to_mod(a, p);
        break;
      case 2:
        b = RgM_to_F2m(b);
        a = F2m_gauss(a,b);
        if (a) a = F2m_to_mod(a);
        break;
      default:
        b = RgM_to_Flm(b, pp);
        a = Flm_gauss(a,b,pp);
        if (a) a = Flm_to_mod(a, pp);
        break;
      }
      break;
    default: return 0;
  }
  *u = a; return 1;
}
/* Gaussan Elimination. If a is square, return a^(-1)*b;
 * if a has more rows than columns and b is NULL, return c such that c a = Id.
 * a is a (not necessarily square) matrix
 * b is a matrix or column vector, NULL meaning: take the identity matrix,
 *   effectively returning the inverse of a
 * If a and b are empty, the result is the empty matrix.
 *
 * li: number of rows of a and b
 * aco: number of columns of a
 * bco: number of columns of b (if matrix)
 */
GEN
RgM_solve(GEN a, GEN b)
{
  pari_sp av = avma;
  long i, j, k, li, bco, aco;
  int iscol;
  pivot_fun pivot;
  GEN p, u, data, ff = NULL;

  if (is_modular_solve(a,b,&u)) return gerepileupto(av, u);
  if (!b && RgM_is_FFM(a, &ff)) return FFM_inv(a, ff);
  avma = av;

  if (lg(a)-1 == 2 && nbrows(a) == 2) {
    /* 2x2 matrix, start by inverting a */
    GEN detinv = ginv(det (a));
    GEN ainv = cgetg(3, t_MAT);
    for (j = 1; j <= 2; j++)
      gel (ainv, j) = cgetg (3, t_COL);
    gcoeff(ainv, 1, 1) = gcoeff(a, 2, 2);
    gcoeff(ainv, 2, 2) = gcoeff(a, 1, 1);
    gcoeff(ainv, 1, 2) = gneg(gcoeff (a, 1, 2));
    gcoeff(ainv, 2, 1) = gneg(gcoeff (a, 2, 1));
    ainv = gmul(ainv, detinv);
    if (b != NULL)
      ainv = gmul(ainv, b);
    return gerepileupto(av, ainv);
  }

  if (!init_gauss(a, &b, &aco, &li, &iscol)) return cgetg(1, iscol?t_COL:t_MAT);
  pivot = get_pivot_fun(a, a, &data);
  a = RgM_shallowcopy(a);
  bco = lg(b)-1;
  if(DEBUGLEVEL>4) err_printf("Entering gauss\n");

  p = NULL; /* gcc -Wall */
  for (i=1; i<=aco; i++)
  {
    /* k is the line where we find the pivot */
    k = pivot(a, data, i, NULL);
    if (k > li) return NULL;
    if (k != i)
    { /* exchange the lines s.t. k = i */
      for (j=i; j<=aco; j++) swap(gcoeff(a,i,j), gcoeff(a,k,j));
      for (j=1; j<=bco; j++) swap(gcoeff(b,i,j), gcoeff(b,k,j));
    }
    p = gcoeff(a,i,i);
    if (i == aco) break;

    for (k=i+1; k<=li; k++)
    {
      GEN m = gcoeff(a,k,i);
      if (!gequal0(m))
      {
        m = gdiv(m,p);
        for (j=i+1; j<=aco; j++) _submul(gel(a,j),k,i,m);
        for (j=1;   j<=bco; j++) _submul(gel(b,j),k,i,m);
      }
    }
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"gauss. i=%ld",i);
      gerepileall(av,2, &a,&b);
    }
  }

  if(DEBUGLEVEL>4) err_printf("Solving the triangular system\n");
  u = cgetg(bco+1,t_MAT);
  for (j=1; j<=bco; j++) gel(u,j) = get_col(a,gel(b,j),p,aco);
  return gerepilecopy(av, iscol? gel(u,1): u);
}

/* assume dim A >= 1, A invertible + upper triangular  */
static GEN
RgM_inv_upper_ind(GEN A, long index)
{
  long n = lg(A)-1, i = index, j;
  GEN u = zerocol(n);
  gel(u,i) = ginv(gcoeff(A,i,i));
  for (i--; i>0; i--)
  {
    pari_sp av = avma;
    GEN m = gneg(gmul(gcoeff(A,i,i+1),gel(u,i+1))); /* j = i+1 */
    for (j=i+2; j<=n; j++) m = gsub(m, gmul(gcoeff(A,i,j),gel(u,j)));
    gel(u,i) = gerepileupto(av, gdiv(m, gcoeff(A,i,i)));
  }
  return u;
}
GEN
RgM_inv_upper(GEN A)
{
  long i, l;
  GEN B = cgetg_copy(A, &l);
  for (i = 1; i < l; i++) gel(B,i) = RgM_inv_upper_ind(A, i);
  return B;
}

/* assume dim A >= 1, A invertible + upper triangular, 1s on diagonal  */
static GEN
FpM_inv_upper_1_ind(GEN A, long index, GEN p)
{
  long n = lg(A)-1, i = index, j;
  GEN u = zerocol(n);
  gel(u,i) = gen_1;
  for (i--; i>0; i--)
  {
    pari_sp av = avma;
    GEN m = negi(mulii(gcoeff(A,i,i+1),gel(u,i+1))); /* j = i+1 */
    for (j=i+2; j<=n; j++) m = subii(m, mulii(gcoeff(A,i,j),gel(u,j)));
    gel(u,i) = gerepileuptoint(av, modii(m,p));
  }
  return u;
}
static GEN
FpM_inv_upper_1(GEN A, GEN p)
{
  long i, l;
  GEN B = cgetg_copy(A, &l);
  for (i = 1; i < l; i++) gel(B,i) = FpM_inv_upper_1_ind(A, i, p);
  return B;
}
/* assume dim A >= 1, A invertible + upper triangular, 1s on diagonal,
 * reduced mod p */
static GEN
Flm_inv_upper_1_ind(GEN A, long index, ulong p)
{
  long n = lg(A)-1, i = index, j;
  GEN u = const_vecsmall(n, 0);
  u[i] = 1;
  if (SMALL_ULONG(p))
    for (i--; i>0; i--)
    {
      ulong m = ucoeff(A,i,i+1) * uel(u,i+1); /* j = i+1 */
      for (j=i+2; j<=n; j++)
      {
        if (m & HIGHMASK) m %= p;
        m += ucoeff(A,i,j) * uel(u,j);
      }
      u[i] = Fl_neg(m % p, p);
    }
  else
    for (i--; i>0; i--)
    {
      ulong m = Fl_mul(ucoeff(A,i,i+1),uel(u,i+1), p); /* j = i+1 */
      for (j=i+2; j<=n; j++) m = Fl_add(m, Fl_mul(ucoeff(A,i,j),uel(u,j),p), p);
      u[i] = Fl_neg(m, p);
    }
  return u;
}
static GEN
F2m_inv_upper_1_ind(GEN A, long index)
{
  pari_sp av = avma;
  long n = lg(A)-1, i = index, j;
  GEN u = const_vecsmall(n, 0);
  u[i] = 1;
  for (i--; i>0; i--)
  {
    ulong m = F2m_coeff(A,i,i+1) & uel(u,i+1); /* j = i+1 */
    for (j=i+2; j<=n; j++) m ^= F2m_coeff(A,i,j) & uel(u,j);
    u[i] = m & 1;
  }
  return gerepileuptoleaf(av, Flv_to_F2v(u));
}
static GEN
Flm_inv_upper_1(GEN A, ulong p)
{
  long i, l;
  GEN B = cgetg_copy(A, &l);
  for (i = 1; i < l; i++) gel(B,i) = Flm_inv_upper_1_ind(A, i, p);
  return B;
}
static GEN
F2m_inv_upper_1(GEN A)
{
  long i, l;
  GEN B = cgetg_copy(A, &l);
  for (i = 1; i < l; i++) gel(B,i) = F2m_inv_upper_1_ind(A, i);
  return B;
}

static GEN
split_realimag_col(GEN z, long r1, long r2)
{
  long i, ru = r1+r2;
  GEN x = cgetg(ru+r2+1,t_COL), y = x + r2;
  for (i=1; i<=r1; i++) {
    GEN a = gel(z,i);
    if (typ(a) == t_COMPLEX) a = gel(a,1); /* paranoia: a should be real */
    gel(x,i) = a;
  }
  for (   ; i<=ru; i++) {
    GEN b, a = gel(z,i);
    if (typ(a) == t_COMPLEX) { b = gel(a,2); a = gel(a,1); } else b = gen_0;
    gel(x,i) = a;
    gel(y,i) = b;
  }
  return x;
}
GEN
split_realimag(GEN x, long r1, long r2)
{
  long i,l; GEN y;
  if (typ(x) == t_COL) return split_realimag_col(x,r1,r2);
  y = cgetg_copy(x, &l);
  for (i=1; i<l; i++) gel(y,i) = split_realimag_col(gel(x,i), r1, r2);
  return y;
}

/* assume M = (r1+r2) x (r1+2r2) matrix and y compatible vector or matrix
 * r1 first lines of M,y are real. Solve the system obtained by splitting
 * real and imaginary parts. */
GEN
RgM_solve_realimag(GEN M, GEN y)
{
  long l = lg(M), r2 = l - lgcols(M), r1 = l-1 - 2*r2;
  return RgM_solve(split_realimag(M, r1,r2),
                   split_realimag(y, r1,r2));
}

GEN
gauss(GEN a, GEN b)
{
  GEN z;
  if (typ(a)!=t_MAT) pari_err_TYPE("gauss",a);
  if (RgM_is_ZM(a) && b &&
      ((typ(b) == t_COL && RgV_is_ZV(b)) || (typ(b) == t_MAT && RgM_is_ZM(b))))
    z = ZM_gauss(a,b);
  else
    z = RgM_solve(a,b);
  if (!z) pari_err_INV("gauss",a);
  return z;
}

static GEN
F2_get_col(GEN b, GEN d, long li, long aco)
{
  long i, l = nbits2lg(aco);
  GEN u = cgetg(l, t_VECSMALL);
  u[1] = aco;
  for (i = 1; i <= li; i++)
    if (d[i]) /* d[i] can still be 0 if li > aco */
    {
      if (F2v_coeff(b, i))
        F2v_set(u, d[i]);
      else
        F2v_clear(u, d[i]);
    }
  return u;
}

/* destroy a, b */
static GEN
F2m_gauss_sp(GEN a, GEN b)
{
  long i, j, k, l, li, bco, aco = lg(a)-1;
  GEN u, d;

  if (!aco) return cgetg(1,t_MAT);
  li = gel(a,1)[1];
  d = zero_Flv(li);
  bco = lg(b)-1;
  for (i=1; i<=aco; i++)
  {
    GEN ai = vecsmall_copy(gel(a,i));
    if (!d[i] && F2v_coeff(ai, i))
      k = i;
    else
      for (k = 1; k <= li; k++) if (!d[k] && F2v_coeff(ai,k)) break;
    /* found a pivot on row k */
    if (k > li) return NULL;
    d[k] = i;

    /* Clear k-th row but column-wise instead of line-wise */
    /*  a_ij -= a_i1*a1j/a_11
       line-wise grouping:  L_j -= a_1j/a_11*L_1
       column-wise:         C_i -= a_i1/a_11*C_1
    */
    F2v_clear(ai,k);
    for (l=1; l<=aco; l++)
    {
      GEN al = gel(a,l);
      if (F2v_coeff(al,k)) F2v_add_inplace(al,ai);
    }
    for (l=1; l<=bco; l++)
    {
      GEN bl = gel(b,l);
      if (F2v_coeff(bl,k)) F2v_add_inplace(bl,ai);
    }
  }
  u = cgetg(bco+1,t_MAT);
  for (j = 1; j <= bco; j++) gel(u,j) = F2_get_col(gel(b,j), d, li, aco);
  return u;
}

GEN
F2m_gauss(GEN a, GEN b)
{
  pari_sp av = avma;
  if (lg(a) == 1) return cgetg(1,t_MAT);
  return gerepileupto(av, F2m_gauss_sp(F2m_copy(a), F2m_copy(b)));
}
GEN
F2m_F2c_gauss(GEN a, GEN b)
{
  pari_sp av = avma;
  GEN z = F2m_gauss(a, mkmat(b));
  if (lg(z) == 1) { avma = av; return cgetg(1,t_VECSMALL); }
  return gerepileuptoleaf(av, gel(z,1));
}

GEN
F2m_inv(GEN a)
{
  pari_sp av = avma;
  if (lg(a) == 1) return cgetg(1,t_MAT);
  return gerepileupto(av, F2m_gauss_sp(F2m_copy(a), matid_F2m(gel(a,1)[1])));
}

/* destroy a, b */
static GEN
Flm_gauss_sp(GEN a, GEN b, ulong *detp, ulong p)
{
  long i, j, k, li, bco, aco = lg(a)-1, s = 1;
  const int OK_ulong = SMALL_ULONG(p);
  ulong det = 1;
  GEN u;

  if (!aco) { if (detp) *detp = 1; return cgetg(1,t_MAT); }
  li = nbrows(a);
  bco = lg(b)-1;
  for (i=1; i<=aco; i++)
  {
    ulong invpiv;
    /* Fl_get_col wants 0 <= a[i,j] < p for all i,j */
    if (OK_ulong)
    {
      for (k = 1; k < i; k++) ucoeff(a,k,i) %= p;
      for (k = i; k <= li; k++)
      {
        ulong piv = ( ucoeff(a,k,i) %= p );
        if (piv)
        {
          ucoeff(a,k,i) = Fl_inv(piv, p);
          if (detp)
          {
            if (det & HIGHMASK) det %= p;
            det *= piv;
          }
          break;
        }
      }
    }
    else
    {
      for (k = i; k <= li; k++)
      {
        ulong piv = ucoeff(a,k,i);
        if (piv)
        {
          ucoeff(a,k,i) = Fl_inv(piv, p);
          if (detp) det = Fl_mul(det, piv, p);
          break;
        }
      }
    }
    /* found a pivot on line k */
    if (k > li) return NULL;
    if (k != i)
    { /* swap lines so that k = i */
      s = -s;
      for (j=i; j<=aco; j++) swap(gcoeff(a,i,j), gcoeff(a,k,j));
      for (j=1; j<=bco; j++) swap(gcoeff(b,i,j), gcoeff(b,k,j));
    }
    if (i == aco) break;

    invpiv = ucoeff(a,i,i); /* 1/piv mod p */
    for (k=i+1; k<=li; k++)
    {
      ulong m = ( ucoeff(a,k,i) %= p );
      if (!m) continue;

      m = Fl_mul(m, invpiv, p);
      if (OK_ulong)
      {
        m = p - m; /* = -m */
        if (m == 1) {
          for (j=i+1; j<=aco; j++) _Fl_add_OK(gel(a,j),k,i, p);
          for (j=1;   j<=bco; j++) _Fl_add_OK(gel(b,j),k,i, p);
        } else {
          for (j=i+1; j<=aco; j++) _Fl_addmul_OK(gel(a,j),k,i,m, p);
          for (j=1;   j<=bco; j++) _Fl_addmul_OK(gel(b,j),k,i,m, p);
        }
      } else {
        if (m == 1) {
          for (j=i+1; j<=aco; j++) _Fl_sub(gel(a,j),k,i, p);
          for (j=1;   j<=bco; j++) _Fl_sub(gel(b,j),k,i, p);
        } else {
          for (j=i+1; j<=aco; j++) _Fl_submul(gel(a,j),k,i,m, p);
          for (j=1;   j<=bco; j++) _Fl_submul(gel(b,j),k,i,m, p);
        }
      }
    }
  }
  if (detp)
  {
    det %=  p;
    if (s < 0 && det) det = p - det;
    *detp = det;
  }
  u = cgetg(bco+1,t_MAT);
  if (OK_ulong)
    for (j=1; j<=bco; j++) gel(u,j) = Fl_get_col_OK(a,gel(b,j), aco,p);
  else
    for (j=1; j<=bco; j++) gel(u,j) = Fl_get_col(a,gel(b,j), aco,p);
  return u;
}

GEN
Flm_gauss(GEN a, GEN b, ulong p) {
  return Flm_gauss_sp(RgM_shallowcopy(a), RgM_shallowcopy(b), NULL, p);
}
static GEN
Flm_inv_sp(GEN a, ulong *detp, ulong p) {
  if (lg(a) == 1) return cgetg(1,t_MAT);
  return Flm_gauss_sp(a, matid_Flm(nbrows(a)), detp, p);
}
GEN
Flm_inv(GEN a, ulong p) {
  return Flm_inv_sp(RgM_shallowcopy(a), NULL, p);
}
GEN
Flm_Flc_gauss(GEN a, GEN b, ulong p) {
  pari_sp av = avma;
  GEN z = Flm_gauss(a, mkmat(b), p);
  if (lg(z) == 1) { avma = av; return cgetg(1,t_VECSMALL); }
  return gerepileuptoleaf(av, gel(z,1));
}

static GEN
FpM_gauss_gen(GEN a, GEN b, GEN p)
{
  void *E;
  const struct bb_field *S = get_Fp_field(&E,p);
  return gen_Gauss(a,b, E, S);
}
/* a an FpM, lg(a)>1; b an FpM or NULL (replace by identity) */
static GEN
FpM_gauss_i(GEN a, GEN b, GEN p, ulong *pp)
{
  long n = nbrows(a);
  a = FpM_init(a,p,pp);
  switch(*pp)
  {
  case 0:
    if (!b) b = matid(n);
    return FpM_gauss_gen(a,b,p);
  case 2:
    if (b) b = ZM_to_F2m(b); else b = matid_F2m(n);
    return F2m_gauss_sp(a,b);
  default:
    if (b) b = ZM_to_Flm(b, *pp); else b = matid_Flm(n);
    return Flm_gauss_sp(a,b, NULL, *pp);
  }
}
GEN
FpM_gauss(GEN a, GEN b, GEN p)
{
  pari_sp av = avma;
  ulong pp;
  GEN u;
  if (lg(a) == 1 || lg(b)==1) return cgetg(1, t_MAT);
  u = FpM_gauss_i(a, b, p, &pp);
  if (!u) { avma = av; return NULL; }
  switch(pp)
  {
  case 0: return gerepilecopy(av, u);
  case 2:  u = F2m_to_ZM(u); break;
  default: u = Flm_to_ZM(u); break;
  }
  return gerepileupto(av, u);
}
GEN
FpM_inv(GEN a, GEN p)
{
  pari_sp av = avma;
  ulong pp;
  GEN u;
  if (lg(a) == 1) return cgetg(1, t_MAT);
  u = FpM_gauss_i(a, NULL, p, &pp);
  if (!u) { avma = av; return NULL; }
  switch(pp)
  {
  case 0: return gerepilecopy(av, u);
  case 2:  u = F2m_to_ZM(u); break;
  default: u = Flm_to_ZM(u); break;
  }
  return gerepileupto(av, u);
}

GEN
FpM_FpC_gauss(GEN a, GEN b, GEN p)
{
  pari_sp av = avma;
  ulong pp;
  GEN u;
  if (lg(a) == 1) return cgetg(1, t_COL);
  u = FpM_gauss_i(a, mkmat(b), p, &pp);
  if (!u) { avma = av; return NULL; }
  switch(pp)
  {
  case 0: return gerepilecopy(av, gel(u,1));
  case 2:  u = F2c_to_ZC(gel(u,1)); break;
  default: u = Flc_to_ZC(gel(u,1)); break;
  }
  return gerepileupto(av, u);
}

static GEN
FlxqM_gauss_gen(GEN a, GEN b, GEN T, ulong p)
{
  void *E;
  const struct bb_field *S = get_Flxq_field(&E, T, p);
  return gen_Gauss(a, b, E, S);
}
GEN
FlxqM_gauss(GEN a, GEN b, GEN T, ulong p)
{
  pari_sp av = avma;
  long n = lg(a)-1;
  GEN u;
  if (!n || lg(b)==1) { avma = av; return cgetg(1, t_MAT); }
  u = FlxqM_gauss_gen(a, b, T, p);
  if (!u) { avma = av; return NULL; }
  return gerepilecopy(av, u);
}
GEN
FlxqM_inv(GEN a, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN u;
  if (lg(a) == 1) { avma = av; return cgetg(1, t_MAT); }
  u = FlxqM_gauss_gen(a, matid_FlxqM(nbrows(a),T,p), T,p);
  if (!u) { avma = av; return NULL; }
  return gerepilecopy(av, u);
}
GEN
FlxqM_FlxqC_gauss(GEN a, GEN b, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN u;
  if (lg(a) == 1) return cgetg(1, t_COL);
  u = FlxqM_gauss_gen(a, mkmat(b), T, p);
  if (!u) { avma = av; return NULL; }
  return gerepilecopy(av, gel(u,1));
}

static GEN
FqM_gauss_gen(GEN a, GEN b, GEN T, GEN p)
{
  void *E;
  const struct bb_field *S = get_Fq_field(&E,T,p);
  return gen_Gauss(a,b,E,S);
}
GEN
FqM_gauss(GEN a, GEN b, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN u;
  long n;
  if (!T) return FpM_gauss(a,b,p);
  n = lg(a)-1; if (!n || lg(b)==1) return cgetg(1, t_MAT);
  u = FqM_gauss_gen(a,b,T,p);
  if (!u) { avma = av; return NULL; }
  return gerepilecopy(av, u);
}
GEN
FqM_inv(GEN a, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN u;
  if (!T) return FpM_inv(a,p);
  if (lg(a) == 1) return cgetg(1, t_MAT);
  u = FqM_gauss_gen(a,matid(nbrows(a)),T,p);
  if (!u) { avma = av; return NULL; }
  return gerepilecopy(av, u);
}
GEN
FqM_FqC_gauss(GEN a, GEN b, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN u;
  if (!T) return FpM_FpC_gauss(a,b,p);
  if (lg(a) == 1) return cgetg(1, t_COL);
  u = FqM_gauss_gen(a,mkmat(b),T,p);
  if (!u) { avma = av; return NULL; }
  return gerepilecopy(av, gel(u,1));
}

/* Dixon p-adic lifting algorithm.
 * Numer. Math. 40, 137-141 (1982), DOI: 10.1007/BF01459082 */
GEN
ZM_gauss(GEN a, GEN b0)
{
  pari_sp av = avma, av2;
  int iscol;
  long n, ncol, i, m, elim;
  ulong p;
  GEN N, C, delta, xb, nb, nmin, res, b = b0;

  if (!init_gauss(a, &b, &n, &ncol, &iscol)) return cgetg(1, iscol?t_COL:t_MAT);
  nb = gen_0; ncol = lg(b);
  for (i = 1; i < ncol; i++)
  {
    GEN ni = gnorml2(gel(b, i));
    if (cmpii(nb, ni) < 0) nb = ni;
  }
  if (!signe(nb)) { avma = av; return gcopy(b0); }
  delta = gen_1; nmin = nb;
  for (i = 1; i <= n; i++)
  {
    GEN ni = gnorml2(gel(a, i));
    if (cmpii(ni, nmin) < 0)
    {
      delta = mulii(delta, nmin); nmin = ni;
    }
    else
      delta = mulii(delta, ni);
  }
  if (!signe(nmin)) return NULL;
  elim = expi(delta)+1;
  av2 = avma;
#ifdef LONG_IS_64BIT
  p = 1000000000000000000;
#else
  p = 1000000000;
#endif
  for(;;)
  {
    p = unextprime(p+1);
    C = Flm_inv(ZM_to_Flm(a, p), p);
    if (C) break;
    elim -= expu(p);
    if (elim < 0) return NULL;
    avma = av2;
  }
  /* N.B. Our delta/lambda are SQUARES of those in the paper
   * log(delta lambda) / log p, where lambda is 3+sqrt(5) / 2,
   * whose log is < 1, hence + 1 (to cater for rounding errors) */
  m = (long)ceil((rtodbl(logr_abs(itor(delta,LOWDEFAULTPREC))) + 1)
                 / log((double)p));
  xb = ZlM_gauss(a, b, p, m, C);
  N = powuu(p, m);
  delta = sqrti(delta);
  if (iscol)
    res = FpC_ratlift(gel(xb,1), N, delta,delta, NULL);
  else
    res = FpM_ratlift(xb, N, delta,delta, NULL);
  return gerepileupto(av, res);
}

/* M integral, dM such that M' = dM M^-1 is integral [e.g det(M)]. Return M' */
GEN
ZM_inv(GEN M, GEN dM)
{
  pari_sp av2, av = avma;
  GEN Hp,q,H;
  ulong p;
  long lM = lg(M), stable = 0;
  int negate = 0;
  forprime_t S;

  if (lM == 1) return cgetg(1,t_MAT);

  /* HACK: include dM = -1 ! */
  if (dM && is_pm1(dM))
  {
    /* modular algorithm computes M^{-1}, NOT multiplied by det(M) = -1.
     * We will correct (negate) at the end. */
    if (signe(dM) < 0) negate = 1;
    dM = gen_1;
  }
  init_modular(&S);
  av2 = avma;
  H = NULL;
  while ((p = u_forprime_next(&S)))
  {
    ulong dMp;
    GEN Mp;
    Mp = ZM_to_Flm(M,p);
    if (dM == gen_1)
      Hp = Flm_inv_sp(Mp, NULL, p);
    else
    {
      if (dM) {
        dMp = umodiu(dM,p); if (!dMp) continue;
        Hp = Flm_inv_sp(Mp, NULL, p);
        if (!Hp) pari_err_INV("ZM_inv", Mp);
      } else {
        Hp = Flm_inv_sp(Mp, &dMp, p);
        if (!Hp) continue;
      }
      if (dMp != 1) Flm_Fl_mul_inplace(Hp, dMp, p);
    }

    if (!H)
    {
      H = ZM_init_CRT(Hp, p);
      q = utoipos(p);
    }
    else
      stable = ZM_incremental_CRT(&H, Hp, &q, p);
    if (DEBUGLEVEL>5) err_printf("inverse mod %ld (stable=%ld)\n", p,stable);
    if (stable) {/* DONE ? */
      if (dM != gen_1)
      { if (RgM_isscalar(ZM_mul(M, H), dM)) break; }
      else
      { if (ZM_isidentity(ZM_mul(M, H))) break; }
    }

    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"ZM_inv");
      gerepileall(av2, 2, &H, &q);
    }
  }
  if (!p) pari_err_OVERFLOW("ZM_inv [ran out of primes]");
  if (DEBUGLEVEL>5) err_printf("ZM_inv done\n");
  if (negate)
    return gerepileupto(av, ZM_neg(H));
  else
    return gerepilecopy(av, H);
}

/* same as above, M rational */
GEN
QM_inv(GEN M, GEN dM)
{
  pari_sp av = avma;
  GEN cM, pM = Q_primitive_part(M, &cM);
  if (!cM) return ZM_inv(pM,dM);
  return gerepileupto(av, ZM_inv(pM, gdiv(dM,cM)));
}

/* x a ZM. Return a multiple of the determinant of the lattice generated by
 * the columns of x. From Algorithm 2.2.6 in GTM138 */
GEN
detint(GEN A)
{
  if (typ(A) != t_MAT) pari_err_TYPE("detint",A);
  RgM_check_ZM(A, "detint");
  return ZM_detmult(A);
}
GEN
ZM_detmult(GEN A)
{
  pari_sp av1, av = avma;
  GEN B, c, v, piv;
  long rg, i, j, k, m, n = lg(A) - 1;

  if (!n) return gen_1;
  m = nbrows(A);
  if (n < m) return gen_0;
  c = zero_zv(m);
  av1 = avma;
  B = zeromatcopy(m,m);
  v = cgetg(m+1, t_COL);
  piv = gen_1; rg = 0;
  for (k=1; k<=n; k++)
  {
    GEN pivprec = piv;
    long t = 0;
    for (i=1; i<=m; i++)
    {
      pari_sp av2 = avma;
      GEN vi;
      if (c[i]) continue;

      vi = mulii(piv, gcoeff(A,i,k));
      for (j=1; j<=m; j++)
        if (c[j]) vi = addii(vi, mulii(gcoeff(B,j,i),gcoeff(A,j,k)));
      if (!t && signe(vi)) t = i;
      gel(v,i) = gerepileuptoint(av2, vi);
    }
    if (!t) continue;
    /* at this point c[t] = 0 */

    if (++rg >= m) { /* full rank; mostly done */
      GEN det = gel(v,t); /* last on stack */
      if (++k > n)
        det = absi(det);
      else
      {
        /* improve further; at this point c[i] is set for all i != t */
        gcoeff(B,t,t) = piv; v = centermod(gel(B,t), det);
        av1 = avma;
        for ( ; k<=n; k++)
        {
          det = gcdii(det, ZV_dotproduct(v, gel(A,k)));
          if (gc_needed(av1,1))
          {
            if(DEBUGMEM>1) pari_warn(warnmem,"detint end. k=%ld",k);
            det = gerepileuptoint(av1, det);
          }
        }
      }
      return gerepileuptoint(av, det);
    }

    piv = gel(v,t);
    for (i=1; i<=m; i++)
    {
      GEN mvi;
      if (c[i] || i == t) continue;

      gcoeff(B,t,i) = mvi = negi(gel(v,i));
      for (j=1; j<=m; j++)
        if (c[j]) /* implies j != t */
        {
          pari_sp av2 = avma;
          GEN z = addii(mulii(gcoeff(B,j,i), piv), mulii(gcoeff(B,j,t), mvi));
          if (rg > 1) z = diviiexact(z, pivprec);
          gcoeff(B,j,i) = gerepileuptoint(av2, z);
        }
    }
    c[t] = k;
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"detint. k=%ld",k);
      gerepileall(av1, 2, &piv,&B); v = zerovec(m);
    }
  }
  avma = av; return gen_0;
}

/* Reduce x modulo (invertible) y */
GEN
closemodinvertible(GEN x, GEN y)
{
  return gmul(y, ground(RgM_solve(y,x)));
}
GEN
reducemodinvertible(GEN x, GEN y)
{
  return gsub(x, closemodinvertible(x,y));
}
GEN
reducemodlll(GEN x,GEN y)
{
  return reducemodinvertible(x, ZM_lll(y, 0.75, LLL_INPLACE));
}

/*******************************************************************/
/*                                                                 */
/*                    KERNEL of an m x n matrix                    */
/*          return n - rk(x) linearly independent vectors          */
/*                                                                 */
/*******************************************************************/
/* x has INTEGER coefficients. Gauss-Bareiss */
GEN
keri(GEN x)
{
  pari_sp av, av0;
  GEN c, l, y, p, pp;
  long i, j, k, r, t, n, m;

  n = lg(x)-1; if (!n) return cgetg(1,t_MAT);
  av0 = avma; m = nbrows(x);
  pp = cgetg(n+1,t_COL);
  x = RgM_shallowcopy(x);
  c = zero_zv(m);
  l = cgetg(n+1, t_VECSMALL);
  av = avma;
  for (r=0, p=gen_1, k=1; k<=n; k++)
  {
    j = 1;
    while ( j <= m && (c[j] || !signe(gcoeff(x,j,k))) ) j++;
    if (j > m)
    {
      r++; l[k] = 0;
      for(j=1; j<k; j++)
        if (l[j]) gcoeff(x,l[j],k) = gclone(gcoeff(x,l[j],k));
      gel(pp,k) = gclone(p);
    }
    else
    {
      GEN p0 = p;
      c[j] = k; l[k] = j; p = gcoeff(x,j,k);
      for (t=1; t<=m; t++)
        if (t!=j)
        {
          GEN q = gcoeff(x,t,k);
          for (i=k+1; i<=n; i++)
          {
            pari_sp av1 = avma;
            GEN p1 = subii(mulii(p,gcoeff(x,t,i)), mulii(q,gcoeff(x,j,i)));
            gcoeff(x,t,i) = gerepileuptoint(av1, diviiexact(p1,p0));
          }
          if (gc_needed(av,1))
          {
            GEN _p0 = gclone(p0);
            GEN _p  = gclone(p);
            gerepile_gauss_ker(x,k,t,av);
            p = icopy(_p);  gunclone(_p);
            p0= icopy(_p0); gunclone(_p0);
          }
        }
    }
  }
  if (!r) { avma = av0; y = cgetg(1,t_MAT); return y; }

  /* non trivial kernel */
  y = cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    p = cgetg(n+1, t_COL);
    gel(y,j) = p; while (l[k]) k++;
    for (i=1; i<k; i++)
      if (l[i])
      {
        c = gcoeff(x,l[i],k);
        gel(p,i) = icopy(c); gunclone(c);
      }
      else
        gel(p,i) = gen_0;
    gel(p,k) = negi(gel(pp,k)); gunclone(gel(pp,k));
    for (i=k+1; i<=n; i++) gel(p,i) = gen_0;
  }
  return gerepileupto(av0, y);
}

static GEN
deplin_aux(GEN x0)
{
  pari_sp av = avma;
  long i, j, k, nl, nc = lg(x0)-1;
  GEN D, x, y, c, l, d, ck;

  if (!nc) { avma=av; return cgetg(1,t_COL); }
  x = RgM_shallowcopy(x0);
  nl = nbrows(x);
  d = const_vec(nl, gen_1); /* pivot list */
  c = zero_zv(nl);
  l = cgetg(nc+1, t_VECSMALL); /* not initialized */
  ck = NULL; /* gcc -Wall */
  for (k=1; k<=nc; k++)
  {
    ck = gel(x,k);
    for (j=1; j<k; j++)
    {
      GEN cj = gel(x,j), piv = gel(d,j), q = gel(ck,l[j]);
      for (i=1; i<=nl; i++)
        if (i!=l[j]) gel(ck,i) = gsub(gmul(piv, gel(ck,i)), gmul(q, gel(cj,i)));
    }

    i = gauss_get_pivot_NZ(x, NULL, k, c);
    if (i > nl) break;

    gel(d,k) = gel(ck,i);
    c[i] = k; l[k] = i; /* pivot d[k] in x[i,k] */
  }
  if (k > nc) { avma = av; return cgetg(1,t_COL); }
  if (k == 1) { avma = av; return scalarcol_shallow(gen_1,nc); }
  y = cgetg(nc+1,t_COL);
  gel(y,1) = gcopy(gel(ck, l[1]));
  for (D=gel(d,1),j=2; j<k; j++)
  {
    gel(y,j) = gmul(gel(ck, l[j]), D);
    D = gmul(D, gel(d,j));
  }
  gel(y,j) = gneg(D);
  for (j++; j<=nc; j++) gel(y,j) = gen_0;
  y = primitive_part(y, &c);
  return c? gerepileupto(av, y): gerepilecopy(av, y);
}
static GEN
RgV_deplin(GEN v)
{
  pari_sp av = avma;
  long n = lg(v)-1;
  GEN y, p = NULL;
  if (n <= 1)
  {
    if (n == 1 && gequal0(gel(v,1))) return mkcol(gen_1);
    return cgetg(1, t_COL);
  }
  if (gequal0(gel(v,1))) return scalarcol_shallow(gen_1, n);
  v = primpart(mkvec2(gel(v,1),gel(v,2)));
  if (RgV_is_FpV(v, &p) && p) v = centerlift(v);
  y = zerocol(n);
  gel(y,1) = gneg(gel(v,2));
  gel(y,2) = gcopy(gel(v,1));
  return gerepileupto(av, y);

}
GEN
deplin(GEN x)
{
  GEN p = NULL;
  switch(typ(x))
  {
    case t_MAT: break;
    case t_VEC: return RgV_deplin(x);
    default: pari_err_TYPE("deplin",x);
  }
  if (RgM_is_FpM(x, &p) && p)
  {
    pari_sp av = avma;
    ulong pp;
    x = RgM_Fp_init(x, p, &pp);
    switch(pp)
    {
    case 0:
      x = FpM_ker_gen(x,p,1);
      if (!x) { avma = av; return cgetg(1,t_COL); }
      x = FpC_center(x,p,shifti(p,-1));
      break;
    case 2:
      x = F2m_ker_sp(x,1);
      if (!x) { avma = av; return cgetg(1,t_COL); }
      x = F2c_to_ZC(x); break;
    default:
      x = Flm_ker_sp(x,pp,1);
      if (!x) { avma = av; return cgetg(1,t_COL); }
      x = Flv_center(x, pp, pp>>1);
      x = zc_to_ZC(x);
      break;
    }
    return gerepileupto(av, x);
  }
  return deplin_aux(x);
}
/*******************************************************************/
/*                                                                 */
/*         GAUSS REDUCTION OF MATRICES  (m lines x n cols)         */
/*           (kernel, image, complementary image, rank)            */
/*                                                                 */
/*******************************************************************/
/* return the transform of x under a standard Gauss pivot.
 * x0 is a reference point when guessing whether x[i,j] ~ 0
 * (iff x[i,j] << x0[i,j])
 * Set r = dim ker(x). d[k] contains the index of the first non-zero pivot
 * in column k */
static GEN
gauss_pivot_ker(GEN x, GEN x0, GEN *dd, long *rr)
{
  GEN c, d, p, data;
  pari_sp av;
  long i, j, k, r, t, n, m;
  pivot_fun pivot;

  n=lg(x)-1; if (!n) { *dd=NULL; *rr=0; return cgetg(1,t_MAT); }
  m=nbrows(x); r=0;
  pivot = get_pivot_fun(x, x0, &data);
  x = RgM_shallowcopy(x);
  c = zero_zv(m);
  d = cgetg(n+1,t_VECSMALL);
  av=avma;
  for (k=1; k<=n; k++)
  {
    j = pivot(x, data, k, c);
    if (j > m)
    {
      r++; d[k]=0;
      for(j=1; j<k; j++)
        if (d[j]) gcoeff(x,d[j],k) = gclone(gcoeff(x,d[j],k));
    }
    else
    { /* pivot for column k on row j */
      c[j]=k; d[k]=j; p = gdiv(gen_m1,gcoeff(x,j,k));
      gcoeff(x,j,k) = gen_m1;
      /* x[j,] /= - x[j,k] */
      for (i=k+1; i<=n; i++) gcoeff(x,j,i) = gmul(p,gcoeff(x,j,i));
      for (t=1; t<=m; t++)
        if (t!=j)
        { /* x[t,] -= 1 / x[j,k] x[j,] */
          p = gcoeff(x,t,k); gcoeff(x,t,k) = gen_0;
          for (i=k+1; i<=n; i++)
            gcoeff(x,t,i) = gadd(gcoeff(x,t,i),gmul(p,gcoeff(x,j,i)));
          if (gc_needed(av,1)) gerepile_gauss_ker(x,k,t,av);
        }
    }
  }
  *dd=d; *rr=r; return x;
}

static GEN FpM_gauss_pivot(GEN x, GEN p, long *rr);
static GEN FqM_gauss_pivot(GEN x, GEN T, GEN p, long *rr);
static GEN F2m_gauss_pivot(GEN x, long *rr);
static GEN Flm_gauss_pivot(GEN x, ulong p, long *rry);

/* r = dim ker(x).
 * Returns d:
 *   d[k] != 0 contains the index of a non-zero pivot in column k
 *   d[k] == 0 if column k is a linear combination of the (k-1) first ones */
GEN
RgM_pivots(GEN x0, GEN data, long *rr, pivot_fun pivot)
{
  GEN x, c, d, p;
  long i, j, k, r, t, m, n = lg(x0)-1;
  pari_sp av;

  if (RgM_is_ZM(x0)) return ZM_pivots(x0, rr);
  if (!n) { *rr = 0; return NULL; }

  d = cgetg(n+1, t_VECSMALL);
  x = RgM_shallowcopy(x0);
  m = nbrows(x); r = 0;
  c = zero_zv(m);
  av = avma;
  for (k=1; k<=n; k++)
  {
    j = pivot(x, data, k, c);
    if (j > m) { r++; d[k] = 0; }
    else
    {
      c[j] = k; d[k] = j; p = gdiv(gen_m1, gcoeff(x,j,k));
      for (i=k+1; i<=n; i++) gcoeff(x,j,i) = gmul(p,gcoeff(x,j,i));

      for (t=1; t<=m; t++)
        if (!c[t]) /* no pivot on that line yet */
        {
          p = gcoeff(x,t,k); gcoeff(x,t,k) = gen_0;
          for (i=k+1; i<=n; i++)
            gcoeff(x,t,i) = gadd(gcoeff(x,t,i), gmul(p, gcoeff(x,j,i)));
          if (gc_needed(av,1)) gerepile_gauss(x,k,t,av,j,c);
        }
      for (i=k; i<=n; i++) gcoeff(x,j,i) = gen_0; /* dummy */
    }
  }
  *rr = r; avma = (pari_sp)d; return d;
}

static long
ZM_count_0_cols(GEN M)
{
  long i, l = lg(M), n = 0;
  for (i = 1; i < l; i++)
    if (ZV_equal0(gel(M,i))) n++;
  return n;
}

static void indexrank_all(long m, long n, long r, GEN d, GEN *prow, GEN *pcol);
/* As RgM_pivots, integer entries. Set *rr = dim Ker M0 */
GEN
ZM_pivots(GEN M0, long *rr)
{
  GEN d, dbest = NULL;
  long m, n, i, imax, rmin, rbest, zc;
  int beenthere = 0;
  pari_sp av, av0 = avma;
  forprime_t S;

  rbest = n = lg(M0)-1;
  if (n == 0) { *rr = 0; return NULL; }
  zc = ZM_count_0_cols(M0);
  if (n == zc) { *rr = zc; return zero_zv(n); }

  m = nbrows(M0);
  rmin = maxss(zc, n-m);
  init_modular(&S);
  imax = (n < (1<<4))? 1: (n>>3); /* heuristic */

  for(;;)
  {
    GEN row, col, M, KM, IM, RHS, X, cX;
    long rk;
    for (av = avma, i = 0;; avma = av, i++)
    {
      ulong p = u_forprime_next(&S);
      long rp;
      if (!p) pari_err_OVERFLOW("ZM_pivots [ran out of primes]");
      d = Flm_gauss_pivot(ZM_to_Flm(M0, p), p, &rp);
      if (rp == rmin) { rbest = rp; goto END; } /* maximal rank, return */
      if (rp < rbest) { /* save best r so far */
        rbest = rp;
        if (dbest) gunclone(dbest);
        dbest = gclone(d);
        if (beenthere) break;
      }
      if (!beenthere && i >= imax) break;
    }
    beenthere = 1;
    /* Dubious case: there is (probably) a non trivial kernel */
    indexrank_all(m,n, rbest, dbest, &row, &col);
    M = rowpermute(vecpermute(M0, col), row);
    rk = n - rbest; /* (probable) dimension of image */
    IM = vecslice(M,1,rk);
    KM = vecslice(M,rk+1, n);
    M = rowslice(IM, 1,rk); /* square maximal rank */
    X = ZM_gauss(M, rowslice(KM, 1,rk));
    X = Q_remove_denom(X, &cX);
    RHS = rowslice(KM,rk+1,m);
    if (cX) RHS = ZM_Z_mul(RHS, cX);
    if (ZM_equal(ZM_mul(rowslice(IM,rk+1,m), X), RHS))
    {
      d = vecsmall_copy(dbest);
      goto END;
    }
    avma = av;
  }
END:
  *rr = rbest; if (dbest) gunclone(dbest);
  return gerepileuptoleaf(av0, d);
}

/* set *pr = dim Ker x */
static GEN
gauss_pivot(GEN x, long *pr) {
  GEN data;
  pivot_fun pivot = get_pivot_fun(x, x, &data);
  return RgM_pivots(x, data, pr, pivot);
}

/* compute ker(x), x0 is a reference point when guessing whether x[i,j] ~ 0
 * (iff x[i,j] << x0[i,j]) */
static GEN
ker_aux(GEN x, GEN x0)
{
  pari_sp av = avma;
  GEN d,y;
  long i,j,k,r,n;

  x = gauss_pivot_ker(x,x0,&d,&r);
  if (!r) { avma=av; return cgetg(1,t_MAT); }
  n = lg(x)-1; y=cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN p = cgetg(n+1,t_COL);

    gel(y,j) = p; while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i])
      {
        GEN p1=gcoeff(x,d[i],k);
        gel(p,i) = gcopy(p1); gunclone(p1);
      }
      else
        gel(p,i) = gen_0;
    gel(p,k) = gen_1; for (i=k+1; i<=n; i++) gel(p,i) = gen_0;
  }
  return gerepileupto(av,y);
}
GEN
ker(GEN x)
{
  pari_sp av = avma;
  GEN p = NULL, ff = NULL;
  if (RgM_is_FpM(x, &p) && p)
  {
    ulong pp;
    x = RgM_Fp_init(x, p, &pp);
    switch(pp)
    {
    case 0: x = FpM_to_mod(FpM_ker_gen(x,p,0),p); break;
    case 2: x = F2m_to_mod(F2m_ker_sp(x,0)); break;
    default:x = Flm_to_mod(Flm_ker_sp(x,pp,0), pp); break;
    }
    return gerepileupto(av, x);
  }
  if (RgM_is_FFM(x, &ff)) return FFM_ker(x, ff);
  return ker_aux(x,x);
}
GEN
matker0(GEN x,long flag)
{
  if (typ(x)!=t_MAT) pari_err_TYPE("matker",x);
  if (!flag) return ker(x);
  RgM_check_ZM(x, "keri");
  return keri(x);
}

GEN
image(GEN x)
{
  pari_sp av = avma;
  GEN d, ff = NULL, p = NULL;
  long r;

  if (typ(x)!=t_MAT) pari_err_TYPE("matimage",x);
  if (RgM_is_FpM(x, &p) && p)
  {
    ulong pp;
    x = RgM_Fp_init(x, p, &pp);
    switch(pp)
    {
    case 0: x = FpM_to_mod(FpM_image(x,p), p); break;
    case 2: x = F2m_to_mod(F2m_image(x)); break;
    default:x = Flm_to_mod(Flm_image(x,pp), pp);
    }
    return gerepileupto(av, x);
  }
  if (RgM_is_FFM(x, &ff)) return FFM_image(x, ff);
  d = gauss_pivot(x,&r); /* d left on stack for efficiency */
  return image_from_pivot(x,d,r);
}

static GEN
imagecompl_aux(GEN x, GEN(*PIVOT)(GEN,long*))
{
  pari_sp av = avma;
  GEN d,y;
  long j,i,r;

  if (typ(x)!=t_MAT) pari_err_TYPE("imagecompl",x);
  (void)new_chunk(lg(x) * 4 + 1); /* HACK */
  d = PIVOT(x,&r); /* if (!d) then r = 0 */
  avma = av; y = cgetg(r+1,t_VECSMALL);
  for (i=j=1; j<=r; i++)
    if (!d[i]) y[j++] = i;
  return y;
}
GEN
imagecompl(GEN x) { return imagecompl_aux(x, &gauss_pivot); }
GEN
ZM_imagecompl(GEN x) { return imagecompl_aux(x, &ZM_pivots); }

/* permutation giving imagecompl(x') | image(x'), x' = transpose of x */
static GEN
imagecomplspec_aux(GEN x, long *nlze, GEN(*PIVOT)(GEN,long*))
{
  pari_sp av = avma;
  GEN d,y;
  long i,j,k,l,r;

  if (typ(x)!=t_MAT) pari_err_TYPE("imagecomplspec",x);
  x = shallowtrans(x); l = lg(x);
  d = PIVOT(x,&r);
  *nlze = r;
  avma = av; /* HACK: shallowtrans(x) big enough to avoid overwriting d */
  if (!d) return identity_perm(l-1);
  y = cgetg(l,t_VECSMALL);
  for (i=j=1, k=r+1; i<l; i++)
    if (d[i]) y[k++]=i; else y[j++]=i;
  return y;
}
GEN
imagecomplspec(GEN x, long *nlze)
{ return imagecomplspec_aux(x,nlze,&gauss_pivot); }
GEN
ZM_imagecomplspec(GEN x, long *nlze)
{ return imagecomplspec_aux(x,nlze,&ZM_pivots); }

GEN
RgM_RgC_invimage(GEN A, GEN y)
{
  pari_sp av = avma;
  long i, l = lg(A);
  GEN M, x, t, p = NULL;

  if (RgM_is_FpM(A, &p) && RgV_is_FpV(y, &p) && p)
  {
    ulong pp;
    A = RgM_Fp_init(A,p,&pp);
    switch(pp)
    {
    case 0:
      y = RgC_to_FpC(y,p);
      x = FpM_FpC_invimage(A, y, p);
      if (x) x = FpC_to_mod(x,p);
      break;
    case 2:
      y = RgV_to_F2v(y);
      x = F2m_F2c_invimage(A, y);
      if (x) x = F2c_to_mod(x);
      break;
    default:
      y = RgC_to_Flc(y,pp);
      x = Flm_Flc_invimage(A, y, pp);
      if (x) x = Flc_to_mod(x,pp);
    }
    if (!x) { avma = av; return NULL; }
    return gerepileupto(av, x);
  }

  if (l==1) return NULL;
  if (lg(y) != lgcols(A)) pari_err_DIM("inverseimage");
  M = ker(shallowconcat(A, y));
  i = lg(M)-1;
  if (!i) { avma = av; return NULL; }

  x = gel(M,i); t = gel(x,l);
  if (gequal0(t)) { avma = av; return NULL; }

  t = gneg_i(t); setlg(x,l);
  return gerepileupto(av, RgC_Rg_div(x, t));
}
GEN
FpM_FpC_invimage(GEN A, GEN y, GEN p)
{
  pari_sp av = avma;
  long i, l = lg(A);
  GEN M, x, t;

  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    A = ZM_to_Flm(A, pp);
    y = ZV_to_Flv(y, pp);
    x = Flm_Flc_invimage(A,y,pp);
    if (!x) { avma = av; return NULL; }
    return gerepileupto(av, Flc_to_ZC(x));
  }
  if (l==1) return NULL;
  if (lg(y) != lgcols(A)) pari_err_DIM("FpM_FpC_invimage");
  M = FpM_ker(shallowconcat(A,y),p);
  i = lg(M)-1; if (!i) { avma = av; return NULL; }

  x = gel(M,i); t = gel(x,l);
  if (!signe(t)) { avma = av; return NULL; }

  setlg(x,l); t = Fp_inv(negi(t),p);
  if (is_pm1(t)) return gerepilecopy(av, x);
  return gerepileupto(av, FpC_Fp_mul(x, t, p));
}
GEN
Flm_Flc_invimage(GEN A, GEN y, ulong p)
{
  pari_sp av = avma;
  long i, l = lg(A);
  GEN M, x;
  ulong t;

  if (l==1) return NULL;
  if (lg(y) != lgcols(A)) pari_err_DIM("Flm_Flc_invimage");
  M = cgetg(l+1,t_MAT);
  for (i=1; i<l; i++) gel(M,i) = gel(A,i);
  gel(M,l) = y; M = Flm_ker(M,p);
  i = lg(M)-1; if (!i) { avma = av; return NULL; }

  x = gel(M,i); t = x[l];
  if (!t) { avma = av; return NULL; }

  setlg(x,l); t = Fl_inv(Fl_neg(t,p),p);
  if (t!=1) x = Flc_Fl_mul(x, t, p);
  return gerepileuptoleaf(av, x);
}
GEN
F2m_F2c_invimage(GEN A, GEN y)
{
  pari_sp av = avma;
  long i, l = lg(A);
  GEN M, x;

  if (l==1) return NULL;
  if (lg(y) != lgcols(A)) pari_err_DIM("F2m_F2c_invimage");
  M = cgetg(l+1,t_MAT);
  for (i=1; i<l; i++) gel(M,i) = gel(A,i);
  gel(M,l) = y; M = F2m_ker(M);
  i = lg(M)-1; if (!i) { avma = av; return NULL; }

  x = gel(M,i);
  if (!F2v_coeff(x,l)) { avma = av; return NULL; }
  x[1]--; /* remove last coord */
  return gerepileuptoleaf(av, x);
}

/* Return X such that m X = v (t_COL or t_MAT), resp. an empty t_COL / t_MAT
 * if no solution exist */
GEN
inverseimage(GEN m, GEN v)
{
  GEN y;
  if (typ(m)!=t_MAT) pari_err_TYPE("inverseimage",m);
  switch(typ(v))
  {
    case t_COL:
      y = RgM_RgC_invimage(m,v);
      return y? y: cgetg(1,t_COL);
    case t_MAT:
      y = RgM_invimage(m, v);
      return y? y: cgetg(1,t_MAT);
  }
  pari_err_TYPE("inverseimage",v);
  return NULL;/*not reached*/
}

static GEN
Flm_invimage_i(GEN A, GEN B, ulong p)
{
  GEN d, x, X, Y;
  long i, j, nY, nA = lg(A)-1, nB = lg(B)-1;
  x = Flm_ker_sp(shallowconcat(Flm_neg(A,p), B), p, 0);
  /* AX = BY, Y in strict upper echelon form with pivots = 1.
   * We must find T such that Y T = Id_nB then X T = Z. This exists iff
   * Y has at least nB columns and full rank */
  nY = lg(x)-1;
  if (nY < nB) return NULL;
  Y = rowslice(x, nA+1, nA+nB); /* nB rows */
  d = cgetg(nB+1, t_VECSMALL);
  for (i = nB, j = nY; i >= 1; i--)
  {
    for (; j>=1; j--)
      if (coeff(Y,i,j)) { d[i] = j; break; }
    if (!j) return NULL;
  }
  /* reduce to the case Y square, upper triangular with 1s on diagonal */
  Y = vecpermute(Y, d);
  x = vecpermute(x, d);
  X = rowslice(x, 1, nA);
  return Flm_mul(X, Flm_inv_upper_1(Y,p), p);
}

static GEN
F2m_invimage_i(GEN A, GEN B)
{
  GEN d, x, X, Y;
  long i, j, nY, nA = lg(A)-1, nB = lg(B)-1;
  x = F2m_ker_sp(shallowconcat(A, B), 0);
  /* AX = BY, Y in strict upper echelon form with pivots = 1.
   * We must find T such that Y T = Id_nB then X T = Z. This exists iff
   * Y has at least nB columns and full rank */
  nY = lg(x)-1;
  if (nY < nB) return NULL;

  /* implicitly: Y = rowslice(x, nA+1, nA+nB), nB rows */
  d = cgetg(nB+1, t_VECSMALL);
  for (i = nB, j = nY; i >= 1; i--)
  {
    for (; j>=1; j--)
      if (F2m_coeff(x,nA+i,j)) { d[i] = j; break; } /* Y[i,j] */
    if (!j) return NULL;
  }
  x = vecpermute(x, d);

  X = F2m_rowslice(x, 1, nA);
  Y = F2m_rowslice(x, nA+1, nA+nB);
  return F2m_mul(X, F2m_inv_upper_1(Y));
}
GEN
Flm_invimage(GEN A, GEN B, ulong p)
{
  pari_sp av = avma;
  GEN X = Flm_invimage_i(A,B,p);
  if (!X) { avma = av; return NULL; }
  return gerepileupto(av, X);
}
GEN
F2m_invimage(GEN A, GEN B)
{
  pari_sp av = avma;
  GEN X = F2m_invimage_i(A,B);
  if (!X) { avma = av; return NULL; }
  return gerepileupto(av, X);
}
static GEN
FpM_invimage_i(GEN A, GEN B, GEN p)
{
  GEN d, x, X, Y;
  long i, j, nY, nA = lg(A)-1, nB = lg(B)-1;
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    A = ZM_to_Flm(A, pp);
    B = ZM_to_Flm(B, pp);
    x = Flm_invimage_i(A, B, pp);
    return x? Flm_to_ZM(x): NULL;
  }
  x = FpM_ker(shallowconcat(ZM_neg(A), B), p);
  /* AX = BY, Y in strict upper echelon form with pivots = 1.
   * We must find T such that Y T = Id_nB then X T = Z. This exists iff
   * Y has at least nB columns and full rank */
  nY = lg(x)-1;
  if (nY < nB) return NULL;
  Y = rowslice(x, nA+1, nA+nB); /* nB rows */
  d = cgetg(nB+1, t_VECSMALL);
  for (i = nB, j = nY; i >= 1; i--)
  {
    for (; j>=1; j--)
      if (signe(gcoeff(Y,i,j))) { d[i] = j; break; }
    if (!j) return NULL;
  }
  /* reduce to the case Y square, upper triangular with 1s on diagonal */
  Y = vecpermute(Y, d);
  x = vecpermute(x, d);
  X = rowslice(x, 1, nA);
  return FpM_mul(X, FpM_inv_upper_1(Y,p), p);
}
GEN
FpM_invimage(GEN A, GEN B, GEN p)
{
  pari_sp av = avma;
  GEN X = FpM_invimage_i(A,B,p);
  if (!X) { avma = av; return NULL; }
  return gerepileupto(av, X);
}

/* find Z such that A Z = B. Return NULL if no solution */
GEN
RgM_invimage(GEN A, GEN B)
{
  pari_sp av = avma;
  GEN d, x, X, Y;
  long i, j, nY, nA = lg(A)-1, nB = lg(B)-1;
  GEN p = NULL;
  if (RgM_is_FpM(A, &p) && RgM_is_FpM(B, &p) && p)
  {
    ulong pp;
    A = RgM_Fp_init(A,p,&pp);
    switch(pp)
    {
    case 0:
      B = RgM_to_FpM(B,p);
      x = FpM_invimage_i(A, B, p);
      if (x) x = FpM_to_mod(x, p);
    break;
    case 2:
      B = RgM_to_F2m(B);
      x = F2m_invimage_i(A, B);
      if (x) x = F2m_to_mod(x);
      break;
    default:
      B = RgM_to_Flm(B,pp);
      x = Flm_invimage_i(A, B, pp);
      if (x) x = Flm_to_mod(x,pp);
      break;
    }
    if (!x) { avma = av; return NULL; }
    return gerepileupto(av, x);
  }
  x = ker(shallowconcat(RgM_neg(A), B));
  /* AX = BY, Y in strict upper echelon form with pivots = 1.
   * We must find T such that Y T = Id_nB then X T = Z. This exists iff
   * Y has at least nB columns and full rank */
  nY = lg(x)-1;
  if (nY < nB) { avma = av; return NULL; }
  Y = rowslice(x, nA+1, nA+nB); /* nB rows */
  d = cgetg(nB+1, t_VECSMALL);
  for (i = nB, j = nY; i >= 1; i--)
  {
    for (; j>=1; j--)
      if (!gequal0(gcoeff(Y,i,j))) { d[i] = j; break; }
    if (!j) { avma = av; return NULL; }
  }
  /* reduce to the case Y square, upper triangular with 1s on diagonal */
  Y = vecpermute(Y, d);
  x = vecpermute(x, d);
  X = rowslice(x, 1, nA);
  return gerepileupto(av, RgM_mul(X, RgM_inv_upper(Y)));
}

/* r = dim Ker x, n = nbrows(x) */
static GEN
get_suppl(GEN x, GEN d, long n, long r, GEN(*ei)(long,long))
{
  pari_sp av;
  GEN y, c;
  long j, k, rx = lg(x)-1; /* != 0 due to init_suppl() */

  if (rx == n && r == 0) return gcopy(x);
  y = cgetg(n+1, t_MAT);
  av = avma; c = zero_zv(n);
  /* c = lines containing pivots (could get it from gauss_pivot, but cheap)
   * In theory r = 0 and d[j] > 0 for all j, but why take chances? */
  for (k = j = 1; j<=rx; j++)
    if (d[j]) { c[ d[j] ] = 1; gel(y,k++) = gel(x,j); }
  for (j=1; j<=n; j++)
    if (!c[j]) gel(y,k++) = (GEN)j; /* HACK */
  avma = av;

  rx -= r;
  for (j=1; j<=rx; j++) gel(y,j) = gcopy(gel(y,j));
  for (   ; j<=n; j++)  gel(y,j) = ei(n, y[j]);
  return y;
}

static void
init_suppl(GEN x)
{
  if (lg(x) == 1) pari_err_IMPL("suppl [empty matrix]");
  /* HACK: avoid overwriting d from gauss_pivot() after avma=av */
  (void)new_chunk(lgcols(x) * 2);
}

/* x is an n x k matrix, rank(x) = k <= n. Return an invertible n x n matrix
 * whose first k columns are given by x. If rank(x) < k, undefined result. */
GEN
suppl(GEN x)
{
  pari_sp av = avma;
  GEN d, X = x, p = NULL;
  long r;

  if (typ(x)!=t_MAT) pari_err_TYPE("suppl",x);
  if (RgM_is_FpM(x, &p) && p)
  {
    ulong pp;
    x = RgM_Fp_init(x, p, &pp);
    switch(pp)
    {
    case 0: x = FpM_to_mod(FpM_suppl(x,p), p); break;
    case 2: x = F2m_to_mod(F2m_suppl(x)); break;
    default:x = Flm_to_mod(Flm_suppl(x,pp), pp); break;
    }
    return gerepileupto(av, x);
  }
  avma = av; init_suppl(x);
  d = gauss_pivot(X,&r);
  avma = av; return get_suppl(X,d,nbrows(X),r,&col_ei);
}
GEN
FpM_suppl(GEN x, GEN p)
{
  pari_sp av = avma;
  GEN d;
  long r;
  init_suppl(x); d = FpM_gauss_pivot(x,p, &r);
  avma = av; return get_suppl(x,d,nbrows(x),r,&col_ei);
}
GEN
Flm_suppl(GEN x, ulong p)
{
  pari_sp av = avma;
  GEN d;
  long r;
  init_suppl(x); d = Flm_gauss_pivot(Flm_copy(x),p, &r);
  avma = av; return get_suppl(x,d,nbrows(x),r,&vecsmall_ei);

}
GEN
F2m_suppl(GEN x)
{
  pari_sp av = avma;
  GEN d;
  long r;
  init_suppl(x); d = F2m_gauss_pivot(F2m_copy(x), &r);
  avma = av; return get_suppl(x,d,mael(x,1,1),r,&F2v_ei);
}

GEN
FqM_suppl(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN d;
  long r;

  if (!T) return FpM_suppl(x,p);
  init_suppl(x);
  d = FqM_gauss_pivot(x,T,p,&r);
  avma = av; return get_suppl(x,d,nbrows(x),r,&col_ei);
}

GEN
image2(GEN x)
{
  pari_sp av = avma;
  long k, n, i;
  GEN A, B;

  if (typ(x)!=t_MAT) pari_err_TYPE("image2",x);
  if (lg(x) == 1) return cgetg(1,t_MAT);
  A = ker(x); k = lg(A)-1;
  if (!k) { avma = av; return gcopy(x); }
  A = suppl(A); n = lg(A)-1;
  B = cgetg(n-k+1, t_MAT);
  for (i = k+1; i <= n; i++) gel(B,i-k) = RgM_RgC_mul(x, gel(A,i));
  return gerepileupto(av, B);
}

GEN
matimage0(GEN x,long flag)
{
  switch(flag)
  {
    case 0: return image(x);
    case 1: return image2(x);
    default: pari_err_FLAG("matimage");
  }
  return NULL; /* not reached */
}

long
rank(GEN x)
{
  pari_sp av = avma;
  long r;
  GEN ff = NULL, p = NULL;

  if (typ(x)!=t_MAT) pari_err_TYPE("rank",x);
  if (RgM_is_FpM(x, &p) && p)
  {
    ulong pp;
    x = RgM_Fp_init(x,p,&pp);
    switch(pp)
    {
    case 0: r = FpM_rank(x,p); break;
    case 2: r = F2m_rank(x); break;
    default:r = Flm_rank(x,pp); break;
    }
    avma = av; return r;
  }
  if (RgM_is_FFM(x, &ff)) return FFM_rank(x, ff);
  (void)gauss_pivot(x, &r);
  avma = av; return lg(x)-1 - r;
}

/* d a t_VECSMALL of integers in 1..n. Return the vector of the d[i]
 * followed by the missing indices */
static GEN
perm_complete(GEN d, long n)
{
  GEN y = cgetg(n+1, t_VECSMALL);
  long i, j = 1, k = n, l = lg(d);
  pari_sp av = avma;
  char *T = stack_calloc(n+1);
  for (i = 1; i < l; i++) T[d[i]] = 1;
  for (i = 1; i <= n; i++)
    if (T[i]) y[j++] = i; else y[k--] = i;
  avma = av; return y;
}

/* n = dim x, r = dim Ker(x), d from gauss_pivot */
static GEN
indexrank0(long n, long r, GEN d)
{
  GEN p1, p2, res = cgetg(3,t_VEC);
  long i, j;

  r = n - r; /* now r = dim Im(x) */
  p1 = cgetg(r+1,t_VECSMALL); gel(res,1) = p1;
  p2 = cgetg(r+1,t_VECSMALL); gel(res,2) = p2;
  if (d)
  {
    for (i=0,j=1; j<=n; j++)
      if (d[j]) { i++; p1[i] = d[j]; p2[i] = j; }
    vecsmall_sort(p1);
  }
  return res;
}
/* n = dim x, r = dim Ker(x), d from gauss_pivot */
static GEN
indeximage0(long n, long r, GEN d)
{
  long i, j;
  GEN v;

  r = n - r; /* now r = dim Im(x) */
  v = cgetg(r+1,t_VECSMALL);
  if (d) for (i=j=1; j<=n; j++)
    if (d[j]) v[i++] = j;
  return v;
}
/* x an m x n t_MAT, n > 0, r = dim Ker(x), d from gauss_pivot */
static void
indexrank_all(long m, long n, long r, GEN d, GEN *prow, GEN *pcol)
{
  GEN IR = indexrank0(n, r, d);
  *prow = perm_complete(gel(IR,1), m);
  *pcol = perm_complete(gel(IR,2), n);
}
static void
init_indexrank(GEN x) {
  (void)new_chunk(3 + 2*lg(x)); /* HACK */
}

GEN
indexrank(GEN x) {
  pari_sp av = avma;
  long r;
  GEN d, p = NULL;
  if (typ(x)!=t_MAT) pari_err_TYPE("indexrank",x);
  init_indexrank(x);
  if (RgM_is_FpM(x, &p) && p)
  {
    ulong pp;
    x = RgM_Fp_init(x,p,&pp);
    switch(pp)
    {
    case 0: d = FpM_gauss_pivot(x,p,&r); break;
    case 2: d = F2m_gauss_pivot(x,&r); break;
    default:d = Flm_gauss_pivot(x,pp,&r); break;
    }
  }
  else
    d = gauss_pivot(x,&r);
  avma = av; return indexrank0(lg(x)-1, r, d);
}

GEN
FpM_indexrank(GEN x, GEN p) {
  pari_sp av = avma;
  long r;
  GEN d;
  init_indexrank(x);
  d = FpM_gauss_pivot(x,p,&r);
  avma = av; return indexrank0(lg(x)-1, r, d);
}
GEN
Flm_indexrank(GEN x, ulong p) {
  pari_sp av = avma;
  long r;
  GEN d;
  init_indexrank(x);
  d = Flm_gauss_pivot(Flm_copy(x),p,&r);
  avma = av; return indexrank0(lg(x)-1, r, d);
}
GEN
F2m_indexrank(GEN x) {
  pari_sp av = avma;
  long r;
  GEN d;
  init_indexrank(x);
  d = F2m_gauss_pivot(F2m_copy(x),&r);
  avma = av; return indexrank0(lg(x)-1, r, d);
}

GEN
ZM_indeximage(GEN x) {
  pari_sp av = avma;
  long r;
  GEN d;
  init_indexrank(x);
  d = ZM_pivots(x,&r);
  avma = av; return indeximage0(lg(x)-1, r, d);
}
long
ZM_rank(GEN x) {
  pari_sp av = avma;
  long r;
  (void)ZM_pivots(x,&r);
  avma = av; return lg(x)-1-r;
}
GEN
ZM_indexrank(GEN x) {
  pari_sp av = avma;
  long r;
  GEN d;
  init_indexrank(x);
  d = ZM_pivots(x,&r);
  avma = av; return indexrank0(lg(x)-1, r, d);
}

/*******************************************************************/
/*                                                                 */
/*                   Structured Elimination                        */
/*                                                                 */
/*******************************************************************/

static void
rem_col(GEN c, long i, GEN iscol, GEN Wrow, long *rcol, long *rrow)
{
  long lc = lg(c), k;
  iscol[i] = 0; (*rcol)--;
  for (k = 1; k < lc; ++k)
  {
    Wrow[c[k]]--;
    if (Wrow[c[k]]==0) (*rrow)--;
  }
}

static void
rem_singleton(GEN M, GEN iscol, GEN Wrow, long *rcol, long *rrow)
{
  long i, j;
  long nbcol = lg(iscol)-1, last;
  do
  {
    last = 0;
    for (i = 1; i <= nbcol; ++i)
      if (iscol[i])
      {
        GEN c = gmael(M, i, 1);
        long lc = lg(c);
        for (j = 1; j < lc; ++j)
          if (Wrow[c[j]] == 1)
          {
            rem_col(c, i, iscol, Wrow, rcol, rrow);
            last=1; break;
          }
      }
  } while (last);
}

static GEN
fill_wcol(GEN M, GEN iscol, GEN Wrow, long *w, GEN wcol)
{
  long nbcol = lg(iscol)-1;
  long i, j, m, last;
  GEN per;
  for (m = 2, last=0; !last ; m++)
  {
    for (i = 1; i <= nbcol; ++i)
    {
      wcol[i] = 0;
      if (iscol[i])
      {
        GEN c = gmael(M, i, 1);
        long lc = lg(c);
        for (j = 1; j < lc; ++j)
          if (Wrow[c[j]] == m) {  wcol[i]++; last = 1; }
      }
    }
  }
  per = vecsmall_indexsort(wcol);
  *w = wcol[per[nbcol]];
  return per;
}

/* M is a RgMs with nbrow rows, A a list of row indices.
   Eliminate rows of M with a single entry that do not belong to A,
   and the corresponding columns. Also eliminate columns until #colums=#rows.
   Return pcol and prow:
   pcol is a map from the new columns indices to the old one.
   prow is a map from the old rows indices to the new one (0 if removed).
*/

void
RgMs_structelim(GEN M, long nbrow, GEN A, GEN *p_col, GEN *p_row)
{
  long i,j,k;
  long nbcol = lg(M)-1, lA = lg(A);
  GEN prow = cgetg(nbrow+1, t_VECSMALL);
  GEN pcol = zero_zv(nbcol);
  pari_sp av = avma;
  long rcol = nbcol, rrow = 0, imin = nbcol - usqrt(nbcol);
  GEN iscol = const_vecsmall(nbcol, 1);
  GEN Wrow  = zero_zv(nbrow);
  GEN wcol = cgetg(nbcol+1, t_VECSMALL);
  pari_sp av2=avma;
  for (i = 1; i <= nbcol; ++i)
  {
    GEN F = gmael(M, i, 1);
    long l = lg(F)-1;
    for (j = 1; j <= l; ++j)
      Wrow[F[j]]++;
  }
  for (j = 1; j < lA; ++j)
  {
    if (Wrow[A[j]] == 0) { *p_col=NULL; return; }
    Wrow[A[j]] = -1;
  }
  for (i = 1; i <= nbrow; ++i)
    if (Wrow[i])
      rrow++;
  rem_singleton(M, iscol, Wrow, &rcol, &rrow);
  if (rcol<rrow) pari_err_BUG("RgMs_structelim, rcol<rrow");
  for (; rcol>rrow;)
  {
    long w;
    GEN per = fill_wcol(M, iscol, Wrow, &w, wcol);
    for (i = nbcol; i>=imin && wcol[per[i]]>=w && rcol>rrow; i--)
      rem_col(gmael(M, per[i], 1), per[i], iscol, Wrow, &rcol, &rrow);
    rem_singleton(M, iscol, Wrow, &rcol, &rrow);
    avma = av2;
  }
  for (j = 1, i = 1; i <= nbcol; ++i)
    if (iscol[i])
      pcol[j++] = i;
  setlg(pcol,j);
  for (k = 1, i = 1; i <= nbrow; ++i)
    prow[i] = Wrow[i] ? k++: 0;
  avma = av;
  *p_col = pcol; *p_row = prow;
}

/*******************************************************************/
/*                                                                 */
/*                        EIGENVECTORS                             */
/*   (independent eigenvectors, sorted by increasing eigenvalue)   */
/*                                                                 */
/*******************************************************************/

GEN
mateigen(GEN x, long flag, long prec)
{
  GEN y, R, T;
  long k, l, ex, n = lg(x);
  pari_sp av = avma;

  if (typ(x)!=t_MAT) pari_err_TYPE("eigen",x);
  if (n != 1 && n != lgcols(x)) pari_err_DIM("eigen");
  if (flag < 0 || flag > 1) pari_err_FLAG("mateigen");
  if (n == 1)
  {
    if (flag) retmkvec2(cgetg(1,t_VEC), cgetg(1,t_MAT));
    return cgetg(1,t_VEC);
  }
  if (n == 2)
  {
    if (flag) retmkvec2(mkveccopy(gcoeff(x,1,1)), matid(1));
    return matid(1);
  }

  ex = 16 - prec2nbits(prec);
  T = charpoly(x,0);
  if (RgX_is_QX(T))
  {
    T = Q_primpart(T);
    (void)ZX_gcd_all(T, ZX_deriv(T),  &T);
    R = nfrootsQ(T);
    if (lg(R)-1 < degpol(T))
    { /* add missing complex roots */
      GEN r = cleanroots(RgX_div(T, roots_to_pol(R, 0)), prec);
      settyp(r, t_VEC);
      R = shallowconcat(R, r);
    }
  }
  else
  {
    GEN r1, v = vectrunc_init(lg(T));
    long e;
    R = cleanroots(T,prec);
    r1 = NULL;
    for (k = 1; k < lg(R); k++)
    {
      GEN r2 = gel(R,k), r = grndtoi(r2, &e);
      if (e < ex) r2 = r;
      if (r1)
      {
        r = gsub(r1,r2);
        if (gequal0(r) || gexpo(r) < ex) continue;
      }
      vectrunc_append(v, r2);
      r1 = r2;
    }
    R = v;
  }
  /* R = distinct complex roots of charpoly(x) */
  l = lg(R); y = cgetg(l, t_VEC);
  for (k = 1; k < l; k++)
  {
    GEN F = ker_aux(RgM_Rg_sub_shallow(x, gel(R,k)), x);
    long d = lg(F)-1;
    if (!d) pari_err_PREC("mateigen");
    gel(y,k) = F;
    if (flag) gel(R,k) = const_vec(d, gel(R,k));
  }
  y = shallowconcat1(y);
  if (lg(y) > n) pari_err_PREC("mateigen");
  /* lg(y) < n if x is not diagonalizable */
  if (flag) y = mkvec2(shallowconcat1(R), y);
  return gerepilecopy(av,y);
}
GEN
eigen(GEN x, long prec) { return mateigen(x, 0, prec); }

/*******************************************************************/
/*                                                                 */
/*                           DETERMINANT                           */
/*                                                                 */
/*******************************************************************/

GEN
det0(GEN a,long flag)
{
  switch(flag)
  {
    case 0: return det(a);
    case 1: return det2(a);
    default: pari_err_FLAG("matdet");
  }
  return NULL; /* not reached */
}

/* M a 2x2 matrix, returns det(M) */
static GEN
RgM_det2(GEN M)
{
  pari_sp av = avma;
  GEN a = gcoeff(M,1,1), b = gcoeff(M,1,2);
  GEN c = gcoeff(M,2,1), d = gcoeff(M,2,2);
  return gerepileupto(av, gsub(gmul(a,d), gmul(b,c)));
}
/* M a 2x2 ZM, returns det(M) */
static GEN
ZM_det2(GEN M)
{
  pari_sp av = avma;
  GEN a = gcoeff(M,1,1), b = gcoeff(M,1,2);
  GEN c = gcoeff(M,2,1), d = gcoeff(M,2,2);
  return gerepileuptoint(av, subii(mulii(a,d), mulii(b, c)));
}
/* M a 3x3 ZM, return det(M) */
static GEN
ZM_det3(GEN M)
{
  pari_sp av = avma;
  GEN a = gcoeff(M,1,1), b = gcoeff(M,1,2), c = gcoeff(M,1,3);
  GEN d = gcoeff(M,2,1), e = gcoeff(M,2,2), f = gcoeff(M,2,3);
  GEN g = gcoeff(M,3,1), h = gcoeff(M,3,2), i = gcoeff(M,3,3);
  GEN t, D = signe(i)? mulii(subii(mulii(a,e), mulii(b,d)), i): gen_0;
  if (signe(g))
  {
    t = mulii(subii(mulii(b,f), mulii(c,e)), g);
    D = addii(D, t);
  }
  if (signe(h))
  {
    t = mulii(subii(mulii(c,d), mulii(a,f)), h);
    D = addii(D, t);
  }
  return gerepileuptoint(av, D);
}

static GEN
det_simple_gauss(GEN a, GEN data, pivot_fun pivot)
{
  pari_sp av = avma;
  long i,j,k, s = 1, nbco = lg(a)-1;
  GEN p, x = gen_1;

  a = RgM_shallowcopy(a);
  for (i=1; i<nbco; i++)
  {
    k = pivot(a, data, i, NULL);
    if (k > nbco) return gerepilecopy(av, gcoeff(a,i,i));
    if (k != i)
    { /* exchange the lines s.t. k = i */
      for (j=i; j<=nbco; j++) swap(gcoeff(a,i,j), gcoeff(a,k,j));
      s = -s;
    }
    p = gcoeff(a,i,i);

    x = gmul(x,p);
    for (k=i+1; k<=nbco; k++)
    {
      GEN m = gcoeff(a,i,k);
      if (gequal0(m)) continue;

      m = gdiv(m,p);
      for (j=i+1; j<=nbco; j++)
      {
        gcoeff(a,j,k) = gsub(gcoeff(a,j,k), gmul(m,gcoeff(a,j,i)));
        if (gc_needed(av,3))
        {
          if(DEBUGMEM>1) pari_warn(warnmem,"det. col = %ld",i);
          gerepileall(av,2, &a,&x);
          p = gcoeff(a,i,i);
          m = gcoeff(a,i,k); m = gdiv(m, p);
        }
      }
    }
  }
  if (s < 0) x = gneg_i(x);
  return gerepileupto(av, gmul(x, gcoeff(a,nbco,nbco)));
}

GEN
det2(GEN a)
{
  GEN data;
  pivot_fun pivot;
  long n = lg(a)-1;
  if (typ(a)!=t_MAT) pari_err_TYPE("det2",a);
  if (!n) return gen_1;
  if (n != nbrows(a)) pari_err_DIM("det2");
  if (n == 1) return gcopy(gcoeff(a,1,1));
  if (n == 2) return RgM_det2(a);
  pivot = get_pivot_fun(a, a, &data);
  return det_simple_gauss(a, data, pivot);
}

static GEN
mydiv(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y);
  if (tx == ty && tx == t_POL && varn(x) == varn(y)) return RgX_div(x,y);
  return gdiv(x,y);
}

/* Assumes a a square t_MAT of dimension n > 0. Returns det(a) using
 * Gauss-Bareiss. */
static GEN
det_bareiss(GEN a)
{
  pari_sp av = avma;
  long nbco = lg(a)-1,i,j,k,s = 1;
  GEN p, pprec;

  a = RgM_shallowcopy(a);
  for (pprec=gen_1,i=1; i<nbco; i++,pprec=p)
  {
    GEN ci, ck, m;
    int diveuc = (gequal1(pprec)==0);

    p = gcoeff(a,i,i);
    if (gequal0(p))
    {
      k=i+1; while (k<=nbco && gequal0(gcoeff(a,i,k))) k++;
      if (k>nbco) return gerepilecopy(av, p);
      swap(gel(a,k), gel(a,i)); s = -s;
      p = gcoeff(a,i,i);
    }
    ci = gel(a,i);
    for (k=i+1; k<=nbco; k++)
    {
      ck = gel(a,k); m = gel(ck,i);
      if (gequal0(m))
      {
        if (gequal1(p))
        {
          if (diveuc)
            gel(a,k) = mydiv(gel(a,k), pprec);
        }
        else
          for (j=i+1; j<=nbco; j++)
          {
            GEN p1 = gmul(p, gel(ck,j));
            if (diveuc) p1 = mydiv(p1,pprec);
            gel(ck,j) = p1;
          }
      }
      else
      {
        for (j=i+1; j<=nbco; j++)
        {
          pari_sp av2 = avma;
          GEN p1 = gsub(gmul(p,gel(ck,j)), gmul(m,gel(ci,j)));
          if (diveuc) p1 = mydiv(p1,pprec);
          gel(ck,j) = gerepileupto(av2, p1);
          if (gc_needed(av,2))
          {
            if(DEBUGMEM>1) pari_warn(warnmem,"det. col = %ld",i);
            gerepileall(av,2, &a,&pprec);
            ci = gel(a,i);
            ck = gel(a,k); m = gel(ck,i);
            p = gcoeff(a,i,i);
          }
        }
      }
    }
  }
  p = gcoeff(a,nbco,nbco);
  p = (s < 0)? gneg(p): gcopy(p);
  return gerepileupto(av, p);
}

/* count non-zero entries in col j, at most 'max' of them.
 * Return their indices */
static GEN
col_count_non_zero(GEN a, long j, long max)
{
  GEN v = cgetg(max+1, t_VECSMALL);
  GEN c = gel(a,j);
  long i, l = lg(a), k = 1;
  for (i = 1; i < l; i++)
    if (!gequal0(gel(c,i)))
    {
      if (k > max) return NULL; /* fail */
      v[k++] = i;
    }
  setlg(v, k); return v;
}
/* count non-zero entries in row i, at most 'max' of them.
 * Return their indices */
static GEN
row_count_non_zero(GEN a, long i, long max)
{
  GEN v = cgetg(max+1, t_VECSMALL);
  long j, l = lg(a), k = 1;
  for (j = 1; j < l; j++)
    if (!gequal0(gcoeff(a,i,j)))
    {
      if (k > max) return NULL; /* fail */
      v[k++] = j;
    }
  setlg(v, k); return v;
}

static GEN det_develop(GEN a, long max, double bound);
/* (-1)^(i+j) a[i,j] * det RgM_minor(a,i,j) */
static GEN
coeff_det(GEN a, long i, long j, long max, double bound)
{
  GEN c = gcoeff(a, i, j);
  c = gmul(c, det_develop(RgM_minor(a, i,j), max, bound));
  if (odd(i+j)) c = gneg(c);
  return c;
}
/* a square t_MAT, 'bound' a rough upper bound for the number of
 * multiplications we are willing to pay while developing rows/columns before
 * switching to Gaussian elimination */
static GEN
det_develop(GEN M, long max, double bound)
{
  pari_sp av = avma;
  long i,j, n = lg(M)-1, lbest = max+2, best_col = 0, best_row = 0;
  GEN best = NULL;

  if (bound < 1.) return det_bareiss(M); /* too costly now */

  switch(n)
  {
    case 0: return gen_1;
    case 1: return gcopy(gcoeff(M,1,1));
    case 2: return RgM_det2(M);
  }
  if (max > ((n+2)>>1)) max = (n+2)>>1;
  for (j = 1; j <= n; j++)
  {
    pari_sp av2 = avma;
    GEN v = col_count_non_zero(M, j, max);
    long lv;
    if (!v || (lv = lg(v)) >= lbest) { avma = av2; continue; }
    if (lv == 1) { avma = av; return gen_0; }
    if (lv == 2) {
      avma = av;
      return gerepileupto(av, coeff_det(M,v[1],j,max,bound));
    }
    best = v; lbest = lv; best_col = j;
  }
  for (i = 1; i <= n; i++)
  {
    pari_sp av2 = avma;
    GEN v = row_count_non_zero(M, i, max);
    long lv;
    if (!v || (lv = lg(v)) >= lbest) { avma = av2; continue; }
    if (lv == 1) { avma = av; return gen_0; }
    if (lv == 2) {
      avma = av;
      return gerepileupto(av, coeff_det(M,i,v[1],max,bound));
    }
    best = v; lbest = lv; best_row = i;
  }
  if (best_row)
  {
    double d = lbest-1;
    GEN s = NULL;
    long k;
    bound /= d*d*d;
    for (k = 1; k < lbest; k++)
    {
      GEN c = coeff_det(M, best_row, best[k], max, bound);
      s = s? gadd(s, c): c;
    }
    return gerepileupto(av, s);
  }
  if (best_col)
  {
    double d = lbest-1;
    GEN s = NULL;
    long k;
    bound /= d*d*d;
    for (k = 1; k < lbest; k++)
    {
      GEN c = coeff_det(M, best[k], best_col, max, bound);
      s = s? gadd(s, c): c;
    }
    return gerepileupto(av, s);
  }
  return det_bareiss(M);
}

/* area of parallelogram bounded by (v1,v2) */
static GEN
parallelogramarea(GEN v1, GEN v2)
{ return gsub(gmul(gnorml2(v1), gnorml2(v2)), gsqr(RgV_dotproduct(v1, v2))); }

/* Square of Hadamard bound for det(a), a square matrix.
 * Slightly improvement: instead of using the column norms, use the area of
 * the parallelogram formed by pairs of consecutive vectors */
GEN
RgM_Hadamard(GEN a)
{
  pari_sp av = avma;
  long n = lg(a)-1, i;
  GEN B;
  if (n == 0) return gen_1;
  if (n == 1) return gsqr(gcoeff(a,1,1));
  a = RgM_gtofp(a, LOWDEFAULTPREC);
  B = gen_1;
  for (i = 1; i <= n/2; i++)
    B = gmul(B, parallelogramarea(gel(a,2*i-1), gel(a,2*i)));
  if (odd(n)) B = gmul(B, gnorml2(gel(a, n)));
  return gerepileuptoint(av, ceil_safe(B));
}

/* assume dim(a) = n > 0 */
static GEN
ZM_det_i(GEN M, long n)
{
  const long DIXON_THRESHOLD = 40;
  pari_sp av = avma, av2;
  long i;
  ulong p, compp, Dp = 1;
  forprime_t S;
  GEN D, h, q, v, comp;
  if (n == 1) return icopy(gcoeff(M,1,1));
  if (n == 2) return ZM_det2(M);
  if (n == 3) return ZM_det3(M);
  h = RgM_Hadamard(M);
  if (!signe(h)) { avma = av; return gen_0; }
  h = sqrti(h); q = gen_1;
  init_modular(&S);
  p = 0; /* -Wall */
  while( cmpii(q, h) <= 0 && (p = u_forprime_next(&S)) )
  {
    av2 = avma; Dp = Flm_det(ZM_to_Flm(M, p), p);
    avma = av2;
    if (Dp) break;
    q = muliu(q, p);
  }
  if (!p) pari_err_OVERFLOW("ZM_det [ran out of primes]");
  if (!Dp) { avma = av; return gen_0; }
  if (n <= DIXON_THRESHOLD)
    D = q;
  else
  {
    av2 = avma;
    v = cgetg(n+1, t_COL);
    gel(v, 1) = gen_1; /* ensure content(v) = 1 */
    for (i = 2; i <= n; i++) gel(v, i) = stoi(random_Fl(15) - 7);
    D = Q_denom(ZM_gauss(M, v));
    if (expi(D) < expi(h) >> 1)
    { /* First try unlucky, try once more */
      for (i = 2; i <= n; i++) gel(v, i) = stoi(random_Fl(15) - 7);
      D = lcmii(D, Q_denom(ZM_gauss(M, v)));
    }
    D = gerepileuptoint(av2, D);
    if (q != gen_1) D = lcmii(D, q);
  }
  /* determinant is M multiple of D */
  h = shifti(divii(h, D), 1);

  compp = Fl_div(Dp, umodiu(D,p), p);
  comp = Z_init_CRT(compp, p);
  q = utoipos(p);
  while (cmpii(q, h) <= 0)
  {
    p = u_forprime_next(&S);
    if (!p) pari_err_OVERFLOW("ZM_det [ran out of primes]");
    Dp = umodiu(D, p);
    if (!Dp) continue;
    av2 = avma;
    compp = Fl_div(Flm_det(ZM_to_Flm(M, p), p), Dp, p);
    avma = av2;
    (void) Z_incremental_CRT(&comp, compp, &q, p);
  }
  return gerepileuptoint(av, mulii(comp, D));
}

static long
det_init_max(long n)
{
  if (n > 100) return 0;
  if (n > 50) return 1;
  if (n > 30) return 4;
  return 7;
}

GEN
det(GEN a)
{
  long n = lg(a)-1;
  double B;
  GEN data, ff = NULL, p = NULL;
  pivot_fun pivot;

  if (typ(a)!=t_MAT) pari_err_TYPE("det",a);
  if (!n) return gen_1;
  if (n != nbrows(a)) pari_err_DIM("det");
  if (n == 1) return gcopy(gcoeff(a,1,1));
  if (n == 2) return RgM_det2(a);
  if (RgM_is_FpM(a, &p))
  {
    pari_sp av = avma;
    ulong pp, d;
    if (!p) return ZM_det_i(a, n); /* ZM */
    /* FpM */
    a = RgM_Fp_init(a,p,&pp);
    switch(pp)
    {
    case 0: return gerepileupto(av, Fp_to_mod(FpM_det(a,p),p)); break;
    case 2: d = F2m_det(a); break;
    default:d = Flm_det(a,pp); break;
    }
    avma = av; return mkintmodu(d, pp);
  }
  if (RgM_is_FFM(a, &ff)) return FFM_det(a, ff);
  pivot = get_pivot_fun(a, a, &data);
  if (pivot != gauss_get_pivot_NZ) return det_simple_gauss(a, data, pivot);
  B = (double)n;
  return det_develop(a, det_init_max(n), B*B*B);
}

GEN
ZM_det(GEN a)
{
  long n = lg(a)-1;
  if (!n) return gen_1;
  return ZM_det_i(a, n);
}

/* return a solution of congruence system sum M_{ i,j } X_j = Y_i mod D_i
 * If ptu1 != NULL, put in *ptu1 a Z-basis of the homogeneous system */
static GEN
gaussmoduloall(GEN M, GEN D, GEN Y, GEN *ptu1)
{
  pari_sp av = avma;
  long n, m, j, l, lM;
  GEN delta, H, U, u1, u2, x;

  if (typ(M)!=t_MAT) pari_err_TYPE("gaussmodulo",M);
  lM = lg(M);
  if (lM == 1)
  {
    switch(typ(Y))
    {
      case t_INT: break;
      case t_COL: if (lg(Y) != 1) pari_err_DIM("gaussmodulo");
                  break;
      default: pari_err_TYPE("gaussmodulo",Y);
    }
    switch(typ(D))
    {
      case t_INT: break;
      case t_COL: if (lg(D) != 1) pari_err_DIM("gaussmodulo");
                  break;
      default: pari_err_TYPE("gaussmodulo",D);
    }
    if (ptu1) *ptu1 = cgetg(1, t_MAT);
    return gen_0;
  }
  n = nbrows(M);
  switch(typ(D))
  {
    case t_COL:
      if (lg(D)-1!=n) pari_err_DIM("gaussmodulo");
      delta = diagonal_shallow(D); break;
    case t_INT: delta = scalarmat_shallow(D,n); break;
    default: pari_err_TYPE("gaussmodulo",D);
      return NULL; /* not reached */
  }
  switch(typ(Y))
  {
    case t_INT: Y = const_col(n, Y); break;
    case t_COL:
      if (lg(Y)-1!=n) pari_err_DIM("gaussmodulo");
      break;
    default: pari_err_TYPE("gaussmodulo",Y);
      return NULL; /* not reached */
  }
  H = ZM_hnfall(shallowconcat(M,delta), &U, 1);
  Y = hnf_solve(H,Y); if (!Y) return gen_0;
  l = lg(H); /* may be smaller than lM if some moduli are 0 */
  n = l-1;
  m = lg(U)-1 - n;
  u1 = cgetg(m+1,t_MAT);
  u2 = cgetg(n+1,t_MAT);
  for (j=1; j<=m; j++) { GEN c = gel(U,j); setlg(c,lM); gel(u1,j) = c; }
  U += m;
  for (j=1; j<=n; j++) { GEN c = gel(U,j); setlg(c,lM); gel(u2,j) = c; }
  /*       (u1 u2)
   * (M D) (*  * ) = (0 H) */
  u1 = ZM_lll(u1, 0.75, LLL_INPLACE);
  Y = ZM_ZC_mul(u2,Y);
  x = ZC_reducemodmatrix(Y, u1);
  if (!ptu1) x = gerepileupto(av, x);
  else
  {
    gerepileall(av, 2, &x, &u1);
    *ptu1 = u1;
  }
  return x;
}

GEN
matsolvemod0(GEN M, GEN D, GEN Y, long flag)
{
  pari_sp av;
  GEN p1,y;

  if (!flag) return gaussmoduloall(M,D,Y,NULL);

  av=avma; y = cgetg(3,t_VEC);
  p1 = gaussmoduloall(M,D,Y, (GEN*)y+2);
  if (p1==gen_0) { avma=av; return gen_0; }
  gel(y,1) = p1; return y;
}

GEN
gaussmodulo2(GEN M, GEN D, GEN Y) { return matsolvemod0(M,D,Y,1); }

GEN
gaussmodulo(GEN M, GEN D, GEN Y) { return matsolvemod0(M,D,Y,0); }
