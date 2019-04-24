/* Copyright (C) 2012  The PARI group.

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

/***********************************************************************/
/**                                                                   **/
/**               Factorisation over finite field                     **/
/**                                                                   **/
/***********************************************************************/

/*******************************************************************/
/*                                                                 */
/*           ROOTS MODULO a prime p (no multiplicities)            */
/*                                                                 */
/*******************************************************************/
/* Check types and replace F by a monic normalized FpX having the same roots
 * Don't bother to make constant polynomials monic */
static void
factmod_init(GEN *F, GEN p)
{
  if (typ(p)!=t_INT) pari_err_TYPE("factmod",p);
  if (signe(p) < 0) pari_err_PRIME("factmod",p);
  if (typ(*F)!=t_POL) pari_err_TYPE("factmod",*F);
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    if (pp < 2) pari_err_PRIME("factmod", p);
    *F = RgX_to_Flx(*F, pp);
    if (lg(*F) > 3) *F = Flx_normalize(*F, pp);
  }
  else
  {
    *F = RgX_to_FpX(*F, p);
    if (lg(*F) > 3) *F = FpX_normalize(*F, p);
  }
}
/* as above, assume p prime and *F a ZX */
static void
ZX_factmod_init(GEN *F, GEN p)
{
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    *F = ZX_to_Flx(*F, pp);
    if (lg(*F) > 3) *F = Flx_normalize(*F, pp);
  }
  else
  {
    *F = FpX_red(*F, p);
    if (lg(*F) > 3) *F = FpX_normalize(*F, p);
  }
}

/* return 1,...,p-1 [not_0 = 1] or 0,...,p [not_0 = 0] */
static GEN
all_roots_mod_p(ulong p, int not_0)
{
  GEN r;
  ulong i;
  if (not_0) {
    r = cgetg(p, t_VECSMALL);
    for (i = 1; i < p; i++) r[i] = i;
  } else {
    r = cgetg(p+1, t_VECSMALL);
    for (i = 0; i < p; i++) r[i+1] = i;
  }
  return r;
}

/* X^n - 1 */
static GEN
Flx_Xnm1(long sv, long n, ulong p)
{
  GEN t = cgetg(n+3, t_VECSMALL);
  long i;
  t[1] = sv;
  t[2] = p - 1;
  for (i = 3; i <= n+1; i++) t[i] = 0;
  t[i] = 1; return t;
}
/* X^n + 1 */
static GEN
Flx_Xn1(long sv, long n, ulong p)
{
  GEN t = cgetg(n+3, t_VECSMALL);
  long i;
  (void) p;
  t[1] = sv;
  t[2] = 1;
  for (i = 3; i <= n+1; i++) t[i] = 0;
  t[i] = 1; return t;
}

static ulong
Fl_nonsquare(ulong p)
{
  long k = 2;
  for (;; k++)
  {
    long i = krouu(k, p);
    if (!i) pari_err_PRIME("Fl_nonsquare",utoipos(p));
    if (i < 0) return k;
  }
}

/* f monic Flx, f(0) != 0. Return a monic squarefree g with the same
 * roots as f */
static GEN
Flx_cut_out_roots(GEN f, ulong p)
{
  GEN g = Flx_mod_Xnm1(f, p-1, p); /* f mod x^(p-1) - 1 */
  if (g != f && degpol(g) >= 0) {
    (void)Flx_valrem(g, &g); /* reduction may introduce 0 root */
    g = Flx_gcd(g, Flx_Xnm1(g[1], p-1, p), p);
    g = Flx_normalize(g, p);
  }
  return g;
}

/* by checking f(0..p-1) */
GEN
Flx_roots_naive(GEN f, ulong p)
{
  long d, n = 0;
  ulong s = 1UL, r;
  GEN q, y = cgetg(degpol(f) + 1, t_VECSMALL);
  pari_sp av2, av = avma;

  if (Flx_valrem(f, &f)) y[++n] = 0;
  f = Flx_cut_out_roots(f, p);
  d = degpol(f);
  if (d < 0) return all_roots_mod_p(p, n == 0);
  av2 = avma;
  while (d > 1) /* d = current degree of f */
  {
    q = Flx_div_by_X_x(f, s, p, &r); /* TODO: FFT-type multi-evaluation */
    if (r) avma = av2; else { y[++n] = s; d--; f = q; av2 = avma; }
    if (++s == p) break;
  }
  if (d == 1)
  { /* -f[2]/f[3], root of deg 1 polynomial */
    r = Fl_mul(p - Fl_inv(f[3], p), f[2], p);
    if (r >= s) y[++n] = r; /* otherwise double root */
  }
  avma = av; fixlg(y, n+1); return y;
}
static GEN
Flx_root_mod_2(GEN f)
{
  int z1, z0 = !(f[2] & 1);
  long i,n;
  GEN y;

  for (i=2, n=1; i < lg(f); i++) n += f[i];
  z1 = n & 1;
  y = cgetg(z0+z1+1, t_VECSMALL); i = 1;
  if (z0) y[i++] = 0;
  if (z1) y[i  ] = 1;
  return y;
}
static ulong
Flx_oneroot_mod_2(GEN f)
{
  long i,n;
  if (!(f[2] & 1)) return 0;
  for (i=2, n=1; i < lg(f); i++) n += f[i];
  if (n & 1) return 1;
  return 2;
}

static GEN FpX_roots_i(GEN f, GEN p);
static GEN Flx_roots_i(GEN f, ulong p);
static GEN FpX_Berlekamp_i(GEN f, GEN pp, long flag);

/* Generic driver to computes the roots of f modulo pp, using 'Roots' when
 * pp is a small prime.
 * if (gpwrap), check types thoroughly and return t_INTMODs, otherwise
 * assume that f is an FpX, pp a prime and return t_INTs */
static GEN
rootmod_aux(GEN f, GEN pp, GEN (*Roots)(GEN,ulong), int gpwrap)
{
  pari_sp av = avma;
  GEN y;
  if (gpwrap)
    factmod_init(&f, pp);
  else
    ZX_factmod_init(&f, pp);
  switch(lg(f))
  {
    case 2: pari_err_ROOTS0("rootmod");
    case 3: avma = av; return cgetg(1,t_COL);
  }
  if (typ(f) == t_VECSMALL)
  {
    ulong p = pp[2];
    if (p == 2)
      y = Flx_root_mod_2(f);
    else
    {
      if (!odd(p)) pari_err_PRIME("rootmod",utoi(p));
      y = Roots(f, p);
    }
    y = Flc_to_ZC(y);
  }
  else
    y = FpX_roots_i(f, pp);
  if (gpwrap) y = FpC_to_mod(y, pp);
  return gerepileupto(av, y);
}
/* assume that f is a ZX an pp a prime */
GEN
FpX_roots(GEN f, GEN pp)
{ return rootmod_aux(f, pp, Flx_roots_i, 0); }
/* no assumptions on f and pp */
GEN
rootmod2(GEN f, GEN pp) { return rootmod_aux(f, pp, &Flx_roots_naive, 1); }
GEN
rootmod(GEN f, GEN pp) { return rootmod_aux(f, pp, &Flx_roots_i, 1); }
GEN
rootmod0(GEN f, GEN p, long flag)
{
  switch(flag)
  {
    case 0: return rootmod(f,p);
    case 1: return rootmod2(f,p);
    default: pari_err_FLAG("polrootsmod");
  }
  return NULL; /* not reached */
}

/* assume x reduced mod p > 2, monic. */
static int
FpX_quad_factortype(GEN x, GEN p)
{
  GEN b = gel(x,3), c = gel(x,2);
  GEN D = subii(sqri(b), shifti(c,2));
  return kronecker(D,p);
}
/* assume x reduced mod p, monic. Return one root, or NULL if irreducible */
GEN
FpX_quad_root(GEN x, GEN p, int unknown)
{
  GEN s, D, b = gel(x,3), c = gel(x,2);

  if (equaliu(p, 2)) {
    if (!signe(b)) return c;
    return signe(c)? NULL: gen_1;
  }
  D = subii(sqri(b), shifti(c,2));
  D = remii(D,p);
  if (unknown && kronecker(D,p) == -1) return NULL;

  s = Fp_sqrt(D,p);
  /* p is not prime, go on and give e.g. maxord a chance to recover */
  if (!s) return NULL;
  return Fp_halve(Fp_sub(s,b, p), p);
}
static GEN
FpX_otherroot(GEN x, GEN r, GEN p)
{ return Fp_neg(Fp_add(gel(x,3), r, p), p); }

/* disc(x^2+bx+c) = b^2 - 4c */
static ulong
Fl_disc_bc(ulong b, ulong c, ulong p)
{ return Fl_sub(Fl_sqr(b,p), Fl_double(Fl_double(c,p),p), p); }
/* p > 2 */
static ulong
Flx_quad_root(GEN x, ulong p, int unknown)
{
  ulong s, b = x[3], c = x[2];
  ulong D = Fl_disc_bc(b, c, p);
  if (unknown && krouu(D,p) == -1) return p;
  s = Fl_sqrt(D,p);
  if (s==~0UL) return p;
  return Fl_halve(Fl_sub(s,b, p), p);
}
static ulong
Flx_otherroot(GEN x, ulong r, ulong p)
{ return Fl_neg(Fl_add(x[3], r, p), p); }


/* 'todo' contains the list of factors to be split.
 * 'done' the list of finished factors, no longer touched */
struct split_t { GEN todo, done; };
static void
split_init(struct split_t *S, long max)
{
  S->todo = vectrunc_init(max);
  S->done = vectrunc_init(max);
}
#if 0
/* move todo[i] to done */
static void
split_convert(struct split_t *S, long i)
{
  long n = lg(S->todo)-1;
  vectrunc_append(S->done, gel(S->todo,i));
  if (n) gel(S->todo,i) = gel(S->todo, n);
  setlg(S->todo, n);
}
#endif
/* append t to todo */
static void
split_add(struct split_t *S, GEN t) { vectrunc_append(S->todo, t); }
/* delete todo[i], add t to done */
static void
split_moveto_done(struct split_t *S, long i, GEN t)
{
  long n = lg(S->todo)-1;
  vectrunc_append(S->done, t);
  if (n) gel(S->todo,i) = gel(S->todo, n);
  setlg(S->todo, n);

}
/* append t to done */
static void
split_add_done(struct split_t *S, GEN t)
{ vectrunc_append(S->done, t); }
/* split todo[i] into a and b */
static void
split_todo(struct split_t *S, long i, GEN a, GEN b)
{
  gel(S->todo, i) = a;
  split_add(S, b);
}
/* split todo[i] into a and b, moved to done */
static void
split_done(struct split_t *S, long i, GEN a, GEN b)
{
  split_moveto_done(S, i, a);
  split_add_done(S, b);
}

/* by splitting, assume p > 2 prime, deg(f) > 0, and f monic */
static GEN
FpX_roots_i(GEN f, GEN p)
{
  GEN pol, pol0, a, q;
  struct split_t S;

  split_init(&S, lg(f)-1);
  settyp(S.done, t_COL);
  if (ZX_valrem(f, &f)) split_add_done(&S, gen_0);
  switch(degpol(f))
  {
    case 0: return ZC_copy(S.done);
    case 1: split_add_done(&S, subii(p, gel(f,2))); return ZC_copy(S.done);
    case 2: {
      GEN s, r = FpX_quad_root(f, p, 1);
      if (r) {
        split_add_done(&S, r);
        s = FpX_otherroot(f,r, p);
        /* f not known to be square free yet */
        if (!equalii(r, s)) split_add_done(&S, s);
      }
      return sort(S.done);
    }
  }

  a = FpXQ_pow(pol_x(varn(f)), subiu(p,1), f,p);
  if (lg(a) < 3) pari_err_PRIME("rootmod",p);
  a = FpX_Fp_sub_shallow(a, gen_1, p); /* a = x^(p-1) - 1 mod f */
  a = FpX_gcd(f,a, p);
  if (!degpol(a)) return ZC_copy(S.done);
  split_add(&S, FpX_normalize(a,p));

  q = shifti(p,-1);
  pol0 = icopy(gen_1); /* constant term, will vary in place */
  pol = deg1pol_shallow(gen_1, pol0, varn(f));
  for (pol0[2] = 1;; pol0[2]++)
  {
    long j, l = lg(S.todo);
    if (l == 1) return sort(S.done);
    if (pol0[2] == 100 && !BPSW_psp(p)) pari_err_PRIME("polrootsmod",p);
    for (j = 1; j < l; j++)
    {
      GEN c = gel(S.todo,j);
      switch(degpol(c))
      { /* convert linear and quadratics to roots, try to split the rest */
        case 1:
          split_moveto_done(&S, j, subii(p, gel(c,2)));
          j--; l--; break;
        case 2: {
          GEN r = FpX_quad_root(c, p, 0), s = FpX_otherroot(c,r, p);
          split_done(&S, j, r, s);
          j--; l--; break;
        }
        default: {
          /* b = pol^(p-1)/2 - 1 */
          GEN b = FpX_Fp_sub_shallow(FpXQ_pow(pol,q, c,p), gen_1, p);
          long db;
          b = FpX_gcd(c,b, p); db = degpol(b);
          if (db && db < degpol(c))
          {
            b = FpX_normalize(b, p);
            c = FpX_div(c,b, p);
            split_todo(&S, j, b, c);
          }
        }
      }
    }
  }
}

/* Assume f is normalized */
static ulong
Flx_cubic_root(GEN ff, ulong p)
{
  GEN f = Flx_normalize(ff,p);
  ulong pi = get_Fl_red(p);
  ulong a = f[4], b=f[3], c=f[2], p3 = p%3==1 ? (2*p+1)/3 :(p+1)/3;
  ulong t = Fl_mul_pre(a, p3, p, pi), t2 = Fl_sqr_pre(t, p, pi);
  ulong A = Fl_sub(b, Fl_triple(t2, p), p);
  ulong B = Fl_add(Fl_mul_pre(t, Fl_sub(Fl_double(t2, p), b, p), p ,pi), c, p);
  ulong A3 =  Fl_mul_pre(A, p3, p, pi);
  ulong A32 = Fl_sqr_pre(A3, p, pi), A33 = Fl_mul_pre(A3, A32, p, pi);
  ulong S = Fl_neg(B,p), P = Fl_neg(A3,p);
  ulong D = Fl_add(Fl_sqr_pre(S, p, pi), Fl_double(Fl_double(A33, p), p), p);
  ulong s = Fl_sqrt_pre(D, p, pi), vS1, vS2;
  if (s!=~0UL)
  {
    ulong S1 = S==s ? S: Fl_halve(Fl_sub(S, s, p), p);
    if (p%3==2) /* 1 solutions */
      vS1 = Fl_powu_pre(S1, (2*p-1)/3, p, pi);
    else
    {
      vS1 = Fl_sqrtl_pre(S1, 3, p, pi);
      if (vS1==~0UL) return p; /*0 solutions*/
      /*3 solutions*/
    }
    vS2 = P? Fl_mul_pre(P, Fl_inv(vS1, p), p, pi): 0;
    return Fl_sub(Fl_add(vS1,vS2, p), t, p);
  }
  else
  {
    pari_sp av = avma;
    GEN S1 = mkvecsmall2(Fl_halve(S, p), Fl_halve(1UL, p));
    GEN vS1 = Fl2_sqrtn_pre(S1, utoi(3), D, p, pi, NULL);
    ulong Sa;
    if (!vS1) return p; /*0 solutions, p%3==2*/
    Sa = vS1[1];
    if (p%3==1) /*1 solutions*/
    {
      ulong Fa = Fl2_norm_pre(vS1, D, p, pi);
      if (Fa!=P)
        Sa = Fl_mul(Sa, Fl_div(Fa, P, p),p);
    }
    avma = av;
    return Fl_sub(Fl_double(Sa,p),t,p);
  }
}

/* assume p > 2 prime */
static ulong
Flx_oneroot_i(GEN f, ulong p, long fl)
{
  GEN pol, a;
  ulong q;
  long da;

  if (Flx_val(f)) return 0;
  switch(degpol(f))
  {
    case 1: return Fl_neg(f[2], p);
    case 2: return Flx_quad_root(f, p, 1);
    case 3: if (p>3) return Flx_cubic_root(f, p); /*FALL THROUGH*/
  }

  if (!fl)
  {
    a = Flxq_powu(polx_Flx(f[1]), p - 1, f,p);
    if (lg(a) < 3) pari_err_PRIME("rootmod",utoipos(p));
    a = Flx_Fl_add(a, p-1, p); /* a = x^(p-1) - 1 mod f */
    a = Flx_gcd(f,a, p);
  } else a = f;
  da = degpol(a);
  if (!da) return p;
  a = Flx_normalize(a,p);

  q = p >> 1;
  pol = polx_Flx(f[1]);
  for(pol[2] = 1;; pol[2]++)
  {
    if (pol[2] == 1000 && !uisprime(p)) pari_err_PRIME("Flx_oneroot",utoipos(p));
    switch(da)
    {
      case 1: return Fl_neg(a[2], p);
      case 2: return Flx_quad_root(a, p, 0);
      case 3: if (p>3) return Flx_cubic_root(a, p); /*FALL THROUGH*/
      default: {
        GEN b = Flx_Fl_add(Flxq_powu(pol,q, a,p), p-1, p);
        long db;
        b = Flx_gcd(a,b, p); db = degpol(b);
        if (db && db < da)
        {
          b = Flx_normalize(b, p);
          if (db <= (da >> 1)) {
            a = b;
            da = db;
          } else {
            a = Flx_div(a,b, p);
            da -= db;
          }
        }
      }
    }
  }
}

/* assume p > 2 prime */
static GEN
FpX_oneroot_i(GEN f, GEN p)
{
  GEN pol, pol0, a, q;
  long da;

  if (ZX_val(f)) return gen_0;
  switch(degpol(f))
  {
    case 1: return subii(p, gel(f,2));
    case 2: return FpX_quad_root(f, p, 1);
  }

  a = FpXQ_pow(pol_x(varn(f)), subiu(p,1), f,p);
  if (lg(a) < 3) pari_err_PRIME("rootmod",p);
  a = FpX_Fp_sub_shallow(a, gen_1, p); /* a = x^(p-1) - 1 mod f */
  a = FpX_gcd(f,a, p);
  da = degpol(a);
  if (!da) return NULL;
  a = FpX_normalize(a,p);

  q = shifti(p,-1);
  pol0 = icopy(gen_1); /* constant term, will vary in place */
  pol = deg1pol_shallow(gen_1, pol0, varn(f));
  for (pol0[2]=1; ; pol0[2]++)
  {
    if (pol0[2] == 1000 && !BPSW_psp(p)) pari_err_PRIME("FpX_oneroot",p);
    switch(da)
    {
      case 1: return subii(p, gel(a,2));
      case 2: return FpX_quad_root(a, p, 0);
      default: {
        GEN b = FpX_Fp_sub_shallow(FpXQ_pow(pol,q, a,p), gen_1, p);
        long db;
        b = FpX_gcd(a,b, p); db = degpol(b);
        if (db && db < da)
        {
          b = FpX_normalize(b, p);
          if (db <= (da >> 1)) {
            a = b;
            da = db;
          } else {
            a = FpX_div(a,b, p);
            da -= db;
          }
        }
      }
    }
  }
}

ulong
Flx_oneroot(GEN f, ulong p)
{
  pari_sp av = avma;
  ulong r;
  switch(lg(f))
  {
    case 2: return 0;
    case 3: avma = av; return p;
  }
  if (p == 2) return Flx_oneroot_mod_2(f);
  r = Flx_oneroot_i(Flx_normalize(f, p), p, 0);
  avma = av; return r;
}

ulong
Flx_oneroot_split(GEN f, ulong p)
{
  pari_sp av = avma;
  ulong r;
  switch(lg(f))
  {
    case 2: return 0;
    case 3: avma = av; return p;
  }
  if (p == 2) return Flx_oneroot_mod_2(f);
  r = Flx_oneroot_i(Flx_normalize(f, p), p, 1);
  avma = av; return r;
}

/* assume that p is prime */
GEN
FpX_oneroot(GEN f, GEN pp) {
  pari_sp av = avma;
  ZX_factmod_init(&f, pp);
  switch(lg(f))
  {
    case 2: avma = av; return gen_0;
    case 3: avma = av; return NULL;
  }
  if (typ(f) == t_VECSMALL)
  {
    ulong r, p = pp[2];
    if (p == 2)
      r = Flx_oneroot_mod_2(f);
    else
      r = Flx_oneroot_i(f, p, 0);
    avma = av;
    return (r == p)? NULL: utoi(r);
  }
  f = FpX_oneroot_i(f, pp);
  if (!f) { avma = av; return NULL; }
  return gerepileuptoint(av, f);
}

/*******************************************************************/
/*                                                                 */
/*                     FACTORISATION MODULO p                      */
/*                                                                 */
/*******************************************************************/

/* Functions giving information on the factorisation. */

/* u in Z[X], return kernel of (Frob - Id) over Fp[X] / u */
GEN
FpX_Berlekamp_ker(GEN u, GEN p)
{
  pari_sp ltop=avma;
  long j,N = degpol(u);
  GEN Q  = FpX_matFrobenius(u, p);
  for (j=1; j<=N; j++)
    gcoeff(Q,j,j) = Fp_sub(gcoeff(Q,j,j), gen_1, p);
  return gerepileupto(ltop, FpM_ker(Q,p));
}

GEN
F2x_Berlekamp_ker(GEN u)
{
  pari_sp ltop=avma;
  long j,N = F2x_degree(u);
  GEN Q, XP;
  pari_timer T;
  timer_start(&T);
  XP = F2xq_sqr(polx_F2x(u[1]),u);
  Q  = F2xq_matrix_pow(XP,N,N,u);
  for (j=1; j<=N; j++)
    F2m_flip(Q,j,j);
  if(DEBUGLEVEL>=9) timer_printf(&T,"Berlekamp matrix");
  Q = F2m_ker_sp(Q,0);
  if(DEBUGLEVEL>=9) timer_printf(&T,"kernel");
  return gerepileupto(ltop,Q);
}

GEN
Flx_Berlekamp_ker(GEN u, ulong l)
{
  pari_sp ltop=avma;
  long j,N = degpol(u);
  GEN Q;
  pari_timer T;
  timer_start(&T);
  Q  = Flx_matFrobenius(u, l);
  for (j=1; j<=N; j++)
    coeff(Q,j,j) = Fl_sub(coeff(Q,j,j),1,l);
  if(DEBUGLEVEL>=9) timer_printf(&T,"Berlekamp matrix");
  Q = Flm_ker_sp(Q,l,0);
  if(DEBUGLEVEL>=9) timer_printf(&T,"kernel");
  return gerepileupto(ltop,Q);
}

/* product of terms of degree 1 in factorization of f */
GEN
FpX_split_part(GEN f, GEN p)
{
  long n = degpol(f);
  GEN z, X = pol_x(varn(f));
  if (n <= 1) return f;
  f = FpX_red(f, p);
  z = FpX_sub(FpX_Frobenius(f, p), X, p);
  return FpX_gcd(z,f,p);
}

/* Compute the number of roots in Fp without counting multiplicity
 * return -1 for 0 polynomial. lc(f) must be prime to p. */
long
FpX_nbroots(GEN f, GEN p)
{
  pari_sp av = avma;
  GEN z = FpX_split_part(f, p);
  avma = av; return degpol(z);
}

int
FpX_is_totally_split(GEN f, GEN p)
{
  long n=degpol(f);
  pari_sp av = avma;
  if (n <= 1) return 1;
  if (cmpui(n, p) > 0) return 0;
  f = FpX_red(f, p);
  avma = av; return gequalX(FpX_Frobenius(f, p));
}

/* Flv_Flx( Flm_Flc_mul(x, Flx_Flv(y), p) ) */
static GEN
Flm_Flx_mul(GEN x, GEN y, ulong p)
{
  long i,k,l, ly = lg(y)-1;
  GEN z;
  long vs=y[1];
  if (ly==1) return zero_Flx(vs);
  l = lgcols(x);
  y++;
  z = zero_zv(l) + 1;
  if (SMALL_ULONG(p))
  {
    for (k=1; k<ly; k++)
    {
      GEN c;
      if (!y[k]) continue;
      c = gel(x,k);
      if (y[k] == 1)
        for (i=1; i<l; i++)
        {
          z[i] += c[i];
          if (z[i] & HIGHBIT) z[i] %= p;
        }
      else
        for (i=1; i<l; i++)
        {
          z[i] += c[i] * y[k];
          if (z[i] & HIGHBIT) z[i] %= p;
        }
    }
    for (i=1; i<l; i++) z[i] %= p;
  }
  else
  {
    for (k=1; k<ly; k++)
    {
      GEN c;
      if (!y[k]) continue;
      c = gel(x,k);
      if (y[k] == 1)
        for (i=1; i<l; i++)
          z[i] = Fl_add(z[i], c[i], p);
      else
        for (i=1; i<l; i++)
          z[i] = Fl_add(z[i], Fl_mul(c[i],y[k],p), p);
    }
  }
  while (--l && !z[l]);
  if (!l) return zero_Flx(vs);
  *z-- = vs; return z;
}

/* z must be squarefree mod p*/
GEN
Flx_nbfact_by_degree(GEN z, long *nb, ulong p)
{
  long lgg, d = 0, e = degpol(z);
  GEN D = zero_zv(e);
  pari_sp av = avma;
  GEN g, w, PolX = polx_Flx(z[1]);
  GEN MP = Flx_matFrobenius(z, p);

  w = PolX; *nb = 0;
  while (d < (e>>1))
  { /* here e = degpol(z) */
    d++;
    w = Flm_Flx_mul(MP, w, p); /* w^p mod (z,p) */
    g = Flx_gcd(z, Flx_sub(w, PolX, p), p);
    lgg = degpol(g); if (!lgg) continue;

    e -= lgg;
    D[d] = lgg/d; *nb += D[d];
    if (DEBUGLEVEL>5) err_printf("   %3ld fact. of degree %3ld\n", D[d], d);
    if (!e) break;
    z = Flx_div(z, g, p);
    w = Flx_rem(w, z, p);
  }
  if (e)
  {
    if (DEBUGLEVEL>5) err_printf("   %3ld fact. of degree %3ld\n",1,e);
    D[e] = 1; (*nb)++;
  }
  avma = av; return D;
}

/* z must be squarefree mod p*/
long
Flx_nbfact(GEN z, ulong p)
{
  pari_sp av = avma;
  long nb; (void)Flx_nbfact_by_degree(z, &nb, p);
  avma = av; return nb;
}

long
Flx_nbroots(GEN f, ulong p)
{
  long n = degpol(f);
  pari_sp av = avma;
  GEN z;
  if (n <= 1) return n;
  if (n == 2)
  {
    ulong D;
    if (p==2) return (f[2]==0) + (f[2]!=f[3]);
    D = Fl_sub(Fl_sqr(f[3], p), Fl_mul(Fl_mul(f[4], f[2], p), 4%p, p), p);
    return 1 + krouu(D,p);
  }
  z = Flx_sub(Flx_Frobenius(f, p), polx_Flx(f[1]), p);
  z = Flx_gcd(z, f, p);
  avma = av; return degpol(z);
}

long
FpX_nbfact(GEN u, GEN p)
{
  pari_sp av = avma;
  GEN vker = FpX_Berlekamp_ker(u, p);
  avma = av; return lg(vker)-1;
}

static GEN
try_pow(GEN w0, GEN pol, GEN p, GEN q, long r)
{
  GEN w2, w = FpXQ_pow(w0,q, pol,p);
  long s;
  if (gequal1(w)) return w0;
  for (s=1; s<r; s++,w=w2)
  {
    w2 = gsqr(w);
    w2 = FpX_rem(w2, pol, p);
    if (gequal1(w2)) break;
  }
  return gequalm1(w)? NULL: w;
}

static GEN
Flx_try_pow(GEN w0, GEN pol, ulong p, GEN q, long r)
{
  GEN w2, w = Flxq_pow(w0,q, pol,p);
  long s;
  if (Flx_equal1(w)) return w0;
  for (s=1; s<r; s++,w=w2)
  {
    w2 = Flxq_sqr(w,pol,p);
    if (Flx_equal1(w2)) break;
  }
  return degpol(w)==0 && uel(w,2) == p-1 ? NULL: w;
}

/* INPUT:
 *  m integer (converted to polynomial w in Z[X] by stoFpX)
 *  p prime; q = (p^d-1) / 2^r
 *  t[0] polynomial of degree k*d product of k irreducible factors of degree d
 *  t[0] is expected to be normalized (leading coeff = 1)
 * OUTPUT:
 *  t[0],t[1]...t[k-1] the k factors, normalized */

static void
F2x_split(ulong m, GEN *t, long d)
{
  long l, v, dv;
  pari_sp av0, av;
  GEN w;

  dv = F2x_degree(*t); if (dv==d) return;
  v=(*t)[1]; av0=avma;
  for(av=avma;;avma=av)
  {
    GEN w0 = w = F2xq_powu(polx_F2x(v), m-1, *t); m += 2;
    for (l=1; l<d; l++) w = F2x_add(w0, F2xq_sqr(w, *t));
    w = F2x_gcd(*t,w);
    l = F2x_degree(w); if (l && l!=dv) break;
  }
  w = gerepileupto(av0, w);
  l /= d; t[l]=F2x_div(*t,w); *t=w;
  F2x_split(m,t+l,d);
  F2x_split(m,t,  d);
}

static void
Flx_split(GEN *t, long d, ulong p, GEN q, long r)
{
  long l, v, dv;
  pari_sp av0, av;
  GEN w;

  dv=degpol(*t); if (dv==d) return;
  v=(*t)[1]; av0=avma;
  for(av=avma;;avma=av)
  {
    w = random_Flx(dv,v,p);
    w = Flx_try_pow(w,*t,p,q,r);
    if (!w) continue;
    w = Flx_Fl_add(w, p-1, p);
    w = Flx_gcd(*t,w, p);
    l = degpol(w); if (l && l!=dv) break;
  }
  w = Flx_normalize(w, p);
  w = gerepileupto(av0, w);
  l /= d; t[l]=Flx_div(*t,w,p); *t=w;
  Flx_split(t+l,d,p,q,r);
  Flx_split(t,  d,p,q,r);
}


static void
FpX_split(GEN *t, long d, GEN  p, GEN q, long r)
{
  long l, v, dv = degpol(*t);
  pari_sp av;
  GEN w;

  if (dv==d) return;
  v = varn(*t);
  av = avma;
  for(;; avma = av)
  {
    w = random_FpX(dv, v, p);
    w = try_pow(w,*t,p,q,r);
    if (!w) continue;
    w = FpX_Fp_sub_shallow(w, gen_1, p);
    w = FpX_gcd(*t,w, p); l=degpol(w);
    if (l && l!=dv) break;
  }
  w = FpX_normalize(w, p);
  w = gerepileupto(av, w);
  l /= d; t[l]=FpX_div(*t,w,p); *t=w;
  FpX_split(t+l,d,p,q,r);
  FpX_split(t,  d,p,q,r);
}

static int
cmpGuGu(GEN a, GEN b) { return (ulong)a < (ulong)b? -1: (a == b? 0: 1); }

/* p > 2 */
static GEN
FpX_is_irred_2(GEN f, GEN p, long d)
{
  switch(d)
  {
    case -1:
    case 0: return NULL;
    case 1: return gen_1;
  }
  return FpX_quad_factortype(f, p) == -1? gen_1: NULL;
}
/* p > 2 */
static GEN
FpX_degfact_2(GEN f, GEN p, long d)
{
  switch(d)
  {
    case -1:retmkvec2(mkvecsmall(-1),mkvecsmall(1));
    case 0: return trivial_fact();
    case 1: retmkvec2(mkvecsmall(1), mkvecsmall(1));
  }
  switch(FpX_quad_factortype(f, p)) {
    case  1: retmkvec2(mkvecsmall2(1,1), mkvecsmall2(1,1));
    case -1: retmkvec2(mkvecsmall(2), mkvecsmall(1));
    default: retmkvec2(mkvecsmall(1), mkvecsmall(2));
  }
}

GEN
prime_fact(GEN x) { retmkmat2(mkcolcopy(x), mkcol(gen_1)); }
GEN
trivial_fact(void) { retmkmat2(cgetg(1,t_COL), cgetg(1,t_COL)); }

/* Mod(0,p) * x, where x is f's main variable */
static GEN
Mod0pX(GEN f, GEN p)
{ return scalarpol(mkintmod(gen_0, p), varn(f)); }
static GEN
zero_fact_intmod(GEN f, GEN p) { return prime_fact(Mod0pX(f,p)); }

/* not gerepile safe */
static GEN
FpX_factor_2(GEN f, GEN p, long d)
{
  GEN r, s, R, S;
  long v;
  int sgn;
  switch(d)
  {
    case -1: retmkvec2(mkcol(pol_0(varn(f))), mkvecsmall(1));
    case  0: retmkvec2(cgetg(1,t_COL), cgetg(1,t_VECSMALL));
    case  1: retmkvec2(mkcol(f), mkvecsmall(1));
  }
  r = FpX_quad_root(f, p, 1);
  if (!r) return mkvec2(mkcol(f), mkvecsmall(1));
  v = varn(f);
  s = FpX_otherroot(f, r, p);
  if (signe(r)) r = subii(p, r);
  if (signe(s)) s = subii(p, s);
  sgn = cmpii(s, r); if (sgn < 0) swap(s,r);
  R = deg1pol_shallow(gen_1, r, v);
  if (!sgn) return mkvec2(mkcol(R), mkvecsmall(2));
  S = deg1pol_shallow(gen_1, s, v);
  return mkvec2(mkcol2(R,S), mkvecsmall2(1,1));
}
static GEN
FpX_factor_deg2(GEN f, GEN p, long d, long flag)
{
  switch(flag) {
    case 2: return FpX_is_irred_2(f, p, d);
    case 1: return FpX_degfact_2(f, p, d);
    default: return FpX_factor_2(f, p, d);
  }
}

static int
F2x_quad_factortype(GEN x)
{ return x[2] == 7 ? -1: x[2] == 6 ? 1 :0; }

static GEN
F2x_is_irred_2(GEN f, long d)
{ return d == 1 || (d==2 && F2x_quad_factortype(f) == -1)? gen_1: NULL; }

static GEN
F2x_degfact_2(GEN f, long d)
{
  if (!d) return trivial_fact();
  if (d == 1) return mkvec2(mkvecsmall(1), mkvecsmall(1));
  switch(F2x_quad_factortype(f)) {
    case 1: return mkvec2(mkvecsmall2(1,1), mkvecsmall2(1,1));
    case -1:return mkvec2(mkvecsmall(2), mkvecsmall(1));
    default: return mkvec2(mkvecsmall(1), mkvecsmall(2));
  }
}

static GEN
F2x_factor_2(GEN f, long d)
{
  long v = f[1];
  if (d < 0) pari_err(e_ROOTS0,"Flx_factor_2");
  if (!d) return mkvec2(cgetg(1,t_COL), cgetg(1,t_VECSMALL));
  if (d == 1) return mkvec2(mkcol(f), mkvecsmall(1));
  switch(F2x_quad_factortype(f))
  {
  case -1: return mkvec2(mkcol(f), mkvecsmall(1));
  case 0:  return mkvec2(mkcol(mkvecsmall2(v,2+F2x_coeff(f,0))), mkvecsmall(2));
  default: return mkvec2(mkcol2(mkvecsmall2(v,2),mkvecsmall2(v,3)), mkvecsmall2(1,1));
  }
}
static GEN
F2x_factor_deg2(GEN f, long d, long flag)
{
  switch(flag) {
    case 2: return F2x_is_irred_2(f, d);
    case 1: return F2x_degfact_2(f, d);
    default: return F2x_factor_2(f, d);
  }
}

static void
split_squares(struct split_t *S, GEN g, ulong p)
{
  ulong q = p >> 1;
  GEN a = Flx_mod_Xnm1(g, q, p); /* mod x^(p-1)/2 - 1 */
  if (degpol(a) < 0)
  {
    ulong i;
    split_add_done(S, (GEN)1);
    for (i = 2; i <= q; i++) split_add_done(S, (GEN)Fl_sqr(i,p));
  } else {
    (void)Flx_valrem(a, &a);
    if (degpol(a))
    {
      a = Flx_gcd(a, Flx_Xnm1(g[1], q, p), p);
      if (degpol(a)) split_add(S, Flx_normalize(a, p));
    }
  }
}
static void
split_nonsquares(struct split_t *S, GEN g, ulong p)
{
  ulong q = p >> 1;
  GEN a = Flx_mod_Xn1(g, q, p); /* mod x^(p-1)/2 + 1 */
  if (degpol(a) < 0)
  {
    ulong i, z = Fl_nonsquare(p);
    split_add_done(S, (GEN)z);
    for (i = 2; i <= q; i++) split_add_done(S, (GEN)Fl_mul(z, Fl_sqr(i,p), p));
  } else {
    (void)Flx_valrem(a, &a);
    if (degpol(a))
    {
      a = Flx_gcd(a, Flx_Xn1(g[1], q, p), p);
      if (degpol(a)) split_add(S, Flx_normalize(a, p));
    }
  }
}
/* p > 2. f monic Flx, f(0) != 0. Add to split_t structs coprime factors
 * of g = \prod_{f(a) = 0} (X - a). Return 0 when f(x) = 0 for all x in Fp* */
static int
split_Flx_cut_out_roots(struct split_t *S, GEN f, ulong p)
{
  GEN a, g = Flx_mod_Xnm1(f, p-1, p); /* f mod x^(p-1) - 1 */
  long d = degpol(g);
  if (d < 0) return 0;
  if (g != f) { (void)Flx_valrem(g, &g); d = degpol(g); } /*kill powers of x*/
  if (!d) return 1;
  if (p <= 1.4 * (ulong)d) {
    /* small p; split further using x^((p-1)/2) +/- 1.
     * 30% degree drop makes the extra gcd worth it. */
    split_squares(S, g, p);
    split_nonsquares(S, g, p);
  } else { /* large p; use x^(p-1) - 1 directly */
    a = Flxq_powu(polx_Flx(f[1]), p-1, g,p);
    if (lg(a) < 3) pari_err_PRIME("rootmod",utoipos(p));
    a = Flx_Fl_add(a, p-1, p); /* a = x^(p-1) - 1 mod g */
    g = Flx_gcd(g,a, p);
    if (degpol(g)) split_add(S, Flx_normalize(g,p));
  }
  return 1;
}

/* by splitting, assume p > 2 prime, deg(f) > 0, and f monic */
static GEN
Flx_roots_i(GEN f, ulong p)
{
  GEN pol, g;
  long v = Flx_valrem(f, &g);
  ulong q;
  struct split_t S;

  /* optimization: test for small degree first */
  switch(degpol(g))
  {
    case 1: {
      ulong r = p - g[2];
      return v? mkvecsmall2(0, r): mkvecsmall(r);
    }
    case 2: {
      ulong r = Flx_quad_root(g, p, 1), s;
      if (r == p) return v? mkvecsmall(0): cgetg(1,t_VECSMALL);
      s = Flx_otherroot(g,r, p);
      if (r < s)
        return v? mkvecsmall3(0, r, s): mkvecsmall2(r, s);
      else if (r > s)
        return v? mkvecsmall3(0, s, r): mkvecsmall2(s, r);
      else
        return v? mkvecsmall2(0, s): mkvecsmall(s);
    }
  }
  q = p >> 1;
  split_init(&S, lg(f)-1);
  settyp(S.done, t_VECSMALL);
  if (v) split_add_done(&S, (GEN)0);
  if (! split_Flx_cut_out_roots(&S, g, p))
    return all_roots_mod_p(p, lg(S.done) == 1);
  pol = polx_Flx(f[1]);
  for (pol[2]=1; ; pol[2]++)
  {
    long j, l = lg(S.todo);
    if (l == 1) { vecsmall_sort(S.done); return S.done; }
    if (pol[2] == 100 && !uisprime(p)) pari_err_PRIME("polrootsmod",utoipos(p));
    for (j = 1; j < l; j++)
    {
      GEN c = gel(S.todo,j);
      switch(degpol(c))
      {
        case 1:
          split_moveto_done(&S, j, (GEN)(p - c[2]));
          j--; l--; break;
        case 2: {
          ulong r = Flx_quad_root(c, p, 0), s = Flx_otherroot(c,r, p);
          split_done(&S, j, (GEN)r, (GEN)s);
          j--; l--; break;
        }
        default: {
          GEN b = Flx_Fl_add(Flxq_powu(pol,q, c,p), p-1, p); /* pol^(p-1)/2 */
          long db;
          b = Flx_gcd(c,b, p); db = degpol(b);
          if (db && db < degpol(c))
          {
            b = Flx_normalize(b, p);
            c = Flx_div(c,b, p);
            split_todo(&S, j, b, c);
          }
        }
      }
    }
  }
}

GEN
Flx_roots(GEN f, ulong p)
{
  pari_sp av = avma;
  switch(lg(f))
  {
    case 2: pari_err_ROOTS0("Flx_roots");
    case 3: avma = av; return cgetg(1, t_VECSMALL);
  }
  if (p == 2) return Flx_root_mod_2(f);
  return gerepileuptoleaf(av, Flx_roots_i(Flx_normalize(f, p), p));
}

/* assume x reduced mod p, monic. */
static int
Flx_quad_factortype(GEN x, ulong p)
{
  ulong b = x[3], c = x[2];
  return krouu(Fl_disc_bc(b, c, p), p);
}
static GEN
Flx_is_irred_2(GEN f, ulong p, long d)
{
  if (!d) return NULL;
  if (d == 1) return gen_1;
  return Flx_quad_factortype(f, p) == -1? gen_1: NULL;
}
static GEN
Flx_degfact_2(GEN f, ulong p, long d)
{
  if (!d) return trivial_fact();
  if (d == 1) return mkvec2(mkvecsmall(1), mkvecsmall(1));
  switch(Flx_quad_factortype(f, p)) {
    case 1: return mkvec2(mkvecsmall2(1,1), mkvecsmall2(1,1));
    case -1:return mkvec2(mkvecsmall(2), mkvecsmall(1));
    default: return mkvec2(mkvecsmall(1), mkvecsmall(2));
  }
}
/* p > 2 */
static GEN
Flx_factor_2(GEN f, ulong p, long d)
{
  ulong r, s;
  GEN R,S;
  long v = f[1];
  if (d < 0) pari_err(e_ROOTS0,"Flx_factor_2");
  if (!d) return mkvec2(cgetg(1,t_COL), cgetg(1,t_VECSMALL));
  if (d == 1) return mkvec2(mkcol(f), mkvecsmall(1));
  r = Flx_quad_root(f, p, 1);
  if (r==p) return mkvec2(mkcol(f), mkvecsmall(1));
  s = Flx_otherroot(f, r, p);
  r = Fl_neg(r, p);
  s = Fl_neg(s, p);
  if (s < r) lswap(s,r);
  R = mkvecsmall3(v,r,1);
  if (s == r) return mkvec2(mkcol(R), mkvecsmall(2));
  S = mkvecsmall3(v,s,1);
  return mkvec2(mkcol2(R,S), mkvecsmall2(1,1));
}
static GEN
Flx_factor_deg2(GEN f, ulong p, long d, long flag)
{
  switch(flag) {
    case 2: return Flx_is_irred_2(f, p, d);
    case 1: return Flx_degfact_2(f, p, d);
    default: return Flx_factor_2(f, p, d);
  }
}

static GEN
F2x_factcantor_i(GEN f, long flag)
{
  long j, e, nbfact, d = F2x_degree(f);
  ulong k;
  GEN X, E, f2, g, g1, u, v, y, t;

  if (d <= 2) return F2x_factor_deg2(f, d, flag);
  /* to hold factors and exponents */
  t = flag ? cgetg(d+1,t_VECSMALL): cgetg(d+1,t_VEC);
  E = cgetg(d+1, t_VECSMALL);
  X = polx_F2x(f[1]);
  e = nbfact = 1;
  for(;;)
  {
    f2 = F2x_gcd(f,F2x_deriv(f));
    if (flag == 2 && F2x_degree(f2) > 0) return NULL;
    g1 = F2x_div(f,f2);
    k = 0;
    while (F2x_degree(g1)>0)
    {
      pari_sp av;
      long du, dg, dg1;
      k++; if (k%2==0) { k++; f2 = F2x_div(f2,g1); }
      u = g1; g1 = F2x_gcd(f2,g1);
      du = F2x_degree(u);
      dg1 = F2x_degree(g1);
      if (dg1>0)
      {
        f2= F2x_div(f2,g1);
        if (du == dg1) continue;
        u = F2x_div( u,g1);
        du -= dg1;
      }
      /* here u is square-free (product of irred. of multiplicity e * k) */
      v = X;
      av = avma;
      for (d=1; d <= du>>1; d++)
      {
        v = F2xq_sqr(v, u);
        g = F2x_gcd(F2x_add(v, X), u);
        dg = F2x_degree(g);
        if (dg <= 0) {avma = (pari_sp)v; v = gerepileuptoleaf(av,v); continue;}
        /* g is a product of irred. pols, all of which have degree d */
        j = nbfact+dg/d;
        if (flag)
        {
          if (flag == 2) return NULL;
          for ( ; nbfact<j; nbfact++) { t[nbfact]=d; E[nbfact]=e*k; }
        }
        else
        {
          gel(t,nbfact) = g;
          F2x_split(2,&gel(t,nbfact),d);
          for (; nbfact<j; nbfact++) E[nbfact]=e*k;
        }
        du -= dg;
        u = F2x_div(u,g);
        v = F2x_rem(v,u);
        av = avma;
      }
      if (du)
      {
        if (flag) t[nbfact] = du;
        else  gel(t,nbfact) = u;
        E[nbfact++]=e*k;
      }
    }
    if (F2x_degree(f2)==0) break;
    e <<=1; f = F2x_sqrt(f2);
  }
  if (flag == 2) return gen_1; /* irreducible */
  setlg(t, nbfact);
  setlg(E, nbfact); y = mkvec2(t, E);
  return flag ? sort_factor(y, (void*)cmpGuGu, cmp_nodata)
              : sort_factor_pol(y, cmpGuGu);
}
GEN
F2x_factcantor(GEN f, long flag)
{
  pari_sp av = avma;
  GEN z = F2x_factcantor_i(f, flag);
  if (flag == 2) { avma = av; return z; }
  return gerepilecopy(av, z);
}

int
F2x_is_irred(GEN f) { return !!F2x_factcantor_i(f,2); }

void
F2xV_to_FlxV_inplace(GEN v)
{
  long i;
  for(i=1;i<lg(v);i++) gel(v,i)= F2x_to_Flx(gel(v,i));
}
void
FlxV_to_ZXV_inplace(GEN v)
{
  long i;
  for(i=1;i<lg(v);i++) gel(v,i)= Flx_to_ZX(gel(v,i));
}
void
F2xV_to_ZXV_inplace(GEN v)
{
  long i;
  for(i=1;i<lg(v);i++) gel(v,i)= F2x_to_ZX(gel(v,i));
}

/* factor f mod pp.
 * flag = 1: return the degrees, not the factors
 * flag = 2: return NULL if f is not irreducible */
static GEN
Flx_factcantor_i(GEN f, ulong p, long flag)
{
  long j, e, nbfact, d = degpol(f);
  ulong k;
  GEN X, E, f2, g, g1, u, v, q, y, t;
  if (p==2) { /*We need to handle 2 specially */
    GEN F = F2x_factcantor_i(Flx_to_F2x(f),flag);
    if (flag==0) F2xV_to_FlxV_inplace(gel(F,1));
    return F;
  }
  /* Now we assume p odd */
  if (d <= 2) return Flx_factor_deg2(f, p, d, flag);

  /* to hold factors and exponents */
  t = cgetg(d+1, flag? t_VECSMALL: t_VEC);
  E = cgetg(d+1, t_VECSMALL);
  X = polx_Flx(f[1]);
  e = nbfact = 1;
  for(;;)
  {
    f2 = Flx_gcd(f,Flx_deriv(f,p), p);
    if (flag == 2 && degpol(f2) > 0) return NULL;
    g1 = Flx_div(f,f2,p);
    k = 0;
    while (degpol(g1)>0)
    {
      pari_sp av;
      long du,dg;
      k++; if (k%p==0) { k++; f2 = Flx_div(f2,g1,p); }
      u = g1; g1 = Flx_gcd(f2,g1, p);
      if (degpol(g1)>0)
      {
        u = Flx_div( u,g1,p);
        f2= Flx_div(f2,g1,p);
      }
      du = degpol(u);
      if (du <= 0) continue;

      /* here u is square-free (product of irred. of multiplicity e * k) */
      v=X;
      av = avma;
      for (d=1; d <= du>>1; d++)
      {
        v = Flxq_powu(v, p, u, p);
        g = Flx_gcd(Flx_sub(v, X, p), u, p);
        dg = degpol(g);
        if (dg <= 0) {avma = (pari_sp)v; v = gerepileuptoleaf(av,v); continue;}
        /* g is a product of irred. pols, all of which have degree d */
        j = nbfact+dg/d;
        if (flag)
        {
          if (flag == 2) return NULL;
          for ( ; nbfact<j; nbfact++) { t[nbfact]=d; E[nbfact]=e*k; }
        }
        else
        {
          GEN pd = powuu(p, d);
          long r;
          g = Flx_normalize(g, p);
          gel(t,nbfact) = g; q = subis(pd,1);
          r = vali(q); q = shifti(pd,-r);
          Flx_split(&gel(t,nbfact),d,p,q,r);
          for (; nbfact<j; nbfact++) E[nbfact]=e*k;
        }
        du -= dg;
        u = Flx_div(u,g,p);
        v = Flx_rem(v,u,p);
        av = avma;
      }
      if (du)
      {
        if (flag) t[nbfact] = du;
        else  gel(t,nbfact) = Flx_normalize(u, p);
        E[nbfact++]=e*k;
      }
    }
    if (degpol(f2)==0) break;
    e *= p; f = Flx_deflate(f2, p);
  }
  if (flag == 2) return gen_1; /* irreducible */
  setlg(t, nbfact);
  setlg(E, nbfact); y = mkvec2(t, E);
  return flag ? sort_factor(y, (void*)cmpGuGu, cmp_nodata)
              : sort_factor_pol(y, cmpGuGu);
}
GEN
Flx_factcantor(GEN f, ulong p, long flag)
{
  pari_sp av = avma;
  GEN z = Flx_factcantor_i(Flx_normalize(f,p),p,flag);
  if (flag == 2) { avma = av; return z; }
  return gerepilecopy(av, z);
}
GEN
Flx_degfact(GEN f, ulong p)
{
  pari_sp av = avma;
  GEN z = Flx_factcantor_i(Flx_normalize(f,p),p,1);
  return gerepilecopy(av, z);
}
int
Flx_is_irred(GEN f, ulong p) { return !!Flx_factcantor_i(f,p,2); }

/* factor f (FpX or Flx) mod pp.
 * flag = 1: return the degrees, not the factors
 * flag = 2: return NULL if f is not irreducible.
 * Not gerepile-safe */
static GEN
FpX_factcantor_i(GEN f, GEN pp, long flag)
{
  long j, nbfact, d = degpol(f);
  ulong k;
  GEN X, E,y,f2,g,g1,v,q;
  GEN t;
  if (typ(f) == t_VECSMALL)
  { /* lgefint(pp) = 3 */
    GEN F;
    ulong p = pp[2];
    if (p==2) {
      F = F2x_factcantor_i(Flx_to_F2x(f),flag);
      if (flag==0) F2xV_to_ZXV_inplace(gel(F,1));
    } else {
      F = Flx_factcantor_i(f,p,flag);
      if (flag==0) FlxV_to_ZXV_inplace(gel(F,1));
    }
    return F;
  }
  /*Now, we can assume that p is large and odd*/
  if (d <= 2) return FpX_factor_deg2(f,pp,d,flag);

  /* to hold factors and exponents */
  t = cgetg(d+1, flag? t_VECSMALL: t_VEC);
  E = cgetg(d+1, t_VECSMALL);
  X = pol_x(varn(f)); nbfact = 1;
  f2 = FpX_gcd(f,ZX_deriv(f), pp);
  if (flag == 2 && degpol(f2)) return NULL;
  g1 = degpol(f2)? FpX_div(f,f2,pp): f; /* squarefree */
  k = 0;
  while (degpol(g1)>0)
  {
    long du,dg;
    GEN u, S;
    k++;
    u = g1; g1 = FpX_gcd(f2,g1, pp);
    if (degpol(g1)>0)
    {
      u = FpX_div( u,g1,pp);
      f2= FpX_div(f2,g1,pp);
    }
    du = degpol(u);
    if (du <= 0) continue;

    /* here u is square-free (product of irred. of multiplicity e * k) */
    v=X;
    S = du==1 ?  cgetg(1, t_VEC): FpXQ_powers(FpX_Frobenius(u, pp), du-1, u, pp);
    for (d=1; d <= du>>1; d++)
    {
      v = FpX_FpXQV_eval(v, S, u, pp);
      g = FpX_gcd(ZX_sub(v, X), u, pp);
      dg = degpol(g);
      if (dg <= 0) continue;

      /* g is a product of irred. pols, all of which have degree d */
      j = nbfact+dg/d;
      if (flag)
      {
        if (flag == 2) return NULL;
        for ( ; nbfact<j; nbfact++) { t[nbfact]=d; E[nbfact]=k; }
      }
      else
      {
        GEN pd = powiu(pp,d);
        long r;
        g = FpX_normalize(g, pp);
        gel(t,nbfact) = g; q = subis(pd,1);
        r = vali(q); q = shifti(q,-r);
        FpX_split(&gel(t,nbfact),d,pp,q,r);
        for (; nbfact<j; nbfact++) E[nbfact]=k;
      }
      du -= dg;
      u = FpX_div(u,g,pp);
      v = FpX_rem(v,u,pp);
    }
    if (du)
    {
      if (flag) t[nbfact] = du;
      else gel(t,nbfact) = FpX_normalize(u, pp);
      E[nbfact++]=k;
    }
  }
  if (flag == 2) return gen_1; /* irreducible */
  setlg(t, nbfact);
  setlg(E, nbfact); y = mkvec2(t, E);
  return flag ? sort_factor(y, (void*)&cmpGuGu, cmp_nodata)
              : sort_factor_pol(y, cmpii);
}
GEN
FpX_factcantor(GEN f, GEN pp, long flag)
{
  pari_sp av = avma;
  GEN z;
  ZX_factmod_init(&f,pp);
  z = FpX_factcantor_i(f,pp,flag);
  if (flag == 2) { avma = av; return z; }
  return gerepilecopy(av, z);
}

static GEN
factmod_aux(GEN f, GEN p, GEN (*Factor)(GEN,GEN,long), long flag)
{
  pari_sp av = avma;
  long j, nbfact;
  GEN z, y, t, E, u, v;

  factmod_init(&f, p);
  switch(lg(f))
  {
    case 3: avma = av; return trivial_fact();
    case 2: return gerepileupto(av, zero_fact_intmod(f, p));
  }
  z = Factor(f,p,flag); t = gel(z,1); E = gel(z,2);
  y = cgetg(3, t_MAT); nbfact = lg(t);
  u = cgetg(nbfact,t_COL); gel(y,1) = u;
  v = cgetg(nbfact,t_COL); gel(y,2) = v;
  if (flag)
    for (j=1; j<nbfact; j++)
    {
      gel(u,j) = utoi(uel(t,j));
      gel(v,j) = utoi(uel(E,j));
    }
  else
    for (j=1; j<nbfact; j++)
    {
      gel(u,j) = FpX_to_mod(gel(t,j), p);
      gel(v,j) = utoi(uel(E,j));
    }
  return gerepileupto(av, y);
}
GEN
factcantor0(GEN f, GEN p, long flag)
{ return factmod_aux(f, p, &FpX_factcantor_i, flag); }
GEN
factmod(GEN f, GEN p)
{ return factmod_aux(f, p, &FpX_Berlekamp_i, 0); }

/* Use this function when you think f is reducible, and that there are lots of
 * factors. If you believe f has few factors, use FpX_nbfact(f,p)==1 instead */
int
FpX_is_irred(GEN f, GEN p) {
  ZX_factmod_init(&f,p);
  return !!FpX_factcantor_i(f,p,2);
}
GEN
FpX_degfact(GEN f, GEN p) {
  pari_sp av = avma;
  GEN z;
  ZX_factmod_init(&f,p);
  z = FpX_factcantor_i(f,p,1);
  return gerepilecopy(av, z);
}
GEN
factcantor(GEN f, GEN p) { return factcantor0(f,p,0); }
GEN
simplefactmod(GEN f, GEN p) { return factcantor0(f,p,1); }

/* set x <-- x + c*y mod p */
/* x is not required to be normalized.*/
static void
Flx_addmul_inplace(GEN gx, GEN gy, ulong c, ulong p)
{
  long i, lx, ly;
  ulong *x=(ulong *)gx;
  ulong *y=(ulong *)gy;
  if (!c) return;
  lx = lg(gx);
  ly = lg(gy);
  if (lx<ly) pari_err_BUG("lx<ly in Flx_addmul_inplace");
  if (SMALL_ULONG(p))
    for (i=2; i<ly;  i++) x[i] = (x[i] + c*y[i]) % p;
  else
    for (i=2; i<ly;  i++) x[i] = Fl_add(x[i], Fl_mul(c,y[i],p),p);
}

/* return a random polynomial in F_q[v], degree < d1 */
GEN
FqX_rand(long d1, long v, GEN T, GEN p)
{
  long i, d = d1+2, k = get_FpX_degree(T), w = get_FpX_var(T);
  GEN y = cgetg(d,t_POL); y[1] = evalsigne(1) | evalvarn(v);
  for (i=2; i<d; i++) gel(y,i) = random_FpX(k, w, p);
  (void)normalizepol_lg(y,d); return y;
}

#define set_irred(i) { if ((i)>ir) swap(t[i],t[ir]); ir++;}
/* assume x1 != 0 */
static GEN
deg1_Flx(ulong x1, ulong x0, ulong sv)
{
  return mkvecsmall3(sv, x0, x1);
}

long
F2x_split_Berlekamp(GEN *t)
{
  GEN u = *t, a, b, vker;
  long lb, d, i, ir, L, la, sv = u[1], du = F2x_degree(u);

  if (du == 1) return 1;
  if (du == 2)
  {
    if (F2x_quad_factortype(u) == 1) /* 0 is a root: shouldn't occur */
    {
      t[0] = mkvecsmall2(sv, 2);
      t[1] = mkvecsmall2(sv, 3);
      return 2;
    }
    return 1;
  }

  vker = F2x_Berlekamp_ker(u);
  lb = lgcols(vker);
  d = lg(vker)-1;
  ir = 0;
  /* t[i] irreducible for i < ir, still to be treated for i < L */
  for (L=1; L<d; )
  {
    GEN pol;
    if (d == 2)
      pol = F2v_to_F2x(gel(vker,2), sv);
    else
    {
      GEN v = zero_zv(lb);
      v[1] = du;
      v[2] = random_Fl(2); /*Assume vker[1]=1*/
      for (i=2; i<=d; i++)
        if (random_Fl(2)) F2v_add_inplace(v, gel(vker,i));
      pol = F2v_to_F2x(v, sv);
    }
    for (i=ir; i<L && L<d; i++)
    {
      a = t[i]; la = F2x_degree(a);
      if (la == 1) { set_irred(i); }
      else if (la == 2)
      {
        if (F2x_quad_factortype(a) == 1) /* 0 is a root: shouldn't occur */
        {
          t[i] = mkvecsmall2(sv, 2);
          t[L] = mkvecsmall2(sv, 3); L++;
        }
        set_irred(i);
      }
      else
      {
        pari_sp av = avma;
        long lb;
        b = F2x_rem(pol, a);
        if (F2x_degree(b) <= 0) { avma=av; continue; }
        b = F2x_gcd(a,b); lb = F2x_degree(b);
        if (lb && lb < la)
        {
          t[L] = F2x_div(a,b);
          t[i]= b; L++;
        }
        else avma = av;
      }
    }
  }
  return d;
}

/* p != 2 */
long
Flx_split_Berlekamp(GEN *t, ulong p)
{
  GEN u = *t, a,b,vker;
  long d, i, ir, L, la, lb, sv = u[1];
  long l = lg(u);
  ulong po2;

  if (p == 2)
  {
    *t = Flx_to_F2x(*t);
    d = F2x_split_Berlekamp(t);
    for (i = 1; i <= d; i++) t[i] = F2x_to_Flx(t[i]);
    return d;
  }
  la = degpol(u);
  if (la == 1) return 1;
  if (la == 2)
  {
    ulong r = Flx_quad_root(u,p,1);
    if (r != p)
    {
      t[0] = deg1_Flx(1, p - r, sv); r = Flx_otherroot(u,r,p);
      t[1] = deg1_Flx(1, p - r, sv);
      return 2;
    }
    return 1;
  }

  vker = Flx_Berlekamp_ker(u,p);
  vker = Flm_to_FlxV(vker, sv);
  d = lg(vker)-1;
  po2 = p >> 1; /* (p-1) / 2 */
  ir = 0;
  /* t[i] irreducible for i < ir, still to be treated for i < L */
  for (L=1; L<d; )
  {
    GEN pol = zero_zv(l-2);
    pol[1] = sv;
    pol[2] = random_Fl(p); /*Assume vker[1]=1*/
    for (i=2; i<=d; i++)
      Flx_addmul_inplace(pol, gel(vker,i), random_Fl(p), p);
    (void)Flx_renormalize(pol,l-1);

    for (i=ir; i<L && L<d; i++)
    {
      a = t[i]; la = degpol(a);
      if (la == 1) { set_irred(i); }
      else if (la == 2)
      {
        ulong r = Flx_quad_root(a,p,1);
        if (r != p)
        {
          t[i] = deg1_Flx(1, p - r, sv); r = Flx_otherroot(a,r,p);
          t[L] = deg1_Flx(1, p - r, sv); L++;
        }
        set_irred(i);
      }
      else
      {
        pari_sp av = avma;
        b = Flx_rem(pol, a, p);
        if (degpol(b) <= 0) { avma=av; continue; }
        b = Flx_Fl_add(Flxq_powu(b,po2, a,p), p-1, p);
        b = Flx_gcd(a,b, p); lb = degpol(b);
        if (lb && lb < la)
        {
          b = Flx_normalize(b, p);
          t[L] = Flx_div(a,b,p);
          t[i]= b; L++;
        }
        else avma = av;
      }
    }
  }
  return d;
}

long
FpX_split_Berlekamp(GEN *t, GEN p)
{
  GEN u = *t, a,b,po2,vker;
  long d, i, ir, L, la, lb, vu = varn(u);
  if (lgefint(p) == 3)
  {
    ulong up = p[2];
    if (up == 2)
    {
      *t = ZX_to_F2x(*t);
      d = F2x_split_Berlekamp(t);
      for (i = 0; i < d; i++) t[i] = F2x_to_ZX(t[i]);
    }
    else
    {
      *t = ZX_to_Flx(*t, up);
      d = Flx_split_Berlekamp(t, up);
      for (i = 0; i < d; i++) t[i] = Flx_to_ZX(t[i]);
    }
    return d;
  }
  la = degpol(u);
  if (la == 1) return 1;
  if (la == 2)
  {
    GEN r = FpX_quad_root(u,p,1);
    if (r)
    {
      t[0] = deg1pol_shallow(gen_1, subii(p,r), vu); r = FpX_otherroot(u,r,p);
      t[1] = deg1pol_shallow(gen_1, subii(p,r), vu);
      return 2;
    }
    return 1;
  }
  vker = FpX_Berlekamp_ker(u,p);
  vker = RgM_to_RgXV(vker,vu);
  d = lg(vker)-1;
  po2 = shifti(p, -1); /* (p-1) / 2 */
  ir = 0;
  /* t[i] irreducible for i < ir, still to be treated for i < L */
  for (L=1; L<d; )
  {
    GEN pol = scalar_ZX_shallow(randomi(p), vu);
    for (i=2; i<=d; i++)
      pol = ZX_add(pol, ZX_Z_mul(gel(vker,i), randomi(p)));
    pol = FpX_red(pol,p);
    for (i=ir; i<L && L<d; i++)
    {
      a = t[i]; la = degpol(a);
      if (la == 1) { set_irred(i); }
      else if (la == 2)
      {
        GEN r = FpX_quad_root(a,p,1);
        if (r)
        {
          t[i] = deg1pol_shallow(gen_1, subii(p,r), vu); r = FpX_otherroot(a,r,p);
          t[L] = deg1pol_shallow(gen_1, subii(p,r), vu); L++;
        }
        set_irred(i);
      }
      else
      {
        pari_sp av = avma;
        b = FpX_rem(pol, a, p);
        if (degpol(b) <= 0) { avma=av; continue; }
        b = FpX_Fp_sub_shallow(FpXQ_pow(b,po2, a,p), gen_1, p);
        b = FpX_gcd(a,b, p); lb = degpol(b);
        if (lb && lb < la)
        {
          b = FpX_normalize(b, p);
          t[L] = FpX_div(a,b,p);
          t[i]= b; L++;
        }
        else avma = av;
      }
    }
  }
  return d;
}

GEN
FqX_deriv(GEN f, /*unused*/GEN T, GEN p) {
  (void)T; return FpXX_red(RgX_deriv(f), p);
}

long
FqX_is_squarefree(GEN P, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z = FqX_gcd(P, FqX_deriv(P, T, p), T, p);
  avma = av;
  return degpol(z)==0;
}

static GEN
F2x_Berlekamp_i(GEN f, long flag)
{
  long e, nbfact, val, d = F2x_degree(f);
  ulong k, j;
  GEN y, E, f2, g1, t;

  if (d <= 2) return F2x_factor_deg2(f, d, flag);

  /* to hold factors and exponents */
  t = cgetg(d+1, flag? t_VECSMALL: t_VEC);
  E = cgetg(d+1,t_VECSMALL);
  val = F2x_valrem(f, &f);
  e = nbfact = 1;
  if (val) {
    if (flag == 2 && val > 1) return NULL;
    if (flag == 1)
      t[1] = 1;
    else
      gel(t,1) = polx_F2x(f[1]);
    E[1] = val; nbfact++;
  }

  for(;;)
  {
    f2 = F2x_gcd(f,F2x_deriv(f));
    if (flag == 2 && F2x_degree(f2)) return NULL;
    g1 = F2x_degree(f2)? F2x_div(f,f2): f; /* squarefree */
    k = 0;
    while (F2x_degree(g1)>0)
    {
      GEN u;
      k++; if (k%2 == 0) { k++; f2 = F2x_div(f2,g1); }
      u = g1; /* deg(u) > 0 */
      if (!F2x_degree(f2)) g1 = pol1_F2x(0); /* only its degree (= 0) matters */
      else
      {
        long dg1;
        g1 = F2x_gcd(f2,g1);
        dg1 = F2x_degree(g1);
        if (dg1)
        {
          f2= F2x_div(f2,g1);
          if (F2x_degree(u) == dg1) continue;
          u = F2x_div( u,g1);
        }
      }
      /* u is square-free (product of irred. of multiplicity e * k) */
      gel(t,nbfact) = u;
      d = F2x_split_Berlekamp(&gel(t,nbfact));
      if (flag == 2 && d != 1) return NULL;
      if (flag == 1)
        for (j=0; j<(ulong)d; j++) t[nbfact+j] = F2x_degree(gel(t,nbfact+j));
      for (j=0; j<(ulong)d; j++) E[nbfact+j] = e*k;
      nbfact += d;
    }
    j = F2x_degree(f2); if (!j) break;
    e *= 2; f = F2x_deflate(f2, 2);
  }
  if (flag == 2) return gen_1; /* irreducible */
  setlg(t, nbfact);
  setlg(E, nbfact); y = mkvec2(t,E);
  return flag ? sort_factor(y, (void*)&cmpGuGu, cmp_nodata)
              : sort_factor_pol(y, cmpGuGu);
}

static GEN
Flx_Berlekamp_i(GEN f, ulong p, long flag)
{
  long e, nbfact, val, d = degpol(f);
  ulong k, j;
  GEN y, E, f2, g1, t;

  if (p == 2)
  {
    GEN F = F2x_Berlekamp_i(Flx_to_F2x(f),flag);
    if (flag==0) F2xV_to_FlxV_inplace(gel(F,1));
    return F;
  }
  if (d <= 2) return Flx_factor_deg2(f,p,d,flag);

  /* to hold factors and exponents */
  t = cgetg(d+1, flag? t_VECSMALL: t_VEC);
  E = cgetg(d+1,t_VECSMALL);
  val = Flx_valrem(f, &f);
  e = nbfact = 1;
  if (val) {
    if (flag == 2 && val > 1) return NULL;
    if (flag == 1)
      t[1] = 1;
    else
      gel(t,1) = polx_Flx(f[1]);
    E[1] = val; nbfact++;
  }

  for(;;)
  {
    f2 = Flx_gcd(f,Flx_deriv(f,p), p);
    if (flag == 2 && degpol(f2)) return NULL;
    g1 = degpol(f2)? Flx_div(f,f2,p): f; /* squarefree */
    k = 0;
    while (degpol(g1)>0)
    {
      GEN u;
      k++; if (k%p == 0) { k++; f2 = Flx_div(f2,g1,p); }
      u = g1; /* deg(u) > 0 */
      if (!degpol(f2)) g1 = pol1_Flx(0); /* only its degree (= 0) matters */
      else
      {
        g1 = Flx_gcd(f2,g1, p);
        if (degpol(g1))
        {
          f2= Flx_div(f2,g1,p);
          if (lg(u) == lg(g1)) continue;
          u = Flx_div( u,g1,p);
        }
      }
      /* u is square-free (product of irred. of multiplicity e * k) */
      u = Flx_normalize(u,p);
      gel(t,nbfact) = u;
      d = Flx_split_Berlekamp(&gel(t,nbfact), p);
      if (flag == 2 && d != 1) return NULL;
      if (flag == 1)
        for (j=0; j<(ulong)d; j++) t[nbfact+j] = degpol(gel(t,nbfact+j));
      for (j=0; j<(ulong)d; j++) E[nbfact+j] = e*k;
      nbfact += d;
    }
    if (!p) break;
    j = degpol(f2); if (!j) break;
    if (j % p) pari_err_PRIME("factmod",utoi(p));
    e *= p; f = Flx_deflate(f2, p);
  }
  if (flag == 2) return gen_1; /* irreducible */
  setlg(t, nbfact);
  setlg(E, nbfact); y = mkvec2(t,E);
  return flag ? sort_factor(y, (void*)&cmpGuGu, cmp_nodata)
              : sort_factor_pol(y, cmpGuGu);
}

/* f an FpX or an Flx */
static GEN
FpX_Berlekamp_i(GEN f, GEN pp, long flag)
{
  long e, nbfact, val, d = degpol(f);
  ulong k, j;
  GEN y, E, f2, g1, t;

  if (typ(f) == t_VECSMALL)
  {/* lgefint(pp) == 3 */
    ulong p = pp[2];
    GEN F;
    if (p == 2) {
      F = F2x_Berlekamp_i(Flx_to_F2x(f), flag);
      if (flag==0) F2xV_to_ZXV_inplace(gel(F,1));
    } else {
      F = Flx_Berlekamp_i(f, p, flag);
      if (flag==0) FlxV_to_ZXV_inplace(gel(F,1));
    }
    return F;
  }
  /* p is large (and odd) */
  if (d <= 2) return FpX_factor_deg2(f,pp,d,flag);

  /* to hold factors and exponents */
  t = cgetg(d+1, flag? t_VECSMALL: t_VEC);
  E = cgetg(d+1,t_VECSMALL);
  val = ZX_valrem(f, &f);
  e = nbfact = 1;
  if (val) {
    if (flag == 2 && val > 1) return NULL;
    if (flag == 1)
      t[1] = 1;
    else
      gel(t,1) = pol_x(varn(f));
    E[1] = val; nbfact++;
  }

  f2 = FpX_gcd(f,ZX_deriv(f), pp);
  if (flag == 2 && degpol(f2)) return NULL;
  g1 = degpol(f2)? FpX_div(f,f2,pp): f; /* squarefree */
  k = 0;
  while (degpol(g1)>0)
  {
    GEN u;
    k++;
    u = g1; /* deg(u) > 0 */
    if (!degpol(f2)) g1 = pol_1(0); /* only its degree (= 0) matters */
    else
    {
      g1 = FpX_gcd(f2,g1, pp);
      if (degpol(g1))
      {
        f2= FpX_div(f2,g1,pp);
        if (lg(u) == lg(g1)) continue;
        u = FpX_div( u,g1,pp);
      }
    }
    /* u is square-free (product of irred. of multiplicity e * k) */
    u = FpX_normalize(u,pp);
    gel(t,nbfact) = u;
    d = FpX_split_Berlekamp(&gel(t,nbfact), pp);
    if (flag == 2 && d != 1) return NULL;
    if (flag == 1)
      for (j=0; j<(ulong)d; j++) t[nbfact+j] = degpol(gel(t,nbfact+j));
    for (j=0; j<(ulong)d; j++) E[nbfact+j] = e*k;
    nbfact += d;
  }
  if (flag == 2) return gen_1; /* irreducible */
  setlg(t, nbfact);
  setlg(E, nbfact); y = mkvec2(t,E);
  return flag ? sort_factor(y, (void*)&cmpGuGu, cmp_nodata)
              : sort_factor_pol(y, cmpii);
}
GEN
FpX_factor(GEN f, GEN p)
{
  pari_sp av = avma;
  ZX_factmod_init(&f, p);
  return gerepilecopy(av, FpX_Berlekamp_i(f, p, 0));
}
GEN
Flx_factor(GEN f, ulong p)
{
  pari_sp av = avma;
  GEN F = (degpol(f)>log2(p))? Flx_factcantor_i(f,p,0): Flx_Berlekamp_i(f,p,0);
  return gerepilecopy(av, F);
}
GEN
F2x_factor(GEN f)
{
  pari_sp av = avma;
  return gerepilecopy(av, F2x_Berlekamp_i(f, 0));
}

GEN
factormod0(GEN f, GEN p, long flag)
{
  switch(flag)
  {
    case 0: return factmod(f,p);
    case 1: return simplefactmod(f,p);
    default: pari_err_FLAG("factormod");
  }
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                     FACTORIZATION IN F_q                        */
/*                                                                 */
/*******************************************************************/
static GEN
to_Fq(GEN x, GEN T, GEN p)
{
  long i, lx, tx = typ(x);
  GEN y;

  if (tx == t_INT)
    y = mkintmod(x,p);
  else
  {
    if (tx != t_POL) pari_err_TYPE("to_Fq",x);
    lx = lg(x);
    y = cgetg(lx,t_POL); y[1] = x[1];
    for (i=2; i<lx; i++) gel(y,i) = mkintmod(gel(x,i), p);
  }
  return mkpolmod(y, T);
}

static GEN
to_Fq_pol(GEN x, GEN T, GEN p)
{
  long i, lx = lg(x);
  for (i=2; i<lx; i++) gel(x,i) = to_Fq(gel(x,i),T,p);
  return x;
}

static GEN
to_Fq_fact(GEN P, GEN E, GEN T, GEN p, pari_sp av)
{
  GEN y, u, v;
  long j, l = lg(P), nbf = lg(P);

  u = cgetg(nbf,t_COL);
  v = cgetg(nbf,t_COL);
  for (j=1; j<l; j++)
  {
    gel(u,j) = simplify_shallow(gel(P,j)); /* may contain pols of degree 0 */
    gel(v,j) = utoi(uel(E,j));
  }
  y = gerepilecopy(av, mkmat2(u, v));
  u = gel(y,1);
  p = icopy(p);
  T = FpX_to_mod(T, p);
  for (j=1; j<nbf; j++) gel(u,j) = to_Fq_pol(gel(u,j), T,p);
  return y;
}
static GEN
to_FqC(GEN P, GEN T, GEN p, pari_sp av)
{
  GEN u;
  long j, l = lg(P), nbf = lg(P);

  u = cgetg(nbf,t_COL);
  for (j=1; j<l; j++)
    gel(u,j) = simplify_shallow(gel(P,j)); /* may contain pols of degree 0 */
  u = gerepilecopy(av, u);
  p = icopy(p);
  T = FpX_to_mod(T, p);
  for (j=1; j<nbf; j++) gel(u,j) = to_Fq(gel(u,j), T,p);
  return u;
}

GEN
FlxqXQ_halfFrobenius(GEN a, GEN S, GEN T, ulong p)
{
  long vT = get_Flx_var(T);
  GEN xp = Flx_Frobenius(T, p);
  GEN Xp = FlxqXQ_pow(polx_FlxX(varn(S), vT), utoi(p), S, T, p);
  GEN ap2 = FlxqXQ_pow(a,utoi(p>>1), S, T, p);
  GEN V = FlxqXQV_autsum(mkvec3(xp, Xp, ap2), get_Flx_degree(T), S, T, p);
  return gel(V,3);
}

GEN
FpXQXQ_halfFrobenius(GEN a, GEN S, GEN T, GEN p)
{
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    long v = get_FpX_var(T);
    GEN Tp = ZXT_to_FlxT(T,pp), Sp = ZXX_to_FlxX(S, pp, v);
    return FlxX_to_ZXX(FlxqXQ_halfFrobenius(ZXX_to_FlxX(a,pp,v),Sp,Tp,pp));
  }
  else
  {
    GEN xp = FpX_Frobenius(T, p);
    GEN Xp = FpXQXQ_pow(pol_x(varn(S)), p, S, T, p);
    GEN ap2 = FpXQXQ_pow(a,shifti(p,-1), S, T, p);
    GEN V = FpXQXQV_autsum(mkvec3(xp,Xp,ap2), get_FpX_degree(T), S, T, p);
    return gel(V,3);
  }
}

GEN
FlxqX_Frobenius(GEN S, GEN T, ulong p)
{
  pari_sp av = avma;
  long n = get_Flx_degree(T), vT = get_Flx_var(T);
  GEN X  = polx_FlxX(varn(S), vT);
  GEN xp = Flx_Frobenius(T, p);
  GEN Xp = FlxqXQ_pow(X, utoi(p), S, T, p);
  GEN Xq = gel(FlxqXQV_autpow(mkvec2(xp,Xp), n, S, T, p), 2);
  return gerepilecopy(av, Xq);
}

GEN
FpXQX_Frobenius(GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  long n = get_FpX_degree(T);
  GEN X  = pol_x(varn(S));
  GEN xp = FpX_Frobenius(T, p);
  GEN Xp = FpXQXQ_pow(X, p, S, T, p);
  GEN Xq = gel(FpXQXQV_autpow(mkvec2(xp,Xp), n, S, T, p), 2);
  return gerepilecopy(av, Xq);
}

static GEN
FqX_Frobenius_powers(GEN S, GEN T, GEN p)
{
  long N = degpol(S);
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    GEN Tp = ZXT_to_FlxT(T, pp), Sp = ZXX_to_FlxX(S, pp, get_FpX_var(T));
    GEN Xq = FlxqX_Frobenius(Sp, Tp, pp);
    return FlxqXQ_powers(Xq, N-1, Sp, Tp, pp);
  } else
  {
    GEN Xq = FpXQX_Frobenius(S, T, p);
    return FpXQXQ_powers(Xq, N-1, S, T, p);
  }
}

static GEN
FqX_Frobenius_eval(GEN x, GEN V, GEN S, GEN T, GEN p)
{
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    long v = get_FpX_var(T);
    GEN Tp = ZXT_to_FlxT(T, pp), Sp = ZXX_to_FlxX(S, pp, v);
    GEN xp = ZXX_to_FlxX(x, pp, v);
    return FlxX_to_ZXX(FlxqX_FlxqXQV_eval(xp, V, Sp, Tp, pp));
  }
  else
    return FpXQX_FpXQXQV_eval(x, V, S, T, p);
}

static GEN
FpXQX_split_part(GEN f, GEN T, GEN p)
{
  long n = degpol(f);
  GEN z, X = pol_x(varn(f));
  if (n <= 1) return f;
  f = FpXQX_red(f, T, p);
  z = FpXQX_Frobenius(f, T, p);
  z = FpXX_sub(z, X , p);
  return FpXQX_gcd(z, f, T, p);
}

static GEN
FlxqX_split_part(GEN f, GEN T, ulong p)
{
  long n = degpol(f);
  GEN z, Xq, X = polx_FlxX(varn(f),get_Flx_var(T));
  if (n <= 1) return f;
  f = FlxqX_red(f, T, p);
  Xq = FlxqX_Frobenius(f, T, p);
  z = FlxX_sub(Xq, X , p);
  return FlxqX_gcd(z, f, T, p);
}

long
FpXQX_nbroots(GEN f, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z;
  if(lgefint(p)==3)
  {
    ulong pp=p[2];
    z = FlxqX_split_part(ZXX_to_FlxX(f,pp,varn(T)),ZXT_to_FlxT(T,pp),pp);
  }
  else
    z = FpXQX_split_part(f, T, p);
  avma = av; return degpol(z);
}

long
FqX_nbroots(GEN f, GEN T, GEN p)
{ return T ? FpXQX_nbroots(f, T, p): FpX_nbroots(f, p); }

long
FlxqX_nbroots(GEN f, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN z = FlxqX_split_part(f, T, p);
  avma = av; return degpol(z);
}

GEN
FlxqX_Berlekamp_ker(GEN u, GEN T, ulong p)
{
  pari_sp ltop=avma;
  long j,N = degpol(u);
  GEN Xq = FlxqX_Frobenius(u,T,p);
  GEN Q  = FlxqXQ_matrix_pow(Xq,N,N,u,T,p);
  for (j=1; j<=N; j++)
    gcoeff(Q,j,j) = Flx_Fl_add(gcoeff(Q,j,j), p-1, p);
  return gerepileupto(ltop, FlxqM_ker(Q,T,p));
}

GEN
FpXQX_Berlekamp_ker(GEN u, GEN T, GEN p)
{
  if (lgefint(p)==3)
  {
    ulong pp=p[2];
    long v = get_FpX_var(T);
    GEN Tp = ZXT_to_FlxT(T,pp), Sp = ZXX_to_FlxX(u,pp,v);
    return FlxM_to_ZXM(FlxqX_Berlekamp_ker(Sp, Tp, pp));
  } else
  {
    pari_sp ltop=avma;
    long j,N = degpol(u);
    GEN Xq = FpXQX_Frobenius(u,T,p);
    GEN Q  = FpXQXQ_matrix_pow(Xq,N,N,u,T,p);
    for (j=1; j<=N; j++)
      gcoeff(Q,j,j) = Fq_sub(gcoeff(Q,j,j), gen_1, T, p);
    return gerepileupto(ltop, FqM_ker(Q,T,p));
  }
}

long
FpXQX_nbfact(GEN u, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN vker = FpXQX_Berlekamp_ker(u, T, p);
  avma = av; return lg(vker)-1;
}

long
FqX_nbfact(GEN u, GEN T, GEN p)
{
  return T ? FpX_nbfact(u, p): FpXQX_nbfact(u, T, p);
}

long
FqX_split_Berlekamp(GEN *t, GEN T, GEN p)
{
  GEN u = *t, a,b,vker,pol;
  long vu = varn(u), vT = varn(T), dT = degpol(T);
  long d, i, ir, L, la, lb;
  T = FpX_get_red(T, p);
  vker = FpXQX_Berlekamp_ker(u,T,p);
  vker = RgM_to_RgXV(vker,vu);
  d = lg(vker)-1;
  ir = 0;
  /* t[i] irreducible for i < ir, still to be treated for i < L */
  for (L=1; L<d; )
  {
    pol= scalarpol(random_FpX(dT,vT,p),vu);
    for (i=2; i<=d; i++)
      pol = FqX_add(pol, FqX_Fq_mul(gel(vker,i),
                                    random_FpX(dT,vT,p), T, p), T, p);
    pol = FpXQX_red(pol,T,p);
    for (i=ir; i<L && L<d; i++)
    {
      a = t[i]; la = degpol(a);
      if (la == 1) { set_irred(i); }
      else
      {
        pari_sp av = avma;
        b = FqX_rem(pol, a, T,p);
        if (degpol(b)<=0) { avma=av; continue; }
        b = FpXQXQ_halfFrobenius(b, a,T,p);
        if (degpol(b)<=0) { avma=av; continue; }
        gel(b,2) = Fq_sub(gel(b,2), gen_1,T,p);
        b = FqX_gcd(a,b, T,p); lb = degpol(b);
        if (lb && lb < la)
        {
          b = FqX_normalize(b, T,p);
          t[L] = FqX_div(a,b,T,p);
          t[i]= b; L++;
        }
        else avma = av;
      }
    }
  }
  return d;
}

/* split into r factors of degree d */
static void
FqX_split(GEN *t, long d, GEN q, GEN S, GEN T, GEN p)
{
  GEN u = *t;
  long l, v, is2, cnt, dt = degpol(u), dT = degpol(T);
  pari_sp av;
  pari_timer ti;
  GEN w,w0;

  if (dt == d) return;
  v = varn(*t);
  if (DEBUGLEVEL > 6) timer_start(&ti);
  av = avma; is2 = equaliu(p, 2);
  for(cnt = 1;;cnt++, avma = av)
  { /* splits *t with probability ~ 1 - 2^(1-r) */
    w = w0 = FqX_rand(dt,v, T,p);
    if (degpol(w) <= 0) continue;
    for (l=1; l<d; l++) /* sum_{0<i<d} w^(q^i), result in (F_q)^r */
      w = RgX_add(w0, FqX_Frobenius_eval(w, S, u, T, p));
    w = FpXQX_red(w, T,p);
    if (is2)
    {
      w0 = w;
      for (l=1; l<dT; l++) /* sum_{0<i<k} w^(2^i), result in (F_2)^r */
      {
        w = FqX_rem(FqX_sqr(w,T,p), *t, T,p);
        w = FpXX_red(RgX_add(w0,w), p);
      }
    }
    else
    {
      w = FpXQXQ_halfFrobenius(w, *t, T, p);
      /* w in {-1,0,1}^r */
      if (degpol(w) <= 0) continue;
      gel(w,2) = gadd(gel(w,2), gen_1);
    }
    w = FqX_gcd(*t,w, T,p); l = degpol(w);
    if (l && l != dt) break;
  }
  w = gerepileupto(av,FqX_normalize(w,T,p));
  if (DEBUGLEVEL > 6)
    err_printf("[FqX_split] splitting time: %ld (%ld trials)\n",
               timer_delay(&ti),cnt);
  l /= d; t[l] = FqX_div(*t,w, T,p); *t = w;
  FqX_split(t+l,d,q,S,T,p);
  FqX_split(t  ,d,q,S,T,p);
}

/*******************************************************************/
/*                                                                 */
/*                  FACTOR USING TRAGER'S TRICK                    */
/*                                                                 */
/*******************************************************************/
static GEN
FqX_frob_deflate(GEN f, GEN T, GEN p)
{
  GEN F = RgX_deflate(f, itos(p)), frobinv = powiu(p, degpol(T)-1);
  long i, l = lg(F);
  for (i=2; i<l; i++) gel(F,i) = Fq_pow(gel(F,i), frobinv, T,p);
  return F;
}
/* Factor _sqfree_ polynomial a on the finite field Fp[X]/(T). Assumes
 * varncmp (varn(T), varn(A)) > 0 */
static GEN
FqX_split_Trager(GEN A, GEN T, GEN p)
{
  GEN c = NULL, P, u, fa, n;
  long lx, i, k;

  u = A;
  n = NULL;
  for (k = 0; cmpui(k, p) < 0; k++)
  {
    GEN U;
    c = deg1pol_shallow(stoi(k) , gen_0, varn(T));
    U = FqX_translate(u, c, T, p);
    n = FpX_FpXY_resultant(T, U, p);
    if (FpX_is_squarefree(n, p)) break;
    n = NULL;
  }
  if (!n) return NULL;
  if (DEBUGLEVEL>4) err_printf("FqX_split_Trager: choosing k = %ld\n",k);
  /* n guaranteed to be squarefree */
  fa = FpX_factor(n, p); fa = gel(fa,1); lx = lg(fa);
  if (lx == 2) return mkcol(A); /* P^k, P irreducible */

  P = cgetg(lx,t_COL);
  c = FpX_neg(c,p);
  for (i=lx-1; i>1; i--)
  {
    GEN F = FqX_translate(gel(fa,i), c, T, p);
    F = FqX_normalize(FqX_gcd(u, F, T, p), T, p);
    if (typ(F) != t_POL || degpol(F) == 0)
      pari_err_IRREDPOL("FqX_split_Trager [modulus]",T);
    u = FqX_div(u, F, T, p);
    gel(P,i) = F;
  }
  gel(P,1) = u; return P;
}

static long
isabsolutepol(GEN f)
{
  long i, l = lg(f);
  for(i=2; i<l; i++)
  {
    GEN c = gel(f,i);
    if (typ(c) == t_POL && degpol(c) > 0) return 0;
  }
  return 1;
}

static void
add(GEN z, GEN g, long d) { vectrunc_append(z, mkvec2(utoipos(d), g)); }
/* return number of roots of u; assume deg u >= 0 */
long
FqX_split_deg1(GEN *pz, GEN u, GEN T, GEN p)
{
  long dg, N = degpol(u);
  GEN v, S, g, X, z = vectrunc_init(N+1);

  *pz = z;
  if (N == 0) return 0;
  if (N == 1) return 1;
  v = X = pol_x(varn(u));
  S = FqX_Frobenius_powers(u, T, p);
  vectrunc_append(z, S);
  v = FqX_Frobenius_eval(v, S, u, T, p);
  g = FqX_gcd(FpXX_sub(v,X,p),u, T,p);
  dg = degpol(g);
  if (dg > 0) add(z, FqX_normalize(g,T,p), dg);
  return dg;
}

/* return number of factors; z not properly initialized if deg(u) <= 1 */
long
FqX_split_by_degree(GEN *pz, GEN u, GEN T, GEN p)
{
  long nb = 0, d, dg, N = degpol(u);
  GEN v, S, g, X, z = vectrunc_init(N+1);

  *pz = z;
  if (N <= 1) return 1;
  v = X = pol_x(varn(u));
  S = FqX_Frobenius_powers(u, T, p);
  vectrunc_append(z, S);
  for (d=1; d <= N>>1; d++)
  {
    v = FqX_Frobenius_eval(v, S, u, T, p);
    g = FqX_gcd(FpXX_sub(v,X,p),u, T,p);
    dg = degpol(g); if (dg <= 0) continue;
    /* all factors of g have degree d */
    add(z, FqX_normalize(g, T,p), dg / d); nb += dg / d;
    N -= dg;
    if (N)
    {
      u = FqX_div(u,g, T,p);
      v = FqX_rem(v,u, T,p);
    }
  }
  if (N) { add(z, FqX_normalize(u, T,p), 1); nb++; }
  return nb;
}

/* see roots_from_deg1() */
static GEN
FqXC_roots_from_deg1(GEN x, GEN T, GEN p)
{
  long i,l = lg(x);
  GEN r = cgetg(l,t_COL);
  for (i=1; i<l; i++) { GEN P = gel(x,i); gel(r,i) = Fq_neg(gel(P,2), T, p); }
  return r;
}

static GEN
FqX_split_equal(GEN L, GEN S, GEN T, GEN p)
{
  long n = itos(gel(L,1));
  GEN u = gel(L,2), z = cgetg(n + 1, t_COL);
  gel(z,1) = u;
  FqX_split((GEN*)(z+1), degpol(u) / n, powiu(p, degpol(T)), S, T, p);
  return z;
}
GEN
FqX_split_roots(GEN z, GEN T, GEN p, GEN pol)
{
  GEN S = gel(z,1), L = gel(z,2), rep = FqX_split_equal(L, S, T, p);
  if (pol) rep = shallowconcat(rep, FqX_div(pol, gel(L,2), T,p));
  return rep;
}
GEN
FqX_split_all(GEN z, GEN T, GEN p)
{
  GEN S = gel(z,1), rep = cgetg(1, t_VEC);
  long i, l = lg(z);
  for (i = 2; i < l; i++)
    rep = shallowconcat(rep, FqX_split_equal(gel(z,i), S, T, p));
  return rep;
}

/* not memory-clean, as FpX_factorff_i, returning only linear factors */
static GEN
FpX_rootsff_i(GEN P, GEN T, GEN p)
{
  GEN V, F = gel(FpX_factor(P,p), 1);
  long i, lfact = 1, nmax = lgpol(P), n = lg(F), dT = degpol(T);

  V = cgetg(nmax,t_COL);
  for(i=1;i<n;i++)
  {
    GEN R, Fi = gel(F,i);
    long di = degpol(Fi), j, r;
    if (dT % di) continue;
    R = FpX_factorff_irred(gel(F,i),T,p);
    r = lg(R);
    for (j=1; j<r; j++,lfact++)
      gel(V,lfact) = Fq_neg(gmael(R,j, 2), T, p);
  }
  setlg(V,lfact);
  gen_sort_inplace(V, (void*) &cmp_RgX, &cmp_nodata, NULL);
  return V;
}
GEN
FpX_rootsff(GEN P, GEN T, GEN p)
{
  pari_sp av = avma;
  return gerepilecopy(av, FpX_rootsff_i(P, T, p));
}

static GEN
F2xqX_quad_roots(GEN P, GEN T)
{
  GEN b= gel(P,3), c = gel(P,2);
  if (degpol(b)>=0)
  {
    GEN z, d = F2xq_div(c, F2xq_sqr(b,T),T);
    if (F2xq_trace(d,T))
      return cgetg(1, t_COL);
    z = F2xq_mul(b, F2xq_Artin_Schreier(d, T), T);
    return mkcol2(z, F2x_add(b, z));
  }
  else
    return mkcol(F2xq_sqrt(c, T));
}

static GEN
FqX_quad_roots(GEN x, GEN T, GEN p)
{
  GEN s, D, nb, b = gel(x,3), c = gel(x,2);
  if (equaliu(p, 2))
  {
    GEN f2 = ZXX_to_F2xX(x, get_FpX_var(T));
    s = F2xqX_quad_roots(f2, ZX_to_F2x(get_FpX_mod(T)));
    return F2xC_to_ZXC(s);
  }
  D = Fq_sub(Fq_sqr(b,T,p), Fq_Fp_mul(c,utoi(4),T,p), T,p);
  nb = Fq_neg(b,T,p);
  if (signe(D)==0)
    return mkcol(Fq_halve(nb,T, p));
  s = Fq_sqrt(D,T,p);
  if (!s) return cgetg(1, t_COL);
  s = Fq_halve(Fq_add(s,nb,T,p),T, p);
  return mkcol2(s,Fq_sub(nb,s,T,p));
}

static GEN
FqX_roots_i(GEN f, GEN T, GEN p)
{
  GEN R;
  f = FqX_normalize(f, T, p);
  if (!signe(f)) pari_err_ROOTS0("FqX_roots");
  if (isabsolutepol(f))
  {
    f = simplify_shallow(f);
    if (typ(f) == t_INT) return cgetg(1, t_COL);
    return FpX_rootsff_i(f, T, p);
  }
  if (degpol(f)==2)
    return gen_sort(FqX_quad_roots(f,T,p), (void*) &cmp_RgX, &cmp_nodata);
  switch( FqX_split_deg1(&R, f, T, p) )
  {
  case 0: return cgetg(1, t_COL);
  case 1: if (lg(R) == 1) { R = mkvec(f); break; }
            /* fall through */
  default: R = FqX_split_roots(R, T, p, NULL);
  }
  R = FqXC_roots_from_deg1(R, T, p);
  gen_sort_inplace(R, (void*) &cmp_RgX, &cmp_nodata, NULL);
  return R;
}

GEN
FqX_roots(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  if (!T) return FpX_roots(x, p);
  return gerepileupto(av, FqX_roots_i(x, T, p));
}

static long
FqX_sqf_split(GEN *t0, GEN q, GEN T, GEN p)
{
  GEN *t = t0, u = *t, v, S, g, X;
  long d, dg, N = degpol(u);

  if (N == 1) return 1;
  v = X = pol_x(varn(u));
  S = FqX_Frobenius_powers(u, T, p);
  for (d=1; d <= N>>1; d++)
  {
    v = FqX_Frobenius_eval(v, S, u, T, p);
    g = FqX_normalize(FqX_gcd(FpXX_sub(v,X,p),u, T,p),T,p);
    dg = degpol(g); if (dg <= 0) continue;

    /* all factors of g have degree d */
    *t = g;
    FqX_split(t, d, q, S, T, p);
    t += dg / d;
    N -= dg;
    if (N)
    {
      u = FqX_div(u,g, T,p);
      v = FqX_rem(v,u, T,p);
    }
  }
  if (N) *t++ = u;
  return t - t0;
}

/* not memory-clean */
static GEN
FpX_factorff_i(GEN P, GEN T, GEN p)
{
  GEN V, E, F = FpX_factor(P,p);
  long i, lfact = 1, nmax = lgpol(P), n = lgcols(F);

  V = cgetg(nmax,t_VEC);
  E = cgetg(nmax,t_VECSMALL);
  for(i=1;i<n;i++)
  {
    GEN R = FpX_factorff_irred(gmael(F,1,i),T,p), e = gmael(F,2,i);
    long j, r = lg(R);
    for (j=1; j<r; j++,lfact++)
    {
      gel(V,lfact) = gel(R,j);
      gel(E,lfact) = e;
    }
  }
  setlg(V,lfact);
  setlg(E,lfact); return sort_factor_pol(mkvec2(V,E), cmp_RgX);
}
GEN
FpX_factorff(GEN P, GEN T, GEN p)
{
  pari_sp av = avma;
  return gerepilecopy(av, FpX_factorff_i(P, T, p));
}

/* assumes varncmp (varn(T), varn(f)) > 0 */
static GEN
FqX_factor_i(GEN f, GEN T, GEN p)
{
  long pg, j, k, e, N, lfact, pk, d = degpol(f);
  GEN E, f2, f3, df1, df2, g1, u, q, t;

  switch(d)
  {
    case -1: retmkmat2(mkcolcopy(f), mkvecsmall(1));
    case 0: return trivial_fact();
  }
  T = FpX_normalize(T, p);
  f = FqX_normalize(f, T, p);
  if (isabsolutepol(f)) return FpX_factorff_i(simplify_shallow(f), T, p);
  if (degpol(f)==2)
  {
    long v = varn(f);
    GEN r = FqX_quad_roots(f,T,p);
    switch(lg(r)-1)
    {
    case 0:
      return mkvec2(mkcolcopy(f), mkvecsmall(1));
    case 1:
      return mkvec2(mkcol(deg1pol_shallow(gen_1, Fq_neg(gel(r,1), T, p), v)),
                    mkvecsmall(2));
    case 2:
      {
        GEN f1 = deg1pol_shallow(gen_1, Fq_neg(gel(r,1), T, p), v);
        GEN f2 = deg1pol_shallow(gen_1, Fq_neg(gel(r,2), T, p), v);
        t = mkcol2(f1, f2); E = mkvecsmall2(1, 1);
        sort_factor_pol(mkvec2(t, E), cmp_RgX);
        return mkvec2(t, E);
      }
    }
  }

  pg = itos_or_0(p);
  df2  = NULL; /* gcc -Wall */
  t = cgetg(d+1,t_VEC);
  E = cgetg(d+1, t_VECSMALL);

  q = powiu(p, degpol(T));
  e = lfact = 1;
  pk = 1;
  f3 = NULL;
  df1 = FqX_deriv(f, T, p);
  for(;;)
  {
    long nb0;
    while (!signe(df1))
    { /* needs d >= p: pg = 0 can't happen  */
      pk *= pg; e = pk;
      f = FqX_frob_deflate(f, T, p);
      df1 = FqX_deriv(f, T, p); f3 = NULL;
    }
    f2 = f3? f3: FqX_gcd(f,df1, T,p);
    if (!degpol(f2)) u = f;
    else
    {
      g1 = FqX_div(f,f2, T,p);
      df2 = FqX_deriv(f2, T,p);
      if (gequal0(df2)) { u = g1; f3 = f2; }
      else
      {
        f3 = FqX_gcd(f2,df2, T,p);
        u = degpol(f3)? FqX_div(f2, f3, T,p): f2;
        u = FqX_div(g1, u, T,p);
      }
    }
    /* u is square-free (product of irreducibles of multiplicity e) */
    N = degpol(u);
    if (N) {
      nb0 = lfact;
      gel(t,lfact) = FqX_normalize(u, T,p);
      if (N == 1) lfact++;
      else
      {
        if (!equaliu(p,2))
          lfact += FqX_split_Berlekamp(&gel(t,lfact), T, p);
        else
        {
          GEN P = FqX_split_Trager(gel(t,lfact), T, p);
          if (P) {
            for (j = 1; j < lg(P); j++) gel(t,lfact++) = gel(P,j);
          } else {
            if (DEBUGLEVEL) pari_warn(warner, "FqX_split_Trager failed!");
            lfact += FqX_sqf_split(&gel(t,lfact), q, T, p);
          }
        }
      }
      for (j = nb0; j < lfact; j++) E[j] = e;
    }

    if (!degpol(f2)) break;
    f = f2; df1 = df2; e += pk;
  }
  setlg(t, lfact);
  setlg(E, lfact);
  for (j=1; j<lfact; j++) gel(t,j) = FqX_normalize(gel(t,j), T,p);
  (void)sort_factor_pol(mkvec2(t, E), cmp_RgX);
  k = 1;
  for (j = 2; j < lfact; j++)
  {
    if (RgX_equal(gel(t,j), gel(t,k)))
      E[k] += E[j];
    else
    { /* new factor */
      k++;
      E[k] = E[j];
      gel(t,k) = gel(t,j);
    }
  }
  setlg(t, k+1);
  setlg(E, k+1); return mkvec2(t, E);
}

static void
ffcheck(pari_sp *av, GEN *f, GEN *T, GEN p)
{
  long v;
  if (typ(*T)!=t_POL) pari_err_TYPE("factorff",*T);
  if (typ(*f)!=t_POL) pari_err_TYPE("factorff",*f);
  if (typ(p)!=t_INT) pari_err_TYPE("factorff",p);
  v = varn(*T);
  if (varncmp(v, varn(*f)) <= 0)
    pari_err_PRIORITY("factorff", *T, "<=", varn(*f));
  *T = RgX_to_FpX(*T, p); *av = avma;
  *f = RgX_to_FqX(*f, *T,p);
}
GEN
factorff(GEN f, GEN p, GEN T)
{
  pari_sp av;
  GEN z;
  if (!p || !T)
  {
    long pa, t;
    if (typ(f) != t_POL) pari_err_TYPE("factorff",f);
    T = p = NULL;
    t = RgX_type(f, &p, &T, &pa);
    if (t != t_FFELT) pari_err_TYPE("factorff",f);
    return FFX_factor(f,T);
  }
  ffcheck(&av, &f, &T, p); z = FqX_factor_i(f, T, p);
  return to_Fq_fact(gel(z,1),gel(z,2), T,p, av);
}
GEN
polrootsff(GEN f, GEN p, GEN T)
{
  pari_sp av;
  GEN z;
  if (!p || !T)
  {
    long pa, t;
    if (typ(f) != t_POL) pari_err_TYPE("polrootsff",f);
    T = p = NULL;
    t = RgX_type(f, &p, &T, &pa);
    if (t != t_FFELT) pari_err_TYPE("polrootsff",f);
    return FFX_roots(f,T);
  }
  ffcheck(&av, &f, &T, p); z = FqX_roots_i(f, T, p);
  return to_FqC(z, T,p, av);
}

/* factorization of x modulo (T,p). Assume x already reduced */
GEN
FqX_factor(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  if (!T) return FpX_factor(x, p);
  return gerepilecopy(av, FqX_factor_i(x, T, p));
}
/* See also: Isomorphisms between finite field and relative
 * factorization in polarit3.c */
