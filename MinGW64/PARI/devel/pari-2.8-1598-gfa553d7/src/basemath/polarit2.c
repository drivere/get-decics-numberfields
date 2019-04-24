/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/***********************************************************************/
/**                                                                   **/
/**               ARITHMETIC OPERATIONS ON POLYNOMIALS                **/
/**                         (second part)                             **/
/**                                                                   **/
/***********************************************************************/
#include "pari.h"
#include "paripriv.h"

#define addshift(x,y) addshiftpol((x),(y),1)

/* compute Newton sums S_1(P), ... , S_n(P). S_k(P) = sum a_j^k, a_j root of P
 * If N != NULL, assume p-adic roots and compute mod N [assume integer coeffs]
 * If T != NULL, compute mod (T,N) [assume integer coeffs if N != NULL]
 * If y0!= NULL, precomputed i-th powers, i=1..m, m = length(y0).
 * Not memory clean in the latter case */
GEN
polsym_gen(GEN P, GEN y0, long n, GEN T, GEN N)
{
  long dP=degpol(P), i, k, m;
  pari_sp av1, av2;
  GEN s,y,P_lead;

  if (n<0) pari_err_IMPL("polsym of a negative n");
  if (typ(P) != t_POL) pari_err_TYPE("polsym",P);
  if (!signe(P)) pari_err_ROOTS0("polsym");
  y = cgetg(n+2,t_COL);
  if (y0)
  {
    if (typ(y0) != t_COL) pari_err_TYPE("polsym_gen",y0);
    m = lg(y0)-1;
    for (i=1; i<=m; i++) gel(y,i) = gel(y0,i); /* not memory clean */
  }
  else
  {
    m = 1;
    gel(y,1) = stoi(dP);
  }
  P += 2; /* strip codewords */

  P_lead = gel(P,dP); if (gequal1(P_lead)) P_lead = NULL;
  if (P_lead)
  {
    if (N) P_lead = Fq_inv(P_lead,T,N);
    else if (T) P_lead = QXQ_inv(P_lead,T);
  }
  for (k=m; k<=n; k++)
  {
    av1 = avma; s = (dP>=k)? gmulsg(k,gel(P,dP-k)): gen_0;
    for (i=1; i<k && i<=dP; i++)
      s = gadd(s, gmul(gel(y,k-i+1),gel(P,dP-i)));
    if (N)
    {
      s = Fq_red(s, T, N);
      if (P_lead) s = Fq_mul(s, P_lead, T, N);
    }
    else if (T)
    {
      s = grem(s, T);
      if (P_lead) s = grem(gmul(s, P_lead), T);
    }
    else
      if (P_lead) s = gdiv(s, P_lead);
    av2 = avma; gel(y,k+1) = gerepile(av1,av2, gneg(s));
  }
  return y;
}

GEN
polsym(GEN x, long n)
{
  return polsym_gen(x, NULL, n, NULL,NULL);
}

/* centered residue x mod p. po2 = shifti(p, -1) or NULL (euclidean residue) */
GEN
centermodii(GEN x, GEN p, GEN po2)
{
  GEN y = remii(x, p);
  switch(signe(y))
  {
    case 0: break;
    case 1: if (po2 && absi_cmp(y,po2) > 0) y = subii(y, p);
      break;
    case -1: if (!po2 || absi_cmp(y,po2) > 0) y = addii(y, p);
      break;
  }
  return y;
}

static long
s_centermod(long x, ulong pp, ulong pps2)
{
  long y = x % (long)pp;
  if (y < 0) y += pp;
  return Fl_center(y, pp,pps2);
}

/* for internal use */
GEN
centermod_i(GEN x, GEN p, GEN ps2)
{
  long i, lx;
  pari_sp av;
  GEN y;

  if (!ps2) ps2 = shifti(p,-1);
  switch(typ(x))
  {
    case t_INT: return centermodii(x,p,ps2);

    case t_POL: lx = lg(x);
      y = cgetg(lx,t_POL); y[1] = x[1];
      for (i=2; i<lx; i++)
      {
        av = avma;
        gel(y,i) = gerepileuptoint(av, centermodii(gel(x,i),p,ps2));
      }
      return normalizepol_lg(y, lx);

    case t_COL: lx = lg(x);
      y = cgetg(lx,t_COL);
      for (i=1; i<lx; i++) gel(y,i) = centermodii(gel(x,i),p,ps2);
      return y;

    case t_MAT: lx = lg(x);
      y = cgetg(lx,t_MAT);
      for (i=1; i<lx; i++) gel(y,i) = centermod_i(gel(x,i),p,ps2);
      return y;

    case t_VECSMALL: lx = lg(x);
    {
      ulong pp = itou(p), pps2 = itou(ps2);
      y = cgetg(lx,t_VECSMALL);
      for (i=1; i<lx; i++) y[i] = s_centermod(x[i], pp, pps2);
      return y;
    }
  }
  return x;
}

GEN
centermod(GEN x, GEN p) { return centermod_i(x,p,NULL); }

/***********************************************************************/
/**                                                                   **/
/**                          FACTORIZATION                            **/
/**                                                                   **/
/***********************************************************************/
#define assign_or_fail(x,y) { GEN __x = x;\
  if (!*y) *y=__x; else if (!gequal(__x,*y)) return 0;\
}
#define update_prec(x,y) { long __x = x; if (__x < *y) *y=__x; }

static const long tsh = 6;
static long
code(long t1, long t2) { return (t1 << tsh) | t2; }
void
RgX_type_decode(long x, long *t1, long *t2)
{
  *t1 = x >> tsh;
  *t2 = (x & ((1L<<tsh)-1));
}
int
RgX_type_is_composite(long t) { return t >= tsh; }

long
RgX_type(GEN x, GEN *p, GEN *pol, long *pa)
{
  long t[] = {0,0,0,0,0,0,0,0,0,0};
  long tx = typ(x), lx, i, j, t2 = 0;
  GEN ff = NULL;
  *p = *pol = NULL; *pa = LONG_MAX;
  if (is_scalar_t(tx))
  {
    if (tx == t_POLMOD) return 0;
    x = scalarpol(x,0);
  }
  /* t[0..1] unused. Other values, if set, indicate a coefficient of type
   * t[2] : t_REAL
   * t[3] : t_INTMOD
   * t[4] : t_COMPLEX of rationals (t_INT/t_FRAC)
   * t[5] : t_FFELT
   * t[6] : t_COMPLEX of t_REAL
   * t[7] : t_PADIC
   * t[8] : t_QUAD of rationals (t_INT/t_FRAC)
   * t[9]: t_POLMOD of rationals (t_INT/t_FRAC) */
  /* if t2 != 0: t_POLMOD/t_QUAD/t_COMPLEX of modular (t_INTMOD/t_PADIC,
   * given by t) */
  lx = lg(x);
  for (i=2; i<lx; i++)
  {
    GEN c = gel(x,i);
    switch(typ(c))
    {
      case t_INT: case t_FRAC:
        break;
      case t_REAL:
        update_prec(precision(c), pa);
        t[2]=1; break;
      case t_INTMOD:
        assign_or_fail(gel(c,1),p);
        t[3]=1; break;
      case t_FFELT:
        if (!ff) ff=c; else if (!FF_samefield(c,ff)) return 0;
        assign_or_fail(FF_p_i(c),p);
        t[5]=1; break;
      case t_COMPLEX:
        for (j=1; j<=2; j++)
        {
          GEN d = gel(c,j);
          switch(typ(d))
          {
            case t_INT: case t_FRAC:
              t[4]=1; break;
            case t_REAL:
              update_prec(precision(d), pa);
              t[6]=1; break;
            case t_INTMOD:
              assign_or_fail(gel(d,1),p);
              if (!signe(*p) || mod4(*p) != 3) return 0;
              if (!t2) t2 = t_COMPLEX;
              t[3]=1; break;
            case t_PADIC:
              update_prec(precp(d)+valp(d), pa);
              assign_or_fail(gel(d,2),p);
              if (!t2) t2 = t_COMPLEX;
              t[7]=1; break;
            default: return 0;
          }
        }
        if (!t[6]) assign_or_fail(mkpoln(3, gen_1,gen_0,gen_1), pol); /*x^2+1*/
        break;
      case t_PADIC:
        update_prec(precp(c)+valp(c), pa);
        assign_or_fail(gel(c,2),p);
        t[7]=1; break;
      case t_QUAD:
        assign_or_fail(gel(c,1),pol);
        for (j=2; j<=3; j++)
        {
          GEN d = gel(c,j);
          switch(typ(d))
          {
            case t_INT: case t_FRAC:
              t[8]=1; break;
            case t_INTMOD:
              assign_or_fail(gel(d,1),p);
              if (t2 != t_POLMOD) t2 = t_QUAD;
              t[3]=1; break;
            case t_PADIC:
              update_prec(precp(d)+valp(d), pa);
              assign_or_fail(gel(d,2),p);
              if (t2 != t_POLMOD) t2 = t_QUAD;
              t[7]=1; break;
            default: return 0;
          }
        }
        break;
      case t_POLMOD:
        assign_or_fail(gel(c,1),pol);
        for (j=1; j<=2; j++)
        {
          GEN pbis = NULL, polbis = NULL;
          long pabis;
          switch(RgX_type(gel(c,j),&pbis,&polbis,&pabis))
          {
            case t_INT: t[9]=1; break;
            case t_INTMOD: t[3]=1; t2 = t_POLMOD; break;
            case t_PADIC: t[7]=1; t2 = t_POLMOD; update_prec(pabis,pa); break;
            default: return 0;
          }
          if (pbis) assign_or_fail(pbis,p);
          if (polbis) assign_or_fail(polbis,pol);
        }
        break;
      default: return 0;
    }
  }
  if (t[5]) /* ffelt */
  {
    if (t2 ||t[2]||t[4]||t[6]||t[8]||t[9]) return 0;
    *pol=ff; return t_FFELT;
  }
  if (t[6]) /* inexact, complex */
  {
    if (t2 ||t[3]||t[7]||t[9]) return 0;
    return t_COMPLEX;
  }
  if (t[2]) /* inexact, real */
  {
    if (t2 ||t[3]||t[7]||t[9]) return 0;
    return t[4]?t_COMPLEX:t_REAL;
  }
  if (t2) /* polmod/quad/complex of intmod/padic */
  {
    if (t[3]) return code(t2,t_INTMOD);
    if (t[7]) return code(t2,t_PADIC);
  }
  if (t[9]) return code(t_POLMOD,t_INT);
  if (t[8]) return code(t_QUAD,t_INT);
  if (t[4]) return code(t_COMPLEX,t_INT);
  if (t[3]) return t_INTMOD;
  if (t[7]) return t_PADIC;
  return t_INT;
}

GEN
factor0(GEN x,long flag)
{
  return (flag<0)? factor(x): boundfact(x,flag);
}

/* only present for interface with GP */
GEN
gp_factor0(GEN x, GEN flag)
{
  ulong B;
  if (!flag) return factor(x);
  if (typ(flag) != t_INT || signe(flag) < 0) pari_err_FLAG("factor");
  switch(lgefint(flag))
  {
    case 2: B = 0; break;
    case 3: B = flag[2]; break;
    default: pari_err_OVERFLOW("factor [large prime bound]");
             return NULL; /*not reached*/
  }
  return boundfact(x, B);
}

GEN
deg1_from_roots(GEN L, long v)
{
  long i, l = lg(L);
  GEN z = cgetg(l,t_COL);
  for (i=1; i<l; i++)
    gel(z,i) = deg1pol_shallow(gen_1, gneg(gel(L,i)), v);
  return z;
}
GEN
roots_from_deg1(GEN x)
{
  long i,l = lg(x);
  GEN r = cgetg(l,t_VEC);
  for (i=1; i<l; i++) { GEN P = gel(x,i); gel(r,i) = gneg(gel(P,2)); }
  return r;
}

static GEN
gauss_factor_p(GEN p)
{
  GEN a, b; (void)cornacchia(gen_1, p, &a,&b);
  return mkcomplex(a, b);
}

static GEN
gauss_primpart(GEN x, GEN *c)
{
  GEN a = gel(x,1), b = gel(x,2), n = gcdii(a, b);
  *c = n; if (n == gen_1) return x;
  retmkcomplex(diviiexact(a,n), diviiexact(b,n));
}

static GEN
gauss_primpart_try(GEN x, GEN c)
{
  GEN r, y;
  if (typ(x) == t_INT)
  {
    y = dvmdii(x, c, &r); if (r != gen_0) return NULL;
  }
  else
  {
    GEN a = gel(x,1), b = gel(x,2); y = cgetg(3, t_COMPLEX);
    gel(y,1) = dvmdii(a, c, &r); if (r != gen_0) return NULL;
    gel(y,2) = dvmdii(b, c, &r); if (r != gen_0) return NULL;
  }
  return y;
}

static int
gauss_cmp(GEN x, GEN y)
{
  int v;
  if (typ(x) != t_COMPLEX)
    return (typ(y) == t_COMPLEX)? -1: gcmp(x, y);
  if (typ(y) != t_COMPLEX) return 1;
  v = cmpii(gel(x,2), gel(y,2));
  if (v) return v;
  return gcmp(gel(x,1), gel(y,1));
}

/* 0 or canonical representative in Z[i]^* / <i> (impose imag(x) >= 0) */
static GEN
gauss_normal(GEN x)
{
  if (typ(x) != t_COMPLEX) return (signe(x) < 0)? absi(x): x;
  if (signe(gel(x,1)) < 0) x = gneg(x);
  if (signe(gel(x,2)) < 0) x = mulcxI(x);
  return x;
}

static GEN
gauss_factor(GEN x)
{
  pari_sp av = avma;
  GEN a = gel(x,1), b = gel(x,2), d = gen_1, n, y, fa, P, E, P2, E2;
  long t1 = typ(a);
  long t2 = typ(b), i, j, l, exp = 0;
  if (t1 == t_FRAC) d = gel(a,2);
  if (t2 == t_FRAC) d = lcmii(d, gel(b,2));
  if (d == gen_1) y = x;
  else
  {
    y = gmul(x, d);
    a = gel(y,1); t1 = typ(a);
    b = gel(y,2); t2 = typ(b);
  }
  if (t1 != t_INT || t2 != t_INT) return NULL;
  y = gauss_primpart(y, &n);
  fa = factor(cxnorm(y));
  P = gel(fa,1);
  E = gel(fa,2); l = lg(P);
  P2 = cgetg(l, t_COL);
  E2 = cgetg(l, t_COL);
  for (j = 1, i = l-1; i > 0; i--) /* remove largest factors first */
  { /* either p = 2 (ramified) or those factors split in Q(i) */
    GEN p = gel(P,i), w, w2, t, we, pe;
    long v, e = itos(gel(E,i));
    int is2 = equaliu(p, 2);
    w = is2? mkcomplex(gen_1,gen_1): gauss_factor_p(p);
    w2 = gauss_normal( gconj(w) );
    /* w * w2 * I^3 = p, w2 = gconj(w) * I */
    pe = powiu(p, e);
    we = gpowgs(w, e);
    t = gauss_primpart_try( gmul(y, gconj(we)), pe );
    if (t) y = t; /* y /= w^e */
    else {
      /* y /= conj(w)^e, should be y /= w2^e */
      y = gauss_primpart_try( gmul(y, we), pe );
      swap(w, w2); exp -= e; /* += 3*e mod 4 */
    }
    gel(P,i) = w;
    v = Z_pvalrem(n, p, &n);
    if (v) {
      exp -= v; /* += 3*v mod 4 */
      if (is2) v <<= 1; /* 2 = w^2 I^3 */
      else {
        gel(P2,j) = w2;
        gel(E2,j) = utoipos(v); j++;
      }
      gel(E,i) = stoi(e + v);
    }
    v = Z_pvalrem(d, p, &d);
    if (v) {
      exp += v; /* -= 3*v mod 4 */
      if (is2) v <<= 1; /* 2 is ramified */
      else {
        gel(P2,j) = w2;
        gel(E2,j) = utoineg(v); j++;
      }
      gel(E,i) = stoi(e - v);
    }
    exp &= 3;
  }
  if (j > 1) {
    long k = 1;
    GEN P1 = cgetg(l, t_COL);
    GEN E1 = cgetg(l, t_COL);
    /* remove factors with exponent 0 */
    for (i = 1; i < l; i++)
      if (signe(gel(E,i)))
      {
        gel(P1,k) = gel(P,i);
        gel(E1,k) = gel(E,i);
        k++;
      }
    setlg(P1, k); setlg(E1, k);
    setlg(P2, j); setlg(E2, j);
    fa = famat_mul_shallow(mkmat2(P1,E1), mkmat2(P2,E2));
  }
  if (!is_pm1(n) || !is_pm1(d))
  {
    GEN Fa = factor(gdiv(n, d));
    P = gel(Fa,1); l = lg(P);
    E = gel(Fa,2);
    for (i = 1; i < l; i++)
    {
      GEN w, p = gel(P,i);
      long e;
      int is2;
      switch(mod4(p))
      {
        case 3: continue;
        case 2: is2 = 1; break;
        default:is2 = 0; break;
      }
      e = itos(gel(E,i));
      w = is2? mkcomplex(gen_1,gen_1): gauss_factor_p(p);
      gel(P,i) = w;
      if (is2)
        gel(E,i) = stoi(e << 1);
      else
      {
        P = shallowconcat(P, gauss_normal( gconj(w) ));
        E = shallowconcat(E, gel(E,i));
      }
      exp -= e; /* += 3*e mod 4 */
      exp &= 3;
    }
    gel(Fa,1) = P;
    gel(Fa,2) = E;
    fa = famat_mul_shallow(fa, Fa);
  }
  fa = sort_factor(fa, (void*)&gauss_cmp, &cmp_nodata);

  y = gmul(y, powIs(exp));
  if (!gequal1(y)) {
    gel(fa,1) = shallowconcat(mkcol(y), gel(fa,1));
    gel(fa,2) = shallowconcat(gen_1,    gel(fa,2));
  }
  return gerepilecopy(av, fa);
}

GEN
factor(GEN x)
{
  long tx=typ(x), lx, i, pa, v, r1;
  pari_sp av, tetpil;
  GEN  y, p, p1, p2, pol;

  if (gequal0(x))
    switch(tx)
    {
      case t_INT:
      case t_COMPLEX:
      case t_POL:
      case t_RFRAC: return prime_fact(x);
      default: pari_err_TYPE("factor",x);
    }
  av = avma;
  switch(tx)
  {
    case t_INT: return Z_factor(x);

    case t_FRAC:
      p1 = Z_factor(gel(x,1));
      p2 = Z_factor(gel(x,2)); gel(p2,2) = gneg_i(gel(p2,2));
      return gerepilecopy(av, merge_factor_i(p1,p2));

    case t_POL:
      tx=RgX_type(x,&p,&pol,&pa);
      switch(tx)
      {
        case 0: pari_err_IMPL("factor for general polynomials");
        case t_INT: return QX_factor(x);
        case t_INTMOD: return factmod(x,p);

        case t_COMPLEX: y=cgetg(3,t_MAT); lx=lg(x)-2;
          av = avma; p1 = roots(x,pa); tetpil = avma;
          p1 = deg1_from_roots(p1, varn(x));
          gel(y,1) = gerepile(av,tetpil,p1);
          gel(y,2) = const_col(lx-1, gen_1); return y;

        case t_REAL: y=cgetg(3,t_MAT); lx=lg(x)-2; v=varn(x);
          av=avma; p1=cleanroots(x,pa); tetpil=avma;
          for(r1=1; r1<lx; r1++)
            if (typ(gel(p1,r1)) == t_COMPLEX) break;
          lx=(r1+lx)>>1; p2=cgetg(lx,t_COL);
          for(i=1; i<r1; i++)
            gel(p2,i) = deg1pol_shallow(gen_1, negr(gel(p1,i)), v);
          for(   ; i<lx; i++)
          {
            GEN a = gel(p1,2*i-r1);
            p = cgetg(5, t_POL); gel(p2,i) = p;
            p[1] = x[1];
            gel(p,2) = gnorm(a);
            gel(p,3) = gmul2n(gel(a,1),1); togglesign(gel(p,3));
            gel(p,4) = gen_1;
          }
          gel(y,1) = gerepile(av,tetpil,p2);
          gel(y,2) = const_col(lx-1, gen_1); return y;

        case t_PADIC: return factorpadic(x,p,pa);

        case t_FFELT: return FFX_factor(x,pol);

        default:
        {
          GEN w;
          long killv, t1, t2;
          x = leafcopy(x); lx=lg(x);
          pol = leafcopy(pol);
          v = pari_var_next_temp();
          for(i=2; i<lx; i++)
          {
            p1 = gel(x,i);
            switch(typ(p1))
            {
              case t_QUAD: p1++;
              case t_COMPLEX:
                gel(x,i) = mkpolmod(deg1pol_shallow(gel(p1,2), gel(p1,1), v), pol);
            }
          }
          killv = (avma != (pari_sp)pol);
          if (killv) setvarn(pol, fetch_var());
          RgX_type_decode(tx, &t1, &t2);
          switch (t2)
          {
            case t_INT: p1 = polfnf(x,pol); break;
            case t_INTMOD:
              pol = RgX_to_FpX(pol, p);
              if (FpX_is_squarefree(pol,p) && FpX_nbfact(pol, p) == 1)
              {
                p1 = factorff(x,p,pol); break;
              }
            /*fall through*/
            default: pari_err_IMPL("factor for general polynomial");
              return NULL; /* not reached */
          }
          switch (t1)
          {
            case t_POLMOD:
              if (killv) (void)delete_var();
              return gerepileupto(av,p1);
            case t_COMPLEX: w = gen_I(); break;
            case t_QUAD: w = mkquad(pol,gen_0,gen_1);
              break;
            default: pari_err_IMPL("factor for general polynomial");
              return NULL; /* not reached */
          }
          p2=gel(p1,1);
          for(i=1; i<lg(p2); i++)
          {
            GEN P = gel(p2,i);
            long j;
            for(j=2; j<lg(P); j++)
            {
              GEN p = gel(P,j);
              if(typ(p)==t_POLMOD) gel(P,j) = gsubst(gel(p,2),v,w);
            }
          }
          if (killv) (void)delete_var();
          return gerepilecopy(av, p1);
        }
      }
    case t_RFRAC: {
      GEN a = gel(x,1), b = gel(x,2);
      y = factor(b); gel(y,2) = gneg_i(gel(y,2));
      if (typ(a)==t_POL && varn(a)==varn(b)) y = famat_mul_shallow(factor(a), y);
      return gerepilecopy(av, y);
    }

    case t_COMPLEX:
      y = gauss_factor(x);
      if (y) return y;
      /* fall through */
  }
  pari_err_TYPE("factor",x);
  return NULL; /* not reached */
}

/*******************************************************************/
/*                                                                 */
/*                     ROOTS --> MONIC POLYNOMIAL                  */
/*                                                                 */
/*******************************************************************/
static GEN
normalized_mul(void *E, GEN x, GEN y)
{
  long a = gel(x,1)[1], b = gel(y,1)[1];
  (void) E;
  return mkvec2(mkvecsmall(a + b),
                RgX_mul_normalized(gel(x,2),a, gel(y,2),b));
}
/* L = [Vecsmall([a]), A], with a > 0, A an RgX, deg(A) < a; return X^a + A */
static GEN
normalized_to_RgX(GEN L)
{
  long i, a = gel(L,1)[1];
  GEN A = gel(L,2);
  GEN z = cgetg(a + 3, t_POL);
  z[1] = evalsigne(1) | evalvarn(varn(A));
  for (i = 2; i < lg(A); i++) gel(z,i) = gcopy(gel(A,i));
  for (     ; i < a+2;   i++) gel(z,i) = gen_0;
  gel(z,i) = gen_1; return z;
}

/* compute prod (x - a[i]) */
GEN
roots_to_pol(GEN a, long v)
{
  pari_sp av = avma;
  long i, k, lx = lg(a);
  GEN L;
  if (lx == 1) return pol_1(v);
  L = cgetg(lx, t_VEC);
  for (k=1,i=1; i<lx-1; i+=2)
  {
    GEN s = gel(a,i), t = gel(a,i+1);
    GEN x0 = gmul(s,t);
    GEN x1 = gneg(gadd(s,t));
    gel(L,k++) = mkvec2(mkvecsmall(2), deg1pol_shallow(x1,x0,v));
  }
  if (i < lx) gel(L,k++) = mkvec2(mkvecsmall(1),
                                  scalarpol_shallow(gneg(gel(a,i)), v));
  setlg(L, k); L = gen_product(L, NULL, normalized_mul);
  return gerepileupto(av, normalized_to_RgX(L));
}

/* prod_{i=1..r1} (x - a[i]) prod_{i=1..r2} (x - a[i])(x - conj(a[i]))*/
GEN
roots_to_pol_r1(GEN a, long v, long r1)
{
  pari_sp av = avma;
  long i, k, lx = lg(a);
  GEN L;
  if (lx == 1) return pol_1(v);
  L = cgetg(lx, t_VEC);
  for (k=1,i=1; i<r1; i+=2)
  {
    GEN s = gel(a,i), t = gel(a,i+1);
    GEN x0 = gmul(s,t);
    GEN x1 = gneg(gadd(s,t));
    gel(L,k++) = mkvec2(mkvecsmall(2), deg1pol_shallow(x1,x0,v));
  }
  if (i < r1+1) gel(L,k++) = mkvec2(mkvecsmall(1),
                                    scalarpol_shallow(gneg(gel(a,i)), v));
  for (i=r1+1; i<lx; i++)
  {
    GEN s = gel(a,i);
    GEN x0 = gnorm(s);
    GEN x1 = gneg(gtrace(s));
    gel(L,k++) = mkvec2(mkvecsmall(2), deg1pol_shallow(x1,x0,v));
  }
  setlg(L, k); L = gen_product(L, NULL, normalized_mul);
  return gerepileupto(av, normalized_to_RgX(L));
}

/*******************************************************************/
/*                                                                 */
/*                          FACTORBACK                             */
/*                                                                 */
/*******************************************************************/
static GEN
idmulred(void *nf, GEN x, GEN y) { return idealmulred((GEN) nf, x, y); }
static GEN
idpowred(void *nf, GEN x, GEN n) { return idealpowred((GEN) nf, x, n); }
static GEN
idmul(void *nf, GEN x, GEN y) { return idealmul((GEN) nf, x, y); }
static GEN
idpow(void *nf, GEN x, GEN n) { return idealpow((GEN) nf, x, n); }
static GEN
eltmul(void *nf, GEN x, GEN y) { return nfmul((GEN) nf, x, y); }
static GEN
eltpow(void *nf, GEN x, GEN n) { return nfpow((GEN) nf, x, n); }
static GEN
mul(void *a, GEN x, GEN y) { (void)a; return gmul(x,y);}
static GEN
powi(void *a, GEN x, GEN y) { (void)a; return powgi(x,y);}

#if 0
static GEN
_ellmul(void *ell, GEN x, GEN y) { return elladd((GEN) ell, x, y); }
static GEN
_ellpow(void *ell, GEN x, GEN n) { return ellmul((GEN) ell, x, n); }
#endif

/* [L,e] = [fa, NULL] or [elts, NULL] or [elts, exponents] */
GEN
gen_factorback(GEN L, GEN e, GEN (*_mul)(void*,GEN,GEN),
               GEN (*_pow)(void*,GEN,GEN), void *data)
{
  pari_sp av = avma;
  long k, l, lx;
  GEN p,x;

  if (e) /* supplied vector of exponents */
    p = L;
  else
  {
    switch(typ(L)) {
      case t_VEC:
      case t_COL: /* product of the L[i] */
        return gerepileupto(av, gen_product(L, data, _mul));
      case t_MAT: /* genuine factorization */
        l = lg(L);
        if (l == 1) return gen_1;
        if (l == 3) break;
        /*fall through*/
      default:
        pari_err_TYPE("factorback [not a factorization]", L);
    }
    p = gel(L,1);
    e = gel(L,2);
  }
  /* p = elts, e = expo */
  lx = lg(p);
  /* check whether e is an integral vector of correct length */
  switch(typ(e))
  {
    case t_VECSMALL:
      if (lx != lg(e))
        pari_err_TYPE("factorback [not an exponent vector]", e);
      if (lx == 1) return gen_1;
      x = cgetg(lx,t_VEC);
      for (l=1,k=1; k<lx; k++)
        if (e[k]) gel(x,l++) = _pow(data, gel(p,k), stoi(e[k]));
      break;
    case t_VEC: case t_COL:
      if (lx != lg(e) || !RgV_is_ZV(e))
        pari_err_TYPE("factorback [not an exponent vector]", e);
      if (lx == 1) return gen_1;
      x = cgetg(lx,t_VEC);
      for (l=1,k=1; k<lx; k++)
        if (signe(gel(e,k))) gel(x,l++) = _pow(data, gel(p,k), gel(e,k));
      break;
    default:
      pari_err_TYPE("factorback [not an exponent vector]", e);
      return NULL;
  }
  x[0] = evaltyp(t_VEC) | _evallg(l);
  return gerepileupto(av, gen_product(x, data, _mul));
}

GEN
idealfactorback(GEN nf, GEN L, GEN e, int red)
{
  nf = checknf(nf);
  if (red) return gen_factorback(L, e, &idmulred, &idpowred, (void*)nf);
  else     return gen_factorback(L, e, &idmul, &idpow, (void*)nf);
}

GEN
nffactorback(GEN nf, GEN L, GEN e)
{ return gen_factorback(L, e, &eltmul, &eltpow, (void*)checknf(nf)); }

GEN
factorback2(GEN L, GEN e) { return gen_factorback(L, e, &mul, &powi, NULL); }
GEN
factorback(GEN fa) { return factorback2(fa, NULL); }

static int
RgX_is_irred_i(GEN x)
{
  GEN y, p, pol;
  long l = lg(x), pa;

  if (!signe(x) || l <= 3) return 0;
  switch(RgX_type(x,&p,&pol,&pa))
  {
    case t_INTMOD: return FpX_is_irred(RgX_to_FpX(x,p), p);
    case t_COMPLEX: return l == 4;
    case t_REAL:
      if (l == 4) return 1;
      if (l > 5) return 0;
      return gsigne(RgX_disc(x)) > 0;
  }
  y = factor(x);
  return (lg(gcoeff(y,1,1))==l);
}
static int
RgX_is_irred(GEN x)
{
  pari_sp av = avma;
  int r = RgX_is_irred_i(x);
  avma = av; return r;
}
long
isirreducible(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC: return 0;
    case t_POL: return RgX_is_irred(x);
  }
  pari_err_TYPE("isirreducible",x);
  return 0;
}

/*******************************************************************/
/*                                                                 */
/*                         GENERIC GCD                             */
/*                                                                 */
/*******************************************************************/
/* x is a COMPLEX or a QUAD */
static GEN
triv_cont_gcd(GEN x, GEN y)
{
  pari_sp av = avma;
  GEN c;
  if (typ(x)==t_COMPLEX)
  {
    GEN a = gel(x,1), b = gel(x,2);
    if (typ(a) == t_REAL || typ(b) == t_REAL) return gen_1;
    c = ggcd(a,b);
  }
  else
    c = ggcd(gel(x,2),gel(x,3));
  return gerepileupto(av, ggcd(c,y));
}

/* y is a PADIC, x a rational number or an INTMOD */
static GEN
padic_gcd(GEN x, GEN y)
{
  GEN p = gel(y,2);
  long v = gvaluation(x,p), w = valp(y);
  if (w < v) v = w;
  return powis(p, v);
}

/* x,y in Z[i], at least one of which is t_COMPLEX */
static GEN
gauss_gcd(GEN x, GEN y)
{
  pari_sp av = avma;
  GEN dx, dy;
  dx = denom(x); x = gmul(x, dx);
  dy = denom(y); y = gmul(y, dy);
  while (!gequal0(y))
  {
    GEN z = gsub(x, gmul(ground(gdiv(x,y)), y));
    x = y; y = z;
  }
  x = gauss_normal(x);
  if (typ(x) == t_COMPLEX)
  {
    if      (gequal0(gel(x,2))) x = gel(x,1);
    else if (gequal0(gel(x,1))) x = gel(x,2);
  }
  return gerepileupto(av, gdiv(x, lcmii(dx, dy)));
}

static int
is_rational(GEN x) { long t = typ(x); return is_rational_t(t); }
static int
c_is_rational(GEN x)
{
  return (is_rational(gel(x,1)) && is_rational(gel(x,2)));
}
static GEN
c_zero_gcd(GEN c)
{
  GEN x = gel(c,1), y = gel(c,2);
  long tx = typ(x), ty = typ(y);
  if (tx == t_REAL || ty == t_REAL) return gen_1;
  if (tx == t_PADIC || tx == t_INTMOD
   || ty == t_PADIC || ty == t_INTMOD) return ggcd(x, y);
  return gauss_gcd(c, gen_0);
}

/* y == 0 */
static GEN
zero_gcd(GEN x, long tx)
{
  pari_sp av;
  switch(tx)
  {
    case t_INT: return absi(x);
    case t_FRAC: return absfrac(x);
    case t_COMPLEX: return c_zero_gcd(x);
    case t_REAL: return gen_1;
    case t_PADIC: return powis(gel(x,2), valp(x));
    case t_SER: return monomial(gen_1, valp(x), varn(x));
    case t_POLMOD: {
      GEN d = gel(x,2);
      if (typ(d) == t_POL && varn(d) == varn(gel(x,1))) return content(d);
      return isinexact(d)? zero_gcd(d, typ(d)): gcopy(d);
    }
    case t_POL:
      if (!isinexact(x)) break;
      av = avma;
      return gerepileupto(av,
        monomialcopy(content(x), RgX_val(x), varn(x))
      );

    case t_RFRAC:
      if (!isinexact(x)) break;
      av = avma;
      return gerepileupto(av,
        gdiv(zero_gcd(gel(x,1), typ(gel(x,1))), gel(x,2))
      );
  }
  return gcopy(x);
}

/* tx = t_RFRAC, y considered as constant */
static GEN
cont_gcd_rfrac(GEN x, GEN y)
{
  pari_sp av = avma;
  GEN cx; x = primitive_part(x, &cx);
  return gerepileupto(av, gred_rfrac_simple(ggcd(cx? cx: gen_1, y), gel(x,2)));
}
/* tx = t_POL, y considered as constant */
static GEN
cont_gcd_pol(GEN x, GEN y)
{
  pari_sp av = avma;
  return gerepileupto(av, scalarpol(ggcd(content(x),y), varn(x)));
}
/* !is_const_t(tx), tx != t_POL,t_RFRAC, y considered as constant */
static GEN
cont_gcd_gen(GEN x, GEN y)
{
  pari_sp av = avma;
  return gerepileupto(av, ggcd(content(x),y));
}
/* !is_const(tx), y considered as constant */
static GEN
cont_gcd(GEN x, long tx, GEN y)
{
  switch(tx)
  {
    case t_RFRAC: return cont_gcd_rfrac(x,y);
    case t_POL: return cont_gcd_pol(x,y);
    default: return cont_gcd_gen(x,y);
  }
}
static GEN
gcdiq(GEN x, GEN y)
{
  GEN z;
  if (!signe(x)) return Q_abs(y);
  z = cgetg(3,t_FRAC);
  gel(z,1) = gcdii(x,gel(y,1));
  gel(z,2) = icopy(gel(y,2));
  return z;
}
static GEN
gcdqq(GEN x, GEN y)
{
  GEN z = cgetg(3,t_FRAC);
  gel(z,1) = gcdii(gel(x,1), gel(y,1));
  gel(z,2) = lcmii(gel(x,2), gel(y,2));
  return z;
}
/* assume x,y t_INT or t_FRAC */
GEN
Q_gcd(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y);
  if (tx == t_INT)
  { return (ty == t_INT)? gcdii(x,y): gcdiq(x,y); }
  else
  { return (ty == t_INT)? gcdiq(y,x): gcdqq(x,y); }
}

GEN
ggcd(GEN x, GEN y)
{
  long l, i, vx, vy, tx = typ(x), ty = typ(y);
  pari_sp av, tetpil;
  GEN p1,z;

  if (is_noncalc_t(tx) || is_noncalc_t(ty)) pari_err_TYPE2("gcd",x,y);
  if (is_matvec_t(ty))
  {
    z = cgetg_copy(y, &l);
    for (i=1; i<l; i++) gel(z,i) = ggcd(x,gel(y,i));
    return z;
  }
  if (is_matvec_t(tx))
  {
    z = cgetg_copy(x, &l);
    for (i=1; i<l; i++) gel(z,i) = ggcd(gel(x,i),y);
    return z;
  }
  if (tx>ty) { swap(x,y); lswap(tx,ty); }
  /* tx <= ty */
  if (isrationalzero(x)) return zero_gcd(y, ty);
  if (isrationalzero(y)) return zero_gcd(x, tx);
  if (is_const_t(tx))
  {
    if (ty == tx) switch(tx)
    {
      case t_INT:
        return gcdii(x,y);

      case t_INTMOD: z=cgetg(3,t_INTMOD);
        if (equalii(gel(x,1),gel(y,1)))
          gel(z,1) = icopy(gel(x,1));
        else
          gel(z,1) = gcdii(gel(x,1),gel(y,1));
        if (gequal1(gel(z,1))) gel(z,2) = gen_0;
        else
        {
          av = avma; p1 = gcdii(gel(z,1),gel(x,2));
          if (!is_pm1(p1))
          {
            p1 = gcdii(p1,gel(y,2));
            if (equalii(p1, gel(z,1))) { cgiv(p1); p1 = gen_0; }
            else p1 = gerepileuptoint(av, p1);
          }
          gel(z,2) = p1;
        }
        return z;

      case t_FRAC:
        return gcdqq(x,y);

      case t_FFELT:
        if (!FF_samefield(x,y)) pari_err_OP("gcd",x,y);
        return FF_equal0(x) && FF_equal0(y)? FF_zero(y): FF_1(y);

      case t_COMPLEX:
        if (c_is_rational(x) && c_is_rational(y)) return gauss_gcd(x,y);
        return triv_cont_gcd(y,x);

      case t_PADIC:
        if (!equalii(gel(x,2),gel(y,2))) return gen_1;
        return powis(gel(y,2), minss(valp(x), valp(y)));

      case t_QUAD:
        av=avma; p1=gdiv(x,y);
        if (gequal0(gel(p1,3)))
        {
          p1=gel(p1,2);
          if (typ(p1)==t_INT) { avma=av; return gcopy(y); }
          tetpil=avma; return gerepile(av,tetpil, gdiv(y,gel(p1,2)));
        }
        if (typ(gel(p1,2))==t_INT && typ(gel(p1,3))==t_INT) {avma=av; return gcopy(y);}
        p1 = ginv(p1); avma=av;
        if (typ(gel(p1,2))==t_INT && typ(gel(p1,3))==t_INT) return gcopy(x);
        return triv_cont_gcd(y,x);

      default: return gen_1; /* t_REAL */
    }
    if (is_const_t(ty)) switch(tx)
    {
      case t_INT:
        switch(ty)
        {
          case t_INTMOD: z = cgetg(3,t_INTMOD);
            gel(z,1) = icopy(gel(y,1)); av = avma;
            p1 = gcdii(gel(y,1),gel(y,2));
            if (!is_pm1(p1)) {
              p1 = gcdii(x,p1);
              if (equalii(p1, gel(z,1))) { cgiv(p1); p1 = gen_0; }
              else
                p1 = gerepileuptoint(av, p1);
            }
            gel(z,2) = p1; return z;

          case t_REAL: return gen_1;

          case t_FRAC:
            return gcdiq(x,y);

          case t_COMPLEX:
            if (c_is_rational(y)) return gauss_gcd(x,y);
            return triv_cont_gcd(y,x);

          case t_FFELT:
            if (!FF_equal0(y)) return FF_1(y);
            return dvdii(x, gel(y,4))? FF_zero(y): FF_1(y);

          case t_PADIC:
            return padic_gcd(x,y);

          case t_QUAD:
            return triv_cont_gcd(y,x);
          default:
            pari_err_TYPE2("gcd",x,y);
        }

      case t_REAL:
        switch(ty)
        {
          case t_INTMOD:
          case t_FFELT:
          case t_PADIC: pari_err_TYPE2("gcd",x,y);
          default: return gen_1;
        }

      case t_INTMOD:
        switch(ty)
        {
          case t_FRAC:
            av = avma; p1=gcdii(gel(x,1),gel(y,2)); avma = av;
            if (!is_pm1(p1)) pari_err_OP("gcd",x,y);
            return ggcd(gel(y,1), x);

          case t_FFELT:
          {
            GEN p = gel(y,4);
            if (!dvdii(gel(x,1), p)) pari_err_OP("gcd",x,y);
            if (!FF_equal0(y)) return FF_1(y);
            return dvdii(gel(x,2),p)? FF_zero(y): FF_1(y);
          }

          case t_COMPLEX: case t_QUAD:
            return triv_cont_gcd(y,x);

          case t_PADIC:
            return padic_gcd(x,y);

          default: pari_err_TYPE2("gcd",x,y);
        }

      case t_FRAC:
        switch(ty)
        {
          case t_COMPLEX:
            if (c_is_rational(y)) return gauss_gcd(x,y);
          case t_QUAD:
            return triv_cont_gcd(y,x);
          case t_FFELT:
          {
            GEN p = gel(y,4);
            if (dvdii(gel(x,2), p)) pari_err_OP("gcd",x,y);
            if (!FF_equal0(y)) return FF_1(y);
            return dvdii(gel(x,1),p)? FF_zero(y): FF_1(y);
          }

          case t_PADIC:
            return padic_gcd(x,y);

          default: pari_err_TYPE2("gcd",x,y);
        }
      case t_FFELT:
        switch(ty)
        {
          case t_PADIC:
          {
            GEN p = gel(y,2);
            long v = valp(y);
            if (!equalii(p, gel(x,4)) || v < 0) pari_err_OP("gcd",x,y);
            return (v && FF_equal0(x))? FF_zero(x): FF_1(x);
          }
          default: pari_err_TYPE2("gcd",x,y);
        }

      case t_COMPLEX:
        switch(ty)
        {
          case t_PADIC:
          case t_QUAD: return triv_cont_gcd(x,y);
          default: pari_err_TYPE2("gcd",x,y);
        }

      case t_PADIC:
        switch(ty)
        {
          case t_QUAD: return triv_cont_gcd(y,x);
          default: pari_err_TYPE2("gcd",x,y);
        }

      default: return gen_1; /* tx = t_REAL */
    }
    return cont_gcd(y,ty, x);
  }

  if (tx == t_POLMOD)
  {
    if (ty == t_POLMOD)
    {
      GEN T = gel(x,1);
      z = cgetg(3,t_POLMOD);
      T = RgX_equal_var(T,gel(y,1))? RgX_copy(T): RgX_gcd(T, gel(y,1));
      gel(z,1) = T;
      if (degpol(T) <= 0) gel(z,2) = gen_0;
      else
      {
        GEN X, Y, d;
        av = avma; X = gel(x,2); Y = gel(y,2);
        d = ggcd(content(X), content(Y));
        if (!gequal1(d)) { X = gdiv(X,d); Y = gdiv(Y,d); }
        p1 = ggcd(T, X);
        gel(z,2) = gerepileupto(av, gmul(d, ggcd(p1, Y)));
      }
      return z;
    }
    vx = varn(gel(x,1));
    switch(ty)
    {
      case t_POL:
        vy = varn(y);
        if (varncmp(vy,vx) < 0) return cont_gcd_pol(y, x);
        z = cgetg(3,t_POLMOD);
        gel(z,1) = RgX_copy(gel(x,1));
        av = avma; p1 = ggcd(gel(x,1),gel(x,2));
        gel(z,2) = gerepileupto(av, ggcd(p1,y));
        return z;

      case t_RFRAC:
        vy = varn(gel(y,2));
        if (varncmp(vy,vx) < 0) return cont_gcd_rfrac(y, x);
        av = avma;
        p1 = ggcd(gel(x,1),gel(y,2));
        if (degpol(p1)) pari_err_OP("gcd",x,y);
        avma = av; return gdiv(ggcd(gel(y,1),x), content(gel(y,2)));
    }
  }

  vx = gvar(x);
  vy = gvar(y);
  if (varncmp(vy, vx) < 0) return cont_gcd(y,ty, x);
  if (varncmp(vy, vx) > 0) return cont_gcd(x,tx, y);

  /* vx = vy: same main variable */
  switch(tx)
  {
    case t_POL:
      switch(ty)
      {
        case t_POL: return RgX_gcd(x,y);
        case t_SER:
          z = ggcd(content(x), content(y));
          return monomialcopy(z, minss(valp(y),gval(x,vx)), vx);
        case t_RFRAC: return cont_gcd_rfrac(y, x);
      }
      break;

    case t_SER:
      z = ggcd(content(x), content(y));
      switch(ty)
      {
        case t_SER:   return monomialcopy(z, minss(valp(x),valp(y)), vx);
        case t_RFRAC: return monomialcopy(z, minss(valp(x),gval(y,vx)), vx);
      }
      break;

    case t_RFRAC:
    {
      GEN xd = gel(x,2), yd = gel(y,2);
      if (ty != t_RFRAC) pari_err_TYPE2("gcd",x,y);
      z = cgetg(3,t_RFRAC); av = avma;
      gel(z,2) = gerepileupto(av, RgX_mul(xd, RgX_div(yd, RgX_gcd(xd, yd))));
      gel(z,1) = ggcd(gel(x,1), gel(y,1)); return z;
    }
  }
  pari_err_TYPE2("gcd",x,y);
  return NULL; /* not reached */
}
GEN
ggcd0(GEN x, GEN y) { return y? ggcd(x,y): content(x); }

/* x a t_VEC,t_COL or t_MAT */
static GEN
vec_lcm(GEN x)
{
  if (typ(x) == t_MAT)
  {
    long i, l = lg(x);
    GEN z = cgetg(l, t_VEC);
    for (i = 1; i < l; i++) gel(z,i) = glcm0(gel(x,i), NULL);
    x = z;
  }
  return glcm0(x, NULL);
}
static GEN
scal_lcm(GEN x, GEN y)
{
  pari_sp av = avma;
  long tx = typ(x), ty = typ(y);
  if (is_matvec_t(tx)) x = vec_lcm(x);
  if (is_matvec_t(ty)) y = vec_lcm(y);
  return gerepileupto(av, glcm(x, y));
}

static GEN
fix_lcm(GEN x)
{
  GEN t;
  switch(typ(x))
  {
    case t_INT: if (signe(x)<0) x = negi(x);
      break;
    case t_POL:
      if (lg(x) <= 2) break;
      t = leading_term(x);
      if (typ(t) == t_INT && signe(t) < 0) x = gneg(x);
  }
  return x;
}

GEN
glcm0(GEN x, GEN y) {
  if (!y && lg(x) == 2)
  {
    long tx = typ(x);
    if (is_vec_t(tx))
    {
      x = gel(x,1);
      tx = typ(x);
      return is_matvec_t(tx)? vec_lcm(x): fix_lcm(x);
    }
  }
  return gassoc_proto(scal_lcm,x,y);
}

GEN
glcm(GEN x, GEN y)
{
  long tx, ty, i, l;
  pari_sp av;
  GEN p1, z;

  ty = typ(y);
  if (is_matvec_t(ty))
  {
    z = cgetg_copy(y, &l);
    for (i=1; i<l; i++) gel(z,i) = glcm(x,gel(y,i));
    return z;
  }
  tx = typ(x);
  if (is_matvec_t(tx))
  {
    z = cgetg_copy(x, &l);
    for (i=1; i<l; i++) gel(z,i) = glcm(gel(x,i),y);
    return z;
  }
  if (tx==t_INT && ty==t_INT) return lcmii(x,y);
  if (gequal0(x)) return gen_0;

  av = avma;
  p1 = ggcd(x,y); if (!gequal1(p1)) y = gdiv(y,p1);
  return gerepileupto(av, fix_lcm(gmul(x,y)));
}

/* x + r ~ x ? Assume x,r are t_POL, deg(r) <= deg(x) */
static int
pol_approx0(GEN r, GEN x, int exact)
{
  long i, lx,lr;
  if (exact) return gequal0(r);
  lx = lg(x);
  lr = lg(r); if (lr < lx) lx = lr;
  for (i=2; i<lx; i++)
    if (!approx_0(gel(r,i), gel(x,i))) return 0;
  return 1;
}

GEN
RgX_gcd_simple(GEN x, GEN y)
{
  pari_sp av1, av = avma;
  GEN r, yorig = y;
  int exact = !(isinexactreal(x) || isinexactreal(y));

  for(;;)
  {
    av1 = avma; r = RgX_rem(x,y);
    if (pol_approx0(r, x, exact))
    {
      avma = av1;
      if (y == yorig) return RgX_copy(y);
      y = normalizepol_approx(y, lg(y));
      if (lg(y) == 3) { avma = av; return pol_1(varn(x)); }
      return gerepileupto(av,y);
    }
    x = y; y = r;
    if (gc_needed(av,1)) {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgX_gcd_simple");
      gerepileall(av,2, &x,&y);
    }
  }
}
GEN
RgX_extgcd_simple(GEN a, GEN b, GEN *pu, GEN *pv)
{
  pari_sp av = avma;
  GEN q, r, d, d1, u, v, v1;
  int exact = !(isinexactreal(a) || isinexactreal(b));

  d = a; d1 = b; v = gen_0; v1 = gen_1;
  for(;;)
  {
    if (pol_approx0(d1, a, exact)) break;
    q = poldivrem(d,d1, &r);
    v = gsub(v, gmul(q,v1));
    u=v; v=v1; v1=u;
    u=r; d=d1; d1=u;
  }
  u = gsub(d, gmul(b,v));
  u = RgX_div(u,a);

  gerepileall(av, 3, &u,&v,&d);
  *pu = u;
  *pv = v; return d;
}
/*******************************************************************/
/*                                                                 */
/*                    CONTENT / PRIMITIVE PART                     */
/*                                                                 */
/*******************************************************************/

GEN
content(GEN x)
{
  long lx, i, t, tx = typ(x);
  pari_sp av = avma;
  GEN c;

  if (is_scalar_t(tx)) return zero_gcd(x, tx);
  switch(tx)
  {
    case t_RFRAC:
    {
      GEN n = gel(x,1), d = gel(x,2);
      /* -- varncmp(vn, vd) < 0 can't happen
       * -- if n is POLMOD, its main variable (in the sense of gvar2)
       *    has lower priority than denominator */
      if (typ(n) == t_POLMOD || varncmp(gvar(n), varn(d)) > 0)
        n = isinexact(n)? zero_gcd(n, typ(n)): gcopy(n);
      else
        n = content(n);
      return gerepileupto(av, gdiv(n, content(d)));
    }

    case t_VEC: case t_COL:
      lx = lg(x); if (lx==1) return gen_0;
      break;

    case t_MAT:
    {
      long hx, j;
      lx = lg(x);
      if (lx == 1) return gen_0;
      hx = lgcols(x);
      if (hx == 1) return gen_0;
      if (lx == 2) { x = gel(x,1); lx = lg(x); break; }
      if (hx == 2) { x = row_i(x, 1, 1, lx-1); break; }
      c = content(gel(x,1));
      for (j=2; j<lx; j++)
        for (i=1; i<hx; i++) c = ggcd(c,gcoeff(x,i,j));
      if (typ(c) == t_INTMOD || isinexact(c)) { avma=av; return gen_1; }
      return gerepileupto(av,c);
    }

    case t_POL: case t_SER:
      lx = lg(x); if (lx == 2) return gen_0;
      break;
    case t_VECSMALL: return utoi(zv_content(x));
    case t_QFR: case t_QFI:
      lx = 4; break;

    default: pari_err_TYPE("content",x);
      return NULL; /* not reached */
  }
  for (i=lontyp[tx]; i<lx; i++)
    if (typ(gel(x,i)) != t_INT) break;
  lx--; c = gel(x,lx);
  t = typ(c); if (is_matvec_t(t)) c = content(c);
  if (i > lx)
  { /* integer coeffs */
    while (lx-- > lontyp[tx])
    {
      c = gcdii(c, gel(x,lx));
      if (is_pm1(c)) { avma=av; return gen_1; }
    }
  }
  else
  {
    if (isinexact(c)) c = zero_gcd(c, typ(c));
    while (lx-- > lontyp[tx])
    {
      GEN d = gel(x,lx);
      t = typ(d); if (is_matvec_t(t)) d = content(d);
      c = ggcd(c, d);
    }
    if (isinexact(c)) { avma=av; return gen_1; }
  }
  switch(typ(c))
  {
    case t_INT:
      if (signe(c) < 0) c = negi(c);
      break;
    case t_VEC: case t_COL: case t_MAT:
      pari_err_TYPE("content",x);
  }

  return av==avma? gcopy(c): gerepileupto(av,c);
}

GEN
primitive_part(GEN x, GEN *ptc)
{
  pari_sp av = avma;
  GEN c = content(x);
  if (gequal1(c)) { avma = av; c = NULL; }
  else if (!gequal0(c)) x = gdiv(x,c);
  if (ptc) *ptc = c;
  return x;
}
GEN
primpart(GEN x) { return primitive_part(x, NULL); }

/* As content(), but over Q. Treats polynomial as elts of Q[x1,...xn], instead
 * of Q(x2,...,xn)[x1] */
GEN
Q_content(GEN x)
{
  long i, l;
  GEN d;
  pari_sp av;

  switch(typ(x))
  {
    case t_INT:  return absi(x);
    case t_FRAC: return absfrac(x);

    case t_VEC: case t_COL: case t_MAT:
      l = lg(x); if (l == 1) return gen_1;
      av = avma; d = Q_content(gel(x,1));
      for (i=2; i<l; i++)
      {
        d = Q_gcd(d, Q_content(gel(x,i)));
        if ((i & 255) == 0) d = gerepileupto(av, d);
      }
      return gerepileupto(av, d);

    case t_POL:
      l = lg(x); if (l == 2) return gen_0;
      av = avma; d = Q_content(gel(x,2));
      for (i=3; i<l; i++) d = Q_gcd(d, Q_content(gel(x,i)));
      return gerepileupto(av, d);
    case t_POLMOD: return Q_content(gel(x,2));
    case t_COMPLEX: return Q_gcd(Q_content(gel(x,1)), Q_content(gel(x,2)));
  }
  pari_err_TYPE("Q_content",x);
  return NULL; /* not reached */
}

GEN
ZX_content(GEN x)
{
  long i, l = lg(x);
  GEN d;
  pari_sp av;

  if (l == 2) return gen_0;
  d = gel(x,2);
  if (l == 3) return absi(d);
  av = avma;
  for (i=3; !is_pm1(d) && i<l; i++) d = gcdii(d, gel(x,i));
  if (signe(d) < 0) d = absi(d);
  return gerepileuptoint(av, d);
}

/* NOT MEMORY CLEAN (because of t_FRAC).
 * As denom(), but over Q. Treats polynomial as elts of Q[x1,...xn], instead
 * of Q(x2,...,xn)[x1] */
GEN
Q_denom(GEN x)
{
  long i, l;
  GEN d, D;
  pari_sp av;

  switch(typ(x))
  {
    case t_INT: return gen_1;
    case t_FRAC: return gel(x,2);

    case t_VEC: case t_COL: case t_MAT:
      l = lg(x); if (l == 1) return gen_1;
      av = avma; d = Q_denom(gel(x,1));
      for (i=2; i<l; i++)
      {
        D = Q_denom(gel(x,i));
        if (D != gen_1) d = lcmii(d, D);
        if ((i & 255) == 0) d = gerepileuptoint(av, d);
      }
      return gerepileuptoint(av, d);

    case t_POL:
      l = lg(x); if (l == 2) return gen_1;
      av = avma; d = Q_denom(gel(x,2));
      for (i=3; i<l; i++)
      {
        D = Q_denom(gel(x,i));
        if (D != gen_1) d = lcmii(d, D);
      }
      return gerepileuptoint(av, d);

    case t_POLMOD: return Q_denom(gel(x,2));
  }
  pari_err_TYPE("Q_denom",x);
  return NULL; /* not reached */
}

GEN
Q_remove_denom(GEN x, GEN *ptd)
{
  GEN d = Q_denom(x);
  if (d == gen_1) d = NULL; else x = Q_muli_to_int(x,d);
  if (ptd) *ptd = d;
  return x;
}

/* return y = x * d, assuming x rational, and d,y integral */
GEN
Q_muli_to_int(GEN x, GEN d)
{
  long i, l;
  GEN y, xn, xd;
  pari_sp av;

  if (typ(d) != t_INT) pari_err_TYPE("Q_muli_to_int",d);
  switch (typ(x))
  {
    case t_INT:
      return mulii(x,d);

    case t_FRAC:
      xn = gel(x,1);
      xd = gel(x,2); av = avma;
      y = mulii(xn, diviiexact(d, xd));
      return gerepileuptoint(av, y);

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &l);
      for (i=1; i<l; i++) gel(y,i) = Q_muli_to_int(gel(x,i), d);
      return y;

    case t_POL:
      y = cgetg_copy(x, &l); y[1] = x[1];
      for (i=2; i<l; i++) gel(y,i) = Q_muli_to_int(gel(x,i), d);
      return y;

    case t_POLMOD:
      y = cgetg(3, t_POLMOD);
      gel(y,1) = RgX_copy(gel(x,1));
      gel(y,2) = Q_muli_to_int(gel(x,2), d);
      return y;
  }
  pari_err_TYPE("Q_muli_to_int",x);
  return NULL; /* not reached */
}

/* return x * n/d. x: rational; d,n,result: integral; d,n coprime */
static GEN
Q_divmuli_to_int(GEN x, GEN d, GEN n)
{
  long i, l;
  GEN y, xn, xd;
  pari_sp av;

  switch(typ(x))
  {
    case t_INT:
      av = avma; y = diviiexact(x,d);
      return gerepileuptoint(av, mulii(y,n));

    case t_FRAC:
      xn = gel(x,1);
      xd = gel(x,2); av = avma;
      y = mulii(diviiexact(xn, d), diviiexact(n, xd));
      return gerepileuptoint(av, y);

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &l);
      for (i=1; i<l; i++) gel(y,i) = Q_divmuli_to_int(gel(x,i), d,n);
      return y;

    case t_POL:
      y = cgetg_copy(x, &l); y[1] = x[1];
      for (i=2; i<l; i++) gel(y,i) = Q_divmuli_to_int(gel(x,i), d,n);
      return y;

    case t_POLMOD:
      y = cgetg(3, t_POLMOD);
      gel(y,1) = RgX_copy(gel(x,1));
      gel(y,2) = Q_divmuli_to_int(gel(x,2), d,n);
      return y;
  }
  pari_err_TYPE("Q_divmuli_to_int",x);
  return NULL; /* not reached */
}

/* return x / d. x: rational; d,result: integral. */
static GEN
Q_divi_to_int(GEN x, GEN d)
{
  long i, l;
  GEN y;

  switch(typ(x))
  {
    case t_INT:
      return diviiexact(x,d);

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &l);
      for (i=1; i<l; i++) gel(y,i) = Q_divi_to_int(gel(x,i), d);
      return y;

    case t_POL:
      y = cgetg_copy(x, &l); y[1] = x[1];
      for (i=2; i<l; i++) gel(y,i) = Q_divi_to_int(gel(x,i), d);
      return y;

    case t_POLMOD:
      y = cgetg(3, t_POLMOD);
      gel(y,1) = RgX_copy(gel(x,1));
      gel(y,2) = Q_divi_to_int(gel(x,2), d);
      return y;
  }
  pari_err_TYPE("Q_divi_to_int",x);
  return NULL; /* not reached */
}
/* c t_FRAC */
static GEN
Q_divq_to_int(GEN x, GEN c)
{
  GEN n = gel(c,1), d = gel(c,2);
  if (is_pm1(n)) {
    GEN y = Q_muli_to_int(x,d);
    if (signe(n) < 0) y = gneg(y);
    return y;
  }
  return Q_divmuli_to_int(x, n,d);
}

/* return y = x / c, assuming x,c rational, and y integral */
GEN
Q_div_to_int(GEN x, GEN c)
{
  switch(typ(c))
  {
    case t_INT:  return Q_divi_to_int(x, c);
    case t_FRAC: return Q_divq_to_int(x, c);
  }
  pari_err_TYPE("Q_div_to_int",c);
  return NULL; /* not reached */
}
/* return y = x * c, assuming x,c rational, and y integral */
GEN
Q_mul_to_int(GEN x, GEN c)
{
  GEN d, n;
  switch(typ(c))
  {
    case t_INT: return Q_muli_to_int(x, c);
    case t_FRAC:
      n = gel(c,1);
      d = gel(c,2);
      return Q_divmuli_to_int(x, d,n);
  }
  pari_err_TYPE("Q_mul_to_int",c);
  return NULL; /* not reached */
}

GEN
Q_primitive_part(GEN x, GEN *ptc)
{
  pari_sp av = avma;
  GEN c = Q_content(x);
  if (typ(c) == t_INT)
  {
    if (is_pm1(c)) { avma = av; c = NULL; }
    else if (signe(c)) x = Q_divi_to_int(x, c);
  }
  else x = Q_divq_to_int(x, c);
  if (ptc) *ptc = c;
  return x;
}
GEN
Q_primpart(GEN x) { return Q_primitive_part(x, NULL); }

/*******************************************************************/
/*                                                                 */
/*                           SUBRESULTANT                          */
/*                                                                 */
/*******************************************************************/
/* for internal use */
GEN
gdivexact(GEN x, GEN y)
{
  long i,lx;
  GEN z;
  if (gequal1(y)) return x;
  switch(typ(x))
  {
    case t_INT:
      if (typ(y)==t_INT) return diviiexact(x,y);
      if (!signe(x)) return gen_0;
      break;
    case t_INTMOD:
    case t_POLMOD: return gmul(x,ginv(y));
    case t_POL:
      switch(typ(y))
      {
        case t_INTMOD:
        case t_POLMOD: return gmul(x,ginv(y));
        case t_POL: { /* not stack-clean */
          long v;
          if (varn(x)!=varn(y)) break;
          v = RgX_valrem(y,&y);
          if (v) x = RgX_shift_shallow(x,-v);
          if (!degpol(y)) { y = gel(y,2); break; }
          return RgX_div(x,y);
        }
      }
      return RgX_Rg_divexact(x, y);
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); z = new_chunk(lx);
      for (i=1; i<lx; i++) gel(z,i) = gdivexact(gel(x,i),y);
      z[0] = x[0]; return z;
  }
  if (DEBUGLEVEL) pari_warn(warner,"missing case in gdivexact");
  return gdiv(x,y);
}

static GEN
init_resultant(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y), vx, vy;
  if (is_scalar_t(tx) || is_scalar_t(ty))
  {
    if (gequal0(x) || gequal0(y)) return gmul(x,y); /* keep type info */
    if (tx==t_POL) return gpowgs(y, degpol(x));
    if (ty==t_POL) return gpowgs(x, degpol(y));
    return gen_1;
  }
  if (tx!=t_POL) pari_err_TYPE("resultant_all",x);
  if (ty!=t_POL) pari_err_TYPE("resultant_all",y);
  if (!signe(x) || !signe(y)) return gmul(RgX_get_0(x),RgX_get_0(y)); /*type*/
  vx = varn(x);
  vy = varn(y); if (vx == vy) return NULL;
  return (varncmp(vx,vy) < 0)? gpowgs(y,degpol(x)): gpowgs(x,degpol(y));
}

static long
RgX_simpletype(GEN x)
{
  long T = t_INT, i, lx = lg(x);
  for (i = 2; i < lx; i++)
  {
    GEN c = gel(x,i);
    long tc = typ(c);
    switch(tc) {
      case t_INT:
        break;
      case t_FRAC:
        if (T == t_INT) T = t_FRAC;
        break;
      default:
        if (isinexact(c)) return t_REAL;
        T = 0; break;
    }
  }
  return T;
}

/* x an RgX, y a scalar */
static GEN
scalar_res(GEN x, GEN y, GEN *U, GEN *V)
{
  *V = gpowgs(y,degpol(x)-1);
  *U = gen_0; return gmul(y, *V);
}

/* return 0 if the subresultant chain can be interrupted.
 * Set u = NULL if the resultant is 0. */
static int
subres_step(GEN *u, GEN *v, GEN *g, GEN *h, GEN *uze, GEN *um1, long *signh)
{
  GEN u0, c, r, q = RgX_pseudodivrem(*u,*v, &r);
  long du, dv, dr, degq;

  dr = lg(r); if (!signe(r)) { *u = NULL; return 0; }
  du = degpol(*u);
  dv = degpol(*v);
  degq = du - dv;
  if (*um1 == gen_1)
    u0 = gpowgs(gel(*v,dv+2),degq+1);
  else if (*um1 == gen_0)
    u0 = gen_0;
  else /* except in those 2 cases, um1 is an RgX */
    u0 = RgX_Rg_mul(*um1, gpowgs(gel(*v,dv+2),degq+1));

  if (*uze == gen_0) /* except in that case, uze is an RgX */
    u0 = scalarpol(u0, varn(*u)); /* now an RgX */
  else
    u0 = gsub(u0, gmul(q,*uze));

  *um1 = *uze;
  *uze = u0; /* uze <- lead(v)^(degq + 1) * um1 - q * uze */

  *u = *v; c = *g; *g  = leading_term(*u);
  switch(degq)
  {
    case 0: break;
    case 1:
      c = gmul(*h,c); *h = *g; break;
    default:
      c = gmul(gpowgs(*h,degq), c);
      *h = gdivexact(gpowgs(*g,degq), gpowgs(*h,degq-1));
  }
  *v  = RgX_Rg_divexact(r,c);
  *uze= RgX_Rg_divexact(*uze,c);
  if (both_odd(du, dv)) *signh = -*signh;
  return (dr > 3);
}

/* compute U, V s.t Ux + Vy = resultant(x,y) */
static GEN
subresext_i(GEN x, GEN y, GEN *U, GEN *V)
{
  pari_sp av, av2;
  long dx, dy, du, signh, tx = typ(x), ty = typ(y);
  GEN r, z, g, h, p1, cu, cv, u, v, um1, uze, vze;

  if (!is_extscalar_t(tx)) pari_err_TYPE("subresext",x);
  if (!is_extscalar_t(ty)) pari_err_TYPE("subresext",y);
  if (gequal0(x) || gequal0(y)) { *U = *V = gen_0; return gen_0; }
  if (tx != t_POL) {
    if (ty != t_POL) { *U = ginv(x); *V = gen_0; return gen_1; }
    return scalar_res(y,x,V,U);
  }
  if (ty != t_POL) return scalar_res(x,y,U,V);
  if (varn(x) != varn(y))
    return varncmp(varn(x), varn(y)) < 0? scalar_res(x,y,U,V)
                                        : scalar_res(y,x,V,U);
  dx = degpol(x); dy = degpol(y); signh = 1;
  if (dx < dy)
  {
    pswap(U,V); lswap(dx,dy); swap(x,y);
    if (both_odd(dx, dy)) signh = -signh;
  }
  if (dy == 0)
  {
    *V = gpowgs(gel(y,2),dx-1);
    *U = gen_0; return gmul(*V,gel(y,2));
  }
  av = avma;
  u = x = primitive_part(x, &cu);
  v = y = primitive_part(y, &cv);
  g = h = gen_1; av2 = avma;
  um1 = gen_1; uze = gen_0;
  for(;;)
  {
    if (!subres_step(&u, &v, &g, &h, &uze, &um1, &signh)) break;
    if (gc_needed(av2,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"subresext, dr = %ld", degpol(v));
      gerepileall(av2,6, &u,&v,&g,&h,&uze,&um1);
    }
  }
  /* uze an RgX */
  if (!u) { *U = *V = gen_0; avma = av; return gen_0; }
  z = gel(v,2); du = degpol(u);
  if (du > 1)
  { /* z = gdivexact(gpowgs(z,du), gpowgs(h,du-1)); */
    p1 = gpowgs(gdiv(z,h),du-1);
    z = gmul(z,p1);
    uze = RgX_Rg_mul(uze, p1);
  }
  if (signh < 0) { z = gneg_i(z); uze = RgX_neg(uze); }

  vze = RgX_divrem(Rg_RgX_sub(z, RgX_mul(uze,x)), y, &r);
  if (signe(r)) pari_warn(warner,"inexact computation in subresext");
  /* uze ppart(x) + vze ppart(y) = z = resultant(ppart(x), ppart(y)), */
  p1 = gen_1;
  if (cu) p1 = gmul(p1, gpowgs(cu,dy));
  if (cv) p1 = gmul(p1, gpowgs(cv,dx));
  cu = cu? gdiv(p1,cu): p1;
  cv = cv? gdiv(p1,cv): p1;
  z = gmul(z,p1);
  *U = RgX_Rg_mul(uze,cu);
  *V = RgX_Rg_mul(vze,cv);
  return z;
}
GEN
subresext(GEN x, GEN y, GEN *U, GEN *V)
{
  pari_sp av = avma;
  GEN z = subresext_i(x, y, U, V);
  gerepileall(av, 3, &z, U, V);
  return z;
}

static GEN
zero_extgcd(GEN y, GEN *U, GEN *V, long vx)
{
  GEN x=content(y);
  *U=pol_0(vx); *V = scalarpol(ginv(x), vx); return gmul(y,*V);
}

static int
must_negate(GEN x)
{
  GEN t = leading_term(x);
  switch(typ(t))
  {
    case t_INT: case t_REAL:
      return (signe(t) < 0);
    case t_FRAC:
      return (signe(gel(t,1)) < 0);
  }
  return 0;
}

/* compute U, V s.t Ux + Vy = GCD(x,y) using subresultant */
GEN
RgX_extgcd(GEN x, GEN y, GEN *U, GEN *V)
{
  pari_sp av, av2, tetpil;
  long signh; /* junk */
  long dx, dy, vx, tx = typ(x), ty = typ(y);
  GEN z, g, h, p1, cu, cv, u, v, um1, uze, vze, *gptr[3];

  if (tx!=t_POL) pari_err_TYPE("RgX_extgcd",x);
  if (ty!=t_POL) pari_err_TYPE("RgX_extgcd",y);
  if ( varncmp(varn(x),varn(y))) pari_err_VAR("RgX_extgcd",x,y);
  vx=varn(x);
  if (!signe(x))
  {
    if (signe(y)) return zero_extgcd(y,U,V,vx);
    *U = pol_0(vx); *V = pol_0(vx);
    return pol_0(vx);
  }
  if (!signe(y)) return zero_extgcd(x,V,U,vx);
  dx = degpol(x); dy = degpol(y);
  if (dx < dy) { pswap(U,V); lswap(dx,dy); swap(x,y); }
  if (dy==0) { *U=pol_0(vx); *V=ginv(y); return pol_1(vx); }

  av = avma;
  u = x = primitive_part(x, &cu);
  v = y = primitive_part(y, &cv);
  g = h = gen_1; av2 = avma;
  um1 = gen_1; uze = gen_0;
  for(;;)
  {
    if (!subres_step(&u, &v, &g, &h, &uze, &um1, &signh)) break;
    if (gc_needed(av2,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgX_extgcd, dr = %ld",degpol(v));
      gerepileall(av2,6,&u,&v,&g,&h,&uze,&um1);
    }
  }
  if (uze != gen_0) {
    GEN r;
    vze = RgX_divrem(RgX_sub(v, RgX_mul(uze,x)), y, &r);
    if (signe(r)) pari_warn(warner,"inexact computation in RgX_extgcd");
    if (cu) uze = RgX_Rg_div(uze,cu);
    if (cv) vze = RgX_Rg_div(vze,cv);
    p1 = ginv(content(v));
  }
  else /* y | x */
  {
    vze = cv ? RgX_Rg_div(pol_1(vx),cv): pol_1(vx);
    uze = pol_0(vx);
    p1 = gen_1;
  }
  if (must_negate(v)) p1 = gneg(p1);
  tetpil = avma;
  z = RgX_Rg_mul(v,p1);
  *U = RgX_Rg_mul(uze,p1);
  *V = RgX_Rg_mul(vze,p1);
  gptr[0] = &z;
  gptr[1] = U;
  gptr[2] = V;
  gerepilemanysp(av,tetpil,gptr,3); return z;
}

int
RgXQ_ratlift(GEN x, GEN T, long amax, long bmax, GEN *P, GEN *Q)
{
  pari_sp av = avma, av2, tetpil;
  long signh; /* junk */
  long vx;
  GEN g, h, p1, cu, cv, u, v, um1, uze, *gptr[2];

  if (typ(x)!=t_POL) pari_err_TYPE("RgXQ_ratlift",x);
  if (typ(T)!=t_POL) pari_err_TYPE("RgXQ_ratlift",T);
  if ( varncmp(varn(x),varn(T)) ) pari_err_VAR("RgXQ_ratlift",x,T);
  if (bmax < 0) pari_err_DOMAIN("ratlift", "bmax", "<", gen_0, stoi(bmax));
  if (!signe(T)) {
    if (degpol(x) <= amax) {
      *P = RgX_copy(x);
      *Q = pol_1(varn(x));
      return 1;
    }
    return 0;
  }
  if (amax+bmax >= degpol(T))
    pari_err_DOMAIN("ratlift", "amax+bmax", ">=", stoi(degpol(T)),
                    mkvec3(stoi(amax), stoi(bmax), T));
  vx = varn(T);
  u = x = primitive_part(x, &cu);
  v = T = primitive_part(T, &cv);
  g = h = gen_1; av2 = avma;
  um1 = gen_1; uze = gen_0;
  for(;;)
  {
    (void) subres_step(&u, &v, &g, &h, &uze, &um1, &signh);
    if (!u || (typ(uze)==t_POL && degpol(uze)>bmax)) { avma=av; return 0; }
    if (typ(v)!=t_POL || degpol(v)<=amax) break;
    if (gc_needed(av2,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgXQ_ratlift, dr = %ld", degpol(v));
      gerepileall(av2,6,&u,&v,&g,&h,&uze,&um1);
    }
  }
  if (uze == gen_0)
  {
    avma = av; *P = pol_0(vx); *Q = pol_1(vx);
    return 1;
  }
  if (cu) uze = RgX_Rg_div(uze,cu);
  p1 = ginv(content(v));
  if (must_negate(v)) p1 = gneg(p1);
  tetpil = avma;
  *P = RgX_Rg_mul(v,p1);
  *Q = RgX_Rg_mul(uze,p1);
  gptr[0] = P;
  gptr[1] = Q;
  gerepilemanysp(av,tetpil,gptr,2); return 1;
}

/*******************************************************************/
/*                                                                 */
/*                RESULTANT USING DUCOS VARIANT                    */
/*                                                                 */
/*******************************************************************/
/* x^n / y^(n-1), assume n > 0 */
static GEN
Lazard(GEN x, GEN y, long n)
{
  long a;
  GEN c;

  if (n == 1) return x;
  a = 1 << expu(n); /* a = 2^k <= n < 2^(k+1) */
  c=x; n-=a;
  while (a>1)
  {
    a>>=1; c=gdivexact(gsqr(c),y);
    if (n>=a) { c=gdivexact(gmul(c,x),y); n -= a; }
  }
  return c;
}

/* F (x/y)^(n-1), assume n >= 1 */
static GEN
Lazard2(GEN F, GEN x, GEN y, long n)
{
  if (n == 1) return F;
  return RgX_Rg_divexact(RgX_Rg_mul(F, Lazard(x,y,n-1)), y);
}

static GEN
RgX_neg_i(GEN x, long lx)
{
  long i;
  GEN y = cgetg(lx, t_POL); y[1] = x[1];
  for (i=2; i<lx; i++) gel(y,i) = gneg(gel(x,i));
  return y;
}
static GEN
RgX_Rg_mul_i(GEN y, GEN x, long ly)
{
  long i;
  GEN z;
  if (isrationalzero(x)) return pol_0(varn(y));
  z = cgetg(ly,t_POL); z[1] = y[1];
  for (i = 2; i < ly; i++) gel(z,i) = gmul(x,gel(y,i));
  return z;
}
static long
reductum_lg(GEN x, long lx)
{
  long i = lx-2;
  while (i > 1 && gequal0(gel(x,i))) i--;
  return i+1;
}

/* delta = deg(P) - deg(Q) > 0, deg(Q) > 0, P,Q,Z t_POL in the same variable,
 * s "scalar". Return prem(P, -Q) / s^delta lc(P) */
static GEN
nextSousResultant(GEN P, GEN Q, GEN Z, GEN s)
{
  GEN p0, q0, h0, TMP, H, A, z0 = leading_term(Z);
  long p, q, j, lP, lQ;
  pari_sp av;

  p = degpol(P); p0 = gel(P,p+2); lP = reductum_lg(P,lg(P));
  q = degpol(Q); q0 = gel(Q,q+2); lQ = reductum_lg(Q,lg(Q));
  /* p > q. Very often p - 1 = q */
  av = avma;
  /* H = RgX_neg(reductum(Z)) optimized, using Q ~ Z */
  H = RgX_neg_i(Z, lQ); /* deg H < q */

  A = (q+2 < lP)? RgX_Rg_mul_i(H, gel(P,q+2), lQ): NULL;
  for (j = q+1; j < p; j++)
  {
    if (degpol(H) == q-1)
    { /* h0 = coeff of degree q-1 = leading coeff */
      h0 = gel(H,q+1); (void)normalizepol_lg(H, q+1);
      H = addshift(H, RgX_Rg_divexact(RgX_Rg_mul_i(Q, gneg(h0), lQ), q0));
    }
    else
      H = RgX_shift_shallow(H, 1);
    if (j+2 < lP)
    {
      TMP = RgX_Rg_mul(H, gel(P,j+2));
      A = A? RgX_add(A, TMP): TMP;
    }
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"nextSousResultant j = %ld/%ld",j,p);
      gerepileall(av,A?2:1,&H,&A);
    }
  }
  if (q+2 < lP) lP = reductum_lg(P, q+3);
  TMP = RgX_Rg_mul_i(P, z0, lP);
  A = A? RgX_add(A, TMP): TMP;
  A = RgX_Rg_divexact(A, p0);
  if (degpol(H) == q-1)
  {
    h0 = gel(H,q+1); (void)normalizepol_lg(H, q+1); /* destroy old H */
    A = RgX_add(RgX_Rg_mul(addshift(H,A),q0), RgX_Rg_mul_i(Q, gneg(h0), lQ));
  }
  else
    A = RgX_Rg_mul(addshift(H,A), q0);
  return RgX_Rg_divexact(A, s);
}

/* Ducos's subresultant */
GEN
RgX_resultant_all(GEN P, GEN Q, GEN *sol)
{
  pari_sp av, av2;
  long dP, dQ, delta, sig = 1;
  GEN cP, cQ, Z, s;

  dP = degpol(P);
  dQ = degpol(Q); delta = dP - dQ;
  if (delta < 0)
  {
    if (both_odd(dP, dQ)) sig = -1;
    swap(P,Q); lswap(dP, dQ); delta = -delta;
  }
  if (sol) *sol = gen_0;
  av = avma;
  if (dQ <= 0)
  {
    if (dQ < 0) return RgX_get_0(P);
    s = gpowgs(gel(Q,2), dP);
    if (sig == -1) s = gerepileupto(av, gneg(s));
    return s;
  }
  P = primitive_part(P, &cP);
  Q = primitive_part(Q, &cQ);
  av2 = avma;
  s = gpowgs(leading_term(Q),delta);
  if (both_odd(dP, dQ)) sig = -sig;
  Z = Q;
  Q = RgX_pseudorem(P, Q);
  P = Z;
  while(degpol(Q) > 0)
  {
    delta = degpol(P) - degpol(Q); /* > 0 */
    Z = Lazard2(Q, leading_term(Q), s, delta);
    if (both_odd(degpol(P), degpol(Q))) sig = -sig;
    Q = nextSousResultant(P, Q, Z, s);
    P = Z;
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"resultant_all, degpol Q = %ld",degpol(Q));
      gerepileall(av2,2,&P,&Q);
    }
    s = leading_term(P);
  }
  if (!signe(Q)) { avma = av; return RgX_get_0(Q); }
  s = Lazard(leading_term(Q), s, degpol(P));
  if (sig == -1) s = gneg(s);
  if (cP) s = gmul(s, gpowgs(cP,dQ));
  if (cQ) s = gmul(s, gpowgs(cQ,dP));
  if (sol) { *sol = P; gerepileall(av, 2, &s, sol); return s; }
  return gerepilecopy(av, s);
}
/* Return resultant(P,Q). If sol != NULL: set *sol to the last non-constant
 * polynomial in the prs IF the sequence was computed, and gen_0 otherwise.
 * Uses Sylvester's matrix if P or Q inexact, a modular algorithm if they
 * are in Q[X], and Ducos/Lazard optimization of the subresultant algorithm
 * in the "generic" case. */
GEN
resultant_all(GEN P, GEN Q, GEN *sol)
{
  long TP, TQ;
  GEN s;

  if (sol) *sol = gen_0;
  if ((s = init_resultant(P,Q))) return s;
  if ((TP = RgX_simpletype(P)) == t_REAL || (TQ = RgX_simpletype(Q)) == t_REAL)
    return resultant2(P,Q); /* inexact */
  if (TP && TQ) /* rational */
  {
    if (TP == t_INT && TQ == t_INT) return ZX_resultant(P,Q);
    return QX_resultant(P,Q);
  }
  return RgX_resultant_all(P, Q, sol);
}

/*******************************************************************/
/*                                                                 */
/*               RESULTANT USING SYLVESTER MATRIX                  */
/*                                                                 */
/*******************************************************************/
static GEN
_pol_0(void)
{
  GEN x = cgetg(3,t_POL);
  x[1] = 0;
  gel(x,2) = gen_0; return x;
}

static GEN
sylvester_col(GEN x, long j, long d, long D)
{
  GEN c = cgetg(d+1,t_COL);
  long i;
  for (i=1; i< j; i++) gel(c,i) = gen_0;
  for (   ; i<=D; i++) gel(c,i) = gel(x,D-i+2);
  for (   ; i<=d; i++) gel(c,i) = gen_0;
  return c;
}

GEN
sylvestermatrix_i(GEN x, GEN y)
{
  long j,d,dx,dy;
  GEN M;

  dx = degpol(x); if (dx < 0) { dx = 0; x = _pol_0(); }
  dy = degpol(y); if (dy < 0) { dy = 0; y = _pol_0(); }
  d = dx+dy; M = cgetg(d+1,t_MAT);
  for (j=1; j<=dy; j++) gel(M,j)    = sylvester_col(x,j,d,j+dx);
  for (j=1; j<=dx; j++) gel(M,j+dy) = sylvester_col(y,j,d,j+dy);
  return M;
}

GEN
sylvestermatrix(GEN x, GEN y)
{
  long i,j,lx;
  if (typ(x)!=t_POL) pari_err_TYPE("sylvestermatrix",x);
  if (typ(y)!=t_POL) pari_err_TYPE("sylvestermatrix",y);
  if (varn(x) != varn(y)) pari_err_VAR("sylvestermatrix",x,y);
  x = sylvestermatrix_i(x,y); lx = lg(x);
  for (i=1; i<lx; i++)
    for (j=1; j<lx; j++) gcoeff(x,i,j) = gcopy(gcoeff(x,i,j));
  return x;
}

GEN
resultant2(GEN x, GEN y)
{
  pari_sp av;
  GEN r;
  if ((r = init_resultant(x,y))) return r;
  av = avma; return gerepileupto(av,det(sylvestermatrix_i(x,y)));
}

/* If x a t_POL, let vx = main variable of x; return a t_POL in variable v0:
 * if vx <= v, return subst(x, v, pol_x(v0))
 * if vx >  v, return scalarpol(x, v0) */
static GEN
fix_pol(GEN x, long v, long v0)
{
  long vx;
  if (typ(x) != t_POL) return x;
  vx = varn(x);
  if (v == vx)
  {
    if (v) { x = leafcopy(x); setvarn(x, v0); }
    return x;
  }
  if (varncmp(v, vx) > 0)
  {
    x = gsubst(x,v,pol_x(v0));
    if (typ(x) == t_POL && varn(x) == v0) return x;
  }
  return scalarpol_shallow(x, v0);
}

/* resultant of x and y with respect to variable v, or with respect to their
 * main variable if v < 0. */
GEN
polresultant0(GEN x, GEN y, long v, long flag)
{
  long v0 = 0;
  pari_sp av = avma;

  if (v >= 0)
  {
    v0 = fetch_var_higher();
    x = fix_pol(x,v, v0);
    y = fix_pol(y,v, v0);
  }
  switch(flag)
  {
    case 2:
    case 0: x=resultant_all(x,y,NULL); break;
    case 1: x=resultant2(x,y); break;
    default: pari_err_FLAG("polresultant");
  }
  if (v >= 0) (void)delete_var();
  return gerepileupto(av,x);
}
GEN
polresultantext0(GEN x, GEN y, long v)
{
  GEN R, U, V;
  long v0 = 0;
  pari_sp av = avma;

  if (v >= 0)
  {
    v0 = fetch_var_higher();
    x = fix_pol(x,v, v0);
    y = fix_pol(y,v, v0);
  }
  R = subresext_i(x,y, &U,&V);
  if (v >= 0)
  {
    (void)delete_var();
    if (typ(U) == t_POL && varn(U) != v) U = poleval(U, pol_x(v));
    if (typ(V) == t_POL && varn(V) != v) V = poleval(V, pol_x(v));
  }
  return gerepilecopy(av, mkvec3(U,V,R));
}
GEN
polresultantext(GEN x, GEN y) { return polresultantext0(x,y,-1); }

/*******************************************************************/
/*                                                                 */
/*             CHARACTERISTIC POLYNOMIAL USING RESULTANT           */
/*                                                                 */
/*******************************************************************/

/* (v - x)^d */
static GEN
caract_const(pari_sp av, GEN x, long v, long d)
{ return gerepileupto(av, gpowgs(deg1pol_shallow(gen_1, gneg_i(x), v), d)); }

/* return caract(Mod(x,T)) in variable v */
GEN
RgXQ_charpoly(GEN x, GEN T, long v)
{
  pari_sp av = avma;
  long d = degpol(T), dx, vx, vp, v0;
  GEN ch, L;

  if (typ(x) != t_POL) return caract_const(av, x, v, d);
  vx = varn(x);
  vp = varn(T);
  if (varncmp(vx, vp) > 0) return caract_const(av, x, v, d);
  if (varncmp(vx, vp) < 0) pari_err_PRIORITY("RgXQ_charpoly", x, "<", vp);
  dx = degpol(x);
  if (dx <= 0)
    return dx? monomial(gen_1, d, v): caract_const(av, gel(x,2), v, d);

  v0 = fetch_var_higher();
  x = RgX_neg(x);
  gel(x,2) = gadd(gel(x,2), pol_x(v));
  setvarn(x, v0);
  T = leafcopy(T); setvarn(T, v0);
  ch = resultant_all(T, x, NULL);
  (void)delete_var();
  /* test for silly input: x mod (deg 0 polynomial) */
  if (typ(ch) != t_POL) { avma = av; return pol_1(v); }

  L = leading_term(ch);
  if (!gequal1(L)) ch = RgX_Rg_div(ch, L);
  return gerepileupto(av, ch);
}

/* characteristic polynomial (in v) of x over nf, where x is an element of the
 * algebra nf[t]/(Q(t)) */
GEN
rnfcharpoly(GEN nf, GEN Q, GEN x, long v)
{
  const char *f = "rnfcharpoly";
  long dQ = degpol(Q);
  pari_sp av = avma;
  GEN T;

  if (v < 0) v = 0;
  nf = checknf(nf); T = nf_get_pol(nf);
  Q = RgX_nffix(f, T,Q,0);
  switch(typ(x))
  {
    case t_INT:
    case t_FRAC: return caract_const(av, x, v, dQ);
    case t_POLMOD:
      x = polmod_nffix2(f,T,Q, x,0);
      break;
    case t_POL:
      x = varn(x) == varn(T)? Rg_nffix(f,T,x,0): RgX_nffix(f, T,x,0);
      break;
    default: pari_err_TYPE(f,x);
  }
  if (typ(x) != t_POL) return caract_const(av, x, v, dQ);
  /* x a t_POL in variable vQ */
  if (degpol(x) >= dQ) x = RgX_rem(x, Q);
  if (dQ <= 1) return caract_const(av, constant_term(x), v, 1);
  return gerepilecopy(av, lift_if_rational( RgXQ_charpoly(x, Q, v) ));
}

/*******************************************************************/
/*                                                                 */
/*                  GCD USING SUBRESULTANT                         */
/*                                                                 */
/*******************************************************************/
static int inexact(GEN x, int *simple, int *rational);
static int
isinexactall(GEN x, int *simple, int *rational)
{
  long i, lx = lg(x);
  for (i=2; i<lx; i++)
    if (inexact(gel(x,i), simple, rational)) return 1;
  return 0;
}
/* return 1 if coeff explosion is not possible */
static int
inexact(GEN x, int *simple, int *rational)
{
  int junk = 0;
  switch(typ(x))
  {
    case t_INT: case t_FRAC: return 0;

    case t_REAL: case t_PADIC: case t_SER: return 1;

    case t_INTMOD:
    case t_FFELT:
      *rational = 0;
      if (!*simple) *simple = 1;
      return 0;

    case t_COMPLEX:
      *rational = 0;
      return inexact(gel(x,1), simple, rational)
          || inexact(gel(x,2), simple, rational);
    case t_QUAD:
      *rational = *simple = 0;
      return inexact(gel(x,2), &junk, rational)
          || inexact(gel(x,3), &junk, rational);

    case t_POLMOD:
      *rational = 0;
      return isinexactall(gel(x,1), simple, rational);
    case t_POL:
      *rational = 0;
      *simple = -1;
      return isinexactall(x, &junk, rational);
    case t_RFRAC:
      *rational = 0;
      *simple = -1;
      return inexact(gel(x,1), &junk, rational)
          || inexact(gel(x,2), &junk, rational);
  }
  *rational = 0;
  *simple = -1; return 0;
}

/* x monomial, y t_POL in the same variable */
static GEN
gcdmonome(GEN x, GEN y)
{
  pari_sp av = avma;
  long dx = degpol(x), e = RgX_valrem(y, &y);
  long i, l = lg(y);
  GEN t, v = cgetg(l, t_VEC);
  gel(v,1) = gel(x,dx+2);
  for (i = 2; i < l; i++) gel(v,i) = gel(y,i);
  t = content(v); /* gcd(lc(x), cont(y)) */
  t = simplify_shallow(t);
  if (dx < e) e = dx;
  return gerepileupto(av, monomialcopy(t, e, varn(x)));
}

/* x, y are t_POL in the same variable */
GEN
RgX_gcd(GEN x, GEN y)
{
  long dx, dy;
  pari_sp av, av1;
  GEN d, g, h, p1, p2, u, v;
  int simple = 0, rational = 1;

  if (isexactzero(y)) return RgX_copy(x);
  if (isexactzero(x)) return RgX_copy(y);
  if (RgX_is_monomial(x)) return gcdmonome(x,y);
  if (RgX_is_monomial(y)) return gcdmonome(y,x);
  if (isinexactall(x,&simple,&rational) || isinexactall(y,&simple,&rational))
  {
    av = avma; u = ggcd(content(x), content(y));
    return gerepileupto(av, scalarpol(u, varn(x)));
  }
  if (rational) return QX_gcd(x,y); /* Q[X] */

  av = avma;
  if (simple > 0) x = RgX_gcd_simple(x,y);
  else
  {
    dx = lg(x); dy = lg(y);
    if (dx < dy) { swap(x,y); lswap(dx,dy); }
    if (dy==3)
    {
      d = ggcd(gel(y,2), content(x));
      return gerepileupto(av, scalarpol(d, varn(x)));
    }
    u = primitive_part(x, &p1); if (!p1) p1 = gen_1;
    v = primitive_part(y, &p2); if (!p2) p2 = gen_1;
    d = ggcd(p1,p2);
    av1 = avma;
    g = h = gen_1;
    for(;;)
    {
      GEN r = RgX_pseudorem(u,v);
      long degq, du, dv, dr = lg(r);

      if (!signe(r)) break;
      if (dr <= 3)
      {
        avma = av1; return gerepileupto(av, scalarpol(d, varn(x)));
      }
      if (DEBUGLEVEL > 9) err_printf("RgX_gcd: dr = %ld\n", degpol(r));
      du = lg(u); dv = lg(v); degq = du-dv;
      u = v; p1 = g; g = leading_term(u);
      switch(degq)
      {
        case 0: break;
        case 1:
          p1 = gmul(h,p1); h = g; break;
        default:
          p1 = gmul(gpowgs(h,degq), p1);
          h = gdiv(gpowgs(g,degq), gpowgs(h,degq-1));
      }
      v = RgX_Rg_div(r,p1);
      if (gc_needed(av1,1))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"RgX_gcd");
        gerepileall(av1,4, &u,&v,&g,&h);
      }
    }
    x = RgX_Rg_mul(primpart(v), d);
  }
  if (must_negate(x)) x = RgX_neg(x);
  return gerepileupto(av,x);
}

static GEN
RgX_disc_aux(GEN x)
{
  long dx = degpol(x), Tx;
  GEN D, L, y, p;
  if (!signe(x) || !dx) return RgX_get_0(x);
  if (dx == 1) return RgX_get_1(x);
  if (dx == 2) {
    GEN a = gel(x,4), b = gel(x,3), c = gel(x,2);
    return gsub(gsqr(b), gmul2n(gmul(a,c),2));
  }
  Tx = RgX_simpletype(x);
  if (Tx == t_INT) return ZX_disc(x);
  if (Tx == t_FRAC) return QX_disc(x);
  p = NULL;
  if (RgX_is_FpX(x, &p) && p)
    return Fp_to_mod(FpX_disc(RgX_to_FpX(x,p), p), p);

  y = RgX_deriv(x);
  if (!signe(y)) return RgX_get_0(y);
  if (Tx == t_REAL)
    D = resultant2(x,y);
  else
  {
    D = RgX_resultant_all(x, y, NULL);
    if (D == gen_0) return RgX_get_0(y);
  }
  L = leading_term(x); if (!gequal1(L)) D = gdiv(D,L);
  if (dx & 2) D = gneg(D);
  return D;
}
GEN
RgX_disc(GEN x) { pari_sp av = avma; return gerepileupto(av, RgX_disc_aux(x)); }

GEN
poldisc0(GEN x, long v)
{
  pari_sp av;
  switch(typ(x))
  {
    case t_POL:
    {
      GEN D;
      long v0 = -1;
      av = avma;
      if (v >= 0 && v != varn(x))
      {
        v0 = fetch_var_higher();
        x = fix_pol(x,v, v0);
      }
      D = RgX_disc_aux(x);
      if (v0 >= 0) (void)delete_var();
      return gerepileupto(av, D);
    }

    case t_COMPLEX:
      return utoineg(4);

    case t_QUAD:
      return quad_disc(x);
    case t_POLMOD:
      return poldisc0(gel(x,1), v);

    case t_QFR: case t_QFI:
      av = avma; return gerepileuptoint(av, qfb_disc(x));

    case t_VEC: case t_COL: case t_MAT:
    {
      long i;
      GEN z = cgetg_copy(x, &i);
      for (i--; i; i--) gel(z,i) = poldisc0(gel(x,i), v);
      return z;
    }
  }
  pari_err_TYPE("poldisc",x);
  return NULL; /* not reached */
}

GEN
reduceddiscsmith(GEN x)
{
  long j, n = degpol(x);
  pari_sp av = avma;
  GEN xp, M;

  if (typ(x) != t_POL) pari_err_TYPE("poldiscreduced",x);
  if (n<=0) pari_err_CONSTPOL("poldiscreduced");
  RgX_check_ZX(x,"poldiscreduced");
  if (!gequal1(gel(x,n+2)))
    pari_err_IMPL("non-monic polynomial in poldiscreduced");
  M = cgetg(n+1,t_MAT);
  xp = ZX_deriv(x);
  for (j=1; j<=n; j++)
  {
    gel(M,j) = RgX_to_RgC(xp, n);
    if (j<n) xp = RgX_rem(RgX_shift_shallow(xp, 1), x);
  }
  return gerepileupto(av, ZM_snf(M));
}

/***********************************************************************/
/**                                                                   **/
/**                       STURM ALGORITHM                             **/
/**              (number of real roots of x in [a,b])                 **/
/**                                                                   **/
/***********************************************************************/
static int
exact_sturm(GEN a)
{
  switch(typ(a))
  {
    case t_INT: case t_FRAC: case t_INFINITY: return 1;
    default: return 0;
  }
}

/* Deprecated: support the old format: if a (resp. b) is NULL, set it
 * to -oo resp. +oo). ZX_sturmpart() should be preferred  */
static long
sturmpart_i(GEN x, GEN a, GEN b)
{
  long sl, sr, s, t, r1;
  pari_sp av = avma;
  int integral;
  GEN g,h,u,v;

  if (gequal0(x)) pari_err_ROOTS0("sturm");
  t = typ(x);
  if (t != t_POL)
  {
    if (t == t_INT || t == t_REAL || t == t_FRAC) return 0;
    pari_err_TYPE("sturm",x);
  }
  s=lg(x); if (s==3) return 0;
  u = primpart(x);
  integral = RgX_is_ZX(u);
  if (!b && a && typ(a) == t_VEC && lg(a) == 3)
  { /* new format */
    if (integral && exact_sturm(gel(a,1)) && exact_sturm(gel(a,2)))
    {
      if (!ZX_is_squarefree(u))
        pari_err_DOMAIN("polsturm","issquarefree(pol)","=",gen_0,u);
      return ZX_sturmpart(u, a);
    }
    /* but can't use new function; convert to old form */
    integral = 0;
    b = gel(a,2);
    if (typ(b) == t_INFINITY)
    {
      if (inf_get_sign(b) < 0) return 0;
      b = NULL;
    }
    a = gel(a,1);
    if (typ(a) == t_INFINITY)
    {
      if (inf_get_sign(a) > 0) return 0;
      a = NULL;
    }
  }
  if (integral)
  {
    if (!a) a = mkmoo();
    if (!b) b = mkoo();
    if (exact_sturm(a) && exact_sturm(b))
    {
      if (!ZX_is_squarefree(u))
        pari_err_DOMAIN("polsturm","issquarefree(pol)","=",gen_0,u);
      return ZX_sturmpart(u, mkvec2(a,b));
    }
  }
  /* legacy code: should only be used if we have a t_REAL somewhere; and even
   * then, the calling program should be changed */
  sl = gsigne(leading_term(u));
  t = a? gsigne(poleval(u,a)): (odd(s)? sl: -sl);
  if (s==4)
  {
    if (t == 0) return 1;
    s = b? gsigne(poleval(u,b)):  sl;
    return (s == t)? 0: 1;
  }
  s = b? gsigne(poleval(u,b)): sl;
  r1= (t == 0)? 1: 0;
  v = primpart(RgX_deriv(x));
  sr = b? gsigne(poleval(v,b)): s;
  if (sr)
  {
    if (!s) s=sr;
    else if (sr!=s) { s= -s; r1--; }
  }
  sr = a? gsigne(poleval(v,a)): -t;
  if (sr)
  {
    if (!t) t=sr;
    else if (sr!=t) { t= -t; r1++; }
  }
  g=gen_1; h=gen_1;
  for(;;)
  {
    GEN p1, r = RgX_pseudorem(u,v);
    long du=lg(u), dv=lg(v), dr=lg(r), degq=du-dv;

    if (dr<=2) pari_err_DOMAIN("polsturm","issquarefree(pol)","=",gen_0,x);
    if (gsigne(leading_term(v)) > 0 || degq&1) r=gneg_i(r);
    sl = gsigne(gel(r,dr-1));
    sr = b? gsigne(poleval(r,b)): sl;
    if (sr)
    {
      if (!s) s=sr;
      else if (sr!=s) { s= -s; r1--; }
    }
    sr = a? gsigne(poleval(r,a)): ((dr&1)? sl: -sl);
    if (sr)
    {
      if (!t) t=sr;
      else if (sr!=t) { t= -t; r1++; }
    }
    if (dr==3) return r1;

    u=v; p1 = g; g = gabs(leading_term(u),DEFAULTPREC);
    switch(degq)
    {
      case 0: break;
      case 1:
        p1 = gmul(h,p1); h = g; break;
      default:
        p1 = gmul(gpowgs(h,degq),p1);
        h = gdivexact(gpowgs(g,degq), gpowgs(h,degq-1));
    }
    v = RgX_Rg_divexact(r,p1);
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"polsturm, dr = %ld",dr);
      gerepileall(av,4,&u,&v,&g,&h);
    }
  }
}
long
sturmpart(GEN x, GEN a, GEN b)
{
  pari_sp av = avma;
  long r = sturmpart_i(x,a,b);
  avma = av; return r;
}
long
RgX_sturmpart(GEN x, GEN ab) { return sturmpart(x, ab, NULL); }

/***********************************************************************/
/**                                                                   **/
/**                        GENERIC EXTENDED GCD                       **/
/**                                                                   **/
/***********************************************************************/
/* assume typ(x) = typ(y) = t_POL */
GEN
RgXQ_inv(GEN x, GEN y)
{
  long vx=varn(x), vy=varn(y);
  pari_sp av;
  GEN u, v, d;

  while (vx != vy)
  {
    if (varncmp(vx,vy) > 0)
    {
      d = (vx == NO_VARIABLE)? ginv(x): gred_rfrac_simple(gen_1, x);
      return scalarpol(d, vy);
    }
    if (lg(x)!=3) pari_err_INV("RgXQ_inv",mkpolmod(x,y));
    x = gel(x,2); vx = gvar(x);
  }
  av = avma; d = subresext_i(x,y,&u,&v/*junk*/);
  if (gequal0(d)) pari_err_INV("RgXQ_inv",mkpolmod(x,y));
  d = gdiv(u,d);
  if (typ(d) != t_POL || varn(d) != vy) d = scalarpol(d, vy);
  return gerepileupto(av, d);
}

/*Assume x is a polynomial and y is not */
static GEN
scalar_bezout(GEN x, GEN y, GEN *U, GEN *V)
{
  long vx = varn(x);
  int xis0 = signe(x)==0, yis0 = gequal0(y);
  if (xis0 && yis0) { *U = *V = pol_0(vx); return pol_0(vx); }
  if (yis0) { *U=pol_1(vx); *V = pol_0(vx); return RgX_copy(x);}
  *U=pol_0(vx); *V= ginv(y); return pol_1(vx);
}
/* Assume x==0, y!=0 */
static GEN
zero_bezout(GEN y, GEN *U, GEN *V)
{
  *U=gen_0; *V = ginv(y); return gen_1;
}

GEN
gbezout(GEN x, GEN y, GEN *u, GEN *v)
{
  long tx=typ(x), ty=typ(y), vx;
  if (tx == t_INT && ty == t_INT) return bezout(x,y,u,v);
  if (tx != t_POL)
  {
    if (ty == t_POL)
      return scalar_bezout(y,x,v,u);
    else
    {
      int xis0 = gequal0(x), yis0 = gequal0(y);
      if (xis0 && yis0) { *u = *v = gen_0; return gen_0; }
      if (xis0) return zero_bezout(y,u,v);
      else return zero_bezout(x,v,u);
    }
  }
  else if (ty != t_POL) return scalar_bezout(x,y,u,v);
  vx = varn(x);
  if (vx != varn(y))
    return varncmp(vx, varn(y)) < 0? scalar_bezout(x,y,u,v)
                                   : scalar_bezout(y,x,v,u);
  return RgX_extgcd(x,y,u,v);
}

GEN
gcdext0(GEN x, GEN y)
{
  GEN z=cgetg(4,t_VEC);
  gel(z,3) = gbezout(x,y,(GEN*)(z+1),(GEN*)(z+2));
  return z;
}

/*******************************************************************/
/*                                                                 */
/*                    GENERIC (modular) INVERSE                    */
/*                                                                 */
/*******************************************************************/

GEN
ginvmod(GEN x, GEN y)
{
  long tx=typ(x);

  switch(typ(y))
  {
    case t_POL:
      if (tx==t_POL) return RgXQ_inv(x,y);
      if (is_scalar_t(tx)) return ginv(x);
      break;
    case t_INT:
      if (tx==t_INT) return Fp_inv(x,y);
      if (tx==t_POL) return gen_0;
  }
  pari_err_TYPE2("ginvmod",x,y);
  return NULL; /* not reached */
}

/***********************************************************************/
/**                                                                   **/
/**                         NEWTON POLYGON                            **/
/**                                                                   **/
/***********************************************************************/

/* assume leading coeff of x is non-zero */
GEN
newtonpoly(GEN x, GEN p)
{
  GEN y;
  long n,ind,a,b,c,u1,u2,r1,r2;
  long *vval, num[] = {evaltyp(t_INT) | _evallg(3), 0, 0};

  if (typ(x)!=t_POL) pari_err_TYPE("newtonpoly",x);
  n=degpol(x); if (n<=0) return cgetg(1,t_VEC);
  y = cgetg(n+1,t_VEC); x += 2; /* now x[i] = term of degree i */
  vval = (long *) pari_malloc(sizeof(long)*(n+1));
  for (a=0; a<=n; a++) vval[a] = gvaluation(gel(x,a),p);
  for (a=0, ind=1; a<n; a++)
  {
    if (vval[a] != LONG_MAX) break;
    gel(y,ind++) = utoipos(LONG_MAX);
  }
  for (b=a+1; b<=n; a=b, b=a+1)
  {
    while (vval[b] == LONG_MAX) b++;
    u1=vval[a]-vval[b]; u2=b-a;
    for (c=b+1; c<=n; c++)
    {
      if (vval[c] == LONG_MAX) continue;
      r1=vval[a]-vval[c]; r2=c-a;
      if (u1*r2<=u2*r1) { u1=r1; u2=r2; b=c; }
    }
    while (ind<=b) { affsi(u1,num); gel(y,ind++) = gdivgs(num,u2); }
  }
  pari_free(vval); return y;
}
