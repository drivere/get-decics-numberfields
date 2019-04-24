/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/**************************************************************/
/*                                                            */
/*                        NUMBER FIELDS                       */
/*                                                            */
/**************************************************************/
#include "pari.h"
#include "paripriv.h"

int new_galois_format = 0;

int
checkrnf_i(GEN rnf)
{ return (typ(rnf)==t_VEC && lg(rnf)==13); }

void
checkrnf(GEN rnf)
{ if (!checkrnf_i(rnf)) pari_err_TYPE("checkrnf",rnf); }

GEN
checkbnf_i(GEN X)
{
  if (typ(X) == t_VEC)
    switch (lg(X))
    {
      case 11: return X;
      case 7:  return checkbnf_i(bnr_get_bnf(X));
    }
  return NULL;
}

GEN
checknf_i(GEN X)
{
  if (typ(X)==t_VEC)
    switch(lg(X))
    {
      case 10: return X;
      case 11: return checknf_i(bnf_get_nf(X));
      case 7:  return checknf_i(bnr_get_bnf(X));
      case 3: if (typ(gel(X,2)) == t_POLMOD) return checknf_i(gel(X,1));
    }
  return NULL;
}

GEN
checkbnf(GEN x)
{
  GEN bnf = checkbnf_i(x);
  if (!bnf) pari_err_TYPE("checkbnf [please apply bnfinit()]",x);
  return bnf;
}

GEN
checknf(GEN x)
{
  GEN nf = checknf_i(x);
  if (!nf) pari_err_TYPE("checknf [please apply nfinit()]",x);
  return nf;
}

void
checkbnr(GEN bnr)
{
  if (typ(bnr)!=t_VEC || lg(bnr)!=7)
    pari_err_TYPE("checkbnr [please apply bnrinit()]",bnr);
  (void)checkbnf(bnr_get_bnf(bnr));
}

void
checkbnrgen(GEN bnr)
{
  checkbnr(bnr);
  if (lg(bnr_get_clgp(bnr))<=3)
    pari_err_TYPE("checkbnrgen [apply bnrinit(,,1), not bnrinit()]",bnr);
}

void
checksqmat(GEN x, long N)
{
  if (typ(x)!=t_MAT) pari_err_TYPE("checksqmat",x);
  if (lg(x) == 1 || lgcols(x) != N+1) pari_err_DIM("checksqmat");
}

GEN
checkbid_i(GEN bid)
{
  GEN f;
  if (typ(bid)!=t_VEC || lg(bid)!=6) return NULL;
  f = bid_get_mod(bid);
  if (typ(f)!=t_VEC || lg(f)!=3) return NULL;
  return bid;
}
void
checkbid(GEN bid)
{
  if (!checkbid_i(bid)) pari_err_TYPE("checkbid",bid);
}
void
checkabgrp(GEN v)
{
  if (typ(v) == t_VEC) switch(lg(v))
  {
    case 4: if (typ(gel(v,3)) != t_VEC) break;
    case 3: if (typ(gel(v,2)) != t_VEC) break;
            if (typ(gel(v,1)) != t_INT) break;
            return;/*OK*/
    default: break;
  }
  pari_err_TYPE("checkabgrp",v);
}

GEN
checknfelt_mod(GEN nf, GEN x, const char *s)
{
  GEN T = gel(x,1), a = gel(x,2), Tnf = nf_get_pol(nf);
  if (!RgX_equal_var(T, Tnf)) pari_err_MODULUS(s, T, Tnf);
  return a;
}

void
check_ZKmodule(GEN x, const char *s)
{
  if (typ(x) != t_VEC || lg(x) < 3) pari_err_TYPE(s,x);
  if (typ(gel(x,1)) != t_MAT) pari_err_TYPE(s,gel(x,1));
  if (typ(gel(x,2)) != t_VEC) pari_err_TYPE(s,gel(x,2));
  if (lg(gel(x,2)) != lgcols(x)) pari_err_DIM(s);
}

GEN
get_bnf(GEN x, long *t)
{
  switch(typ(x))
  {
    case t_POL: *t = typ_POL;  return NULL;
    case t_QUAD: *t = typ_Q  ; return NULL;
    case t_VEC:
      switch(lg(x))
      {
        case 5: *t = typ_QUA; return NULL;
        case 6:
          if (typ(gel(x,1)) == t_VEC && typ(gel(x,3)) == t_MAT)
          { *t = typ_BID; return NULL; }
          if (typ(gel(x,2)) == t_COL && typ(gel(x,3)) == t_INT)
          { *t = typ_PRID; return NULL; }
          break;
        case 7:  *t = typ_BNR;
          x = bnr_get_bnf(x); if (typ(x)!=t_VEC || lg(x)!=11) break;
          return x;
        case 9:
          x = gel(x,2);
          if (typ(x) == t_VEC && lg(x) == 4) *t = typ_GAL;
          return NULL;
        case 10: *t = typ_NF; return NULL;
        case 11: *t = typ_BNF; return x;
        case 13: *t = typ_RNF; return NULL;
        case 17: *t = typ_ELL; return NULL;
      }
      break;
    case t_COL:
      if (get_prid(x)) { *t = typ_MODPR; return NULL; }
      break;
  }
  *t = typ_NULL; return NULL;
}

GEN
get_nf(GEN x, long *t)
{
  switch(typ(x))
  {
    case t_POL : *t = typ_POL; return NULL;
    case t_QUAD: *t = typ_Q  ; return NULL;
    case t_VEC:
      switch(lg(x))
      {
        case 3:
          if (typ(gel(x,2)) != t_POLMOD) break;
          return get_nf(gel(x,1),t);
        case 5: *t = typ_QUA; return NULL;
        case 6:
          if (typ(gel(x,1)) == t_VEC && typ(gel(x,3)) == t_MAT)
          { *t = typ_BID; return NULL; }
          if (typ(gel(x,2)) == t_COL && typ(gel(x,3)) == t_INT)
          { *t = typ_PRID; return NULL; }
          break;
        case 7: *t = typ_BNR;
          x = bnr_get_bnf(x); if (typ(x)!=t_VEC || lg(x)!=11) break;
          x = bnf_get_nf(x);  if (typ(x)!=t_VEC || lg(x)!=10) break;
          return x;
        case 9:
          x = gel(x,2);
          if (typ(x) == t_VEC && lg(x) == 4) *t = typ_GAL;
          return NULL;
        case 10: *t = typ_NF; return x;
        case 11: *t = typ_BNF;
          x = bnf_get_nf(x); if (typ(x)!=t_VEC || lg(x)!=10) break;
          return x;
        case 13: *t = typ_RNF; return NULL;
        case 17: *t = typ_ELL; return NULL;
      }
      break;
    case t_COL:
      if (get_prid(x)) { *t = typ_MODPR; return NULL; }
      break;
  }
  *t = typ_NULL; return NULL;
}

long
nftyp(GEN x)
{
  switch(typ(x))
  {
    case t_POL : return typ_POL;
    case t_QUAD: return typ_Q;
    case t_VEC:
      switch(lg(x))
      {
        case 13: return typ_RNF;
        case 10:
          if (typ(gel(x,1))!=t_POL) break;
          return typ_NF;
        case 11:
          x = bnf_get_nf(x); if (typ(x)!=t_VEC || lg(x)!=10) break;
          return typ_BNF;
        case 7:
          x = bnr_get_bnf(x); if (typ(x)!=t_VEC || lg(x)!=11) break;
          x = bnf_get_nf(x);  if (typ(x)!=t_VEC || lg(x)!=10) break;
          return typ_BNR;
        case 6:
          if (typ(gel(x,1)) != t_VEC || typ(gel(x,3)) != t_MAT) break;
          return typ_BID;
        case 9:
          x = gel(x,2);
          if (typ(x) == t_VEC && lg(x) == 4) return typ_GAL;
        case 17: return typ_ELL;
      }
  }
  return typ_NULL;
}

/*************************************************************************/
/**                                                                     **/
/**                           GALOIS GROUP                              **/
/**                                                                     **/
/*************************************************************************/

/* exchange elements i and j in vector x */
static GEN
transroot(GEN x, int i, int j)
{ x = leafcopy(x); swap(gel(x,i), gel(x,j)); return x; }

GEN
tschirnhaus(GEN x)
{
  pari_sp av = avma, av2;
  long a, v = varn(x);
  GEN u, y = cgetg(5,t_POL);

  if (typ(x)!=t_POL) pari_err_TYPE("tschirnhaus",x);
  if (lg(x) < 4) pari_err_CONSTPOL("tschirnhaus");
  if (v) { u = leafcopy(x); setvarn(u,0); x=u; }
  y[1] = evalsigne(1)|evalvarn(0);
  do
  {
    a = random_bits(2); if (a==0) a  = 1; gel(y,4) = stoi(a);
    a = random_bits(3); if (a>=4) a -= 8; gel(y,3) = stoi(a);
    a = random_bits(3); if (a>=4) a -= 8; gel(y,2) = stoi(a);
    u = RgXQ_charpoly(y,x,v); av2 = avma;
  }
  while (degpol(RgX_gcd(u,RgX_deriv(u)))); /* while u not separable */
  if (DEBUGLEVEL>1)
    err_printf("Tschirnhaus transform. New pol: %Ps",u);
  avma=av2; return gerepileupto(av,u);
}

/* Assume pol in Z[X], monic of degree n. Find L in Z such that
 * POL = L^(-n) pol(L x) is monic in Z[X]. Return POL and set *ptk = L.
 * No GC. */
GEN
ZX_Z_normalize(GEN pol, GEN *ptk)
{
  long i,j, sk, n = degpol(pol); /* > 0 */
  GEN k, fa, P, E, a, POL;

  a = pol + 2; k = gel(a,n-1); /* a[i] = coeff of degree i */
  for (i = n-2; i >= 0; i--)
  {
    k = gcdii(k, gel(a,i));
    if (is_pm1(k)) { if (ptk) *ptk = gen_1; return pol; }
  }
  sk = signe(k);
  if (!sk) { if (ptk) *ptk = gen_1; return pol; /* monomial! */ }
  fa = absi_factor_limit(k, 0); k = gen_1;
  P = gel(fa,1);
  E = gel(fa,2);
  POL = leafcopy(pol); a = POL+2;
  for (i = lg(P)-1; i > 0; i--)
  {
    GEN p = gel(P,i), pv, pvj;
    long vmin = itos(gel(E,i));
    /* find v_p(k) = min floor( v_p(a[i]) / (n-i)) */
    for (j=n-1; j>=0; j--)
    {
      long v;
      if (!signe(gel(a,j))) continue;
      v = Z_pval(gel(a,j), p) / (n - j);
      if (v < vmin) vmin = v;
    }
    if (!vmin) continue;
    pvj = pv = powiu(p,vmin); k = mulii(k, pv);
    /* a[j] /= p^(v*(n-j)) */
    for (j=n-1; j>=0; j--)
    {
      if (j < n-1) pvj = mulii(pvj, pv);
      gel(a,j) = diviiexact(gel(a,j), pvj);
    }
  }
  if (ptk) *ptk = k; return POL;
}

/* Assume pol != 0 in Z[X]. Find C in Q, L in Z such that POL = C pol(x/L) monic
 * in Z[X]. Return POL and set *pL = L. Wasteful (but correct) if pol is not
 * primitive: better if caller used Q_primpart already. No GC. */
GEN
ZX_primitive_to_monic(GEN pol, GEN *pL)
{
  long i,j, n = degpol(pol);
  GEN lc = leading_term(pol), L, fa, P, E, a, POL;

  if (is_pm1(lc))
  {
    if (pL) *pL = gen_1;
    return signe(lc) < 0? ZX_neg(pol): pol;
  }
  if (signe(lc) < 0)
    POL = ZX_neg(pol);
  else
    POL = leafcopy(pol);
  a = POL+2; lc = gel(a,n);
  fa = Z_factor_limit(lc,0); L = gen_1;
  P = gel(fa,1);
  E = gel(fa,2);
  for (i = lg(P)-1; i > 0; i--)
  {
    GEN p = gel(P,i), pk, pku;
    long v, j0, e = itos(gel(E,i)), k = e/n, d = k*n - e;

    if (d < 0) { k++; d += n; }
    /* k = ceil(e[i] / n); find d, k such that  p^d pol(x / p^k) monic */
    for (j=n-1; j>0; j--)
    {
      if (!signe(gel(a,j))) continue;
      v = Z_pval(gel(a,j), p);
      while (v + d < k * j) { k++; d += n; }
    }
    pk = powiu(p,k); j0 = d/k;
    L = mulii(L, pk);

    pku = powiu(p,d - k*j0);
    /* a[j] *= p^(d - kj) */
    for (j=j0; j>=0; j--)
    {
      if (j < j0) pku = mulii(pku, pk);
      gel(a,j) = mulii(gel(a,j), pku);
    }
    j0++;
    pku = powiu(p,k*j0 - d);
    /* a[j] /= p^(kj - d) */
    for (j=j0; j<=n; j++)
    {
      if (j > j0) pku = mulii(pku, pk);
      gel(a,j) = diviiexact(gel(a,j), pku);
    }
  }
  if (pL) *pL = L;
  return POL;
}
/* Assume pol != 0 in Z[X]. Find C,L in Q such that POL = C pol(x/L)
 * monic in Z[X]. Return POL and set *pL = L.
 * Wasteful (but correct) if pol is not primitive: better if caller used
 * Q_primpart already. No GC. */
GEN
ZX_Q_normalize(GEN pol, GEN *pL)
{
  GEN lc, POL = ZX_primitive_to_monic(pol, &lc);
  POL = ZX_Z_normalize(POL, pL);
  if (pL) *pL = gdiv(lc, *pL);
  return POL;
}
/* pol != 0 in Z[x], returns a monic polynomial POL in Z[x] generating the
 * same field: there exist C in Q, L in Z such that POL(x) = C pol(x/L).
 * Set *L = NULL if L = 1, and to L otherwise. No garbage collecting. */
GEN
ZX_to_monic(GEN pol, GEN *L)
{
  long n = lg(pol)-1;
  GEN lc = gel(pol,n);
  if (is_pm1(lc)) { *L = gen_1; return signe(lc) > 0? pol: ZX_neg(pol); }
  return ZX_primitive_to_monic(Q_primpart(pol), L);
}

/* x1*x2^2 + x2*x3^2 + x3*x4^2 + x4*x1^2 */
static GEN
F4(GEN x)
{
  return gadd(
    gmul(gel(x,1), gadd(gsqr(gel(x,2)), gmul(gel(x,4),gel(x,1)))),
    gmul(gel(x,3), gadd(gsqr(gel(x,4)), gmul(gel(x,2),gel(x,3)))));
}

static GEN
roots_to_ZX(GEN z, long *e)
{
  GEN a = roots_to_pol(z,0);
  GEN b = grndtoi(real_i(a),e);
  long e1 = gexpo(imag_i(a));
  if (e1 > *e) *e = e1;
  return b;
}

static GEN
polgaloisnames(long a, long b)
{
  const char * const t[]={"S1", "S2", "A3", "S3",
       "C(4) = 4", "E(4) = 2[x]2", "D(4)", "A4", "S4",
       "C(5) = 5", "D(5) = 5:2", "F(5) = 5:4", "A5", "S5",
       "C(6) = 6 = 3[x]2", "D_6(6) = [3]2", "D(6) = S(3)[x]2",
             "A_4(6) = [2^2]3", "F_18(6) = [3^2]2 = 3 wr 2",
             "2A_4(6) = [2^3]3 = 2 wr 3", "S_4(6d) = [2^2]S(3)",
             "S_4(6c) = 1/2[2^3]S(3)", "F_18(6):2 = [1/2.S(3)^2]2",
             "F_36(6) = 1/2[S(3)^2]2", "2S_4(6) = [2^3]S(3) = 2 wr S(3)",
             "L(6) = PSL(2,5) = A_5(6)", "F_36(6):2 = [S(3)^2]2 = S(3) wr 2",
             "L(6):2 = PGL(2,5) = S_5(6)", "A6", "S6",
       "C(7) = 7", "D(7) = 7:2", "F_21(7) = 7:3", "F_42(7) = 7:6",
             "L(7) = L(3,2)", "A7", "S7"};

   const long idx[]={0,1,2,4,9,14,30};
   return strtoGENstr(t[idx[a-1]+b-1]);
}

static GEN
galois_res(long d, long n, long s, long k)
{
  long kk = k;
  GEN z = cgetg(5,t_VEC);
  if (!new_galois_format)
  {
    switch (d) {
      case 6:
        kk = (k == 6 || k == 2)? 2: 1;
        break;
      default:
        kk = 1;
    }
  }
  gel(z,1) = stoi(n);
  gel(z,2) = stoi(s);
  gel(z,3) = stoi(kk);
  gel(z,4) = polgaloisnames(d,k);
  return z;
}

GEN
polgalois(GEN x, long prec)
{
  pari_sp av = avma, av1;
  long i,j,k,n,f,l,l2,e,e1,pr,ind;
  GEN x1,p1,p2,p3,p4,p5,w,z,ee;
  const int ind5[20]={2,5,3,4, 1,3,4,5, 1,5,2,4, 1,2,3,5, 1,4,2,3};
  const int ind6[60]={3,5,4,6, 2,6,4,5, 2,3,5,6, 2,4,3,6, 2,5,3,4,
                      1,4,5,6, 1,5,3,6, 1,6,3,4, 1,3,4,5, 1,6,2,5,
                      1,2,4,6, 1,5,2,4, 1,3,2,6, 1,2,3,5, 1,4,2,3};
  if (typ(x)!=t_POL) pari_err_TYPE("galois",x);
  n=degpol(x);
  if (n>11) pari_err_IMPL("galois of degree higher than 11");
  x = Q_primpart(x);
  RgX_check_ZX(x, "galois");
  if (!ZX_is_irred(x)) pari_err_IRREDPOL("galois",x);

  if (n<4)
  {
    if (n == 1) { avma = av; return galois_res(n,1, 1,1); }
    if (n == 2) { avma = av; return galois_res(n,2,-1,1); }
    /* n = 3 */
    f = Z_issquare(ZX_disc(x));
    avma = av;
    return f? galois_res(n,3,1,1):
              galois_res(n,6,-1,2);
  }
  x1 = x = ZX_Q_normalize(x,NULL); av1=avma;
  if (n > 7) return galoisbig(x, prec);
  for(;;)
  {
    double fb = fujiwara_bound(x);
    switch(n)
    {
      case 4: z = cgetg(7,t_VEC);
        prec = nbits2prec((long)(fb*18.) + 64);
        for(;;)
        {
          p1=QX_complex_roots(x,prec);
          gel(z,1) = F4(p1);
          gel(z,2) = F4(transroot(p1,1,2));
          gel(z,3) = F4(transroot(p1,1,3));
          gel(z,4) = F4(transroot(p1,1,4));
          gel(z,5) = F4(transroot(p1,2,3));
          gel(z,6) = F4(transroot(p1,3,4));
          p5 = roots_to_ZX(z, &e); if (e <= -10) break;
          prec = precdbl(prec);
        }
        if (!ZX_is_squarefree(p5)) goto tchi;
        p2 = gel(ZX_factor(p5),1);
        switch(lg(p2)-1)
        {
          case 1: f = Z_issquare(ZX_disc(x)); avma = av;
            return f? galois_res(n,12,1,4): galois_res(n,24,-1,5);

          case 2: avma = av; return galois_res(n,8,-1,3);

          case 3: avma = av;
            return (degpol(gel(p2,1))==2)? galois_res(n,4,1,2)
                                         : galois_res(n,4,-1,1);

          default: pari_err_BUG("galois (bug1)");
        }

      case 5: z = cgetg(7,t_VEC);
        ee= cgetg(7,t_VECSMALL);
        w = cgetg(7,t_VECSMALL);
        prec = nbits2prec((long)(fb*21.) + 64);
        for(;;)
        {
          for(;;)
          {
            p1=QX_complex_roots(x,prec);
            for (l=1; l<=6; l++)
            {
              p2=(l==1)?p1: ((l<6)?transroot(p1,1,l): transroot(p1,2,5));
              p3=gen_0;
              for (k=0,i=1; i<=5; i++,k+=4)
              {
                p5 = gadd(gmul(gel(p2,ind5[k]),gel(p2,ind5[k+1])),
                          gmul(gel(p2,ind5[k+2]),gel(p2,ind5[k+3])));
                p3 = gadd(p3, gmul(gsqr(gel(p2,i)),p5));
              }
              gel(w,l) = grndtoi(real_i(p3),&e);
              e1 = gexpo(imag_i(p3)); if (e1>e) e=e1;
              ee[l]=e; gel(z,l) = p3;
            }
            p5 = roots_to_ZX(z, &e); if (e <= -10) break;
            prec = precdbl(prec);
          }
          if (!ZX_is_squarefree(p5)) goto tchi;
          p3=gel(ZX_factor(p5),1);
          f=Z_issquare(ZX_disc(x));
          if (lg(p3)-1==1)
          {
            avma = av;
            return f? galois_res(n,60,1,4): galois_res(n,120,-1,5);
          }
          if (!f) { avma = av; return galois_res(n,20,-1,3); }

          pr = - (prec2nbits(prec) >> 1);
          for (l=1; l<=6; l++)
            if (ee[l] <= pr && gequal0(poleval(p5,gel(w,l)))) break;
          if (l>6) pari_err_BUG("galois (bug4)");
          p2=(l==6)? transroot(p1,2,5):transroot(p1,1,l);
          p3=gen_0;
          for (i=1; i<=5; i++)
          {
            j = (i == 5)? 1: i+1;
            p3 = gadd(p3,gmul(gmul(gel(p2,i),gel(p2,j)),
                              gsub(gel(p2,j),gel(p2,i))));
          }
          p5=gsqr(p3); p4=grndtoi(real_i(p5),&e);
          e1 = gexpo(imag_i(p5)); if (e1>e) e=e1;
          if (e <= -10)
          {
            if (gequal0(p4)) goto tchi;
            f = Z_issquare(p4); avma = av;
            return f? galois_res(n,5,1,1): galois_res(n,10,1,2);
          }
          prec = precdbl(prec);
        }

      case 6: z = cgetg(7, t_VEC);
        prec = nbits2prec((long) (fb * 42) + 64);
        for(;;)
        {
          for(;;)
          {
            p1=QX_complex_roots(x,prec);
            for (l=1; l<=6; l++)
            {
              p2=(l==1)?p1:transroot(p1,1,l);
              p3=gen_0; k=0;
              for (i=1; i<=5; i++) for (j=i+1; j<=6; j++)
              {
                p5=gadd(gmul(gel(p2,ind6[k]),gel(p2,ind6[k+1])),
                        gmul(gel(p2,ind6[k+2]),gel(p2,ind6[k+3])));
                p3=gadd(p3,gmul(gsqr(gmul(gel(p2,i),gel(p2,j))),p5));
                k += 4;
              }
              gel(z,l) = p3;
            }
            p5 = roots_to_ZX(z, &e); if (e <= -10) break;
            prec = precdbl(prec);
          }
          if (!ZX_is_squarefree(p5)) goto tchi;
          p2=gel(ZX_factor(p5),1);
          switch(lg(p2)-1)
          {
            case 1:
              z = cgetg(11,t_VEC); ind=0;
              p3=gadd(gmul(gmul(gel(p1,1),gel(p1,2)),gel(p1,3)),
                      gmul(gmul(gel(p1,4),gel(p1,5)),gel(p1,6)));
              gel(z,++ind) = p3;
              for (i=1; i<=3; i++)
                for (j=4; j<=6; j++)
                {
                  p2=transroot(p1,i,j);
                  p3=gadd(gmul(gmul(gel(p2,1),gel(p2,2)),gel(p2,3)),
                          gmul(gmul(gel(p2,4),gel(p2,5)),gel(p2,6)));
                  gel(z,++ind) = p3;
                }
              p5 = roots_to_ZX(z, &e);
              if (e <= -10)
              {
                if (!ZX_is_squarefree(p5)) goto tchi;
                p2 = gel(ZX_factor(p5),1);
                f = Z_issquare(ZX_disc(x));
                avma = av;
                if (lg(p2)-1==1)
                  return f? galois_res(n,360,1,15): galois_res(n,720,-1,16);
                else
                  return f? galois_res(n,36,1,10): galois_res(n,72,-1,13);
              }
              prec = precdbl(prec); break;

            case 2: l2=degpol(gel(p2,1)); if (l2>3) l2=6-l2;
              switch(l2)
              {
                case 1: f = Z_issquare(ZX_disc(x));
                  avma = av;
                  return f? galois_res(n,60,1,12): galois_res(n,120,-1,14);
                case 2: f = Z_issquare(ZX_disc(x));
                  if (f) { avma = av; return galois_res(n,24,1,7); }
                  p3 = (degpol(gel(p2,1))==2)? gel(p2,2): gel(p2,1);
                  f = Z_issquare(ZX_disc(p3));
                  avma = av;
                  return f? galois_res(n,24,-1,6): galois_res(n,48,-1,11);
                case 3: f = Z_issquare(ZX_disc(gel(p2,1)))
                         || Z_issquare(ZX_disc(gel(p2,2)));
                  avma = av;
                  return f? galois_res(n,18,-1,5): galois_res(n,36,-1,9);
              }
            case 3:
              for (l2=1; l2<=3; l2++)
                if (degpol(gel(p2,l2)) >= 3) p3 = gel(p2,l2);
              if (degpol(p3) == 3)
              {
                f = Z_issquare(ZX_disc(p3)); avma = av;
                return f? galois_res(n,6,-1,1): galois_res(n,12,-1,3);
              }
              else
              {
                f = Z_issquare(ZX_disc(x)); avma = av;
                return f? galois_res(n,12,1,4): galois_res(n,24,-1,8);
              }
            case 4: avma = av; return galois_res(n,6,-1,2);
            default: pari_err_BUG("galois (bug3)");
          }
        }

      case 7: z = cgetg(36,t_VEC);
        prec = nbits2prec((long)(fb*7.) + 64);
        for(;;)
        {
          ind = 0; p1=QX_complex_roots(x,prec);
          for (i=1; i<=5; i++)
            for (j=i+1; j<=6; j++)
            {
              GEN t = gadd(gel(p1,i),gel(p1,j));
              for (k=j+1; k<=7; k++) gel(z,++ind) = gadd(t, gel(p1,k));
            }
          p5 = roots_to_ZX(z, &e); if (e <= -10) break;
          prec = precdbl(prec);
        }
        if (!ZX_is_squarefree(p5)) goto tchi;
        p2=gel(ZX_factor(p5),1);
        switch(lg(p2)-1)
        {
          case 1: f = Z_issquare(ZX_disc(x)); avma = av;
            return f? galois_res(n,2520,1,6): galois_res(n,5040,-1,7);
          case 2: f = degpol(gel(p2,1)); avma = av;
            return (f==7 || f==28)? galois_res(n,168,1,5): galois_res(n,42,-1,4);
          case 3: avma = av; return galois_res(n,21,1,3);
          case 4: avma = av; return galois_res(n,14,-1,2);
          case 5: avma = av; return galois_res(n,7,1,1);
          default: pari_err_BUG("galois (bug2)");
        }
    }
    tchi: avma = av1; x = tschirnhaus(x1);
  }
}

#undef _res

/* Evaluate pol in s using nfelt arithmetic and Horner rule */
GEN
nfpoleval(GEN nf, GEN pol, GEN s)
{
  pari_sp av=avma;
  long i=lg(pol)-1;
  GEN res;
  if (i==1) return gen_0;
  res = nf_to_scalar_or_basis(nf, gel(pol,i));
  for (i-- ; i>=2; i--)
    res = nfadd(nf, nfmul(nf, s, res), gel(pol,i));
  return gerepileupto(av, res);
}

static GEN
QX_table_nfpoleval(GEN nf, GEN pol, GEN m)
{
  pari_sp av = avma;
  long i = lg(pol)-1;
  GEN res, den;
  if (i==1) return gen_0;
  pol = Q_remove_denom(pol, &den);
  res = scalarcol_shallow(gel(pol,i), nf_get_degree(nf));
  for (i-- ; i>=2; i--)
    res = ZC_Z_add(ZM_ZC_mul(m, res), gel(pol,i));
  if (den) res = RgC_Rg_div(res, den);
  return gerepileupto(av, res);
}

GEN
FpX_FpC_nfpoleval(GEN nf, GEN pol, GEN a, GEN p)
{
  pari_sp av=avma;
  long i=lg(pol)-1, n=nf_get_degree(nf);
  GEN res, Ma;
  if (i==1) return zerocol(n);
  Ma = FpM_red(zk_multable(nf, a), p);
  res = scalarcol(gel(pol,i),n);
  for (i-- ; i>=2; i--)
  {
    res = FpM_FpC_mul(Ma, res, p);
    gel(res,1) = Fp_add(gel(res,1), gel(pol,i), p);
  }
  return gerepileupto(av, res);
}

/* compute s(x), not stack clean */
static GEN
table_galoisapply(GEN nf, GEN m, GEN x)
{
  x = nf_to_scalar_or_alg(nf, x);
  if (typ(x) != t_POL) return scalarcol(x, nf_get_degree(nf));
  return QX_table_nfpoleval(nf, x, m);
}

/* compute s(x), not stack clean */
static GEN
ZC_galoisapply(GEN nf, GEN s, GEN x)
{
  x = nf_to_scalar_or_alg(nf, x);
  if (typ(x) != t_POL) return scalarcol(x, nf_get_degree(nf));
  return QX_table_nfpoleval(nf, x, zk_multable(nf, s));
}

static GEN
QX_galoisapplymod(GEN nf, GEN pol, GEN S, GEN p)
{
  GEN den, P = Q_remove_denom(pol,&den);
  GEN pe, pe1, denpe, R;
  if (den)
  {
    ulong e = Z_pval(den, p);
    pe = powiu(p, e); pe1 = mulii(pe, p);
    denpe = Fp_inv(diviiexact(den, pe), pe1);
  } else {
    pe = gen_1; pe1 = p; denpe = gen_1;
  }
  R = FpX_FpC_nfpoleval(nf, FpX_red(P, pe1), FpC_red(S, pe1), pe1);
  return gdivexact(FpC_Fp_mul(R, denpe, pe1), pe);
}

static GEN
pr_galoisapply(GEN nf, GEN pr, GEN aut)
{
  GEN p, t, u;
  if (typ(pr_get_tau(pr)) == t_INT) return pr; /* inert */
  p = pr_get_p(pr);
  u = QX_galoisapplymod(nf, coltoliftalg(nf, pr_get_gen(pr)), aut, p);
  t = FpM_deplin(zk_multable(nf, u), p);
  t = zk_scalar_or_multable(nf, t);
  return mkvec5(p, u, gel(pr,3), gel(pr,4), t);
}

static GEN
vecgaloisapply(GEN nf, GEN aut, GEN v)
{
  long i, l;
  GEN V = cgetg_copy(v, &l);
  for (i = 1; i < l; i++) gel(V,i) = galoisapply(nf, aut, gel(v,i));
  return V;
}

/* x: famat or standard algebraic number, aut automorphism in ZC form
 * simplified from general galoisapply */
static GEN
elt_galoisapply(GEN nf, GEN aut, GEN x)
{
  pari_sp av = avma;
  switch(typ(x))
  {
    case t_INT:  return icopy(x);
    case t_FRAC: return gcopy(x);
    case t_POLMOD: x = gel(x,2); /* fall through */
    case t_POL: {
      GEN y = basistoalg(nf, ZC_galoisapply(nf, aut, x));
      return gerepileupto(av,y);
    }
    case t_COL:
      return gerepileupto(av, ZC_galoisapply(nf, aut, x));
    case t_MAT:
      switch(lg(x)) {
        case 1: return cgetg(1, t_MAT);
        case 3: retmkmat2(vecgaloisapply(nf,aut,gel(x,1)), ZC_copy(gel(x,2)));
      }
  }
  pari_err_TYPE("galoisapply",x);
  return NULL; /* not reached */
}

GEN
galoisapply(GEN nf, GEN aut, GEN x)
{
  pari_sp av = avma;
  long lx, j;
  GEN y;

  nf = checknf(nf);
  switch(typ(x))
  {
    case t_INT:  return icopy(x);
    case t_FRAC: return gcopy(x);

    case t_POLMOD: x = gel(x,2); /* fall through */
    case t_POL:
      aut = algtobasis(nf, aut);
      y = basistoalg(nf, ZC_galoisapply(nf, aut, x));
      return gerepileupto(av,y);

    case t_VEC:
      aut = algtobasis(nf, aut);
      switch(lg(x))
      {
        case 6: return gerepilecopy(av, pr_galoisapply(nf, x, aut));
        case 3: y = cgetg(3,t_VEC);
          gel(y,1) = galoisapply(nf, aut, gel(x,1));
          gel(y,2) = elt_galoisapply(nf, aut, gel(x,2));
          return gerepileupto(av, y);
      }
      break;

    case t_COL:
      aut = algtobasis(nf, aut);
      return gerepileupto(av, ZC_galoisapply(nf, aut, x));

    case t_MAT: /* ideal */
      lx = lg(x); if (lx==1) return cgetg(1,t_MAT);
      if (nbrows(x) != nf_get_degree(nf)) break;
      aut = zk_multable(nf, algtobasis(nf, aut));
      y = cgetg(lx,t_MAT);
      for (j=1; j<lx; j++) gel(y,j) = table_galoisapply(nf, aut, gel(x,j));
      return gerepileupto(av, idealhnf_shallow(nf,y));
  }
  pari_err_TYPE("galoisapply",x);
  return NULL; /* not reached */
}

GEN
nfgaloismatrix(GEN nf, GEN s)
{
  GEN zk, M, m;
  long k, l;
  nf = checknf(nf);
  zk = nf_get_zk(nf);
  if (typ(s) != t_COL) s = algtobasis(nf, s); /* left on stack for efficiency */
  m = zk_multable(nf, s);
  l = lg(s); M = cgetg(l, t_MAT);
  gel(M, 1) = col_ei(l-1, 1); /* s(1) = 1 */
  for (k = 2; k < l; k++)
    gel(M, k) = QX_table_nfpoleval(nf, gel(zk, k), m);
  return M;
}

static GEN
idealquasifrob(GEN nf, GEN gal, GEN pr, GEN subg, GEN *S)
{
  pari_sp av = avma;
  long i, n = nf_get_degree(nf), f = pr_get_f(pr);
  GEN grp = gal_get_group(gal), pi = pr_get_gen(pr);
  for (i=1; i<=n; i++)
  {
    GEN g = gel(grp,i);
    if ((!subg && perm_order(g)==f)
      || (subg && perm_relorder(g, subg)==f))
    {
      *S = poltobasis(nf, galoispermtopol(gal, g));
      if (ZC_prdvd(nf, ZC_galoisapply(nf, *S, pi), pr)) return g;
      avma = av;
    }
  }
  pari_err_BUG("idealquasifrob [Frobenius not found]");
  return NULL; /*NOT REACHED*/
}

static void
gal_check_pol(const char *f, GEN x, GEN y)
{ if (!RgX_equal_var(x,y)) pari_err_MODULUS(f,x,y); }

GEN
idealfrobenius(GEN nf, GEN gal, GEN pr)
{
  pari_sp av = avma;
  GEN S=NULL, g=NULL; /*-Wall*/
  GEN T, p, a, b, modpr;
  long f, n, s;
  nf = checknf(nf);
  checkgal(gal);
  checkprid(pr);
  gal_check_pol("idealfrobenius",nf_get_pol(nf),gal_get_pol(gal));
  if (pr_get_e(pr)>1) pari_err_DOMAIN("idealfrobenius","pr.e", ">", gen_1,pr);
  f = pr_get_f(pr); n = nf_get_degree(nf);
  if (f==1) { avma = av; return identity_perm(n); }
  modpr = zk_to_Fq_init(nf,&pr,&T,&p);
  g = idealquasifrob(nf, gal, pr, NULL, &S);
  a = pol_x(nf_get_varn(nf));
  b = nf_to_Fq(nf, QX_galoisapplymod(nf, modpr_genFq(modpr), S, p), modpr);
  for (s=0; !ZX_equal(a, b); s++)
    a = Fq_pow(a, p, T, p);
  g = perm_pow(g, Fl_inv(s, f));
  return gerepileupto(av, g);
}

static GEN
idealinertiagroup(GEN nf, GEN gal, GEN pr)
{
  long i, n = nf_get_degree(nf);
  GEN p, T, modpr = zk_to_Fq_init(nf,&pr,&T,&p);
  GEN b = modpr_genFq(modpr);
  long e = pr_get_e(pr), coprime = cgcd(e, pr_get_f(pr)) == 1;
  GEN grp = gal_get_group(gal), pi = pr_get_gen(pr);
  pari_sp ltop = avma;
  for (i=1; i<=n; i++)
  {
    GEN iso = gel(grp,i);
    if (perm_order(iso) == e)
    {
      GEN S = poltobasis(nf, galoispermtopol(gal, iso));
      if (ZC_prdvd(nf, ZC_galoisapply(nf, S, pi), pr)
          && (coprime || gequalX(nf_to_Fq(nf, galoisapply(nf,S,b), modpr))))
          return iso;
      avma = ltop;
    }
  }
  pari_err_BUG("idealinertiagroup [no isotropic element]");
  return NULL;
}

static GEN
idealramgroupstame(GEN nf, GEN gal, GEN pr)
{
  pari_sp av = avma;
  GEN iso, frob, giso, isog, S, res;
  long e = pr_get_e(pr), f = pr_get_f(pr);
  if (e == 1)
  {
    if (f==1)
      return cgetg(1,t_VEC);
    frob = idealquasifrob(nf, gal, pr, NULL, &S);
    avma = av;
    res = cgetg(2, t_VEC);
    gel(res, 1) = cyclicgroup(frob, f);
    return res;
  }
  res = cgetg(3, t_VEC);
  av = avma;
  iso = idealinertiagroup(nf, gal, pr);
  avma = av;
  giso = cyclicgroup(iso, e);
  gel(res, 2) = giso;
  if (f==1)
  {
    gel(res, 1) = giso;
    return res;
  }
  av = avma;
  isog = group_set(giso, nf_get_degree(nf));
  frob = idealquasifrob(nf, gal, pr, isog, &S);
  avma = av;
  gel(res, 1) = dicyclicgroup(iso,frob,e,f);
  return res;
}

static GEN
idealramgroupindex(GEN nf, GEN gal, GEN pr)
{
  pari_sp av = avma;
  GEN p, T, g, idx, modpr;
  long i, e, f, n;
  ulong nt,rorder;
  GEN grp = vecvecsmall_sort(gal_get_group(gal));
  e = pr_get_e(pr); f = pr_get_f(pr); n = nf_get_degree(nf);
  modpr = zk_to_Fq_init(nf,&pr,&T,&p);
  (void) u_pvalrem(n,p,&nt);
  rorder = e*f*(n/nt);
  idx = const_vecsmall(n,-1);
  g = modpr_genFq(modpr);
  for (i=2; i<=n; i++)
  {
    GEN iso;
    long o;
    if (idx[i]>=0) continue;
    iso = gel(grp,i); o = perm_order(iso);
    if (rorder%o == 0)
    {
      GEN piso = iso;
      GEN S = poltobasis(nf, galoispermtopol(gal, iso));
      GEN pi = pr_get_gen(pr);
      GEN spi = ZC_galoisapply(nf, S, pi);
      long j;
      idx[i] = idealval(nf, gsub(spi,pi), pr);
      if (idx[i] >=1)
      {
        if (f>1)
        {
          GEN b = nf_to_Fq(nf, QX_galoisapplymod(nf, g, S, p), modpr);
          if (!gequalX(b)) idx[i] = 0;
        }
      }
      else idx[i] = -1;
      for(j=2;j<o;j++)
      {
        piso = perm_mul(piso,iso);
        if(cgcd(j,o)==1) idx[piso[1]] = idx[i];
      }
    }
  }
  return gerepileuptoleaf(av, idx);
}

GEN
idealramgroups(GEN nf, GEN gal, GEN pr)
{
  pari_sp av = avma;
  GEN tbl, idx, res, set, sub;
  long i, j, e, n, maxm, p;
  ulong et;
  nf = checknf(nf);
  checkgal(gal);
  checkprid(pr);
  gal_check_pol("idealramgroups",nf_get_pol(nf),gal_get_pol(gal));
  e = pr_get_e(pr); n = nf_get_degree(nf);
  p = itos(pr_get_p(pr));
  if (e%p) return idealramgroupstame(nf, gal, pr);
  (void) u_lvalrem(e,p,&et);
  idx = idealramgroupindex(nf, gal, pr);
  sub = group_subgroups(galois_group(gal));
  tbl = subgroups_tableset(sub, n);
  maxm = vecsmall_max(idx)+1;
  res = cgetg(maxm+1,t_VEC);
  set = zero_F2v(n); F2v_set(set,1);
  for(i=maxm; i>0; i--)
  {
    for(j=1;j<=n;j++)
      if (idx[j]==i-1)
        F2v_set(set,j);
    gel(res,i) = gel(sub, tableset_find_index(tbl, set));
  }
  return gerepilecopy(av, res);
}

/* x = relative polynomial nf = absolute nf, bnf = absolute bnf */
GEN
get_bnfpol(GEN x, GEN *bnf, GEN *nf)
{
  *bnf = checkbnf_i(x);
  *nf  = checknf_i(x);
  if (*nf) x = nf_get_pol(*nf);
  if (typ(x) != t_POL) pari_err_TYPE("get_bnfpol",x);
  return x;
}

GEN
get_nfpol(GEN x, GEN *nf)
{
  if (typ(x) == t_POL) { *nf = NULL; return x; }
  *nf = checknf(x); return nf_get_pol(*nf);
}

/* is isomorphism / inclusion (a \subset b) compatible with what we know about
 * basic invariants ? (degree, signature, discriminant) */
static int
tests_OK(GEN a, GEN nfa, GEN b, GEN nfb, long fliso)
{
  GEN da, db, fa, P, E, U;
  long i, nP, m = degpol(a), n = degpol(b), q = m / n; /* relative degree */

  if (m <= 0) pari_err_IRREDPOL("nfisincl",a);
  if (n <= 0) pari_err_IRREDPOL("nfisincl",b);
  if (fliso) { if (n != m) return 0; } else { if (n % m) return 0; }
  if (m == 1) return 1;

  if (nfa && nfb) /* both nf structures available */
  {
    long r1a = nf_get_r1(nfa), r1b = nf_get_r1(nfb) ;
    if (fliso)
      return (r1a == r1b && equalii(nf_get_disc(nfa), nf_get_disc(nfb)));
    else
      return (r1b <= r1a * q &&
              dvdii(nf_get_disc(nfb), powiu(nf_get_disc(nfa), q)));
  }
  da = nfa? nf_get_disc(nfa): ZX_disc(a);
  if (!signe(da)) pari_err_IRREDPOL("nfisincl",a);
  db = nfb? nf_get_disc(nfb): ZX_disc(b);
  if (!signe(db)) pari_err_IRREDPOL("nfisincl",a);
  if (fliso) return issquare(gdiv(da,db));

  if (odd(q) && signe(da) != signe(db)) return 0;
  fa = absi_factor_limit(da, 0);
  P = gel(fa,1);
  E = gel(fa,2); nP = lg(P) - 1;
  for (i=1; i<nP; i++)
    if (mod2(gel(E,i)) && !dvdii(db, powiu(gel(P,i),q))) return 0;
  U = gel(P,nP);
  if (mod2(gel(E,i)) && expi(U) < 150)
  { /* "unfactored" cofactor is small, finish */
    if (cmpiu(U, maxprime()) > 0)
    {
      fa = Z_factor(U);
      P = gel(fa,1);
      E = gel(fa,2);
    }
    else
    {
      P = mkvec(U);
      E = mkvec(gen_1);
    }
    nP = lg(P) - 1;
    for (i=1; i<=nP; i++)
      if (mod2(gel(E,i)) && !dvdii(db, powiu(gel(P,i),q))) return 0;
  }
  return 1;
}

/* if fliso test for isomorphism, for inclusion otherwise. */
static GEN
nfiso0(GEN a, GEN b, long fliso)
{
  pari_sp av = avma;
  long i, vb, lx;
  GEN nfa, nfb, y, la, lb;
  int newvar;

  a = get_nfpol(a, &nfa);
  b = get_nfpol(b, &nfb);
  if (!nfa) { a = Q_primpart(a); RgX_check_ZX(a, "nsiso0"); }
  if (!nfb) { b = Q_primpart(b); RgX_check_ZX(b, "nsiso0"); }
  if (fliso && nfa && !nfb) { swap(a,b); nfb = nfa; nfa = NULL; }
  if (!tests_OK(a, nfa, b, nfb, fliso)) { avma = av; return gen_0; }

  if (nfb) lb = gen_1; else b = ZX_Q_normalize(b,&lb);
  if (nfa) la = gen_1; else a = ZX_Q_normalize(a,&la);
  vb = varn(b); newvar = (varncmp(vb,varn(a)) <= 0);
  if (newvar) { a = leafcopy(a); setvarn(a, fetch_var_higher()); }
  if (nfb)
    y = lift_intern(nfroots(nfb,a));
  else
  {
    y = gel(polfnf(a,b),1); lx = lg(y);
    for (i=1; i<lx; i++)
    {
      GEN t = gel(y,i);
      if (degpol(t) != 1) { setlg(y,i); break; }
      gel(y,i) = gneg_i(lift_intern(gel(t,2)));
    }
    settyp(y, t_VEC);
    gen_sort_inplace(y, (void*)&cmp_RgX, &cmp_nodata, NULL);
  }
  if (newvar) (void)delete_var();
  lx = lg(y); if (lx==1) { avma=av; return gen_0; }
  for (i=1; i<lx; i++)
  {
    GEN t = gel(y,i);
    if (typ(t) == t_POL) setvarn(t, vb); else t = scalarpol(t, vb);
    if (lb != gen_1) t = RgX_unscale(t, lb);
    if (la != gen_1) t = RgX_Rg_div(t, la);
    gel(y,i) = t;
  }
  return gerepilecopy(av,y);
}

GEN
nfisisom(GEN a, GEN b) { return nfiso0(a,b,1); }

GEN
nfisincl(GEN a, GEN b) { return nfiso0(a,b,0); }

/*************************************************************************/
/**                                                                     **/
/**                               INITALG                               **/
/**                                                                     **/
/*************************************************************************/

GEN
get_roots(GEN x, long r1, long prec)
{
  long i, ru;
  GEN z;
  if (typ(x) != t_POL)
  {
    z = leafcopy(x);
    ru = (lg(z)-1 + r1) >> 1;
  }
  else
  {
    long n = degpol(x);
    z = (r1 == n)? realroots(x, NULL, prec): QX_complex_roots(x,prec);
    ru = (n+r1)>>1;
  }
  for (i=r1+1; i<=ru; i++) gel(z,i) = gel(z, (i<<1)-r1);
  z[0]=evaltyp(t_VEC)|evallg(ru+1); return z;
}

GEN
nf_get_allroots(GEN nf)
{
  return embed_roots(nf_get_roots(nf), nf_get_r1(nf));
}

/* For internal use. compute trace(x mod pol), sym=polsym(pol,deg(pol)-1) */
GEN
quicktrace(GEN x, GEN sym)
{
  GEN p1 = gen_0;
  long i;

  if (typ(x) != t_POL) return gmul(x, gel(sym,1));
  if (signe(x))
  {
    sym--;
    for (i=lg(x)-1; i>1; i--)
      p1 = gadd(p1, gmul(gel(x,i),gel(sym,i)));
  }
  return p1;
}

static GEN
get_Tr(GEN mul, GEN x, GEN basden)
{
  GEN t, bas = gel(basden,1), den = gel(basden,2);
  long i, j, n = lg(bas)-1;
  GEN T = cgetg(n+1,t_MAT), TW = cgetg(n+1,t_COL), sym = polsym(x, n-1);

  gel(TW,1) = utoipos(n);
  for (i=2; i<=n; i++)
  {
    t = quicktrace(gel(bas,i), sym);
    if (den && den[i]) t = diviiexact(t,gel(den,i));
    gel(TW,i) = t; /* tr(w[i]) */
  }
  gel(T,1) = TW;
  for (i=2; i<=n; i++)
  {
    gel(T,i) = cgetg(n+1,t_COL); gcoeff(T,1,i) = gel(TW,i);
    for (j=2; j<=i; j++) /* Tr(W[i]W[j]) */
      gcoeff(T,i,j) = gcoeff(T,j,i) = ZV_dotproduct(gel(mul,j+(i-1)*n), TW);
  }
  return T;
}

/* return [bas[i]*denom(bas[i]), denom(bas[i])], denom 1 is given as NULL */
GEN
get_bas_den(GEN bas)
{
  GEN b,d,den, dbas = leafcopy(bas);
  long i, l = lg(bas);
  int power = 1;
  den = cgetg(l,t_VEC);
  for (i=1; i<l; i++)
  {
    b = Q_remove_denom(gel(bas,i), &d);
    gel(dbas,i) = b;
    gel(den,i) = d; if (d) power = 0;
  }
  if (power) den = NULL; /* power basis */
  return mkvec2(dbas, den);
}

/* Internal: nf partially filled. Require pol; fill zk, invzk, multable */
void
nf_set_multable(GEN nf, GEN bas, GEN basden)
{
  GEN T = nf_get_pol(nf), invbas, basM;
  long i,j, n = degpol(T);
  GEN w, den, mul = cgetg(n*n+1,t_MAT);

  if (typ(bas) == t_MAT)
  { basM = bas; bas = RgM_to_RgXV(basM, varn(T)); }
  else
    basM = RgV_to_RgM(bas, n);
  gel(nf,7) = bas;
  gel(nf,8) = invbas = QM_inv(basM, gen_1);
  gel(nf,9) = mul;

  if (!basden) basden = get_bas_den(nf_get_zk(nf)); /*integral basis*/
  w   = gel(basden,1);
  den = gel(basden,2);
  /* i = 1 split for efficiency, assume w[1] = 1 */
  for (j=1; j<=n; j++)
    gel(mul,j) = gel(mul,1+(j-1)*n) = col_ei(n, j);
  for (i=2; i<=n; i++)
    for (j=i; j<=n; j++)
    {
      pari_sp av = avma;
      GEN z = (i == j)? ZXQ_sqr(gel(w,i), T): ZXQ_mul(gel(w,i),gel(w,j), T);
      z = mulmat_pol(invbas, z); /* integral column */
      if (den)
      {
        GEN d = mul_denom(gel(den,i), gel(den,j));
        if (d) z = ZC_Z_divexact(z, d);
      }
      gel(mul,j+(i-1)*n) = gel(mul,i+(j-1)*n) = gerepileupto(av,z);
    }
}

/* as get_Tr, mul_table not precomputed */
static GEN
make_Tr(GEN x, GEN basden)
{
  long i,j, n = degpol(x);
  GEN c, t, d;
  GEN T   = cgetg(n+1,t_MAT);
  GEN sym = polsym(x, n-1);
  GEN w   = gel(basden,1); /* W[i] = w[i]/den[i] */
  GEN den = gel(basden,2);
  /* assume W[1] = 1, case i = 1 split for efficiency */
  c = cgetg(n+1,t_COL); gel(T,1) = c;
  gel(c, 1) = utoipos(n);
  for (j=2; j<=n; j++)
  {
    pari_sp av = avma;
    t = quicktrace(gel(w,j), sym);
    if (den)
    {
      d = gel(den,j);
      if (d) t = diviiexact(t, d);
    }
    gel(c,j) = gerepileuptoint(av, t);
  }
  for (i=2; i<=n; i++)
  {
    c = cgetg(n+1,t_COL); gel(T,i) = c;
    for (j=1; j<i ; j++) gel(c,j) = gcoeff(T,i,j);
    for (   ; j<=n; j++)
    {
      pari_sp av = avma;
      t = (i == j)? ZXQ_sqr(gel(w,i), x): ZXQ_mul(gel(w,i),gel(w,j), x);
      t = quicktrace(t, sym);
      if (den)
      {
        d = mul_denom(gel(den,i),gel(den,j));
        if (d) t = diviiexact(t, d);
      }
      gel(c,j) = gerepileuptoint(av, t); /* Tr (W[i]W[j]) */
    }
  }
  return T;
}

/* compute roots so that _absolute_ accuracy of M >= prec [also holds for G] */
static void
get_roots_for_M(nffp_t *F)
{
  long n, eBD, PREC;

  if (F->extraprec < 0)
  { /* not initialized yet */
    double er;
    n = degpol(F->x);
    eBD = 1 + gexpo(gel(F->basden,1));
    er  = F->ro? (1+gexpo(F->ro)): fujiwara_bound(F->x);
    if (er < 0) er = 0;
    F->extraprec = nbits2extraprec(n*er + eBD + log2(n));
  }

  PREC = F->prec + F->extraprec;
  /* make sure that default accuracy is the same on 32/64bit */
#ifndef LONG_IS_64BIT
  if (odd(PREC)) PREC += EXTRAPRECWORD;
#endif
  if (F->ro && gprecision(gel(F->ro,1)) >= PREC) return;
  F->ro = get_roots(F->x, F->r1, PREC);
}

/* [bas[i]/den[i]]= integer basis. roo = real part of the roots */
static void
make_M(nffp_t *F, int trunc)
{
  GEN bas = gel(F->basden,1), den = gel(F->basden,2), ro = F->ro;
  GEN m, d, M;
  long i, j, l = lg(ro), n = lg(bas);
  M = cgetg(n,t_MAT);
  gel(M,1) = const_col(l-1, gen_1); /* bas[1] = 1 */
  for (j=2; j<n; j++) gel(M,j) = cgetg(l,t_COL);
  for (i=1; i<l; i++)
  {
    GEN r = gel(ro,i), ri;
    ri = (gexpo(r) > 1)? ginv(r): NULL;
    for (j=2; j<n; j++) gcoeff(M,i,j) = RgX_cxeval(gel(bas,j), r, ri);
  }
  if (den)
    for (j=2; j<n; j++)
    {
      d = gel(den,j); if (!d) continue;
      m = gel(M,j);
      for (i=1; i<l; i++) gel(m,i) = gdiv(gel(m,i), d);
    }

  if (trunc && gprecision(M) > F->prec)
  {
    M     = gprec_w(M, F->prec);
    F->ro = gprec_w(ro,F->prec);
  }
  F->M = M;
}

/* return G real such that G~ * G = T_2 */
static void
make_G(nffp_t *F)
{
  GEN G, M = F->M;
  long i, j, k, r1 = F->r1, l = lg(M);

  G = cgetg(l, t_MAT);
  for (j=1; j<l; j++)
  {
    GEN g = cgetg(l, t_COL);
    GEN m = gel(M,j);
    gel(G,j) = g;
    for (k=i=1; i<=r1; i++) g[k++] = m[i];
    for (     ; k < l; i++)
    {
      GEN r = gel(m,i);
      if (typ(r) == t_COMPLEX)
      {
        gel(g,k++) = mpadd(gel(r,1), gel(r,2));
        gel(g,k++) = mpsub(gel(r,1), gel(r,2));
      }
      else
      {
        gel(g,k++) = r;
        gel(g,k++) = r;
      }
    }
  }
  F->G = G;
}

static void
make_M_G(nffp_t *F, int trunc)
{
  get_roots_for_M(F);
  make_M(F, trunc);
  make_G(F);
}

void
remake_GM(GEN nf, nffp_t *F, long prec)
{
  F->x  = nf_get_pol(nf);
  F->ro = NULL;
  F->r1 = nf_get_r1(nf);
  F->basden = get_bas_den(nf_get_zk(nf));
  F->extraprec = -1;
  F->prec = prec; make_M_G(F, 1);
}

static void
nffp_init(nffp_t *F, nfbasic_t *T, GEN ro, long prec)
{
  F->x  = T->x;
  F->ro = ro;
  F->r1 = T->r1;
  if (!T->basden) T->basden = get_bas_den(T->bas);
  F->basden = T->basden;
  F->extraprec = -1;
  F->prec = prec;
}

static void
get_nf_fp_compo(nfbasic_t *T, nffp_t *F, GEN ro, int trunc, long prec)
{
  nffp_init(F,T,ro,prec);
  make_M_G(F, trunc);
}

static GEN
get_sign(long r1, long n) { return mkvec2s(r1, (n-r1)>>1); }

GEN
nfbasic_to_nf(nfbasic_t *T, GEN ro, long prec)
{
  GEN nf = cgetg(10,t_VEC);
  GEN x = T->x, absdK, Tr, D, TI, A, dA, MDI, mat = cgetg(9,t_VEC);
  long n = degpol(T->x);
  nffp_t F;
  get_nf_fp_compo(T, &F, ro, 0, prec);

  gel(nf,1) = T->x;
  gel(nf,2) = get_sign(T->r1, n);
  gel(nf,3) = T->dK;
  gel(nf,4) = T->index;
  gel(nf,6) = F.ro;
  gel(nf,5) = mat;

  gel(mat,1) = F.M;
  gel(mat,2) = F.G;

  nf_set_multable(nf, T->bas, F.basden);

  Tr = get_Tr(gel(nf,9), x, F.basden);
  absdK = T->dK; if (signe(absdK) < 0) absdK = negi(absdK);
  TI = ZM_inv(Tr, absdK); /* dK T^-1 */
  A = Q_primitive_part(TI, &dA);
  gel(mat,6) = A; /* primitive part of codifferent, dA its content */
  dA = dA? diviiexact(absdK, dA): absdK;
  A = ZM_hnfmodid(A, dA);
  MDI = idealtwoelt(nf, A);
  gel(MDI,2) = zk_scalar_or_multable(nf, gel(MDI,2));
  gel(mat,7) = MDI;
  if (is_pm1(T->index)) /* principal ideal (x'), whose norm is |dK| */
  {
    D = zk_scalar_or_multable(nf, ZX_deriv(x));
    if (typ(D) == t_MAT) D = ZM_hnfmod(D, absdK);
  }
  else
    D = RgM_Rg_mul(idealinv(nf, A), dA);
  gel(mat,3) = RM_round_maxrank(F.G);
  gel(mat,4) = Tr;
  gel(mat,5) = D;
  gel(mat,8) = T->dKP? shallowtrans(T->dKP): cgetg(1,t_VEC);
  return nf;
}

static GEN
primes_certify(GEN dK, GEN dKP)
{
  pari_sp av = avma;
  long i, l = lg(dKP);
  GEN v, D = dK;
  v = vectrunc_init(l);
  for (i = 1; i < l; i++)
  {
    GEN p = gel(dKP,i);
    if (!isprime(p)) vectrunc_append(v, p);
    (void)Z_pvalrem(D, p, &D);
  }
  if (!is_pm1(D))
  {
    if (signe(D) < 0) D = negi(D);
    if (!isprime(D)) vectrunc_append(v, D);
  }
  fixlg(v, lg(v)); return gerepilecopy(av, v);
}
GEN
nfcertify(GEN nf)
{
  nf = checknf(nf);
  return primes_certify(nf_get_disc(nf), nf_get_ramified_primes(nf));
}

#if 0 /* used to check benches between HNF nf.zk and LLL-reduced nf.zk */
static GEN
hnffromLLL(GEN nf)
{
  GEN d, x;
  x = RgV_to_RgM(nf_get_zk(nf), nf_get_degree(nf));
  x = Q_remove_denom(x, &d);
  if (!d) return x; /* power basis */
  return RgM_solve(ZM_hnfmodid(x, d), x);
}

static GEN
nfbasechange(GEN u, GEN x)
{
  long i,lx;
  GEN y;
  switch(typ(x))
  {
    case t_COL: /* nfelt */
      return RgM_RgC_mul(u, x);

    case t_MAT: /* ideal */
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = RgM_RgC_mul(u, gel(x,i));
      break;

    case t_VEC: /* pr */
      checkprid(x); y = leafcopy(x);
      gel(y,2) = RgM_RgC_mul(u, gel(y,2));
      gel(y,5) = RgM_RgC_mul(u, gel(y,5));
      break;
    default: y = x;
  }
  return y;
}

GEN
nffromhnfbasis(GEN nf, GEN x)
{
  long tx = typ(x);
  pari_sp av = avma;
  GEN u;
  if (!is_vec_t(tx)) return gcopy(x);
  nf = checknf(nf);
  u = hnffromLLL(nf);
  return gerepilecopy(av, nfbasechange(u, x));
}

GEN
nftohnfbasis(GEN nf, GEN x)
{
  long tx = typ(x);
  pari_sp av = avma;
  GEN u;
  if (!is_vec_t(tx)) return gcopy(x);
  nf = checknf(nf);
  u = ZM_inv(hnffromLLL(nf), gen_1);
  return gerepilecopy(av, nfbasechange(u, x));
}
#endif

/* set *pro to roots of T->x */
static GEN
get_red_G(nfbasic_t *T, GEN *pro)
{
  GEN G, u, u0 = NULL;
  pari_sp av;
  long i, prec, n = degpol(T->x);
  nffp_t F;

  prec = nbits2prec(n+32);
  nffp_init(&F, T, NULL, prec);
  av = avma;
  for (i=1; ; i++)
  {
    F.prec = prec; make_M_G(&F, 0); G = F.G;
    if (u0) G = RgM_mul(G, u0);
    if (DEBUGLEVEL)
      err_printf("get_red_G: starting LLL, prec = %ld (%ld + %ld)\n",
                  prec + F.extraprec, prec, F.extraprec);
    if ((u = lllfp(G, 0.99, LLL_KEEP_FIRST|LLL_COMPATIBLE)))
    {
      if (lg(u)-1 == n) break;
      /* singular ==> loss of accuracy */
      if (u0) u0 = gerepileupto(av, RgM_mul(u0,u));
      else    u0 = gerepilecopy(av, u);
    }
    prec = precdbl(prec) + nbits2extraprec(gexpo(u0));
    F.ro = NULL;
    if (DEBUGLEVEL) pari_warn(warnprec,"get_red_G", prec);
  }
  if (u0) u = RgM_mul(u0,u);
  *pro = F.ro; return u;
}

/* Compute an LLL-reduced basis for the integer basis of nf(T).
 * set *pro = roots of x if computed [NULL if not computed] */
static void
set_LLL_basis(nfbasic_t *T, GEN *pro, double DELTA)
{
  GEN B = T->bas;
  if (T->r1 == degpol(T->x)) {
    pari_sp av = avma;
    GEN u, basden = T->basden;
    if (!basden) basden = get_bas_den(B);
    u = ZM_lll(make_Tr(T->x,basden), DELTA,
               LLL_GRAM|LLL_KEEP_FIRST|LLL_IM|LLL_COMPATIBLE);
    B = gerepileupto(av, RgV_RgM_mul(B, u));
    *pro = NULL;
  }
  else
    B = RgV_RgM_mul(B, get_red_G(T, pro));
  T->bas = B;
  T->basden = get_bas_den(B);
}

static int
cmp_abs_ZX(GEN x, GEN y) { return gen_cmp_RgX((void*)&absi_cmp, x, y); }
/* current best: ZX x of discriminant *dx, is ZX y better than x ?
 * (if so update *dx) */
static int
ZX_is_better(GEN y, GEN x, GEN *dx)
{
  GEN d = ZX_disc(y);
  int cmp;
  if (!*dx) *dx = ZX_disc(x);
  cmp = absi_cmp(d, *dx);
  if (cmp < 0) { *dx = d; return 1; }
  if (cmp == 0) return cmp_abs_ZX(y, x) < 0;
  return 0;
}

static void polredbest_aux(nfbasic_t *T, GEN *pro, GEN *px, GEN *pdx, GEN *pa);
/* Seek a simpler, polynomial pol defining the same number field as
 * x (assumed to be monic at this point) */
static GEN
nfpolred(nfbasic_t *T, GEN *pro)
{
  GEN x = T->x, dx, b, rev;
  long n = degpol(x), v = varn(x);

  if (n == 1) {
    T->x = deg1pol_shallow(gen_1, gen_m1, v);
    *pro = NULL; return pol_1(v);
  }
  polredbest_aux(T, pro, &x, &dx, &b);
  if (x == T->x) return NULL; /* no improvement */
  if (DEBUGLEVEL>1) err_printf("xbest = %Ps\n",x);

  /* update T */
  rev = QXQ_reverse(b, T->x);
  T->bas = QXV_QXQ_eval(T->bas, rev, x);
  (void)Z_issquareall(diviiexact(dx,T->dK), &(T->index));
  T->basden = get_bas_den(T->bas);
  T->dx = dx;
  T->x = x;
  *pro = NULL; /* reset */
  return rev;
}

/* let bas a t_VEC of QX giving a Z-basis of O_K. Return the index of the
 * basis. Assume bas[1] is 1 and that the leading coefficient of elements
 * of bas are of the form 1/b for a t_INT b */
GEN
get_nfindex(GEN bas)
{
  pari_sp av = avma;
  long n = lg(bas)-1, i;
  GEN D, d, mat;

  D = gen_1; /* assume bas[1] = 1 */
  for (i = 2; i <= n; i++)
  { /* in most cases [e.g after nfbasis] basis is upper triangular! */
    GEN B = gel(bas,i), lc;
    if (degpol(B) != i-1) break;
    lc = gel(B, i+1);
    switch (typ(lc))
    {
      case t_INT: continue;
      case t_FRAC: lc = gel(lc,2); break;
      default: pari_err_TYPE("get_nfindex",lc);
    }
    D = mulii(D, lc);
  }
  if (i <= n)
  { /* not triangular after all */
    bas = Q_remove_denom(bas, &d);
    if (!d) { avma = av; return D; }
    mat = RgV_to_RgM(bas, n);
    d = diviiexact(powiu(d, n), ZM_det(mat));
    D = mulii(D,absi(d));
  }
  return gerepileuptoint(av, D);
}

/* Either nf type or ZX or [monic ZX, data], where data is either an integral
 * basis (deprecated), or listP data (nfbasis input format) to specify
 * a set of primes at with the basis order must be maximal.
 * 1) nf type (or unrecognized): return t_VEC
 * 2) ZX or [ZX, listP]: return t_POL
 * 3) [ZX, order basis]: return 0 (deprecated)
 * incorrect: return -1 */
static long
nf_input_type(GEN x)
{
  GEN T, V;
  long i, d, v;
  switch(typ(x))
  {
    case t_POL: return t_POL;
    case t_VEC:
      if (lg(x) != 3) return t_VEC; /* nf or incorrect */
      T = gel(x,1); V = gel(x,2);
      if (typ(T) != t_POL) return -1;
      switch(typ(V))
      {
        case t_INT: case t_MAT: return t_POL;
        case t_VEC: case t_COL:
          if (RgV_is_ZV(V)) return t_POL;
          break;
        default: return -1;
      }
      d = degpol(T); v = varn(T);
      if (d<1 || !RgX_is_ZX(T) || !isint1(gel(T,d+2)) || lg(V)-1!=d) return -1;
      for (i = 1; i <= d; i++)
      { /* check integer basis */
        GEN c = gel(V,i);
        switch(typ(c))
        {
          case t_INT: break;
          case t_POL: if (varn(c) == v && RgX_is_QX(c) && degpol(c) < d) break;
          /* fall through */
          default: return -1;
        }
      }
      return 0;
  }
  return t_VEC; /* nf or incorrect */
}

static void
nfbasic_add_disc(nfbasic_t *T)
{
  if (!T->index) T->index = get_nfindex(T->bas);
  if (!T->dx) T->dx = ZX_disc(T->x);
  if (!T->dK) T->dK = diviiexact(T->dx, sqri(T->index));
}

static void
nfbasic_init(GEN x, long flag, nfbasic_t *T)
{
  GEN bas, dK, dx, index, unscale = gen_1;
  long r1;

  T->dKP = NULL;
  switch (nf_input_type(x))
  {
    case t_POL:
    {
      nfmaxord_t S;
      nfmaxord(&S, x, flag);
      x = S.T;
      T->x0 = S.T0;
      T->dKP = S.dKP;
      dK = S.dK;
      index = S.index;
      bas = S.basis;
      dx = S.dT;
      unscale = S.unscale;
      r1 = ZX_sturm(x);
      break;
    }
    case t_VEC:
    { /* nf, bnf, bnr */
      GEN nf = checknf(x);
      x     = nf_get_pol(nf);
      dK    = nf_get_disc(nf);
      index = nf_get_index(nf);
      bas   = nf_get_zk(nf);
      T->x0 = x;
      dx = NULL;
      r1 = nf_get_r1(nf);
      break;
    }
    case 0: /* monic integral polynomial + integer basis */
      bas = gel(x,2); x = gel(x,1);
      T->x0 = x;
      index = NULL;
      dx = NULL;
      dK = NULL;
      r1 = ZX_sturm(x);
      break;
    default: /* -1 */
      pari_err_TYPE("nfbasic_init", x);
      return;
  }
  T->x     = x;
  T->unscale = unscale;
  T->r1    = r1;
  T->dx    = dx;
  T->dK    = dK;
  T->bas   = bas;
  T->basden= NULL;
  T->index = index;
}

/* Initialize the number field defined by the polynomial x (in variable v)
 * flag & nf_RED:     try a polred first.
 * flag & nf_ORIG
 *    do a polred and return [nfinit(x), Mod(a,red)], where
 *    Mod(a,red) = Mod(v,x) (i.e return the base change). */
GEN
nfinitall(GEN x, long flag, long prec)
{
  const pari_sp av = avma;
  GEN nf, unscale;
  nfbasic_t T;

  if (checkrnf_i(x)) return check_and_build_nfabs(x, prec);
  nfbasic_init(x, flag, &T);
  if (!ZX_is_irred(T.x)) pari_err_IRREDPOL("nfinit",x);
  if (!equali1(leading_term(T.x0)) && !(flag & nf_RED))
  {
    pari_warn(warner,"non-monic polynomial. Result of the form [nf,c]");
    flag |= nf_RED | nf_ORIG;
  }
  unscale = T.unscale;
  if (!(flag & nf_RED) && !isint1(unscale))
  { /* implies lc(x0) = 1 and L := 1/unscale is integral */
    long d = degpol(T.x0);
    GEN L = ginv(unscale); /* x = L^(-deg(x)) x0(L X) */
    GEN f= powiu(L, (d*(d-1)) >> 1);
    T.x = T.x0; /* restore original user-supplied x0, unscale data */
    T.unscale = gen_1;
    T.dx    = gmul(T.dx, sqri(f));
    T.bas   = RgXV_unscale(T.bas, unscale);
    T.index = gmul(T.index, f);
  }
  nfbasic_add_disc(&T); /* more expensive after set_LLL_basis */
  if (flag & nf_RED)
  {
    GEN ro, rev;
    /* lie to polred: more efficient to update *after* modreverse, than to
     * unscale in the polred subsystem */
    T.unscale = gen_1;
    rev = nfpolred(&T, &ro);
    nf = nfbasic_to_nf(&T, ro, prec);
    if (flag & nf_ORIG)
    {
      if (!rev) rev = pol_x(varn(T.x)); /* no improvement */
      if (!isint1(unscale)) rev = RgX_Rg_div(rev, unscale);
      nf = mkvec2(nf, mkpolmod(rev, T.x));
    }
    T.unscale = unscale; /* restore */
  } else {
    GEN ro; set_LLL_basis(&T, &ro, 0.99);
    nf = nfbasic_to_nf(&T, ro, prec);
  }
  return gerepilecopy(av, nf);
}

GEN
nfinitred(GEN x, long prec)  { return nfinitall(x, nf_RED, prec); }
GEN
nfinitred2(GEN x, long prec) { return nfinitall(x, nf_RED|nf_ORIG, prec); }
GEN
nfinit(GEN x, long prec)     { return nfinitall(x, 0, prec); }

GEN
nfinit0(GEN x, long flag,long prec)
{
  switch(flag)
  {
    case 0:
    case 1: return nfinitall(x,0,prec);
    case 2: case 4: return nfinitall(x,nf_RED,prec);
    case 3: case 5: return nfinitall(x,nf_RED|nf_ORIG,prec);
    default: pari_err_FLAG("nfinit");
  }
  return NULL; /* not reached */
}

/* assume x a bnr/bnf/nf */
long
nf_get_prec(GEN x)
{
  GEN nf = checknf(x), ro = nf_get_roots(nf);
  return (typ(ro)==t_VEC)? precision(gel(ro,1)): DEFAULTPREC;
}

/* assume nf is an nf */
GEN
nfnewprec_shallow(GEN nf, long prec)
{
  GEN NF = leafcopy(nf);
  nffp_t F;
  gel(NF,5) = leafcopy(gel(NF,5));
  remake_GM(NF, &F, prec);
  gel(NF,6) = F.ro;
  gmael(NF,5,1) = F.M;
  gmael(NF,5,2) = F.G;
  return NF;
}

GEN
nfnewprec(GEN nf, long prec)
{
  GEN z;
  switch(nftyp(nf))
  {
    default: pari_err_TYPE("nfnewprec", nf);
    case typ_BNF: z = bnfnewprec(nf,prec); break;
    case typ_BNR: z = bnrnewprec(nf,prec); break;
    case typ_NF: {
      pari_sp av = avma;
      z = gerepilecopy(av, nfnewprec_shallow(checknf(nf), prec));
      break;
    }
  }
  return z;
}

/********************************************************************/
/**                                                                **/
/**                           POLRED                               **/
/**                                                                **/
/********************************************************************/
GEN
embednorm_T2(GEN x, long r1)
{
  pari_sp av = avma;
  GEN p = RgV_sumpart(x, r1);
  GEN q = RgV_sumpart2(x,r1+1, lg(x)-1);
  if (q != gen_0) p = gadd(p, gmul2n(q,1));
  return avma == av? gcopy(p): gerepileupto(av, p);
}

/* simplified version of gnorm for scalar, non-complex inputs, without GC */
static GEN
real_norm(GEN x)
{
  switch(typ(x))
  {
    case t_INT:  return sqri(x);
    case t_REAL: return sqrr(x);
    case t_FRAC: return sqrfrac(x);
  }
  pari_err_TYPE("real_norm", x);
  return NULL;
}
/* simplified version of gnorm, without GC */
static GEN
complex_norm(GEN x)
{
  return typ(x) == t_COMPLEX? cxnorm(x): real_norm(x);
}
/* return T2(x), argument r1 needed in case x has components whose type
 * is unexpected, e.g. all of them t_INT for embed(gen_1) */
GEN
embed_T2(GEN x, long r1)
{
  pari_sp av = avma;
  long i, l = lg(x);
  GEN c, s = NULL, t = NULL;
  if (typ(gel(x,1)) == t_INT) return muliu(gel(x,1), 2*(l-1)-r1);
  for (i = 1; i <= r1; i++)
  {
    c = real_norm(gel(x,i));
    s = s? gadd(s, c): c;
  }
  for (; i < l; i++)
  {
    c = complex_norm(gel(x,i));
    t = t? gadd(t, c): c;
  }
  if (t) { t = gmul2n(t,1); s = s? gadd(s,t): t; }
  return gerepileupto(av, s);
}
/* return N(x) */
GEN
embed_norm(GEN x, long r1)
{
  pari_sp av = avma;
  long i, l = lg(x);
  GEN c, s = NULL, t = NULL;
  if (typ(gel(x,1)) == t_INT) return powiu(gel(x,1), 2*(l-1)-r1);
  for (i = 1; i <= r1; i++)
  {
    c = gel(x,i);
    s = s? gmul(s, c): c;
  }
  for (; i < l; i++)
  {
    c = complex_norm(gel(x,i));
    t = t? gmul(t, c): c;
  }
  if (t) s = s? gmul(s,t): t;
  return gerepileupto(av, s);
}

typedef struct {
  long r1, v, prec;
  GEN ZKembed; /* embeddings of fincke-pohst-reduced Zk basis */
  GEN u; /* matrix giving fincke-pohst-reduced Zk basis */
  GEN M; /* embeddings of initial (LLL-reduced) Zk basis */
  GEN bound; /* T2 norm of the polynomial defining nf */
  long expo_best_disc; /* expo(disc(x)), best generator so far */
} CG_data;

/* characteristic pol of x (given by embeddings) */
static GEN
get_pol(CG_data *d, GEN x)
{
  long e;
  GEN g = grndtoi(roots_to_pol_r1(x, d->v, d->r1), &e);
  return (e > -5)? NULL: g;
}

/* characteristic pol of x (given as vector on (w_i)) */
static GEN
get_polchar(CG_data *d, GEN x)
{ return get_pol(d, RgM_RgC_mul(d->ZKembed,x)); }

/* Choose a canonical polynomial in the pair { z(X), (+/-)z(-X) }.
 * z a ZX with lc(z) > 0. We want to keep that property, while
 * ensuring that the leading coeff of the odd (resp. even) part of z is < 0
 * if deg z is even (resp. odd).
 * Either leave z alone (return 1) or set z <-- (-1)^deg(z) z(-X). In place. */
static int
ZX_canon_neg(GEN z)
{
  long i,s;

  for (i = lg(z)-2; i >= 2; i -= 2)
  { /* examine the odd (resp. even) part of z if deg(z) even (resp. odd). */
    s = signe(gel(z,i));
    if (!s) continue;
    /* non trivial */
    if (s < 0) break; /* the condition is already satisfied */

    for (; i>=2; i-=2) gel(z,i) = negi(gel(z,i));
    return 1;
  }
  return 0;
}
/* return a defining polynomial for Q(alpha), v = embeddings of alpha.
 * Return NULL on failure: discriminant too large or non primitive */
static GEN
try_polmin(CG_data *d, nfbasic_t *T, GEN v, long flag, GEN *ai)
{
  const long best = flag & nf_ABSOLUTE;
  long ed;
  pari_sp av = avma;
  GEN g;
  if (best)
  {
    ed = expo(embed_disc(v, d->r1, LOWDEFAULTPREC));
    avma = av; if (d->expo_best_disc < ed) return NULL;
  }
  else
    ed = 0;
  g = get_pol(d, v);
  /* accuracy too low, compute algebraically */
  if (!g) { avma = av; g = ZXQ_charpoly(*ai, T->x, varn(T->x)); }
  (void)ZX_gcd_all(g, ZX_deriv(g), &g);
  if (best && degpol(g) != degpol(T->x)) { avma = av; return NULL; }
  g = gerepilecopy(av, g);
  d->expo_best_disc = ed;
  if (flag & nf_ORIG)
  {
    if (ZX_canon_neg(g)) *ai = RgX_neg(*ai);
    if (!isint1(T->unscale)) *ai = RgX_unscale(*ai, T->unscale);
  }
  else
    (void)ZX_canon_neg(g);
  if (DEBUGLEVEL>3) err_printf("polred: generator %Ps\n", g);
  return g;
}

/* does x generate the correct field ? */
static GEN
chk_gen(void *data, GEN x)
{
  pari_sp av = avma, av1;
  GEN h, g = get_polchar((CG_data*)data,x);
  if (!g) pari_err_PREC("chk_gen");
  av1 = avma;
  h = ZX_gcd(g, ZX_deriv(g));
  if (degpol(h)) { avma = av; return NULL; }
  if (DEBUGLEVEL>3) err_printf("  generator: %Ps\n",g);
  avma = av1; return gerepileupto(av, g);
}

static long
chk_gen_prec(long N, long bit)
{ return nbits2prec(10 + (long)log2((double)N) + bit); }

/* Remove duplicate polynomials in P, updating A (same indices), in place.
 * Among elements having the same characteristic pol, choose the smallest
 * according to ZV_abscmp */
static void
remove_duplicates(GEN P, GEN A)
{
  long k, i, l = lg(P);
  pari_sp av = avma;
  GEN x, a;

  if (l < 2) return;
  (void)sort_factor_pol(mkmat2(P, A), cmpii);
  x = gel(P,1); a = gel(A,1);
  for  (k=1,i=2; i<l; i++)
    if (ZX_equal(gel(P,i), x))
    {
      if (ZV_abscmp(gel(A,i), a) < 0) a = gel(A,i);
    }
    else
    {
      gel(A,k) = a;
      gel(P,k) = x;
      k++;
      x = gel(P,i); a = gel(A,i);
    }
  gel(A,k) = a;
  gel(P,k) = x;
  l = k+1; setlg(A,l); setlg(P,l);
  avma = av;
}

static long
polred_init(nfbasic_t *T, nffp_t *F, CG_data *d)
{
  long e, prec, n = degpol(T->x);
  double log2rho;
  GEN ro;
  set_LLL_basis(T, &ro, 0.9999);
  /* || polchar ||_oo < 2^e ~ 2 (n * rho)^n, rho = max modulus of root */
  log2rho = ro ? (double)gexpo(ro): fujiwara_bound(T->x);
  e = n * (long)(log2rho + log2((double)n)) + 1;
  if (e < 0) e = 0; /* can occur if n = 1 */
  prec = chk_gen_prec(n, e);
  get_nf_fp_compo(T, F, ro, 1, prec);
  d->v = varn(T->x);
  d->expo_best_disc = -1;
  d->ZKembed = NULL;
  d->M = NULL;
  d->u = NULL;
  d->r1= T->r1; return prec;
}
static GEN
findmindisc(GEN y, GEN *pa)
{
  GEN a = *pa, x = gel(y,1), b = gel(a,1), dx = NULL;
  long i, l = lg(y);
  for (i = 2; i < l; i++)
  {
    GEN yi = gel(y,i);
    if (ZX_is_better(yi,x,&dx)) { x = yi; b = gel(a,i); }
  }
  *pa = b; return x;
}
/* filter [y,b] from polred_aux: keep a single polynomial of degree n in y
 * [ the best wrt discriminant ordering ], but keep all non-primitive
 * polynomials */
static void
filter(GEN y, GEN b, long n)
{
  GEN x, a, dx;
  long i, k = 1, l = lg(y);
  a = x = dx = NULL;
  for (i = 1; i < l; i++)
  {
    GEN yi = gel(y,i), ai = gel(b,i);
    if (degpol(yi) == n)
    {
      pari_sp av = avma;
      if (dx && !ZX_is_better(yi,x,&dx)) { avma = av; continue; }
      if (!dx) dx = ZX_disc(yi);
      x = yi; a = ai; continue;
    }
    gel(y,k) = yi;
    gel(b,k) = ai; k++;
  }
  if (dx)
  {
    gel(y,k) = x;
    gel(b,k) = a; k++;
  }
  setlg(y, k);
  setlg(b, k);
}

static GEN
polred_aux(nfbasic_t *T, GEN *pro, long flag)
{ /* only keep polynomials of max degree and best discriminant */
  const long best = flag & nf_ABSOLUTE;
  const long orig = flag & nf_ORIG;
  GEN M, b, y, x = T->x;
  long maxi, i, j, k, v = varn(x), n = lg(T->bas)-1;
  nffp_t F;
  CG_data d;

  if (n == 1)
  {
    if (!best)
    {
      GEN ch = deg1pol_shallow(gen_1, gen_m1, v);
      return orig? mkmat2(mkcol(ch),mkcol(gen_1)): mkvec(ch);
    }
    else
      return orig? trivial_fact(): cgetg(1,t_VEC);
  }

  (void)polred_init(T, &F, &d);
  *pro = F.ro;
  M = F.M;
  if (best)
  {
    if (!T->dx) T->dx = ZX_disc(T->x);
    d.expo_best_disc = expi(T->dx);
  }

  /* n + 2 sum_{1 <= i <= n} n-i = n + n(n-1) = n*n */
  y = cgetg(n*n + 1, t_VEC);
  b = cgetg(n*n + 1, t_COL);
  k = 1;
  if (!best)
  {
    GEN ch = deg1pol_shallow(gen_1, gen_m1, v);
    gel(y,1) = ch; gel(b,1) = gen_1; k++;
  }
  for (i = 2; i <= n; i++)
  {
    GEN ch, ai;
    ai = gel(T->bas,i);
    ch = try_polmin(&d, T, gel(M,i), flag, &ai);
    if (ch) { gel(y,k) = ch; gel(b,k) = ai; k++; }
  }
  maxi = minss(n, 3);
  for (i = 1; i <= maxi; i++)
    for (j = i+1; j <= n; j++)
    {
      GEN ch, ai, v;
      ai = gadd(gel(T->bas,i), gel(T->bas,j));
      v = RgV_add(gel(M,i), gel(M,j));
      /* defining polynomial for Q(w_i+w_j) */
      ch = try_polmin(&d, T, v, flag, &ai);
      if (ch) { gel(y,k) = ch; gel(b,k) = ai; k++; }

      ai = gsub(gel(T->bas,i), gel(T->bas,j));
      v = RgV_sub(gel(M,i), gel(M,j));
      /* defining polynomial for Q(w_i-w_j) */
      ch = try_polmin(&d, T, v, flag, &ai);
      if (ch) { gel(y,k) = ch; gel(b,k) = ai; k++; }
    }
  setlg(y, k);
  setlg(b, k); filter(y, b, n);
  if (!orig) return gen_sort_uniq(y, (void*)cmpii, &gen_cmp_RgX);
  (void)sort_factor_pol(mkmat2(y, b), cmpii);
  settyp(y, t_COL); return mkmat2(b, y);
}

static GEN
Polred(GEN x, long flag, GEN fa)
{
  pari_sp av = avma;
  GEN ro;
  nfbasic_t T; nfbasic_init(fa? mkvec2(x,fa): x, flag & nf_PARTIALFACT, &T);
  return gerepilecopy(av, polred_aux(&T, &ro, flag));
}

/* finds "best" polynomial in polred_aux list, defaulting to T->x if none of
 * them is primitive. *px is the ZX, characteristic polynomial of Mod(*pb,T->x),
 * *pdx its discriminant. Set *pro = polroots(T->x) [ NOT *px ]. */
static void
polredbest_aux(nfbasic_t *T, GEN *pro, GEN *px, GEN *pdx, GEN *pb)
{
  GEN y, x = T->x; /* default value */
  long i, l;
  y = polred_aux(T, pro, pb? nf_ORIG|nf_ABSOLUTE: nf_ABSOLUTE);
  *pdx = T->dx;
  if (pb)
  {
    GEN a, b = deg1pol_shallow(T->unscale, gen_0, varn(x));
    a = gel(y,1); l = lg(a);
    y = gel(y,2);
    for (i=1; i<l; i++)
    {
      GEN yi = gel(y,i);
      pari_sp av = avma;
      if (ZX_is_better(yi,x,pdx)) { x = yi; b = gel(a,i); } else avma = av;
    }
    *pb = b;
  }
  else
  {
    l = lg(y);
    for (i=1; i<l; i++)
    {
      GEN yi = gel(y,i);
      pari_sp av = avma;
      if (ZX_is_better(yi,x,pdx)) x = yi; else avma = av;
    }
  }
  if (!*pdx) *pdx = ZX_disc(x);
  *px = x;
}
GEN
polredbest(GEN T0, long flag)
{
  pari_sp av = avma;
  GEN T, dT, ro, a;
  nfbasic_t S;
  if (flag < 0 || flag > 1) pari_err_FLAG("polredbest");
  T = T0; nfbasic_init(T, nf_PARTIALFACT, &S);
  polredbest_aux(&S, &ro, &T, &dT, flag? &a: NULL);
  if (flag)
  { /* charpoly(Mod(a,T0)) = T */
    GEN b;
    if (T0 == T)
      b = pol_x(varn(T)); /* no improvement */
    else
      b = QXQ_reverse(a, T0); /* charpoly(Mod(b,T)) = S.x */
    b = (degpol(T) == 1)? gmodulo(b, T): mkpolmod(b,T);
    T = mkvec2(T, b);
  }
  return gerepilecopy(av, T);
}
/* DEPRECATED: backward compatibility */
GEN
polred0(GEN x, long flag, GEN fa)
{
  long fl = 0;
  if (flag & 1) fl |= nf_PARTIALFACT;
  if (flag & 2) fl |= nf_ORIG;
  return Polred(x, fl, fa);
}

GEN
polredord(GEN x)
{
  pari_sp av = avma;
  GEN v, lt;
  long i, n, vx;

  if (typ(x) != t_POL) pari_err_TYPE("polredord",x);
  x = Q_primpart(x); RgX_check_ZX(x,"polredord");
  n = degpol(x); if (n <= 0) pari_err_CONSTPOL("polredord");
  if (n == 1) return gerepilecopy(av, mkvec(x));
  lt = leading_term(x); vx = varn(x);
  if (is_pm1(lt))
  {
    if (signe(lt) < 0) x = ZX_neg(x);
    v = pol_x_powers(n, vx);
  }
  else
  { GEN L;
    /* basis for Dedekind order */
    v = cgetg(n+1, t_VEC);
    gel(v,1) = scalarpol_shallow(lt, vx);
    for (i = 2; i <= n; i++)
      gel(v,i) = RgX_Rg_add(RgX_mulXn(gel(v,i-1), 1), gel(x,n+3-i));
    gel(v,1) = pol_1(vx);
    x = ZX_Q_normalize(x, &L);
    v = gsubst(v, vx, monomial(ginv(L),1,vx));
    for (i=2; i <= n; i++)
      if (Q_denom(gel(v,i)) == gen_1) gel(v,i) = monomial(gen_1, i-1, vx);
  }
  return gerepileupto(av, polred(mkvec2(x, v)));
}

GEN
polred(GEN x) { return Polred(x, 0, NULL); }
GEN
smallpolred(GEN x) { return Polred(x, nf_PARTIALFACT, NULL); }
GEN
factoredpolred(GEN x, GEN fa) { return Polred(x, 0, fa); }
GEN
polred2(GEN x) { return Polred(x, nf_ORIG, NULL); }
GEN
smallpolred2(GEN x) { return Polred(x, nf_PARTIALFACT|nf_ORIG, NULL); }
GEN
factoredpolred2(GEN x, GEN fa) { return Polred(x, nf_PARTIALFACT, fa); }

/********************************************************************/
/**                                                                **/
/**                           POLREDABS                            **/
/**                                                                **/
/********************************************************************/
/* set V[k] := matrix of multiplication by nk.zk[k] */
static GEN
set_mulid(GEN V, GEN M, GEN Mi, long r1, long r2, long N, long k)
{
  GEN v, Mk = cgetg(N+1, t_MAT);
  long i, e;
  for (i = 1; i < k; i++) gel(Mk,i) = gmael(V, i, k);
  for (     ; i <=N; i++)
  {
    v = vecmul(gel(M,k), gel(M,i));
    v = RgM_RgC_mul(Mi, split_realimag(v, r1, r2));
    gel(Mk,i) = grndtoi(v, &e);
    if (e > -5) return NULL;
  }
  gel(V,k) = Mk; return Mk;
}

static GEN
ZM_image_shallow(GEN M, long *pr)
{
  long j, k, r;
  GEN y, d = ZM_pivots(M, &k);
  r = lg(M)-1 - k;
  y = cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; k++)
    if (d[k]) gel(y,j++) = gel(M,k);
  *pr = r; return y;
}

/* U = base change matrix, R = Cholesky form of the quadratic form [matrix
 * Q from algo 2.7.6] */
static GEN
chk_gen_init(FP_chk_fun *chk, GEN R, GEN U)
{
  CG_data *d = (CG_data*)chk->data;
  GEN P, V, D, inv, bound, S, M;
  long N = lg(U)-1, r1 = d->r1, r2 = (N-r1)>>1;
  long i, j, prec, firstprim = 0, skipfirst = 0;
  pari_sp av;

  d->u = U;
  d->ZKembed = M = RgM_mul(d->M, U);

  av = avma; bound = d->bound;
  D = cgetg(N+1, t_VECSMALL);
  for (i = 1; i <= N; i++)
  {
    pari_sp av2 = avma;
    P = get_pol(d, gel(M,i));
    if (!P) pari_err_PREC("chk_gen_init");
    (void)ZX_gcd_all(P, ZX_deriv(P), &P);
    P = gerepilecopy(av2, P);
    D[i] = degpol(P);
    if (D[i] == N)
    { /* primitive element */
      GEN B = embed_T2(gel(M,i), r1);
      if (!firstprim) firstprim = i; /* index of first primitive element */
      if (DEBUGLEVEL>2) err_printf("chk_gen_init: generator %Ps\n",P);
      if (gcmp(B,bound) < 0) bound = gerepileuptoleaf(av2, B);
    }
    else
    {
      if (DEBUGLEVEL>2) err_printf("chk_gen_init: subfield %Ps\n",P);
      if (firstprim)
      { /* cycle basis vectors so that primitive elements come last */
        GEN u = d->u, e = M;
        GEN te = gel(e,i), tu = gel(u,i), tR = gel(R,i);
        long tS = D[i];
        for (j = i; j > firstprim; j--)
        {
          u[j] = u[j-1];
          e[j] = e[j-1];
          R[j] = R[j-1];
          D[j] = D[j-1];
        }
        gel(u,firstprim) = tu;
        gel(e,firstprim) = te;
        gel(R,firstprim) = tR;
        D[firstprim] = tS; firstprim++;
      }
    }
  }
  if (!firstprim)
  { /* try (a little) to find primitive elements to improve bound */
    GEN x = cgetg(N+1, t_VECSMALL);
    if (DEBUGLEVEL>1)
      err_printf("chk_gen_init: difficult field, trying random elements\n");
    for (i = 0; i < 10; i++)
    {
      GEN e, B;
      for (j = 1; j <= N; j++) x[j] = (long)random_Fl(7) - 3;
      e = RgM_zc_mul(M, x);
      B = embed_T2(e, r1);
      if (gcmp(B,bound) >= 0) continue;
      P = get_pol(d, e); if (!P) pari_err_PREC( "chk_gen_init");
      if (!ZX_is_squarefree(P)) continue;
      if (DEBUGLEVEL>2) err_printf("chk_gen_init: generator %Ps\n",P);
      bound = B ;
    }
  }

  if (firstprim != 1)
  {
    inv = ginv( split_realimag(M, r1, r2) ); /*TODO: use QR?*/
    V = gel(inv,1);
    for (i = 2; i <= r1+r2; i++) V = gadd(V, gel(inv,i));
    /* V corresponds to 1_Z */
    V = grndtoi(V, &j);
    if (j > -5) pari_err_BUG("precision too low in chk_gen_init");
    S = mkmat(V); /* 1 */

    V = cgetg(N+1, t_VEC);
    for (i = 1; i <= N; i++,skipfirst++)
    { /* S = Q-basis of subfield generated by nf.zk[1..i-1] */
      GEN Mx, M2;
      long j, k, h, rkM, dP = D[i];

      if (dP == N) break; /* primitive */
      Mx = set_mulid(V, M, inv, r1, r2, N, i);
      if (!Mx) break; /* prec. problem. Stop */
      if (dP == 1) continue;
      rkM = lg(S)-1;
      M2 = cgetg(N+1, t_MAT); /* we will add to S the elts of M2 */
      gel(M2,1) = col_ei(N, i); /* nf.zk[i] */
      k = 2;
      for (h = 1; h < dP; h++)
      {
        long r; /* add to M2 the elts of S * nf.zk[i]  */
        for (j = 1; j <= rkM; j++) gel(M2,k++) = ZM_ZC_mul(Mx, gel(S,j));
        setlg(M2, k); k = 1;
        S = ZM_image_shallow(shallowconcat(S,M2), &r);
        if (r == rkM) break;
        if (r > rkM)
        {
          rkM = r;
          if (rkM == N) break;
        }
      }
      if (rkM == N) break;
      /* Q(w[1],...,w[i-1]) is a strict subfield of nf */
    }
  }
  /* x_1,...,x_skipfirst generate a strict subfield [unless N=skipfirst=1] */
  chk->skipfirst = skipfirst;
  if (DEBUGLEVEL>2) err_printf("chk_gen_init: skipfirst = %ld\n",skipfirst);

  /* should be DEF + gexpo( max_k C^n_k (bound/k)^(k/2) ) */
  bound = gerepileuptoleaf(av, bound);
  prec = chk_gen_prec(N, (gexpo(bound)*N)/2);
  if (DEBUGLEVEL)
    err_printf("chk_gen_init: new prec = %ld (initially %ld)\n", prec, d->prec);
  if (prec > d->prec) pari_err_BUG("polredabs (precision problem)");
  if (prec < d->prec) d->ZKembed = gprec_w(M, prec);
  return bound;
}

/* z "small" minimal polynomial of Mod(a,x), deg z = deg x */
static GEN
store(GEN x, GEN z, GEN a, nfbasic_t *T, long flag, GEN u)
{
  GEN y, b;

  if (u) a = RgV_RgC_mul(T->bas, ZM_ZC_mul(u, a));
  if (flag & (nf_ORIG|nf_ADDZK))
  {
    b = QXQ_reverse(a, x);
    if (!isint1(T->unscale)) b = gdiv(b, T->unscale); /* not RgX_Rg_div */
  }
  else
    b = NULL;

  if (flag & nf_RAW)
    y = mkvec2(z, a);
  else if (flag & nf_ORIG) /* store phi(b mod z). */
    y = mkvec2(z, mkpolmod(b,z));
  else
    y = z;
  if (flag & nf_ADDZK)
  { /* append integral basis for number field Q[X]/(z) to result */
    long n = degpol(x);
    GEN t = RgV_RgM_mul(RgXQ_powers(b, n-1, z), RgV_to_RgM(T->bas,n));
    y = mkvec2(y, t);
  }
  return y;
}
static GEN
polredabs_aux(nfbasic_t *T, GEN *u)
{
  long prec;
  GEN v;
  FP_chk_fun chk = { &chk_gen, &chk_gen_init, NULL, NULL, 0 };
  nffp_t F;
  CG_data d; chk.data = (void*)&d;

  prec = polred_init(T, &F, &d);
  d.bound = embed_T2(F.ro, d.r1);
  if (realprec(d.bound) > prec) d.bound = rtor(d.bound, prec);
  for (;;)
  {
    GEN R = R_from_QR(F.G, prec);
    if (R)
    {
      d.prec = prec;
      d.M    = F.M;
      v = fincke_pohst(mkvec(R),NULL,-1, 0, &chk);
      if (v) break;
    }
    prec = precdbl(prec);
    get_nf_fp_compo(T, &F, NULL, 1, prec);
    if (DEBUGLEVEL) pari_warn(warnprec,"polredabs0",prec);
  }
  *u = d.u; return v;
}

GEN
polredabs0(GEN x, long flag)
{
  pari_sp av = avma;
  long i, l, vx;
  GEN y, a, u;
  nfbasic_t T;

  nfbasic_init(x, flag & nf_PARTIALFACT, &T);
  x = T.x; vx = varn(x);

  if (degpol(x) == 1)
  {
    u = NULL;
    y = mkvec( pol_x(vx) );
    a = mkvec( deg1pol_shallow(gen_1, negi(gel(x,2)), vx) );
    l = 2;
  }
  else
  {
    GEN v;
    if (!(flag & nf_PARTIALFACT)
        && T.dKP && lg(primes_certify(T.dK, T.dKP)) != 1) return gen_0;
    v = polredabs_aux(&T, &u);
    y = gel(v,1);
    a = gel(v,2); l = lg(a);
    for (i=1; i<l; i++)
      if (ZX_canon_neg(gel(y,i))) gel(a,i) = ZC_neg(gel(a,i));
    remove_duplicates(y,a);
    l = lg(a);
    if (l == 1)
      pari_err_BUG("polredabs (missing vector)");
  }
  if (DEBUGLEVEL) err_printf("Found %ld minimal polynomials.\n",l-1);
  if (flag & nf_ALL) {
    for (i=1; i<l; i++) gel(y,i) = store(x, gel(y,i), gel(a,i), &T, flag, u);
  } else {
    GEN z = findmindisc(y, &a);
    y = store(x, z, a, &T, flag, u);
  }
  return gerepilecopy(av, y);
}

GEN
polredabsall(GEN x, long flun) { return polredabs0(x, flun | nf_ALL); }
GEN
polredabs(GEN x) { return polredabs0(x,0); }
GEN
polredabs2(GEN x) { return polredabs0(x,nf_ORIG); }

/* relative polredabs/best. Returns relative polynomial by default (flag = 0)
 * flag & nf_ORIG: + element (base change)
 * flag & nf_ABSOLUTE: absolute polynomial */
static GEN
rnfpolred_i(GEN nf, GEN relpol, long flag, long best)
{
  const char *f = best? "rnfpolredbest": "rnfpolredabs";
  const long abs = ((flag & nf_ORIG) && (flag & nf_ABSOLUTE));
  pari_timer ti;
  GEN listP = NULL, red, bas, A, P, pol, T, rnfeq;
  long ty = typ(relpol);
  pari_sp av = avma;

  if (ty == t_VEC) {
    if (lg(relpol) != 3) pari_err_TYPE(f,relpol);
    listP = gel(relpol,2);
    relpol = gel(relpol,1);
  }
  if (typ(relpol) != t_POL) pari_err_TYPE(f,relpol);
  nf = checknf(nf);
  if (DEBUGLEVEL>1) timer_start(&ti);
  T = nf_get_pol(nf);
  relpol = RgX_nffix(f, T, relpol, 0);
  if (best || (flag & nf_PARTIALFACT))
  {
    if (abs)
    {
      rnfeq = nf_rnfeq(nf, relpol);
      pol = gel(rnfeq,1);
    }
    else
    {
      long sa;
      pol = rnfequationall(nf, relpol, &sa, NULL);
      rnfeq = mkvec5(gen_0,gen_0,stoi(sa),T,liftpol_shallow(relpol));
    }
    bas = listP? mkvec2(pol, listP): pol;
    if (best)
    {
      if (abs) red = polredbest(bas, 1);
      else
      {
        GEN ro, x, dx, a;
        nfbasic_t T;
        nfbasic_init(bas, nf_PARTIALFACT, &T);
        polredbest_aux(&T, &ro, &x, &dx, &a);
        red = mkvec2(x, a);
      }
    }
    else
      red = polredabs0(bas, (abs? nf_ORIG: nf_RAW)|nf_PARTIALFACT);
  }
  else
  {
    GEN rnf = rnfinit(nf, relpol), M = rnf_basM(rnf);
    rnfeq = rnf_get_map(rnf);
    pol = rnf_get_polabs(rnf);
    bas = mkvec2(pol, RgM_to_RgXV(M, varn(pol)));
    if (DEBUGLEVEL>1) timer_printf(&ti, "absolute basis");
    red = polredabs0(bas, nf_RAW);
  }
  P = gel(red,1);
  A = gel(red,2);
  if (DEBUGLEVEL>1) err_printf("reduced absolute generator: %Ps\n",P);
  if (flag & nf_ABSOLUTE)
  {
    if (flag & nf_ORIG)
    {
      GEN a = gel(rnfeq,2); /* Mod(a,pol) root of T */
      GEN k = gel(rnfeq,3); /* Mod(variable(relpol),relpol) + k*a root of pol */
      a = RgX_RgXQ_eval(a, lift_intern(A), P); /* Mod(a, P) root of T */
      P = mkvec3(P, mkpolmod(a,P), gsub(A, gmul(k,a)));
    }
    return gerepilecopy(av, P);
  }
  A = eltabstorel_lift(rnfeq, A);
  P = RgXQ_charpoly(A, relpol, varn(relpol));
  P = lift_if_rational(P);
  if (flag & nf_ORIG) P = mkvec2(P, mkpolmod(RgXQ_reverse(A,relpol),P));
  return gerepilecopy(av, P);
}
GEN
rnfpolredabs(GEN nf, GEN relpol, long flag)
{ return rnfpolred_i(nf,relpol,flag, 0); }
GEN
rnfpolredbest(GEN nf, GEN relpol, long flag)
{
  if (flag < 0 || flag > 3) pari_err_FLAG("rnfpolredbest");
  return rnfpolred_i(nf,relpol,flag, 1);
}
