/* $Id$

Copyright (C) 2011  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

#include "pari.h"
#include "paripriv.h"

/* Adapted from shp_package/moments by Robert Pollack
 * http://www.math.mcgill.ca/darmon/programs/shp/shp.html */
static GEN mskinit(ulong N, long k, long sign);
static GEN mshecke_i(GEN W, ulong p);
static GEN msnew_trivial(GEN W);
static GEN mscuspidal_trivial(GEN W0);
static GEN ZGl2Q_star(GEN v);
static GEN getMorphism_trivial(GEN WW1, GEN WW2, GEN v);
static GEN getMorphism(GEN W1, GEN W2, GEN v);
static GEN voo_act_Gl2Q(GEN g, long k);
static GEN mscuspidal_i(GEN W);

/* Input: P^1(Z/NZ) (formed by create_p1mod)
   Output: # P^1(Z/NZ) */
static long
p1_size(GEN p1N) { return lg(gel(p1N,1)) - 1; }
static ulong
p1N_get_N(GEN p1N) { return gel(p1N,3)[2]; }
static GEN
p1N_get_hash(GEN p1N) { return gel(p1N,2); }
static GEN
p1N_get_fa(GEN p1N) { return gel(p1N,4); }
static GEN
p1N_get_div(GEN p1N) { return gel(p1N,5); }
/* ms-specific accessors */
/* W = msinit or msfromell */
static GEN
get_ms(GEN W) { return lg(W) == 4? gel(W,1): W; }
static GEN
ms_get_p1N(GEN W) { W = get_ms(W); return gel(W,1); }
static long
ms_get_N(GEN W) { return p1N_get_N(ms_get_p1N(W)); }
static GEN
ms_get_hashcusps(GEN W) { W = get_ms(W); return gel(W,16); }
static GEN
ms_get_section(GEN W) { W = get_ms(W); return gel(W,12); }
static GEN
ms_get_genindex(GEN W) { W = get_ms(W); return gel(W,5); }
static long
ms_get_nbgen(GEN W) { return lg(ms_get_genindex(W))-1; }
static long
ms_get_nbE1(GEN W)
{
  GEN W11;
  W = get_ms(W); W11 = gel(W,11);
  return W11[4] - W11[3];
}
/* msk-specific accessors */
static long
msk_get_dim(GEN W) { return gmael(W,3,2)[2]; }
static GEN
msk_get_basis(GEN W) { return gmael(W,3,1); }
static long
msk_get_weight(GEN W) { return gmael(W,3,2)[1]; }
static GEN
msk_get_st(GEN W) { return gmael(W,3,3); }
static GEN
msk_get_link(GEN W) { return gmael(W,3,4); }
static GEN
msk_get_invphiblock(GEN W) { return gmael(W,3,5); }
static long
msk_get_sign(GEN W)
{
  GEN t = gel(W,2);
  return typ(t)==t_INT? 0: itos(gel(t,1));
}
static GEN
msk_get_star(GEN W) { return gmael(W,2,2); }
static GEN
msk_get_starproj(GEN W) { return gmael(W,2,3); }

void
checkms(GEN W)
{
  if (typ(W) != t_VEC || lg(W) != 4)
    pari_err_TYPE("checkms [please apply msinit]", W);
}

/** MODULAR TO SYM **/

/* q a t_FRAC or t_INT */
static GEN
Q_log_init(ulong N, GEN q)
{
  long l, n;
  GEN Q;

  q = gboundcf(q, 0);
  l = lg(q);
  Q = cgetg(l, t_VECSMALL);
  Q[1] = 1;
  for (n=2; n <l; n++) Q[n] = umodiu(gel(q,n), N);
  for (n=3; n < l; n++)
    Q[n] = Fl_add(Fl_mul(Q[n], Q[n-1], N), Q[n-2], N);
  return Q;
}

/** INIT MODSYM STRUCTURE, WEIGHT 2 **/

/* num = [Gamma : Gamma_0(N)] = N * Prod_{p|N} (1+p^-1) */
static ulong
count_Manin_symbols(ulong N, GEN P)
{
  long i, l = lg(P);
  ulong num = N;
  for (i = 1; i < l; i++) { ulong p = P[i]; num *= p+1; num /= p; }
  return num;
}
/* returns the list of "Manin symbols" (c,d) in (Z/NZ)^2, (c,d,N) = 1
 * generating H^1(X_0(N), Z) */
static GEN
generatemsymbols(ulong N, ulong num, GEN divN)
{
  GEN ret = cgetg(num+1, t_VEC);
  ulong c, d, curn = 0;
  long i, l;
  /* generate Manin-symbols in two lists: */
  /* list 1: (c:1) for 0 <= c < N */
  for (c = 0; c < N; c++) gel(ret, ++curn) = mkvecsmall2(c, 1);
  if (N == 1) return ret;
  /* list 2: (c:d) with 1 <= c < N, c | N, 0 <= d < N, gcd(d,N) > 1, gcd(c,d)=1.
   * Furthermore, d != d0 (mod N/c) with c,d0 already in the list */
  l = lg(divN) - 1;
  /* c = 1 first */
  gel(ret, ++curn) = mkvecsmall2(1,0);
  for (d = 2; d < N; d++)
    if (ugcd(d,N) != 1UL)
      gel(ret, ++curn) = mkvecsmall2(1,d);
  /* omit c = 1 (first) and c = N (last) */
  for (i=2; i < l; i++)
  {
    ulong Novc, d0;
    c = divN[i];
    Novc = N / c;
    for (d0 = 2; d0 <= Novc; d0++)
    {
      ulong k, d = d0;
      if (ugcd(d, Novc) == 1UL) continue;
      for (k = 0; k < c; k++, d += Novc)
        if (ugcd(c,d) == 1UL)
        {
          gel(ret, ++curn) = mkvecsmall2(c,d);
          break;
        }
    }
  }
  if (curn != num) pari_err_BUG("generatemsymbols [wrong number of symbols]");
  return ret;
}

#if OLD_HASH
static ulong
hash2(GEN H, long N, long a, long b)
{ return ucoeff(H, smodss(a,N) + 1, smodss(b,N) + 1); }
/* symbols from generatemsymbols(). Returns H such that
 * H[ nc mod N, nd mod N ] = index of (c,d) in 'symbols', n < N, (n,N) = 1 */
static GEN
inithashmsymbols(ulong N, GEN symbols)
{
  GEN H = zero_Flm_copy(N, N);
  long k, l = lg(symbols);
  ulong n;
  for (n = 1; n < N; n++)
    if (ugcd(n,N) == 1)
      for (k=1; k < l; k++)
      {
        GEN s = gel(symbols, k);
        ucoeff(H, Fl_mul(s[1],n,N) + 1, Fl_mul(s[2],n,N) + 1) = k;
      }
  return H;
}
#else
static GEN
inithashmsymbols(ulong N, GEN symbols)
{
  GEN H = zerovec(N);
  long k, l = lg(symbols);
  /* skip the (c:1), 0 <= c < N and (1:0) */
  for (k=N+2; k < l; k++)
  {
    GEN s = gel(symbols, k);
    ulong c = s[1], d = s[2], Novc = N/c;
    if (gel(H,c) == gen_0) gel(H,c) = const_vecsmall(Novc+1,0);
    if (c != 1) { d %= Novc; if (!d) d = Novc; }
    mael(H, c, d) = k;
  }
  return H;
}
#endif

/** Helper functions for Sl2(Z) / Gamma_0(N) **/
/* M a 2x2 ZM in SL2(Z) */
static GEN
SL2_inv(GEN M)
{
  GEN a=gcoeff(M,1,1), b=gcoeff(M,1,2), c=gcoeff(M,2,1), d=gcoeff(M,2,2);
  return mkmat2(mkcol2(d, negi(c)), mkcol2(negi(b), a));
}
/* M a 2x2 zm in SL2(Z) */
static GEN
sl2_inv(GEN M)
{
  long a=coeff(M,1,1), b=coeff(M,1,2), c=coeff(M,2,1), d=coeff(M,2,2);
  return mkmat2(mkvecsmall2(d, -c), mkvecsmall2(-b, a));
}
/* Return the zm [a,b; c,d] */
static GEN
mat2(long a, long b, long c, long d)
{ return mkmat2(mkvecsmall2(a,c), mkvecsmall2(b,d)); }

/* Input: a = 2-vector = path = {r/s,x/y}
 * Output: either [r,x;s,y] or [-r,x;-s,y], whichever has determinant > 0 */
static GEN
path_to_zm(GEN a)
{
  GEN v = gel(a,1), w = gel(a,2);
  long r = v[1], s = v[2], x = w[1], y = w[2];
  if (cmpii(mulss(r,y), mulss(x,s)) < 0) { r = -r; s = -s; }
  return mat2(r,x,s,y);
}
/* path from c1 to c2 */
static GEN
mkpath(GEN c1, GEN c2) { return mat2(c1[1], c2[1], c1[2], c2[2]); }
static long
cc(GEN M) { GEN v = gel(M,1); return v[2]; }
static long
dd(GEN M) { GEN v = gel(M,2); return v[2]; }

/*Input: a,b = 2 paths, N = integer
 *Output: 1 if the a,b are \Gamma_0(N)-equivalent; 0 otherwise */
static int
gamma_equiv(GEN a, GEN b, ulong N)
{
  pari_sp av = avma;
  GEN m = path_to_zm(a);
  GEN n = path_to_zm(b);
  GEN d = subii(mulss(cc(m),dd(n)), mulss(dd(m),cc(n)));
  ulong res = umodiu(d, N);
  avma = av; return res == 0;
}
/* Input: a,b = 2 paths that are \Gamma_0(N)-equivalent, N = integer
 * Output: M in \Gamma_0(N) such that Mb=a */
static GEN
gamma_equiv_matrix(GEN a, GEN b)
{
  GEN m = zm_to_ZM( path_to_zm(a) );
  GEN n = zm_to_ZM( path_to_zm(b) );
  return ZM_mul(m, SL2_inv(n));
}

/*************/
/* P^1(Z/NZ) */
/*************/

/* Input: N = integer
 * Output: creates P^1(Z/NZ) = [symbols, H, N]
 *   symbols: list of vectors [x,y] that give a set of representatives
 *            of P^1(Z/NZ)
 *   H: an M by M grid whose value at the r,c-th place is the index of the
 *      "standard representative" equivalent to [r,c] occuring in the first
 *      list. If gcd(r,c,N) > 1 the grid has value 0. */
static GEN
create_p1mod(ulong N)
{
  GEN fa = factoru(N), div = divisorsu(N);
  ulong nsym = count_Manin_symbols(N, gel(fa,1));
  GEN symbols = generatemsymbols(N, nsym, div);
  GEN H = inithashmsymbols(N,symbols);
  return mkvec5(symbols, H, utoipos(N), fa, div);
}

/* result is known to be representable as an ulong */
static ulong
lcmuu(ulong a, ulong b) { ulong d = ugcd(a,b); return (a/d) * b; }
/* a != 0 in Z/NZ. Return u in (Z/NZ)^* such that au = gcd(a, N) (mod N)*/
static ulong
Fl_inverse(ulong a, ulong N)
{
  pari_sp av;
  ulong d, d0, d1, e, u = Fl_invgen(a, N, &d);
  if (d == 1) return u;
  e = N/d;
  d0 = ucoprime_part(d, e); /* d = d0 d1, d0 coprime to N/d, core(d1) | N/d */
  if (d0 == 1) return u;
  av = avma;
  d1 = d / d0;
  e = lcmuu(e, d1);
  u = itou(Z_chinese_coprime(utoipos(u), gen_1,
                             utoipos(e), utoipos(d0), utoipos(e*d0)));
  avma = av; return u;
}
/* Let (c : d) in P1(Z/NZ).
 * If c = 0 return (0:1). If d = 0 return (1:0).
 * Else replace by (cu : du), where u in (Z/NZ)^* such that C := cu = gcd(c,N).
 * In create_p1mod(), (c : d) is represented by (C:D) where D = du (mod N/c)
 * is smallest such that gcd(C,D) = 1. Return (C : du mod N/c), which need
 * not belong to P1(Z/NZ) ! A second component du mod N/c = 0 is replaced by
 * N/c in this case to avoid problems with array indices */
static GEN
p1_std_form(long c, long d, ulong N)
{
  ulong u;
  c = smodss(c, N);
  d = smodss(d, N);
  if (!c) return mkvecsmall2(0, 1);
  if (!d) return mkvecsmall2(1, 0);
  u = Fl_invsafe(d, N);
  if (u != 0) return mkvecsmall2(Fl_mul(c,u,N), 1); /* (d,N) = 1 */

  u = Fl_inverse(c, N);
  if (u > 1) { c = Fl_mul(c,u,N); d = Fl_mul(d,u,N); }
  /* c | N */
  if (c != 1) d = d % (N/c);
  if (!d) d = N/c;
  return mkvecsmall2(c, d);
}

/* Input: v = [x,y] = elt of P^1(Z/NZ) = class in Gamma_0(N) \ PSL2(Z)
 * Output: returns the index of the standard rep equivalent to v */
static long
p1_index(long x, long y, GEN p1N)
{
  ulong N = p1N_get_N(p1N);
  GEN H = p1N_get_hash(p1N), c;

#ifdef OLD_HASH
  return hash2(p1N_get_hash(p1N), N, x, y);
#else
  c = p1_std_form(x, y, N);
  x = c[1];
  y = c[2];
  if (y == 1) return x+1;
  if (y == 0) return N+1;
  if (mael(H,x,y) == 0) pari_err_BUG("p1_index");
  return mael(H,x,y);
#endif
}

/* Cusps for \Gamma_0(N) */

/* \sum_{d | N} \phi(gcd(d, N/d)), using multiplicativity. fa = factor(N) */
static ulong
nbcusp(GEN fa)
{
  GEN P = gel(fa,1), E = gel(fa,2);
  long i, l = lg(P);
  ulong T = 1;
  for (i = 1; i < l; i++)
  {
    long e = E[i] >> 1; /* floor(E[i] / 2) */
    ulong p = P[i];
    if (odd(E[i]))
      T *= 2 * upowuu(p, e);
    else
      T *= (p+1) * upowuu(p, e - 1);
  }
  return T;
}

/* to each cusp in \Gamma_0(N) P1(Q), represented by p/q, we associate a
 * unique index. Canonical representative: (1:0) or (p:q) with q | N, q < N,
 * p defined modulo d := gcd(N/q,q), (p,d) = 1.
 * Return [[N, nbcusps], H, cusps]*/
static GEN
inithashcusps(GEN p1N)
{
  ulong N = p1N_get_N(p1N);
  GEN div = p1N_get_div(p1N), H = zerovec(N+1);
  long k, ind, l = lg(div), ncusp = nbcusp(p1N_get_fa(p1N));
  GEN cusps = cgetg(ncusp+1, t_VEC);

  gel(H,1) = mkvecsmall2(0/*empty*/, 1/* first cusp: (1:0) */);
  gel(cusps, 1) = mkvecsmall2(1,0);
  ind = 2;
  for (k=1; k < l-1; k++) /* l-1: remove q = N */
  {
    ulong p, q = div[k], d = ugcd(q, N/q);
    GEN h = const_vecsmall(d+1,0);
    gel(H,q+1) = h ;
    for (p = 0; p < d; p++)
      if (ugcd(p,d) == 1)
      {
        h[p+1] = ind;
        gel(cusps, ind) = mkvecsmall2(p,q);
        ind++;
      }
  }
  return mkvec3(mkvecsmall2(N,ind-1), H, cusps);
}
/* c = [p,q], (p,q) = 1, return a canonical representative for
 * \Gamma_0(N)(p/q) */
static GEN
cusp_std_form(GEN c, GEN S)
{
  long p, N = gel(S,1)[1], q = smodss(c[2], N);
  ulong u, d;
  if (q == 0) return mkvecsmall2(1, 0);
  p = smodss(c[1], N);
  u = Fl_inverse(q, N);
  q = Fl_mul(q,u, N);
  d = ugcd(q, N/q);
  return mkvecsmall2(Fl_div(p % d,u % d, d), q);
}
/* c = [p,q], (p,q) = 1, return the index of the corresponding cusp.
 * S from inithashcusps */
static ulong
cusp_index(GEN c, GEN S)
{
  long p, q;
  GEN H = gel(S,2);
  c = cusp_std_form(c, S);
  p = c[1]; q = c[2];
  if (!mael(H,q+1,p+1)) pari_err_BUG("cusp_index");
  return mael(H,q+1,p+1);
}

/* M a square invertible ZM, return a ZM iM such that iM M = M iM = d.Id */
static GEN
ZM_inv_denom(GEN M)
{
  GEN ciM = ZM_det(M);
  GEN c, iM = Q_primitive_part(ZM_inv(M, ciM), &c);
  if (c) ciM = diviiexact(ciM, c);
  return mkvec2(iM, ciM);
}
/* return M^(-1) v, dinv = ZM_inv_denom(M) OR Qevproj_init(M) */
static GEN
ZC_apply_dinv(GEN dinv, GEN v)
{
  GEN x, c, iM;
  if (lg(dinv) == 3)
  {
    iM = gel(dinv,1);
    c = gel(dinv,2);
  }
  else
  { /* Qevproj_init */
    iM = gel(dinv,2);
    c = gel(dinv,3);
    v = typ(v) == t_MAT? rowpermute(v, gel(dinv,4))
                       : vecpermute(v, gel(dinv,4));
  }
  x = RgM_RgC_mul(iM, v);
  if (!isint1(c)) x = RgC_Rg_div(x, c);
  return x;
}

/* M an n x d ZM of rank d (basis of a Q-subspace), n >= d.
 * Initialize a projector on M */
GEN
Qevproj_init(GEN M)
{
  GEN v, perm, MM, dinv, iM, ciM;
  v = ZM_indexrank(M); perm = gel(v,1);
  MM = rowpermute(M, perm); /* square invertible */
  dinv = ZM_inv_denom(MM);
  iM = gel(dinv,1);
  ciM= gel(dinv,2);
  return mkvec4(M, iM, ciM, perm);
}
/* same with typechecks */
static GEN
Qevproj_init0(GEN M)
{
  switch(typ(M))
  {
    case t_VEC:
      if (lg(M) == 5) return M;
      break;
    case t_MAT:
      M = Q_primpart(M);
      RgM_check_ZM(M,"Qevproj_init");
      return Qevproj_init(M);
  }
  pari_err_TYPE("Qevproj_init",M);
  return NULL;
}

/* T an n x n QM, stabilizing d-dimensional Q-vector space spanned by the
 * columns of M, pro = Qevproj_init(M). Return d x d matrix of T acting
 * on M */
GEN
Qevproj_apply(GEN T, GEN pro)
{
  GEN M = gel(pro,1), iM = gel(pro,2), ciM = gel(pro,3), perm = gel(pro,4);
  return RgM_Rg_div(RgM_mul(iM, RgM_mul(rowpermute(T,perm), M)), ciM);
}
/* Qevproj_apply(T,pro)[,k] */
GEN
Qevproj_apply_vecei(GEN T, GEN pro, long k)
{
  GEN M = gel(pro,1), iM = gel(pro,2), ciM = gel(pro,3), perm = gel(pro,4);
  GEN v = RgM_RgC_mul(iM, RgM_RgC_mul(rowpermute(T,perm), gel(M,k)));
  return RgC_Rg_div(v, ciM);
}

/* normalize a Q-basis*/
static GEN
Q_primpart_basis(GEN M)
{
  long i, l;
  GEN N = cgetg_copy(M, &l);
  for (i = 1; i < l; i++) gel(N,i) = Q_primpart(gel(M,i));
  return N;
}
static GEN
ZM_ker(GEN M) { return Q_primpart_basis(keri(M)); }
static GEN
QM_ker(GEN M) { return ZM_ker(Q_primpart(M)); }
static GEN
QM_image(GEN A)
{
  A = Q_primpart_basis(A);
  return vecpermute(A, ZM_indeximage(A));
}

static int
cmp_dim(void *E, GEN a, GEN b)
{
  long k;
  (void)E;
  a = gel(a,1);
  b = gel(b,1); k = lg(a)-lg(b);
  return k? ((k > 0)? 1: -1): 0;
}

/* Decompose the subspace H (Qevproj format) in simple subspaces.
 * Eg for H = msnew */
static GEN
mssplit_i(GEN W, GEN H)
{
  ulong p, N = ms_get_N(W);
  long first, dim;
  forprime_t S;
  GEN T1 = NULL, T2 = NULL, V;
  dim = lg(gel(H,1))-1;
  V = vectrunc_init(dim+1);
  if (!dim) return V;
  (void)u_forprime_init(&S, 2, ULONG_MAX);
  vectrunc_append(V, H);
  first = 1; /* V[1..first-1] contains simple subspaces */
  while ((p = u_forprime_next(&S)))
  {
    GEN T;
    long n, j, lV;
    if (N % p == 0) continue;
    if (T1 && T2)
    {
      T = RgM_add(T1,T2);
      T2 = NULL;
    }
    else
    {
      T2 = T1;
      T1 = T = mshecke_i(W, p);
    }
    lV = lg(V);
    for (j = first; j < lV; j++)
    {
      pari_sp av = avma;
      GEN Vj = gel(V,j), P = gel(Vj,1);
      GEN TVj = Qevproj_apply(T, Vj); /* c T | V_j */
      GEN ch = QM_charpoly_ZX(TVj), fa = ZX_factor(ch), F, E;
      long k;
      F = gel(fa, 1);
      E = gel(fa, 2);
      n = lg(F)-1;
      if (n == 1)
      {
        if (isint1(gel(E,1)))
        { /* simple subspace */
          swap(gel(V,first), gel(V,j));
          first++;
        }
        else
          avma = av;
      }
      else
      { /* can split Vj */
        GEN pows;
        long D = 1;
        for (k = 1; k <= n; k++)
        {
          long d = degpol(gel(F,k));
          if (d > D) D = d;
        }
        /* remove V[j] */
        swap(gel(V,j), gel(V,lg(V)-1)); setlg(V, lg(V)-1);
        pows = RgM_powers(TVj, minss((long)2*sqrt(D), D));
        for (k = 1; k <= n; k++)
        {
          GEN f = gel(F,k);
          GEN M = RgX_RgMV_eval(f, pows); /* f(TVj) */
          GEN K = QM_ker(M);
          GEN p = Q_primpart( RgM_mul(P, K) );
          vectrunc_append(V, Qevproj_init(p));
          if (lg(K) == 2 || isint1(gel(E,k)))
          { /* simple subspace */
            swap(gel(V,first), gel(V, lg(V)-1));
            first++;
          }
        }
        if (j < first) j = first;
      }
    }
    if (first >= lg(V)) {
      gen_sort_inplace(V, NULL, cmp_dim, NULL);
      return V;
    }
  }
  pari_err_BUG("subspaces not found");
  return NULL;
}
GEN
mssplit(GEN W, GEN H)
{
  pari_sp av = avma;
  checkms(W);
  if (!msk_get_sign(W))
    pari_err_DOMAIN("mssplit","abs(sign)","!=",gen_1,gen_0);
  H = Qevproj_init0(H);
  return gerepilecopy(av, mssplit_i(W,H));
}

/* proV = Qevproj_init of a Hecke simple subspace, return [ a_n, n <= B ] */
static GEN
msqexpansion_i(GEN W, GEN proV, ulong B)
{
  ulong p, N = ms_get_N(W), sqrtB;
  long i, d, k = msk_get_weight(W);
  forprime_t S;
  GEN T1=NULL, T2=NULL, TV=NULL, ch=NULL, v, dTiv, Tiv, dinv, ciM, iM, L;
  switch(B)
  {
    case 0: return cgetg(1,t_VEC);
    case 1: return mkvec(gen_1);
  }
  (void)u_forprime_init(&S, 2, ULONG_MAX);
  while ((p = u_forprime_next(&S)))
  {
    GEN T;
    if (N % p == 0) continue;
    if (T1 && T2)
    {
      T = RgM_add(T1,T2);
      T2 = NULL;
    }
    else
    {
      T2 = T1;
      T1 = T = mshecke_i(W, p);
    }
    TV = Qevproj_apply(T, proV); /* T | V */
    ch = QM_charpoly_ZX(TV);
    if (ZX_is_irred(ch)) break;
    ch = NULL;
  }
  if (!ch) pari_err_BUG("q-Expansion not found");
  /* T generates the Hecke algebra */
  d = degpol(ch);
  v = vec_ei(d, 1); /* take v = e_1 */
  Tiv = cgetg(d+1, t_MAT); /* Tiv[i] = T^(i-1)v */
  gel(Tiv, 1) = v;
  for (i = 2; i <= d; i++) gel(Tiv, i) = RgM_RgC_mul(TV, gel(Tiv,i-1));
  Tiv = Q_remove_denom(Tiv, &dTiv);
  dinv = ZM_inv_denom(Tiv);
  iM = gel(dinv,1);
  ciM = gel(dinv,2);
  if (dTiv) ciM = gdiv(ciM, dTiv);
  L = const_vec(B,NULL);
  sqrtB = (ulong)sqrt(B);
  gel(L,1) = d > 1? mkpolmod(gen_1,ch): gen_1;
  for (p = 2; p <= B; p++)
  {
    pari_sp av = avma;
    GEN T, u, Tv, ap, P;
    ulong m;
    if (gel(L,p)) continue;  /* p not prime */
    T = mshecke_i(W, p);
    Tv = Qevproj_apply_vecei(T, proV, 1); /* Tp.v */
    /* Write Tp.v = \sum u_i T^i v */
    u = RgC_Rg_div(RgM_RgC_mul(iM, Tv), ciM);
    ap = gerepilecopy(av, RgV_to_RgX(u, 0));
    if (d > 1)
      ap = mkpolmod(ap,ch);
    else
      ap = simplify_shallow(ap);
    gel(L,p) = ap;
    if (!(N % p))
    { /* p divides the level */
      ulong C = B/p;
      for (m=1; m<=C; m++)
        if (gel(L,m)) gel(L,m*p) = gmul(gel(L,m), ap);
      continue;
    }
    P = powuu(p,k-1);
    if (p <= sqrtB) {
      ulong pj, oldpj = 1;
      for (pj = p; pj <= B; oldpj=pj, pj *= p)
      {
        GEN apj = (pj==p)? ap
                         : gsub(gmul(ap,gel(L,oldpj)), gmul(P,gel(L,oldpj/p)));
        gel(L,pj) = apj;
        for (m = B/pj; m > 1; m--)
          if (gel(L,m) && m%p) gel(L,m*pj) = gmul(gel(L,m), apj);
      }
    } else {
      gel(L,p) = ap;
      for (m = B/p; m > 1; m--)
        if (gel(L,m)) gel(L,m*p) = gmul(gel(L,m), ap);
    }
  }
  return L;
}
GEN
msqexpansion(GEN W, GEN proV, ulong B)
{
  pari_sp av = avma;
  checkms(W);
  proV = Qevproj_init0(proV);
  return gerepilecopy(av, msqexpansion_i(W,proV,B));
}

static GEN
Qevproj_star(GEN W, GEN H)
{
  long s = msk_get_sign(W);
  if (s)
  { /* project on +/- component */
    GEN star = msk_get_star(W);
    GEN A = gmul(star, H);
    A = (s > 0)? gadd(A, H): gsub(A, H);
    /* Im(star + sign) = Ker(star - sign) */
    H = QM_image(A);
  }
  return H;
}
static GEN
msnew_trivial(GEN W)
{
  GEN p1N = ms_get_p1N(W), P = gel(p1N_get_fa(p1N), 1);
  ulong N = ms_get_N(W);
  long i, nP = lg(P)-1;
  GEN Snew, K, v;

  K = mscuspidal_trivial(W);
  if (uisprime(N)) { Snew = K; goto END; }
  v = cgetg(2*nP + 1, t_COL);
  for (i = 1; i <= nP; i++)
  {
    pari_sp av = avma, av2;
    ulong M = N / P[i];
    GEN T1, Td, Wi = mskinit(M, 2, 0);
    T1 = getMorphism_trivial(W, Wi, mat2(1,0,0,1));
    Td = getMorphism_trivial(W, Wi, mat2(P[i],0,0,1));
    av2 = avma;
    T1 = ZM_mul(T1, K); /* multiply by K = restrict to Ker delta */
    Td = ZM_mul(Td, K);
    gerepileallsp(av, av2, 2, &T1,&Td);
    gel(v,2*i-1)= T1;
    gel(v,2*i)  = Td;
  }
  Snew = ZM_mul(K, ZM_ker(matconcat(v)));
END:
  return Qevproj_star(W, Snew);
}

static GEN
msnew_i(GEN W)
{
  GEN p1N = ms_get_p1N(W), P = gel(p1N_get_fa(p1N), 1);
  ulong p, N = ms_get_N(W);
  long i, nP = lg(P)-1, k = msk_get_weight(W);
  GEN S, Snew, Sold, pr_S, pr_Sold, v;
  forprime_t F;
  if (k == 2) return msnew_trivial(W);
  S = gel(mscuspidal_i(W), 2);
  if (uisprime(N)) { Snew = S; goto END; }
  v = cgetg(2*nP + 1, t_VEC);
  for (i = 1; i <= nP; i++)
  {
    GEN Wi = mskinit(N/P[i], k, 0);
    gel(v,2*i-1) = getMorphism(Wi, W, mat2(1,0,0,1));
    gel(v,2*i)   = getMorphism(Wi, W, mat2(P[i],0,0,1));
  }
  v = QM_image(matconcat(v)); /* old forms */
  /* restrict to cuspidal subspace */
  Sold = Q_primpart_basis(intersect(S, v));
  pr_S = Qevproj_init(S);
  pr_Sold = Qevproj_init(Sold);
  Snew = NULL;
  (void)u_forprime_init(&F, 2, ULONG_MAX);
  while ((p = u_forprime_next(&F)))
  {
    pari_sp av = avma;
    GEN T, chS, chSold, chSnew;
    if (N % p == 0) continue;
    T = mshecke_i(W, p);
    chS = QM_charpoly_ZX(Qevproj_apply(T, pr_S));
    chSold = QM_charpoly_ZX(Qevproj_apply(T, pr_Sold));
    chSnew = RgX_div(chS, chSold); /* = char T | S^new */
    if (!degpol( ZX_gcd(chSnew, chSold) ))
    {
      GEN M = RgX_RgM_eval(chSnew, T);
      Snew = QM_ker(M);
      break;
    }
    avma = av;
  }
END:
  return Qevproj_star(W, Snew);
}
GEN
msnew(GEN W)
{
  pari_sp av = avma;
  checkms(W);
  return gerepilecopy(av, Qevproj_init( msnew_i(W)) );
}

/* Solve the Manin relations for a congruence subgroup \Gamma by constructing
 * a well-formed fundamental domain for the action of \Gamma on upper half
 * space. See
 * Pollack and Stevens, Overconvergent modular symbols and p-adic L-functions
 * Annales scientifiques de l'ENS 44, fascicule 1 (2011), 1-42
 * http://math.bu.edu/people/rpollack/Papers/Overconvergent_modular_symbols_and_padic_Lfunctions.pdf
 *
 * FIXME: Implemented for \Gamma = \Gamma_0(N) only. */

#if 0 /* Pollack-Stevens shift their paths so as to solve equations of the
         form f(z+1) - f(z) = g. We don't (to avoid mistakes) so we will
         have to solve eqs of the form f(z-1) - f(z) = g */
/* c = a/b; as a t_VECSMALL [a,b]; return c-1 as a t_VECSMALL */
static GEN
Shift_left_cusp(GEN c) { long a=c[1], b=c[2]; return mkvecsmall2(a - b, b); }
/* c = a/b; as a t_VECSMALL [a,b]; return c+1 as a t_VECSMALL */
static GEN
Shift_right_cusp(GEN c) { long a=c[1], b=c[2]; return mkvecsmall2(a + b, b); }
/*Input: path = [r,s] (thought of as a geodesic between these points)
 *Output: The path shifted by one to the left, i.e. [r-1,s-1] */
static GEN
Shift_left(GEN path)
{
  GEN r = gel(path,1), s = gel(path,2);
  return mkvec2(Shift_left_cusp(r), Shift_left_cusp(s)); }
/*Input: path = [r,s] (thought of as a geodesic between these points)
 *Output: The path shifted by one to the right, i.e. [r+1,s+1] */
GEN
Shift_right(GEN path)
{
  GEN r = gel(path,1), s = gel(path,2);
  return mkvec2(Shift_right_cusp(r), Shift_right_cusp(s)); }
#endif

/* linked lists */
typedef struct list_t { GEN data; struct list_t *next; } list_t;
static list_t *
list_new(GEN x)
{
  list_t *L = (list_t*)stack_malloc(sizeof(list_t));
  L->data = x;
  L->next = NULL; return L;
}
static void
list_insert(list_t *L, GEN x)
{
  list_t *l = list_new(x);
  l->next = L->next;
  L->next = l;
}

/*Input: N > 1, p1N = P^1(Z/NZ)
 *Output: a connected fundamental domain for the action of \Gamma_0(N) on
 *  upper half space.  When \Gamma_0(N) is torsion free, the domain has the
 *  property that all of its vertices are cusps.  When \Gamma_0(N) has
 *  three-torsion, 2 extra triangles need to be added.
 *
 * The domain is constructed by beginning with the triangle with vertices 0,1
 * and oo.  Each adjacent triangle is successively tested to see if it contains
 * points not \Gamma_0(N) equivalent to some point in our region.  If a
 * triangle contains new points, it is added to the region.  This process is
 * continued until the region can no longer be extended (and still be a
 * fundamental domain) by added an adjacent triangle.  The list of cusps
 * between 0 and 1 are then returned
 *
 * Precisely, the function returns a list such that the elements of the list
 * with odd index are the cusps in increasing order.  The even elements of the
 * list are either an "x" or a "t".  A "t" represents that there is an element
 * of order three such that its fixed point is in the triangle directly
 * adjacent to the our region with vertices given by the cusp before and after
 * the "t".  The "x" represents that this is not the case. */
enum { type_X, type_DO /* ? */, type_T };
static GEN
form_list_of_cusps(ulong N, GEN p1N)
{
  pari_sp av = avma;
  long i, position, nbC = 2;
  GEN v, L;
  list_t *C, *c;
  /* Let t be the index of a class in PSL2(Z) / \Gamma in our fixed enumeration
   * v[t] != 0 iff it is the class of z tau^r for z a previous alpha_i
   * or beta_i.
   * For \Gamma = \Gamma_0(N), the enumeration is given by p1_index.
   * We write cl(gamma) = the class of gamma mod \Gamma */
  v = const_vecsmall(p1_size(p1N), 0);
  i = p1_index( 0, 1, p1N); v[i] = 1;
  i = p1_index( 1,-1, p1N); v[i] = 2;
  i = p1_index(-1, 0, p1N); v[i] = 3;
  /* the value is unused [debugging]: what matters is whether it is != 0 */
  position = 4;
  /* at this point, Fund = R, v contains the classes of Id, tau, tau^2 */

  C  = list_new(mkvecsmall3(0,1, type_X));
  list_insert(C, mkvecsmall3(1,1,type_DO));
  /* C is a list of triples[a,b,t], where c = a/b is a cusp, and t is the type
   * of the path between c and the PREVIOUS cusp in the list, coded as
   *   type_DO = "?", type_X = "x", type_T = "t"
   * Initially, C = [0/1,"?",1/1]; */

  /* loop through the current set of cusps C and check to see if more cusps
   * should be added */
  for (;;)
  {
    int done = 1;
    for (c = C; c; c = c->next)
    {
      GEN cusp1, cusp2, gam;
      long pos, b1, b2, b;

      if (!c->next) break;
      cusp1 = c->data; /* = a1/b1 */
      cusp2 = (c->next)->data; /* = a2/b2 */
      if (cusp2[3] != type_DO) continue;

      /* gam (oo -> 0) = (cusp2 -> cusp1), gam in PSL2(Z) */
      gam = path_to_zm(mkpath(cusp2, cusp1)); /* = [a2,a1;b2,b1] */
      /* we have normalized the cusp representation so that a1 b2 - a2 b1 = 1 */
      b1 = coeff(gam,2,1); b2 = coeff(gam,2,2);
      /* gam.1  = (a1 + a2) / (b1 + b2) */
      b = b1 + b2;
      /* Determine whether the adjacent triangle *below* (cusp1->cusp2)
       * should be added */
      pos = p1_index(b1,b2, p1N); /* did we see cl(gam) before ? */
      if (v[pos])
        cusp2[3] = type_X; /* NO */
      else
      { /* YES */
        ulong B1, B2;
        v[pos] = position;
        i = p1_index(-(b1+b2), b1, p1N); v[i] = position+1;
        i = p1_index(b2, -(b1+b2), p1N); v[i] = position+2;
        /* add cl(gam), cl(gam*TAU), cl(gam*TAU^2) to v */
        position += 3;
        /* gam tau gam^(-1) in \Gamma ? */
        B1 = smodss(b1, N);
        B2 = smodss(b2, N);
        if ((Fl_sqr(B2,N) + Fl_sqr(B1,N) + Fl_mul(B1,B2,N)) % N == 0)
          cusp2[3] = type_T;
        else
        {
          long a1 = coeff(gam, 1,1), a2 = coeff(gam, 1,2);
          long a = a1 + a2; /* gcd(a,b) = 1 */
          list_insert(c, mkvecsmall3(a,b,type_DO));
          c = c->next;
          nbC++;
          done = 0;
        }
      }
    }
    if (done) break;
  }
  L = cgetg(nbC+1, t_VEC); i = 1;
  for (c = C; c; c = c->next) gel(L,i++) = c->data;
  return gerepilecopy(av, L);
}

/* M in PSL2(Z). Return index of M in P1^(Z/NZ) = Gamma0(N) \ PSL2(Z),
 * and M0 in Gamma_0(N) such that M = M0 * M', where M' = chosen
 * section( PSL2(Z) -> P1^(Z/NZ) ). */
static GEN
Gamma0N_decompose(GEN W, GEN M, long *index)
{
  GEN p1N = gel(W,1), W3 = gel(W,3), section = ms_get_section(W);
  GEN A;
  ulong N = p1N_get_N(p1N);
  ulong c = umodiu(gcoeff(M,2,1), N);
  ulong d = umodiu(gcoeff(M,2,2), N);
  long s, ind = p1_index(c, d, p1N); /* as an elt of P1(Z/NZ) */
  *index = W3[ind]; /* as an elt of F, E2, ... */
  M = ZM_zm_mul(M, sl2_inv(gel(section,ind)));
  /* normalize mod +/-Id */
  A = gcoeff(M,1,1);
  s = signe(A);
  if (s < 0)
    M = ZM_neg(M);
  else if (!s)
  {
    GEN C = gcoeff(M,2,1);
    if (signe(C) < 0) M = ZM_neg(M);
  }
  return M;
}
/* same for a path. Return [[ind], M] */
static GEN
path_Gamma0N_decompose(GEN W, GEN path)
{
  GEN p1N = gel(W,1);
  GEN p1index_to_ind = gel(W,3);
  GEN section = ms_get_section(W);
  GEN M = path_to_zm(path);
  long p1index = p1_index(cc(M), dd(M), p1N);
  long ind = p1index_to_ind[p1index];
  GEN M0 = ZM_zm_mul(zm_to_ZM(M), sl2_inv(gel(section,p1index)));
  return mkvec2(mkvecsmall(ind), M0);
}

/*Form generators of H_1(X_0(N),{cusps},Z)
*
*Input: N = integer > 1, p1N = P^1(Z/NZ)
*Output: [cusp_list,E,F,T2,T3,E1] where
*  cusps_list = list of cusps describing fundamental domain of
*    \Gamma_0(N).
*  E = list of paths in the boundary of the fundamental domains and oriented
*    clockwise such that they do not contain a point
*    fixed by an element of order 2 and they are not an edge of a
*    triangle containing a fixed point of an element of order 3
*  F = list of paths in the interior of the domain with each
*    orientation appearing separately
* T2 = list of paths in the boundary of domain containing a point fixed
*    by an element of order 2 (oriented clockwise)
* T3 = list of paths in the boundard of domain which are the edges of
*    some triangle containing a fixed point of a matrix of order 3 (both
*    orientations appear)
* E1 = a sublist of E such that every path in E is \Gamma_0(N)-equivalent to
*    either an element of E1 or the flip (reversed orientation) of an element
*    of E1.
* (Elements of T2 are \Gamma_0(N)-equivalent to their own flip.)
*
* sec = a list from 1..#p1N of matrices describing a section of the map
*   SL_2(Z) to P^1(Z/NZ) given by [a,b;c,d]-->[c,d].
*   Given our fixed enumeration of P^1(Z/NZ), the j-th element of the list
*   represents the image of the j-th element of P^1(Z/NZ) under the section. */

/* insert path in set T */
static void
set_insert(hashtable *T, GEN path)
{ hash_insert(T, path,  (void*)(T->nb + 1)); }

static GEN
hash_to_vec(hashtable *h)
{
  GEN v = cgetg(h->nb + 1, t_VEC);
  ulong i;
  for (i = 0; i < h->len; i++)
  {
    hashentry *e = h->table[i];
    while (e)
    {
      GEN key = (GEN)e->key;
      long index = (long)e->val;
      gel(v, index) = key;
      e = e->next;
    }
  }
  return v;
}

static long
path_to_p1_index(GEN path, GEN p1N)
{
  GEN M = path_to_zm(path);
  return p1_index(cc(M), dd(M), p1N);
}

/* Pollack-Stevens sets */
typedef struct PS_sets_t {
  hashtable *F, *T2, *T31, *T32, *E1, *E2;
  GEN E2_in_terms_of_E1, stdE1;
} PS_sets_t;

static hashtable *
set_init(long max)
{ return hash_create(max, (ulong(*)(void*))&hash_GEN,
                          (int(*)(void*,void*))&gidentical, 1); }
static void
insert_E(GEN path, PS_sets_t *S, GEN p1N)
{
  GEN rev = vecreverse(path);
  long std = path_to_p1_index(rev, p1N);
  GEN v = gel(S->stdE1, std);
  if (v)
  { /* [s, p1], where E1[s] = the path p1 \equiv vecreverse(path) mod \Gamma */
    GEN gamma, p1 = gel(v,2);
    long r, s = itos(gel(v,1));

    set_insert(S->E2, path);
    r = S->E2->nb;
    if (gel(S->E2_in_terms_of_E1, r) != gen_0) pari_err_BUG("insert_E");

    gamma = gamma_equiv_matrix(rev, p1);
    /* E2[r] + gamma * E1[s] = 0 */
    gel(S->E2_in_terms_of_E1, r) = mkvec2(utoipos(s),
                                          to_famat_shallow(gamma,gen_m1));
  }
  else
  {
    set_insert(S->E1, path);
    std = path_to_p1_index(path, p1N);
    gel(S->stdE1, std) = mkvec2(utoipos(S->E1->nb), path);
  }
}

static GEN
cusp_infinity() { return mkvecsmall2(1,0); }

static void
form_E_F_T(ulong N, GEN p1N, GEN *pC, PS_sets_t *S)
{
  GEN C, cusp_list = form_list_of_cusps(N, p1N);
  long nbgen = lg(cusp_list)-1, nbmanin = p1_size(p1N), r, s, i;
  hashtable *F, *T2, *T31, *T32, *E1, *E2;

  *pC = C = cgetg(nbgen+1, t_VEC);
  for (i = 1; i <= nbgen; i++)
  {
    GEN c = gel(cusp_list,i);
    gel(C,i) = mkvecsmall2(c[1], c[2]);
  }
  S->F  = F  = set_init(nbmanin);
  S->E1 = E1 = set_init(nbgen);
  S->E2 = E2 = set_init(nbgen);
  S->T2 = T2 = set_init(nbgen);
  S->T31 = T31 = set_init(nbgen);
  S->T32 = T32 = set_init(nbgen);

  /* T31 represents the three torsion paths going from left to right */
  /* T32 represents the three torsion paths going from right to left */
  for (r = 1; r < nbgen; r++)
  {
    GEN c2 = gel(cusp_list,r+1);
    if (c2[3] == type_T)
    {
      GEN c1 = gel(cusp_list,r), path = mkpath(c1,c2), path2 = vecreverse(path);
      set_insert(T31, path);
      set_insert(T32, path2);
    }
  }

  /* to record relations between E2 and E1 */
  S->E2_in_terms_of_E1 = zerovec(nbgen);
  S->stdE1 = const_vec(nbmanin, NULL);

  /* Assumption later: path [oo,0] is E1[1], path [1,oo] is E2[1] */
  {
    GEN oo = cusp_infinity();
    GEN p1 = mkpath(oo, mkvecsmall2(0,1)); /* [oo, 0] */
    GEN p2 = mkpath(mkvecsmall2(1,1), oo); /* [1, oo] */
    insert_E(p1, S, p1N);
    insert_E(p2, S, p1N);
  }

  for (r = 1; r < nbgen; r++)
  {
    GEN c1 = gel(cusp_list,r);
    for (s = r+1; s <= nbgen; s++)
    {
      pari_sp av = avma;
      GEN c2 = gel(cusp_list,s), path;
      GEN d = subii(mulss(c1[1],c2[2]), mulss(c1[2],c2[1]));
      avma = av;
      if (!is_pm1(d)) continue;

      path = mkpath(c1,c2);
      if (r+1 == s)
      {
        GEN w = path;
        ulong hash = T31->hash(w); /* T31, T32 use the same hash function */
        if (!hash_search2(T31, w, hash) && !hash_search2(T32, w, hash))
        {
          if (gamma_equiv(path, vecreverse(path), N))
            set_insert(T2, path);
          else
            insert_E(path, S, p1N);
        }
      } else {
        set_insert(F, mkvec2(path, mkvecsmall2(r,s)));
        set_insert(F, mkvec2(vecreverse(path), mkvecsmall2(s,r)));
      }
    }
  }
  setlg(S->E2_in_terms_of_E1, E2->nb+1);
}

/* v = \sum n_i g_i, return \sum n_i g_i^(-1) */
static GEN
ZGl2Q_star(GEN v)
{
  long i, l;
  GEN w, G;
  if (typ(v) == t_INT) return v;
  G = gel(v,1);
  w = cgetg_copy(G, &l);
  for (i = 1; i < l; i++)
  {
    GEN g = gel(G,i);
    if (typ(g) == t_MAT) g = SL2_inv(g);
    gel(w,i) = g;
  }
  return ZG_normalize(mkmat2(w, gel(v,2)));
}
static GEN
ZGl2QC_star(GEN v)
{
  long i, l;
  GEN w = cgetg_copy(v, &l);
  for (i = 1; i < l; i++) gel(w,i) = ZGl2Q_star(gel(v,i));
  return w;
}

/* Input: h = set of unimodular paths, p1N = P^1(Z/NZ) = Gamma_0(N)\PSL2(Z)
 * Output: Each path is converted to a matrix and then an element of P^1(Z/NZ)
 * Append the matrix to W[12], append the index that represents
 * these elements of P^1 (the classes mod Gamma_0(N) via our fixed
 * enumeration to W[2]. */
static void
paths_decompose(GEN W, hashtable *h, int flag)
{
  GEN p1N = ms_get_p1N(W), section = ms_get_section(W);
  GEN v = hash_to_vec(h);
  long i, l = lg(v);
  for (i = 1; i < l; i++)
  {
    GEN e = gel(v,i);
    GEN M = path_to_zm(flag? gel(e,1): e);
    long index = p1_index(cc(M), dd(M), p1N);
    vecsmalltrunc_append(gel(W,2), index);
    gel(section, index) = M;
  }
}
static void
fill_W2_W12(GEN W, PS_sets_t *S)
{
  GEN p1N = gel(W,1);
  long n = p1_size(p1N);
  gel(W, 2) = vecsmalltrunc_init(n+1);
  gel(W,12) = cgetg(n+1, t_VEC);
  /* F contains [path, [index cusp1, index cusp2]]. Others contain paths only */
  paths_decompose(W, S->F, 1);
  paths_decompose(W, S->E2, 0);
  paths_decompose(W, S->T32, 0);
  paths_decompose(W, S->E1, 0);
  paths_decompose(W, S->T2, 0);
  paths_decompose(W, S->T31, 0);
}

/* x t_VECSMALL, corresponds to a map x(i) = j, where 1 <= j <= max for all i
 * Return y s.t. y[j] = i or 0 (not in image) */
static GEN
reverse_list(GEN x, long max)
{
  GEN y = const_vecsmall(max, 0);
  long r, lx = lg(x);
  for (r = 1; r < lx; r++) y[ x[r] ] = r;
  return y;
}

/* go from C[a] to C[b]; return the indices of paths
 * E.g. if a < b
 *   (C[a]->C[a+1], C[a+1]->C[a+2], ... C[b-1]->C[b])
 * (else reverse direction)
 * = b - a paths */
static GEN
F_indices(GEN W, long a, long b)
{
  GEN v = cgetg(labs(b-a) + 1, t_VEC);
  long s, k = 1;
  if (a < b) {
    GEN index_forward = gel(W,13);
    for (s = a; s < b; s++) gel(v,k++) = gel(index_forward,s);
  } else {
    GEN index_backward = gel(W,14);
    for (s = a; s > b; s--) gel(v,k++) = gel(index_backward,s);
  }
  return v;
}
/* go from C[a] to C[b] via oo; return the indices of paths
 * E.g. if a < b
 *   (C[a]->C[a-1], ... C[2]->C[1],
 *    C[1]->oo, oo-> C[end],
 *    C[end]->C[end-1], ... C[b+1]->C[b])
 *  a-1 + 2 + end-(b+1)+1 = end - b + a + 1 paths  */
static GEN
F_indices_oo(GEN W, long end, long a, long b)
{
  GEN index_oo = gel(W,15);
  GEN v = cgetg(end-labs(b-a)+1 + 1, t_VEC);
  long s, k = 1;

  if (a < b) {
    GEN index_backward = gel(W,14);
    for (s = a; s > 1; s--) gel(v,k++) = gel(index_backward,s);
    gel(v,k++) = gel(index_backward,1); /* C[1] -> oo */
    gel(v,k++) = gel(index_oo,2); /* oo -> C[end] */
    for (s = end; s > b; s--) gel(v,k++) = gel(index_backward,s);
  } else {
    GEN index_forward = gel(W,13);
    for (s = a; s < end; s++) gel(v,k++) = gel(index_forward,s);
    gel(v,k++) = gel(index_forward,end); /* C[end] -> oo */
    gel(v,k++) = gel(index_oo,1); /* oo -> C[1] */
    for (s = 1; s < b; s++) gel(v,k++) = gel(index_forward,s);
  }
  return v;
}
/* index of oo -> C[1], oo -> C[end] */
static GEN
indices_oo(GEN W, GEN C)
{
  long end = lg(C)-1;
  GEN w, v = cgetg(2+1, t_VEC), oo = cusp_infinity();
  w = mkpath(oo, gel(C,1)); /* oo -> C[1]=0 */
  gel(v,1) = path_Gamma0N_decompose(W, w);
  w = mkpath(oo, gel(C,end)); /* oo -> C[end]=1 */
  gel(v,2) = path_Gamma0N_decompose(W, w);
  return v;
}

/* index of C[1]->C[2], C[2]->C[3], ... C[end-1]->C[end], C[end]->oo
 * Recall that C[1] = 0, C[end] = 1 */
static GEN
indices_forward(GEN W, GEN C)
{
  long s, k = 1, end = lg(C)-1;
  GEN v = cgetg(end+1, t_VEC);
  for (s = 1; s <= end; s++)
  {
    GEN w = mkpath(gel(C,s), s == end? cusp_infinity(): gel(C,s+1));
    gel(v,k++) = path_Gamma0N_decompose(W, w);
  }
  return v;
}
/* index of C[1]->oo, C[2]->C[1], ... C[end]->C[end-1] */
static GEN
indices_backward(GEN W, GEN C)
{
  long s, k = 1, end = lg(C)-1;
  GEN v = cgetg(end+1, t_VEC);
  for (s = 1; s <= end; s++)
  {
    GEN w = mkpath(gel(C,s), s == 1? cusp_infinity(): gel(C,s-1));
    gel(v,k++) = path_Gamma0N_decompose(W, w);
  }
  return v;
}

/* N = integer > 1. Returns data describing Delta_0 = Z[P^1(Q)]_0 seen as
 * a Gamma_0(N) - module. */
static GEN
msinit_N(ulong N)
{
  GEN p1N = create_p1mod(N);
  GEN C, vecF, vecT2, vecT31;
  ulong r, s, width;
  long nball, nbgen, nbp1N = p1_size(p1N);
  GEN TAU = mkmat2(mkcol2(gen_0,gen_1), mkcol2(gen_m1,gen_m1)); /*[0,-1;1,-1]*/
  GEN W, W2, singlerel, annT2, annT31;
  GEN F_index;
  hashtable *F, *T2, *T31, *T32, *E1, *E2;
  PS_sets_t S;

  form_E_F_T(N,p1N, &C, &S);
  E1  = S.E1;
  E2  = S.E2;
  T31 = S.T31;
  T32 = S.T32;
  F   = S.F;
  T2  = S.T2;
  nbgen = lg(C)-1;

  W = cgetg(17, t_VEC);
  gel(W,1) = p1N;

 /* Put our paths in the order: F,E2,T32,E1,T2,T31
  * W2[j] associates to the j-th element of this list its index in P1. */
  fill_W2_W12(W, &S);
  W2 = gel(W, 2);
  nball = lg(W2)-1;
  gel(W,3) = reverse_list(W2, nbp1N);

  gel(W,5) = vecslice(gel(W,2), F->nb + E2->nb + T32->nb + 1, nball);
  gel(W,4) = reverse_list(gel(W,5), nbp1N);
  gel(W,13) = indices_forward(W, C);
  gel(W,14) = indices_backward(W, C);
  gel(W,15) = indices_oo(W, C);
  gel(W,11) = mkvecsmall5(F->nb,
                          F->nb + E2->nb,
                          F->nb + E2->nb + T32->nb,
                          F->nb + E2->nb + T32->nb + E1->nb,
                          F->nb + E2->nb + T32->nb + E1->nb + T2->nb);

  /* relations between T32 and T31 [not stored!]
   * T32[i] = - T31[i] */

  /* relations of F */
  width = E1->nb + T2->nb + T31->nb;
  /* F_index[r] = [index_1, ..., index_k], where index_i is the p1_index()
   * of the elementary unimodular path between 2 consecutive cusps
   * [in E1,E2,T2,T31 or T32] */
  F_index = cgetg(F->nb+1, t_VEC);
  vecF = hash_to_vec(F);
  for (r = 1; r <= F->nb; r++)
  {
    GEN w = gel(gel(vecF,r), 2);
    long a = w[1], b = w[2], d = labs(b - a);
    /* c1 = cusp_list[a],  c2 = cusp_list[b], ci != oo */
    gel(F_index,r) = (nbgen-d >= d-1)? F_indices(W, a,b)
                                     : F_indices_oo(W, lg(C)-1,a,b);
  }

  singlerel = cgetg(width+1, t_VEC);
  /* form the single boundary relation */
  for (s = 1; s <= E2->nb; s++)
  {
    GEN data = gel(S.E2_in_terms_of_E1,s);
    long c = itos(gel(data,1));
    GEN u = gel(data,2); /* E2[s] = u * E1[c], u = - [gamma] */
    GEN gamma = gcoeff(u,1,1);
    gel(singlerel, c) = mkmat2(mkcol2(gen_1,gamma),mkcol2(gen_1,gen_m1));
  }
  for (r = E1->nb + 1; r <= width; r++) gel(singlerel, r) = gen_1;

  /* form the 2-torsion relations */
  annT2 = cgetg(T2->nb+1, t_VEC);
  vecT2 = hash_to_vec(T2);
  for (r = 1; r <= T2->nb; r++)
  {
    GEN w = gel(vecT2,r);
    GEN gamma = gamma_equiv_matrix(vecreverse(w), w);
    gel(annT2, r) = mkmat2(mkcol2(gen_1,gamma), mkcol2(gen_1,gen_1));
  }

  /* form the 3-torsion relations */
  annT31 = cgetg(T31->nb+1, t_VEC);
  vecT31 = hash_to_vec(T31);
  for (r = 1; r <= T31->nb; r++)
  {
    GEN M = zm_to_ZM( path_to_zm( vecreverse(gel(vecT31,r)) ) );
    GEN gamma = ZM_mul(ZM_mul(M, TAU), SL2_inv(M));
    gel(annT31, r) = mkmat2(mkcol3(gen_1,gamma,ZM_sqr(gamma)),
                            mkcol3(gen_1,gen_1,gen_1));
  }
  gel(W,6) = F_index;
  gel(W,7) = S.E2_in_terms_of_E1;
  gel(W,8) = annT2;
  gel(W,9) = annT31;
  gel(W,10)= singlerel;
  gel(W,16)= inithashcusps(p1N);
  return W;
}
static GEN
cusp_to_P1Q(GEN c) { return c[2]? gdivgs(stoi(c[1]), c[2]): mkoo(); }
GEN
mspathgens(GEN W)
{
  pari_sp av = avma;
  long i,j, l, nbE1, nbT2, nbT31;
  GEN R, r, g, section, gen, annT2, annT31, singlerel;
  checkms(W); W = get_ms(W);
  section = ms_get_section(W);
  gen = ms_get_genindex(W);
  l = lg(gen);
  g = cgetg(l,t_VEC);
  for (i=1; i<l; i++)
  {
    GEN p = gel(section,gen[i]);
    gel(g,i) = mkvec2(cusp_to_P1Q(gel(p,1)), cusp_to_P1Q(gel(p,2)));
  }
  nbE1 = ms_get_nbE1(W);
  annT2 = gel(W,8); nbT2 = lg(annT2)-1;
  annT31 = gel(W,9);nbT31 = lg(annT31)-1;
  singlerel = gel(W,10);
  R = cgetg(nbT2+nbT31+2, t_VEC);
  l = lg(singlerel);
  r = cgetg(l, t_VEC);
  for (i = 1; i <= nbE1; i++)
    gel(r,i) = mkvec2(gel(singlerel, i), stoi(i));
  for (; i < l; i++)
    gel(r,i) = mkvec2(gen_1, stoi(i));
  gel(R,1) = r; j = 2;
  for (i = 1; i <= nbT2; i++,j++)
    gel(R,j) = mkvec( mkvec2(gel(annT2,i), stoi(i + nbE1)) );
  for (i = 1; i <= nbT31; i++,j++)
    gel(R,j) = mkvec( mkvec2(gel(annT31,i), stoi(i + nbE1 + nbT2)) );
  return gerepilecopy(av, mkvec2(g,R));
}

/* Modular symbols in weight k: Hom_Gamma(Delta, Q[x,y]_{k-2}) */
/* A symbol phi is represented by the {phi(g_i)}, {phi(g'_i)}, {phi(g''_i)}
 * where the {g_i, g'_i, g''_i} are the Z[\Gamma]-generators of Delta,
 * g_i corresponds to E1, g'_i to T2, g''_i to T31.
 */

/* FIXME: export. T^1, ..., T^n */
static GEN
RgX_powers(GEN T, long n)
{
  GEN v = cgetg(n+1, t_VEC);
  long i;
  gel(v, 1) = T;
  for (i = 1; i < n; i++) gel(v,i+1) = RgX_mul(gel(v,i), T);
  return v;
}

/* g = [a,b;c,d]. Return (X^{k-2} | g)(X,Y)[X = 1]. */
static GEN
voo_act_Gl2Q(GEN g, long k)
{
  GEN c = gcoeff(g,2,1), d = gcoeff(g,2,2);
  return RgX_to_RgC(gpowgs(deg1pol_shallow(gneg(c), d, 0), k-2), k-1);
}

/* g = [a,b;c,d]. Return (P | g)(X,Y)[X = 1] = P(dX - cY, -b X + aY)[X = 1],
 * for P = X^{k-2}, X_^{k-3}Y, ..., Y^{k-2} */
GEN
RgX_act_Gl2Q(GEN g, long k)
{
  GEN a = gcoeff(g,1,1), b = gcoeff(g,1,2);
  GEN c = gcoeff(g,2,1), d = gcoeff(g,2,2);
  GEN V1 = RgX_powers(deg1pol_shallow(gneg(c), d, 0), k-2);
  GEN V2 = RgX_powers(deg1pol_shallow(a, gneg(b), 0), k-2);
  GEN V = cgetg(k, t_MAT);
  long i;
  gel(V,1)   = RgX_to_RgC(gel(V1, k-2), k-1);
  for (i = 1; i < k-2; i++)
  {
    GEN v1 = gel(V1, k-2-i); /* (d-cY)^(k-2-i) */
    GEN v2 = gel(V2, i); /* (-b+aY)^i */
    gel(V,i+1) = RgX_to_RgC(RgX_mul(v1,v2), k-1);
  }
  gel(V,k-1) = RgX_to_RgC(gel(V2, k-2), k-1);
  return V; /* V[i+1] = X^i | g */
}
/* z in Z[\Gamma], return the matrix of z acting on (X^{k-2},...,Y^{k-2}) */
GEN
RgX_act_ZGl2Q(GEN z, long k)
{
  long l, j;
  GEN S = NULL, G, E;
  if (typ(z) == t_INT) return matid(k-1);
  G = gel(z,1); l = lg(G);
  E = gel(z,2);
  for (j = 1; j < l; j++)
  {
    GEN M, g = gel(G,j), n = gel(E,j);
    if (typ(g) == t_INT)
      M = scalarmat_shallow(n, k-1);
    else
    {
      M = RgX_act_Gl2Q(g, k);
      if (is_pm1(n))
      { if (signe(n) < 0) M = RgM_neg(M);
      } else
        M = RgM_Rg_mul(M, n);
    }
    S = j == 1? M: RgM_add(S, M);
  }
  return S;
}
/* Given a vector of elements in Z[G], return it as vector of operators on V
 * (given by t_MAT) */
static GEN
ZGl2QC_to_act(GEN v, long k)
{
  long i, l;
  GEN w = cgetg_copy(v, &l);
  for (i = 1; i < l; i++) gel(w,i) = RgX_act_ZGl2Q(gel(v,i), k);
  return w;
}

/* For all V[i] in Z[\Gamma], find the P such that  P . V[i]^* = 0;
 * write P in basis X^{k-2}, ..., Y^{k-2} */
static GEN
ZGV_tors(GEN V, long k)
{
  long i, l = lg(V);
  GEN v = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN a = ZGl2Q_star(gel(V,i));
    gel(v,i) = ZM_ker(RgX_act_ZGl2Q(a,k));
  }
  return v;
}

static long
set_from_index(GEN W11, long i)
{
  if (i <= W11[1]) return 1;
  if (i <= W11[2]) return 2;
  if (i <= W11[3]) return 3;
  if (i <= W11[4]) return 4;
  if (i <= W11[5]) return 5;
  return 6;
}

/* det M = 1 */
static void
treat_index(GEN W, GEN M, long index, GEN v)
{
  GEN W11 = gel(W,11);
  long shift = W11[3]; /* #F + #E2 + T32 */
  switch(set_from_index(W11, index))
  {
    case 1: /*F*/
    {
      GEN F_index = gel(W,6), ind = gel(F_index, index);
      long j, l = lg(ind);
      for (j = 1; j < l; j++)
      {
        GEN IND = gel(ind,j), M0 = gel(IND,2);
        long index = mael(IND,1,1);
        treat_index(W, ZM_mul(M,M0), index, v);
      }
      break;
    }

    case 2: /*E2, E2[r] + gamma * E1[s] = 0 */
    {
      long r = index - W11[1];
      GEN E2_in_terms_of_E1= gel(W,7), z = gel(E2_in_terms_of_E1, r);
      long s = itou(gel(z,1));

      index = s;
      M = G_ZG_mul(M, gel(z,2)); /* M * (-gamma) */
      gel(v, index) = ZG_add(gel(v, index), M);
      break;
    }

    case 3: /*T32, T32[i] = -T31[i] */
    {
      long T3shift = W11[5] - W11[2]; /* #T32 + #E1 + #T2 */
      index += T3shift;
      index -= shift;
      gel(v, index) = ZG_add(gel(v, index), to_famat_shallow(M,gen_m1));
      break;
    }
    default: /*E1,T2,T31*/
      index -= shift;
      gel(v, index) = ZG_add(gel(v, index), to_famat_shallow(M,gen_1));
      break;
  }
}
static void
treat_index_trivial(GEN v, GEN W, long index)
{
  GEN W11 = gel(W,11);
  long shift = W11[3]; /* #F + #E2 + T32 */
  switch(set_from_index(W11, index))
  {
    case 1: /*F*/
    {
      GEN F_index = gel(W,6), ind = gel(F_index, index);
      long j, l = lg(ind);
      for (j = 1; j < l; j++)
      {
        GEN IND = gel(ind,j);
        treat_index_trivial(v, W, mael(IND,1,1));
      }
      break;
    }

    case 2: /*E2, E2[r] + gamma * E1[s] = 0 */
    {
      long r = index - W11[1];
      GEN E2_in_terms_of_E1= gel(W,7), z = gel(E2_in_terms_of_E1, r);
      long s = itou(gel(z,1));
      index = s;
      gel(v, index) = subiu(gel(v, index), 1);
      break;
    }

    case 3: case 5: case 6: /*T32,T2,T31*/
      break;

    case 4: /*E1*/
      index -= shift;
      gel(v, index) = addiu(gel(v, index), 1);
      break;
  }
}

static GEN
M2_log(GEN W, GEN M)
{
  GEN a = gcoeff(M,1,1), b = gcoeff(M,1,2);
  GEN c = gcoeff(M,2,1), d = gcoeff(M,2,2);
  GEN  u, v, D, V;
  long index, s;

  W = get_ms(W);
  V = zerovec(ms_get_nbgen(W));

  D = subii(mulii(a,d), mulii(b,c));
  s = signe(D);
  if (!s) return V;
  if (is_pm1(D))
  { /* shortcut, not need to apply Manin's trick */
    if (s < 0) {
      b = negi(b);
      d = negi(d);
    }
    M = mkmat2(mkcol2(a,c), mkcol2(b,d));
    M = Gamma0N_decompose(W, M, &index);
    treat_index(W, M, index, V);
  }
  else
  {
    GEN U, B, P, Q, PQ, C1,C2;
    long i, l;
    (void)bezout(a,c,&u,&v);
    B = addii(mulii(b,u), mulii(d,v));
    /* [u,v;-c,a] [a,b; c,d] = [1,B; 0,D], i.e. M = U [1,B;0,D] */
    U = mkmat2(mkcol2(a, c), mkcol2(negi(v),u));

    /* {1/0 -> B/D} as \sum g_i, g_i unimodular paths */
    PQ = ZV_allpnqn( gboundcf(gdiv(B,D), 0) );
    P = gel(PQ,1); l = lg(P);
    Q = gel(PQ,2);
    C1 = gel(U,1);
    for (i = 1; i < l; i++, C1 = C2)
    {
      GEN M;
      C2 = ZM_ZC_mul(U, mkcol2(gel(P,i), gel(Q,i)));
      if (!odd(i)) C1 = ZC_neg(C1);
      M = Gamma0N_decompose(W, mkmat2(C1,C2), &index);
      treat_index(W, M, index, V);
    }
  }
  return V;
}

/* express +oo->q=a/b in terms of the Z[G]-generators, trivial action */
static void
Q_log_trivial(GEN v, GEN W, GEN q)
{
  GEN Q, W3 = gel(W,3), p1N = gel(W,1);
  ulong c,d, N = p1N_get_N(p1N);
  long i, lx;

  Q = Q_log_init(N, q);
  lx = lg(Q);
  c = 0;
  for (i = 1; i < lx; i++, c = d)
  {
    long index;
    d = Q[i];
    if (c && !odd(i)) c = N - c;
    index = W3[ p1_index(c,d,p1N) ];
    treat_index_trivial(v, W, index);
  }
}
static void
M2_log_trivial(GEN V, GEN W, GEN M)
{
  GEN p1N = gel(W,1), W3 = gel(W,3);
  ulong N = p1N_get_N(p1N);
  GEN a = gcoeff(M,1,1), b = gcoeff(M,1,2);
  GEN c = gcoeff(M,2,1), d = gcoeff(M,2,2);
  GEN  u, v, D;
  long index, s;

  D = subii(mulii(a,d), mulii(b,c));
  s = signe(D);
  if (!s) return;
  if (is_pm1(D))
  { /* shortcut, not need to apply Manin's trick */
    if (s < 0) d = negi(d);
    index = W3[ p1_index(umodiu(c,N),umodiu(d,N),p1N) ];
    treat_index_trivial(V, W, index);
  }
  else
  {
    GEN U, B, P, Q, PQ;
    long i, l;
    if (!signe(c)) { Q_log_trivial(V,W,gdiv(b,d)); return; }
    (void)bezout(a,c,&u,&v);
    B = addii(mulii(b,u), mulii(d,v));
    /* [u,v;-c,a] [a,b; c,d] = [1,B; 0,D], i.e. M = U [1,B;0,D] */
    U = mkvec2(c, u);

    /* {1/0 -> B/D} as \sum g_i, g_i unimodular paths */
    PQ = ZV_allpnqn( gboundcf(gdiv(B,D), 0) );
    P = gel(PQ,1); l = lg(P);
    Q = gel(PQ,2);
    for (i = 1; i < l; i++, c = d)
    {
      d = addii(mulii(gel(U,1),gel(P,i)), mulii(gel(U,2),gel(Q,i)));
      if (!odd(i)) c = negi(c);
      index = W3[ p1_index(umodiu(c,N),umodiu(d,N),p1N) ];
      treat_index_trivial(V, W, index);
    }
  }
}

static GEN
cusp_to_ZC(GEN c)
{
  switch(typ(c))
  {
    case t_INFINITY:
      return mkcol2(gen_1,gen_0);
    case t_INT:
      return mkcol2(c,gen_1);
    case t_FRAC:
      return mkcol2(gel(c,1),gel(c,2));
    case t_VECSMALL:
      return mkcol2(stoi(c[1]), stoi(c[2]));
    default:
      pari_err_TYPE("mspathlog",c);
      return NULL;
  }
}
static GEN
path_to_M2(GEN p)
{ return mkmat2(cusp_to_ZC(gel(p,1)), cusp_to_ZC(gel(p,2))); }

/* Expresses path p as \sum x_i g_i, where the g_i are our distinguished
 * generators and x_i \in Z[\Gamma]. Returns [x_1,...,x_n] */
static GEN
mspathlog_i(GEN W, GEN p)
{ return M2_log(W, path_to_M2(p)); }
/* in case the action is trivial: v += mspathlog(path) */
static void
mspathlog_i_trivial(GEN v, GEN W, GEN p)
{ M2_log_trivial(v, W, path_to_M2(p)); }

GEN
mspathlog(GEN W, GEN p)
{
  pari_sp av = avma;
  checkms(W);
  if (lg(p) != 3) pari_err_TYPE("mspathlog",p);
  switch(typ(p))
  {
    case t_MAT:
      RgM_check_ZM(p,"mspathlog");
      break;
    case t_VEC:
      p = path_to_M2(p);
      break;
    default: pari_err_TYPE("mspathlog",p);
  }
  return gerepilecopy(av, M2_log(W, p));
}
static GEN
mspathlog_trivial(GEN W, GEN p)
{
  GEN v;
  W = get_ms(W);
  v = zerovec(ms_get_nbgen(W));
  M2_log_trivial(v, W, path_to_M2(p));
  return v;
}

/** HECKE OPERATORS **/
/* [a,b;c,d] * cusp */
static GEN
cusp_mul(GEN cusp, long a, long b, long c, long d)
{
  long x = cusp[1], y = cusp[2];
  long A = a*x+b*y, B = c*x+d*y, u = cgcd(A,B);
  if (u != 1) { A /= u; B /= u; }
  return mkvecsmall2(A, B);
}
static GEN
path_mul(GEN path, long a, long b, long c, long d)
{
  GEN c1 = cusp_mul(gel(path,1), a,b,c,d);
  GEN c2 = cusp_mul(gel(path,2), a,b,c,d);
  return mkpath(c1,c2);
}
/* f in Gl2(Q), act on path (zm) */
static GEN
Gl2Q_act_path(GEN f, GEN path)
{ return path_mul(path, coeff(f,1,1),coeff(f,1,2),coeff(f,2,1),coeff(f,2,2)); }

static GEN
init_act_trivial(GEN W) { return zerocol(ms_get_nbE1(W)); }

/* map from WW1 -> WW2, weight 2, trivial action. v a Gl2_Q or a t_VEC
 * of Gl2_Q (\sum v[i] in Z[Gl2(Q)]). Return the matrix associated to the
 * action of v. */
static GEN
getMorphism_trivial(GEN WW1, GEN WW2, GEN v)
{
  GEN W1 = get_ms(WW1), W2 = get_ms(WW2);
  GEN section = ms_get_section(W1), gen = gel(W1,5);
  long i, j, lv, nbE1 = ms_get_nbE1(W1);
  GEN T = cgetg(nbE1+1, t_MAT);
  if (typ(v) != t_VEC) v = mkvec(v);
  lv = lg(v);
  for (i = 1; i <= nbE1; i++)
  {
    long e = gen[i]; /* path-index of E1-element */
    GEN w = gel(section, e); /* path_to_zm() */
    GEN t = init_act_trivial(W2);
    for (j = 1; j < lv; j++)
      mspathlog_i_trivial(t, W2, Gl2Q_act_path(gel(v,j), w));
    gel(T,i) = t;
  }
  return T;
}

/* f zm/ZM in Gl_2(Q), acts from the left on Delta, which is generated by
 * (g_i) as Z[Gamma1]-module, and by (G_i) as Z[Gamma2]-module.
 * We have f.G_j = \sum_i \lambda_{i,j} g_i,   \lambda_{i,j} in Z[Gamma1]
 *
 * For phi in Hom_Gamma1(D,V), g in D, phi | f is in Hom_Gamma2(D,V) and
 *  (phi | f)(G_j) = phi(f.G_j) | f
 *                 = phi( \sum_i \lambda_{i,j} g_i ) | f
 *                 = \sum_i phi(g_i) | (\lambda_{i,j}^* f)
 *                 = \sum_i phi(g_i) | \mu_{i,j}
 * Return the \mu_{i,j} matrix as operators on V (t_MAT) */
static GEN
init_dual_act(GEN f, GEN W1, GEN W2)
{
  GEN section = ms_get_section(W2), gen = ms_get_genindex(W2);
  long j, dim = lg(gen)-1, k = msk_get_weight(W1);
  GEN T = cgetg(dim+1, t_MAT), F;
  if (typ(gel(f,1)) == t_VEC)
  {
    F = f;
    f = ZM_to_zm(F);
  }
  else
    F = zm_to_ZM(f);
  /* f zm = F ZM */
  for (j = 1; j <= dim; j++)
  {
    pari_sp av = avma;
    GEN w = gel(section, gen[j]); /* path_to_zm( E1/T2/T3 element ) */
    GEN l = mspathlog_i(W1, Gl2Q_act_path(f, w)); /* lambda_{i,j} */
    l = ZGl2QC_star(l); /* lambda_{i,j}^* */
    l = ZGC_G_mul(l, F); /* mu_{i,j} */
    gel(T,j) = gerepilecopy(av, ZGl2QC_to_act(l, k)); /* as operators on V */
  }
  return T;
}
/* phi in Hom_Gamma1(Delta, V), return the matrix whose colums are the
 *   \sum_i phi(g_i) | \mu_{i,j} = (phi|f)(G_j),
 * see init_dual_act. */
static GEN
dual_act(GEN phi, GEN mu)
{
  long l = lg(mu), a, j;
  GEN ind = gel(phi,2), pols = gel(phi,3);
  GEN v = cgetg(l, t_MAT);
  for (j = 1; j < l; j++)
  {
    GEN T = NULL;
    for (a = 1; a < lg(ind); a++)
    {
      long i = ind[a];
      GEN t = gel(pols, a); /* phi(G_i) */
      t = RgM_RgC_mul(gcoeff(mu,i,j), t);
      T = T? RgC_add(T, t): t;
    }
    gel(v,j) = T;
  }
  return v;
}

/* phi in Hom(Delta, V), phi(G_k) = vecT[k]. Write phi as
 *   \sum_{i,j} mu_{i,j} phi_{i,j}, mu_{i,j} in Q */
static GEN
getMorphism_basis(GEN W, GEN vecT)
{
  GEN basis = msk_get_basis(W);
  long i, j, r, lvecT = lg(vecT), dim = lg(basis)-1;
  GEN st = msk_get_st(W);
  GEN link = msk_get_link(W);
  GEN invphiblock = msk_get_invphiblock(W);
  long s = st[1], t = st[2];
  GEN R = zerocol(dim), Q, Ls, T0, T1, Ts, mu_st;
  for (r = 2; r < lvecT; r++)
  {
    GEN Tr, L;
    if (r == s) continue;
    Tr = gel(vecT,r); /* Phi(G_r), r != 1,s */
    L = gel(link, r);
    Q = ZC_apply_dinv(gel(invphiblock,r), Tr);
    /* write Phi(G_r) as sum_{a,b} mu_{a,b} Phi_{a,b}(G_r) */
    for (j = 1; j < lg(L); j++) gel(R, L[j]) = gel(Q,j);
  }
  Ls = gel(link, s);
  T1 = gel(vecT,1); /* Phi(G_1) */
  gel(R, Ls[t]) = mu_st = gel(T1, 1);

  T0 = NULL;
  for (i = 2; i < lg(link); i++)
  {
    GEN L;
    if (i == s) continue;
    L = gel(link,i);
    for (j =1 ; j < lg(L); j++)
    {
      long n = L[j]; /* phi_{i,j} = basis[n] */
      GEN mu_ij = gel(R, n);
      GEN phi_ij = gel(basis, n), pols = gel(phi_ij,3);
      GEN z = RgC_Rg_mul(gel(pols, 3), mu_ij);
      T0 = T0? RgC_add(T0, z): z; /* += mu_{i,j} Phi_{i,j} (G_s) */
    }
  }
  Ts = gel(vecT,s); /* Phi(G_s) */
  if (T0) Ts = RgC_sub(Ts, T0);
  /* solve \sum_{j!=t} mu_{s,j} Phi_{s,j}(G_s) = Ts */
  Q = ZC_apply_dinv(gel(invphiblock,s), Ts);
  for (j = 1; j < t; j++) gel(R, Ls[j]) = gel(Q,j);
  /* avoid mu_{s,t} */
  for (j = t; j < lg(Q); j++) gel(R, Ls[j+1]) = gel(Q,j);
  return R;
}

/* a = s(g_i) for some modular symbol s; b in Z[G]
 * return s(b.g_i) = b^* . s(g_i) */
static GEN
ZGl2Q_act_s(GEN b, GEN a, long k)
{
  if (typ(b) == t_INT)
  {
    if (!signe(b)) return gen_0;
    switch(typ(a))
    {
      case t_POL:
        a = RgX_to_RgC(a, k-1); /*fall through*/
      case t_COL:
        a = RgC_Rg_mul(a,b);
        break;
      default: a = scalarcol_shallow(b,k-1);
    }
  }
  else
  {
    b = RgX_act_ZGl2Q(ZGl2Q_star(b), k);
    switch(typ(a))
    {
      case t_POL:
        a = RgX_to_RgC(a, k-1); /*fall through*/
      case t_COL:
        a = RgM_RgC_mul(b,a);
        break;
      default: a = RgC_Rg_mul(gel(b,1),a);
    }
  }
  return a;
}

static int
checksymbol(GEN W, GEN s)
{
  GEN t, annT2, annT31, singlerel;
  long i, k, l, nbE1, nbT2, nbT31;
  k = msk_get_weight(W);
  W = get_ms(W);
  nbE1 = ms_get_nbE1(W);
  singlerel = gel(W,10);
  l = lg(singlerel);
  if (k == 2)
  {
    for (i = nbE1+1; i < l; i++)
      if (!gequal0(gel(s,i))) return 0;
    return 1;
  }
  annT2 = gel(W,8); nbT2 = lg(annT2)-1;
  annT31 = gel(W,9);nbT31 = lg(annT31)-1;
  t = NULL;
  for (i = 1; i < l; i++)
  {
    GEN a = gel(s,i);
    a = ZGl2Q_act_s(gel(singlerel,i), a, k);
    t = t? gadd(t, a): a;
  }
  if (!gcmp0(t)) return 0;
  for (i = 1; i <= nbT2; i++)
  {
    GEN a = gel(s,i + nbE1);
    a = ZGl2Q_act_s(gel(annT2,i), a, k);
    if (!gcmp0(a)) return 0;
  }
  for (i = 1; i <= nbT31; i++)
  {
    GEN a = gel(s,i + nbE1 + nbT2);
    a = ZGl2Q_act_s(gel(annT31,i), a, k);
    if (!gcmp0(a)) return 0;
  }
  return 1;
}
long
msissymbol(GEN W, GEN s)
{
  long k, nbgen;
  checkms(W);
  k = msk_get_weight(W);
  nbgen = ms_get_nbgen(W);
  switch(typ(s))
  {
    case t_VEC: /* values s(g_i) */
      if (lg(s)-1 != nbgen) return 0;
      break;
    case t_COL:
      if (k == 2) /* on the dual basis of (g_i) */
      {
        if (lg(s)-1 != nbgen) return 0;
      }
      else
      {
        GEN basis = msk_get_basis(W);
        return (lg(s) == lg(basis));
      }
      break;
    default: return 0;
  }
  return checksymbol(W,s);
}
#if DEBUG
/* phi_i(G_j) */
static GEN
eval_phii_Gj(GEN W, long i, long j)
{
  GEN basis = msk_get_basis(W), b = gel(basis,i);
  GEN ind = gel(b,2), pols = gel(b,3);
  long s;
  for (s = 1; s < lg(ind); s++)
    if (ind[s] == j) return gel(pols,s);
  return zerocol(lg(gel(pols,1))-1);
}
/* check that \sum d_i phi_i(G_j)  = T_j for all j */
static void
checkdec(GEN W, GEN D, GEN T)
{
  long i, j;
  if (!checksymbol(W,T)) pari_err_BUG("checkdec");
  for (j = 1; j < lg(T); j++)
  {
    GEN S = gen_0;
    for (i = 1; i < lg(D); i++)
    {
      GEN d = gel(D,i);
      if (gcmp0(d)) continue;
      S = gadd(S, gmul(d, eval_phii_Gj(W, i, j)));
    }
    /* S = \sum_i d_i phi_i(G_j) */
    if (!gequal(S, gel(T,j)))
      pari_warn(warner, "checkdec j = %ld\n\tS = %Ps\n\tT = %Ps", j,S,gel(T,j));
  }
}
#endif

/* map op: Hom(W1,V) -> Hom(W2,V), given by \sum v[i], v[i] in Gl2(Q) */
static GEN
getMorphism(GEN W1, GEN W2, GEN v)
{
  GEN basis1 = msk_get_basis(W1);
  long i, a, lv, dim1 = lg(basis1)-1;
  GEN M = cgetg(dim1+1, t_MAT), act;
  if (typ(v) != t_VEC) v = mkvec(v);
  lv = lg(v); act = cgetg(lv, t_MAT);
  for (i = 1; i < lv; i++) gel(act,i) = init_dual_act(gel(v,i), W1, W2);
  for (a = 1; a <= dim1; a++)
  {
    pari_sp av = avma;
    GEN phi = gel(basis1, a), D, T = NULL;
    for (i = 1; i < lv; i++)
    {
      GEN t = dual_act(phi, gel(act, i));
      T = T? gerepileupto(av, RgM_add(T,t)): t;
    }
    /* T = (phi|op)(G_1,...,G_d2) */
    D = getMorphism_basis(W2, T);
#if DEBUG
    checkdec(W2,D,T);
#endif
    gel(M,a) = gerepilecopy(av, D);
  }
  return M;
}

static GEN
Tp_matrices(ulong p)
{
  GEN v = cgetg(p+2, t_VEC);
  ulong i;
  for (i = 1; i <= p; i++) gel(v,i) = mat2(1, i-1, 0, p);
  gel(v,i) = mat2(p, 0, 0, 1);
  return v;
}
static GEN
Up_matrices(ulong p)
{
  GEN v = cgetg(p+1, t_VEC);
  ulong i;
  for (i = 1; i <= p; i++) gel(v,i) = mat2(1, i-1, 0, p);
  return v;
}
static GEN
msendo(GEN W, GEN v)
{
  return msk_get_weight(W) == 2? getMorphism_trivial(W,W,v)
                               : getMorphism(W, W, v);
}
static GEN
endo_project(GEN W, GEN e, GEN H)
{
  if (H) H = Qevproj_init0(H);
  else if (msk_get_sign(W))
    H = msk_get_starproj(W);
  if (H) e = Qevproj_apply(e, H);
  return e;
}
static GEN
mshecke_i(GEN W, ulong p)
{
  GEN v = ms_get_N(W) % p? Tp_matrices(p): Up_matrices(p);
  return msendo(W,v);
}
GEN
mshecke(GEN W, long p, GEN H)
{
  pari_sp av = avma;
  GEN T;
  checkms(W);
  if (p <= 1) pari_err_PRIME("mshecke",stoi(p));
  T = mshecke_i(W,p);
  T = endo_project(W,T,H);
  if (msk_get_weight(W) == 2) T = shallowtrans(T);
  return gerepilecopy(av, T);
}

static GEN
msatkinlehner_i(GEN W, long Q)
{
  long w, z, d, N = ms_get_N(W), M = N / Q;
  GEN v;
  if (Q == 1) return matid(msk_get_dim(W));
  d = cbezout(Q, -M, &w, &z);
  if (N % Q) pari_err_DOMAIN("msatkinlehner","N % Q","!=",gen_0,stoi(Q));
  if (d != 1) pari_err_DOMAIN("msatkinlehner","gcd(Q,N/Q)","!=",gen_1,stoi(Q));
  v = (Q == N)? mat2(0,1,-N,0): mat2(Q,1,N*z,Q*w);
  return msendo(W,v);
}
GEN
msatkinlehner(GEN W, long Q, GEN H)
{
  pari_sp av = avma;
  GEN w;
  long k;
  checkms(W);
  k = msk_get_weight(W);
  if (Q <= 0) pari_err_DOMAIN("msatkinlehner","Q","<=",gen_0,stoi(Q));
  w = msatkinlehner_i(W,Q);
  w = endo_project(W,w,H);
  if (k == 2) w = shallowtrans(w);
  else if (Q != 1)
    w = RgM_Rg_div(w, powuu(Q,(k-2)>>1));
  return gerepilecopy(av, w);
}

static GEN
msstar_i(GEN W)
{
  GEN v = mat2(-1,0,0,1);
  return msendo(W,v);
}
GEN
msstar(GEN W, GEN H)
{
  pari_sp av = avma;
  GEN s;
  checkms(W);
  s = msstar_i(W);
  s = endo_project(W,s,H);
  if (msk_get_weight(W) == 2) s = shallowtrans(s);
  return gerepilecopy(av, s);
}

#if 0
/* is \Gamma_0(N) cusp1 = \Gamma_0(N) cusp2 ? */
static int
iscuspeq(ulong N, GEN cusp1, GEN cusp2)
{
  long p1, q1, p2, q2, s1, s2, d;
  p1 = cusp1[1]; p2 = cusp2[1];
  q1 = cusp1[2]; q2 = cusp2[2];
  d = Fl_mul(smodss(q1,N),smodss(q2,N), N);
  d = ugcd(d, N);

  s1 = q1 > 2? Fl_inv(smodss(p1,q1), q1): 1;
  s2 = q2 > 2? Fl_inv(smodss(p2,q2), q2): 1;
  return Fl_mul(s1,q2,d) == Fl_mul(s2,q1,d);
}
#endif

static GEN
mscuspidal_trivial(GEN W0)
{
  pari_sp av = avma;
  GEN W = get_ms(W0);
  GEN section = ms_get_section(W), gen = ms_get_genindex(W);
  GEN S = ms_get_hashcusps(W);
  long j, nbE1 = ms_get_nbE1(W), ncusp = gel(S,1)[2];
  GEN T = zeromatcopy(ncusp,nbE1);
  for (j = 1; j <= nbE1; j++)
  {
    long e = gen[j]; /* path-index of E1-element */
    GEN t = gel(section, e); /* path_to_zm() */
    long i1 = cusp_index(gel(t,1), S);
    long i2 = cusp_index(gel(t,2), S);
    if (i1 != i2)
    {
      gcoeff(T, i1, j) = gen_1;
      gcoeff(T, i2, j) = gen_m1;
    }
  }
  return gerepilecopy(av, ZM_ker(T));
}

/* return E_c(r) */
static GEN
get_Ec_r(GEN c, long k)
{
  long p = c[1], q = c[2], u, v;
  GEN gr;
  (void)cbezout(p, q, &u, &v);
  gr = mat2(p, -v, q, u); /* g . (1:0) = (p:q) */
  return voo_act_Gl2Q(zm_to_ZM(sl2_inv(gr)), k);
}
/* returns the modular symbol associated to the cusp c := p/q via the rule
 * E_c(path from a to b in Delta_0) := E_c(b) - E_c(a), where
 * E_c(r) := 0 if r != c mod Gamma
 *           v_oo | gamma_r^(-1)
 * where v_oo is stable by T = [1,1;0,1] (i.e x^(k-2)) and
 * gamma_r . (1:0) = r, for some gamma_r in SL_2(Z) * */
GEN
Eisenstein_symbol(GEN W, GEN c)
{
  GEN section = ms_get_section(W), gen = ms_get_genindex(W);
  GEN S = ms_get_hashcusps(W);
  long j, ic = cusp_index(c, S), l = lg(gen), k = msk_get_weight(W);
  GEN vecT = cgetg(l, t_COL);
  for (j = 1; j < l; j++)
  {
    GEN vj = NULL, g = gel(section, gen[j]); /* path_to_zm(generator) */
    GEN c1 = gel(g,1), c2 = gel(g,2);
    long i1 = cusp_index(c1, S);
    long i2 = cusp_index(c2, S);
    if (i1 == ic) vj = get_Ec_r(c1, k);
    if (i2 == ic)
    {
      GEN s = get_Ec_r(c2, k);
      vj = vj? gsub(vj, s): gneg(s);
    }
    if (!vj) vj = zerocol(k-1);
    gel(vecT, j) = vj;
  }
  return getMorphism_basis(W, vecT);
}

static GEN
EC_subspace_trivial(GEN W)
{
  GEN M, ch, chC, chE, T, TC, C = mscuspidal_trivial(W);
  long N = ms_get_N(W);
  ulong p;
  forprime_t S;
  (void)u_forprime_init(&S, 2, ULONG_MAX);
  while ((p = u_forprime_next(&S)))
    if (N % p) break;
  T = mshecke_i(W, p);
  ch = QM_charpoly_ZX(T);
  TC = Qevproj_apply(T, Qevproj_init(C)); /* T_p | TC */
  chC = QM_charpoly_ZX(TC);
  chE = RgX_div(ch, chC); /* charpoly(T_p | E_k), coprime to chC */
  M = RgX_RgM_eval(chE, T);
  return mkvec2(Qevproj_star(W, QM_ker(M)), C);
}

static GEN
mseisenstein_trivial(GEN W)
{
  GEN ES = EC_subspace_trivial(W);
  return gel(ES,1);
}
static GEN
mseisenstein_i(GEN W)
{
  GEN S, cusps, M;
  long i, l;
  if (msk_get_weight(W) == 2) return mseisenstein_trivial(W);
  S = ms_get_hashcusps(W);
  cusps = gel(S,3);
  l = lg(cusps);
  M = cgetg(l, t_MAT);
  for (i = 1; i < l; i++) gel(M,i) = Eisenstein_symbol(W, gel(cusps,i));
  return Qevproj_star(W, QM_image(M));
}
GEN
mseisenstein(GEN W)
{
  pari_sp av = avma;
  checkms(W);
  return gerepilecopy(av, Qevproj_init(mseisenstein_i(W)));
}

/* upper bound for log_2 |charpoly(T_p|S)|, where S is a cuspidal subspace of
 * dimension d, k is the weight */
static long
TpS_char_bound(ulong p, long k, long d)
{ /* |eigenvalue| <= 2 p^(k-1)/2 */
  return d * (2 + (log2((double)p)*(k-1))/2);
}

/* return [E,S] */
static GEN
mscuspidal_i(GEN W)
{
  GEN E, M, T, TE, chS;
  long k = msk_get_weight(W), bit;
  forprime_t S;
  ulong p, N;
  if (k == 2) return EC_subspace_trivial(W);
  E = mseisenstein_i(W);
  N = ms_get_N(W);
  (void)u_forprime_init(&S, 2, ULONG_MAX);
  while ((p = u_forprime_next(&S)))
    if (N % p) break;
  T = mshecke_i(W, p);
  TE = Qevproj_apply(T, Qevproj_init(E)); /* T_p | E */
  bit = TpS_char_bound(p, k, msk_get_dim(W) - (lg(TE)-1));
  chS = QM_charpoly_ZX2_bound(T,TE,bit); /* charpoly(T_p | S_k) */
  M = RgX_RgM_eval(chS, T);
  return mkvec2(E, Qevproj_star(W, QM_ker(M)));
}
GEN
mscuspidal(GEN W, long flag)
{
  pari_sp av = avma;
  GEN v, S, E;
  checkms(W);
  v = mscuspidal_i(W);
  E = gel(v,1);
  S = gel(v,2); S = Qevproj_init(S);
  if (flag)
  { /* swap arguments to return [S,E] */
    E = Qevproj_init(E);
    v = mkvec2(S,E);
  }
  else
    v = S;
  return gerepilecopy(av, v);
}

/** INIT ELLSYM STRUCTURE **/
/* V a vector of ZM. If all of them have 0 last row, return NULL.
 * Otherwise return [m,i,j], where m = V[i][last,j] contains the value
 * of smallest absolute value */
static GEN
RgMV_find_non_zero_last_row(long offset, GEN V)
{
  long i, lasti = 0, lastj = 0, lV = lg(V);
  GEN m = NULL;
  for (i = 1; i < lV; i++)
  {
    GEN M = gel(V,i);
    long j, n, l = lg(M);
    if (l == 1) continue;
    n = nbrows(M);
    for (j = 1; j < l; j++)
    {
      GEN a = gcoeff(M, n, j);
      if (!gcmp0(a) && (!m || absi_cmp(a, m) < 0))
      {
        m = a; lasti = i; lastj = j;
        if (is_pm1(m)) goto END;
      }
    }
  }
END:
  if (!m) return NULL;
  return mkvec2(m, mkvecsmall2(lasti+offset, lastj));
}
/* invert the d_oo := (\gamma_oo - 1) operator, acting on
 * [x^(k-2), ..., y^(k-2)] */
static GEN
Delta_inv(GEN doo, long k)
{
  GEN M = RgX_act_ZGl2Q(doo, k);
  M = RgM_minor(M, k-1, 1); /* 1st column and last row are 0 */
  return ZM_inv_denom(M);
}
/* The ZX P = \sum a_i x^i y^{k-2-i} is given by the ZV [a_0, ..., a_k-2]~,
 * return Q and d such that P = doo Q + d y^k-2, where d in Z and Q */
static GEN
doo_decompose(GEN dinv, GEN P, GEN *pd)
{
  long l = lg(P); *pd = gel(P, l-1);
  P = vecslice(P, 1, l-2);
  return shallowconcat(gen_0, ZC_apply_dinv(dinv, P));
}

static GEN
get_phi_ij(long i,long j,long n, long s,long t,GEN P_st,GEN Q_st,GEN d_st,
           GEN P_ij, GEN lP_ij, GEN dinv)
{
  GEN ind, pols;
  if (i == s && j == t)
  {
    ind = mkvecsmall(1);
    pols = mkvec(scalarcol_shallow(gen_1, lg(P_st)-1)); /* x^{k-2} */
  }
  else
  {
    GEN d_ij, Q_ij = doo_decompose(dinv, lP_ij, &d_ij);
    GEN a = ZC_Z_mul(P_ij, d_st);
    GEN b = ZC_Z_mul(P_st, negi(d_ij));
    GEN c = RgC_sub(RgC_Rg_mul(Q_ij, d_st), RgC_Rg_mul(Q_st, d_ij));
    if (i == s) { /* j != t */
      ind = mkvecsmall2(1, s);
      pols = mkvec2(c, ZC_add(a, b));
    } else {
      ind = mkvecsmall3(1, i, s);
      pols = mkvec3(c, a, b); /* image of g_1, g_i, g_s */
    }
  }
  return mkvec3(mkvecsmall3(i,j,n), ind, pols);
}

static GEN
mskinit_trivial(GEN WN)
{
  long dim = ms_get_nbE1(WN);
  return mkvec3(WN, gen_0, mkvec2(gen_0,mkvecsmall2(2, dim)));
}
/* sum of #cols of the matrices contained in V */
static long
RgMV_dim(GEN V)
{
  long l = lg(V), d = 0, i;
  for (i = 1; i < l; i++) d += lg(gel(V,i)) - 1;
  return d;
}
static GEN
mskinit_nontrivial(GEN WN, long k)
{
  GEN annT2 = gel(WN,8), annT31 = gel(WN,9), singlerel = gel(WN,10);
  GEN link, basis, monomials, invphiblock;
  long nbE1 = ms_get_nbE1(WN);
  GEN dinv = Delta_inv(ZG_neg( ZGl2Q_star(gel(singlerel,1)) ), k);
  GEN p1 = cgetg(nbE1+1, t_VEC), remove;
  GEN p2 = ZGV_tors(annT2, k);
  GEN p3 = ZGV_tors(annT31, k);
  GEN gentor = shallowconcat(p2, p3);
  GEN P_st, lP_st, Q_st, d_st;
  long n, i, dim, s, t, u;
  gel(p1, 1) = cgetg(1,t_MAT); /* dummy */
  for (i = 2; i <= nbE1; i++) /* skip 1st element = (\gamma_oo-1)g_oo */
  {
    GEN z = gel(singlerel, i);
    gel(p1, i) = RgX_act_ZGl2Q(ZGl2Q_star(z), k);
  }
  remove = RgMV_find_non_zero_last_row(nbE1, gentor);
  if (!remove) remove = RgMV_find_non_zero_last_row(0, p1);
  if (!remove) pari_err_BUG("msinit [no y^k-2]");
  remove = gel(remove,2); /* [s,t] */
  s = remove[1];
  t = remove[2];
  /* +1 because of = x^(k-2), but -1 because of Manin relation */
  dim = (k-1)*(nbE1-1) + RgMV_dim(p2) + RgMV_dim(p3);
  /* Let (g_1,...,g_d) be the Gamma-generators of Delta, g_1 = g_oo.
   * We describe modular symbols by the collection phi(g_1), ..., phi(g_d)
   * \in V := Q[x,y]_{k-2}, with right Gamma action.
   * For each i = 1, .., d, let V_i \subset V be the Q-vector space of
   * allowed values for phi(g_i): with basis (P^{i,j}) given by the monomials
   * x^(j-1) y^{k-2-(j-1)}, j = 1 .. k-1
   * (g_i in E_1) or the solution of the torsion equations (1 + gamma)P = 0
   * (g_i in T2) or (1 + gamma + gamma^2)P = 0 (g_i in T31).
   *
   * The Manin relation (singlerel) is of the form \sum_i \lambda_i g_i = 0,
   * where \lambda_i = 1 if g_i in T2 or T31, and \lambda_i = (1 - \gamma_i)
   * for g_i in E1.
   *
   * If phi \in Hom_Gamma(Delta, V), it is defined by phi(g_i) := P_i in V
   * with \sum_i P_i . \lambda_i^* = 0, where (\sum n_i g_i)^* :=
   * \sum n_i \gamma_i^(-1).
   *
   * We single out gamma_1 / g_1 (g_oo in Pollack-Stevens paper) and
   * write P_{i,j} \lambda_i^* =  Q_{i,j} (\gamma_1 - 1)^* + d_{i,j} y^{k-2}
   * where d_{i,j} is a scalar and Q_{i,j} in V; we normalize Q_{i,j} to
   * that the coefficient of x^{k-2} is 0.
   *
   * There exist (s,t) such that d_{s,t} != 0.
   * A Q-basis of the (dual) space of modular symbols is given by the
   * functions phi_{i,j}, 2 <= i <= d, 1 <= j <= k-1, mapping
   *  g_1 -> d_{s,t} Q_{i,j} - d_{i,j} Q_{s,t} + [(i,j)=(s,t)] x^{k-2}
   * If i != s
   *   g_i -> d_{s,t} P_{i,j}
   *   g_s -> - d_{i,j} P_{s,t}
   * If i = s, j != t
   *   g_i -> d_{s,t} P_{i,j} - d_{i,j} P_{s,t}
   * And everything else to 0. */
  monomials = matid(k-1); /* represent the monomials x^{k-2}, ... , y^{k-2} */
  if (s <= nbE1) /* in E1 */
  {
    P_st = gel(monomials, t);
    lP_st = gmael(p1, s, t); /* P_{s,t} lambda_s^* */
  }
  else /* in T2, T31 */
  {
    P_st = gmael(gentor, s - nbE1, t);
    lP_st = P_st;
  }
  Q_st = doo_decompose(dinv, lP_st, &d_st);
  basis = cgetg(dim+1, t_VEC);
  link = cgetg(nbE1 + lg(gentor), t_VEC);
  gel(link,1) = cgetg(1,t_VECSMALL); /* dummy */
  n = 1;
  for (i = 2; i <= nbE1; i++)
  {
    GEN L = cgetg(k, t_VECSMALL);
    long j;
    /* link[i][j] = n gives correspondance between phi_{i,j} and basis[n] */
    gel(link,i) = L;
    for (j = 1; j < k; j++)
    {
      GEN lP_ij = gmael(p1, i, j); /* P_{i,j} lambda_i^* */
      GEN P_ij = gel(monomials,j);
      L[j] = n;
      gel(basis, n) = get_phi_ij(i,j,n, s,t, P_st, Q_st, d_st, P_ij, lP_ij, dinv);
      n++;
    }
  }
  for (u = 1; u < lg(gentor); u++,i++)
  {
    GEN V = gel(gentor,u);
    long j, lV = lg(V);
    GEN L = cgetg(lV, t_VECSMALL);
    gel(link,i) = L;
    for (j = 1; j < lV; j++)
    {
      GEN lP_ij = gel(V, j); /* P_{i,j} lambda_i^* = P_{i,j} */
      GEN P_ij = lP_ij;
      L[j] = n;
      gel(basis, n) = get_phi_ij(i,j,n, s,t, P_st, Q_st, d_st, P_ij, lP_ij, dinv);
      n++;
    }
  }
  invphiblock = cgetg(lg(link), t_VEC);
  gel(invphiblock,1) = cgetg(1, t_MAT); /* dummy */
  for (i = 2; i < lg(link); i++)
  {
    GEN M, inv, B = gel(link,i);
    long j, lB = lg(B);
    if (i == s) { B = vecsplice(B, t); lB--; } /* remove phi_st */
    M = cgetg(lB, t_MAT);
    for (j = 1; j < lB; j++)
    {
      GEN phi_ij = gel(basis, B[j]), pols = gel(phi_ij,3);
      gel(M, j) = gel(pols, 2); /* phi_ij(g_i) */
    }
    if (i <= nbE1 && i != s) /* maximal rank k-1 */
      inv = ZM_inv_denom(M);
    else /* i = s (rank k-2) or from torsion: rank k/3 or k/2 */
      inv = Qevproj_init(M);
    gel(invphiblock,i) = inv;
  }
  return mkvec3(WN, gen_0, mkvec5(basis, mkvecsmall2(k, dim), mkvecsmall2(s,t),
                                  link, invphiblock));
}
static GEN
add_star(GEN W, long sign)
{
  GEN s = msstar_i(W);
  GEN K = sign? QM_ker(gsubgs(s, sign)): cgetg(1,t_MAT);
  gel(W,2) = mkvec3(stoi(sign), s, Qevproj_init(K));
  return W;
}
/* WN = msinit_N(N) */
static GEN
mskinit(ulong N, long k, long sign)
{
  GEN WN = msinit_N(N);
  GEN W = k == 2? mskinit_trivial(WN)
                : mskinit_nontrivial(WN, k);
  return add_star(W, sign);
}
GEN
msinit(GEN N, GEN K, long sign)
{
  pari_sp av = avma;
  GEN W;
  long k;
  if (typ(N) != t_INT) pari_err_TYPE("msinit", N);
  if (typ(K) != t_INT) pari_err_TYPE("msinit", K);
  k = itos(K);
  if (k < 2) pari_err_DOMAIN("msinit","k", "<", gen_2,K);
  if (odd(k)) pari_err_IMPL("msinit [odd weight]");
  if (signe(N) <= 0) pari_err_DOMAIN("msinit","N", "<=", gen_0,N);
  if (equali1(N)) pari_err_IMPL("msinit [ N = 1 ]");
  W = mskinit(itou(N), k, sign);
  return gerepilecopy(av, W);
}

/* W = msinit, xpm modular symbol attached to elliptic curve E;
 * c t_FRAC; image of <oo->c> */
GEN
Q_xpm(GEN W, GEN xpm, GEN c)
{
  pari_sp av = avma;
  GEN v;
  W = get_ms(W);
  v = init_act_trivial(W);
  Q_log_trivial(v, W, c); /* oo -> (a:b), c = a/b */
  return gerepileuptoint(av, RgV_dotproduct(xpm,v));
}

/* Evaluate symbol s on mspathlog B (= sum p_i g_i, p_i in Z[G]) */
static GEN
mseval_by_values(GEN W, GEN s, GEN p)
{
  long i, l, k = msk_get_weight(W);
  GEN A, B;

  if (k == 2)
  { /* trivial represention: don't bother with Z[G] */
    B = mspathlog_trivial(W,p);
    return RgV_dotproduct(s,B);
  }

  A = cgetg_copy(s,&l);
  B = mspathlog(W,p);
  for (i=1; i<l; i++) gel(A,i) = ZGl2Q_act_s(gel(B,i), gel(s,i), k);
  return RgV_sum(A);
}
/* evaluate symbol s on path p */
GEN
mseval(GEN W, GEN s, GEN p)
{
  pari_sp av = avma;
  long i, k, l, nbgen, v = 0;
  GEN e;
  checkms(W);
  k = msk_get_weight(W);
  nbgen = ms_get_nbgen(W);
  switch(typ(s))
  {
    case t_VEC: /* values s(g_i) */
      if (lg(s)-1 != nbgen) pari_err_TYPE("mseval",s);
      if (!p) return gcopy(s);
      v = gvar(s);
      break;
    case t_COL:
      if (k == 2) /* on the dual basis of (g_i) */
      {
        if (lg(s)-1 != ms_get_nbE1(W)) pari_err_TYPE("mseval",s);
        if (!p) return gtrans(s);
      }
      else
      { /* on the basis phi_{i,j} */
        GEN basis = msk_get_basis(W);
        l = lg(basis);
        if (lg(s) != l) pari_err_TYPE("mseval",s);
        e = const_vec(nbgen, gen_0);
        for (i=1; i<l; i++)
        {
          GEN phi, ind, pols, c = gel(s,i);
          long j, m;
          if (gequal0(c)) continue;
          phi = gel(basis,i);
          ind = gel(phi,2); m = lg(ind);
          pols = gel(phi,3);
          for (j=1; j<m; j++) {
            long t = ind[j];
            gel(e,t) = gadd(gel(e,t), gmul(c, gel(pols,j)));
          }
        }
        s = e;
      }
      break;
    default: pari_err_TYPE("mseval",s);
  }
  if (p)
  {
    s = mseval_by_values(W,s,p);
    if (k != 2 && is_vec_t(typ(s))) s = RgV_to_RgX(s, v);
  }
  else
  {
    l = lg(s);
    for (i = 1; i < l; i++)
    {
      GEN c = gel(s,i);
      if (!isintzero(c)) gel(s,i) = RgV_to_RgX(gel(s,i), v);
    }
  }
  return gerepilecopy(av, s);
}

static GEN
twistcurve(GEN e, GEN D)
{
  GEN D2 = sqri(D);
  GEN a4 = mulii(mulsi(-27, D2), ell_get_c4(e));
  GEN a6 = mulii(mulsi(-54, mulii(D, D2)), ell_get_c6(e));
  return ellinit(mkvec2(a4,a6),NULL,DEFAULTPREC);
}

/* sum_{a <= |D|} (D/a)*xpm(E,a/|D|) */
static GEN
get_X(GEN W, GEN xpm, long D)
{
  ulong a, d = (ulong)labs(D);
  GEN t = gen_0;
  GEN nc, c;
  if (d == 1) return Q_xpm(W, xpm, gen_0);
  nc = icopy(gen_1);
  c = mkfrac(nc, utoipos(d));
  for (a=1; a < d; a++)
  {
    long s = kross(D,a);
    GEN x;
    if (!s) continue;
    nc[2] = a; x = Q_xpm(W, xpm, c);
    t = (s > 0)? addii(t, x): subii(t, x);
  }
  return t;
}
/* quotient of the Neron periods of E^(d) and E, divided by sqrt(d) */
static long
get_alpha_d(GEN E, long d)
{
  if (odd(d)) return 1;
  if (!mpodd(ell_get_c4(E))) return 2; /* additive reduction at 2 */
  /* reduction not additive */
  return (d % 8 == 0 && !mpodd(ell_get_a1(E)))? 2: 1;
}
/* write L(E,1) = Q*w1, return the rational Q */
static GEN
get_Q(GEN E)
{
  GEN L, N, tam, T, n, w1;
  long ex, t, t2;
  E = ellanal_globalred_all(E, NULL, &N, &tam);
  T = elltors(E); t = itos(gel(T,1)); t2 = t*t;
  w1 = gel(ellR_omega(E,DEFAULTPREC), 1);

  /* |Sha| = n^2 */
  L = ellL1(E, 0, DEFAULTPREC);
  n = sqrtr(divrr(mulru(L, t2), mulri(w1,tam)));
  n = grndtoi(n, &ex);
  if (ex > -5) pari_err_BUG("msfromell (can't compute analytic |Sha|)");
  return gdivgs(mulii(tam,sqri(n)), t2);
}

/* return C such that C*L(E,1)_{xpm} = L(E,1) / w1 */
static GEN
ell_get_scale(GEN E, GEN W, GEN xpm, long s)
{
  GEN Q, X = NULL;
  long d, N = ms_get_N(W);

  /* find D = s*d such that twist by D has rank 0 */
  for (d = 1; d < LONG_MAX; d++)
  {
    pari_sp av = avma;
    if (cgcd(N, d) != 1) continue;
    if (s < 0)
    { if (!unegisfundamental(d)) continue; }
    else
    { if (!uposisfundamental(d)) continue; }
    X = get_X(W, xpm, s < 0? -d: d);
    if (signe(X)) break;
    avma = av;
  }
  if (d == LONG_MAX) pari_err_BUG("msfromell (no suitable twist)");
  if (s < 0) d = -d;
  Q = get_Q(twistcurve(E, stoi(d)));
  return gdiv(gmulsg(get_alpha_d(E,d), Q), X);
}

GEN
msfromell(GEN E, long sign)
{
  pari_sp av = avma;
  GEN cond;
  GEN W, K, x, scale;
  ulong p, N;
  forprime_t T;

  if (labs(sign) != 1)
    pari_err_DOMAIN("msfromell","abs(sign)","!=",gen_1,stoi(sign));
  E = ellminimalmodel(E, NULL);
  cond = gel(ellglobalred(E), 1);
  N = itou(cond);
  W = mskinit(N, 2, sign);
  /* linear form = 0 on Im(S - sign) */
  K = keri(shallowtrans(gsubgs(msk_get_star(W), sign)));

  /* loop for p <= count_Manin_symbols(N) / 6 would be enough */
  (void)u_forprime_init(&T, 2, ULONG_MAX);
  while( (p = u_forprime_next(&T)) )
  {
    GEN Tp, ap, M, K2;
    if (N % p == 0) continue;
    Tp = mshecke_i(W, p);
    ap = ellap(E, utoipos(p));
    M = RgM_Rg_add_shallow(Tp, negi(ap));
    K2 = keri( ZM_mul(shallowtrans(M), K) );
    if (lg(K2) < lg(K)) K = ZM_mul(K, K2);
    if (lg(K2)-1 == 1) break;
  }
  if (!p) pari_err_BUG("msfromell: ran out of primes");
  /* linear form = 0 on all Im(Tp - ap) and Im(S - sign) */
  x = Q_primpart(gel(K,1));
  scale = ell_get_scale(E, W, x, sign);
  gmael(W,2,1) = gen_0;
  gmael(W,2,3) = Qevproj_init(cgetg(1,t_MAT));
  return gerepilecopy(av, mkvec2(W, RgC_Rg_mul(x, scale)));
}
