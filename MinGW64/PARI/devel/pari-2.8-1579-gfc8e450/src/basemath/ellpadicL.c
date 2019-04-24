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

/** Batch p-adic logarithms **/

/* a/b mod q */
static GEN
divmodulo(GEN a, ulong b, ulong p, GEN q)
{
  long v = u_lvalrem(b, p, &b);
  if (v) a = divis(a, upowuu(p,v));
  /* a/b is now a p-integer */
  return Fp_div(a, utoipos(b), q);
}

/* to compute log_p(a) mod q = p^n, p < 2^31 */
static GEN
initQplog(long p, GEN q, long n)
{
  long i, nn, nt;
  GEN a, C;
  for(nn = n, nt = n + 1; nn >= p; nn /= p) nt++;
  if (p == 2)
    while(3 * (nt - 1) > u_lval(nt-1, p) + n) nt--;
  else
    while(nt > u_lval(nt-1, p) + n) nt--;

  C = cgetg(nt, t_VEC);
  /* [ (-1)^k-1 p^k / (k*(p-1)) ] k=1..nt
   * [ (-1)^k-1 2^3k / (2*k) ]    k=1..nt if p = 2*/
  for(i = 1, a = utoipos(p); i < nt; i++, a = mulis(a, -p))
    gel(C,i) = divmodulo(a, i * (p==2? 2: p-1), p, q);
  return C;
}

/* compute log_p(a), 'a' a p-unit, C = initQplog(p,q,n), q = p^n */
static GEN
logp(GEN C, GEN a, ulong p, GEN q)
{
  long i, nt = lg(C);
  ulong av = avma;
  GEN b, res;

  if (p == 2)
    b = Fp_sqr(modii(a,q), q);
  else
    b = Fp_powu(a, p-1, q);
  /* now b = 1 mod p, compute (b-1) / p = euclidean quotient */
  b = divis(b, p);
  res = Fp_mul(b, gel(C,nt-1), q);
  for(i = nt-2; i > 0; i--)
    res = Fp_mul(addii(res, gel(C,i)), b, q);
  return gerepileuptoint(av, res);
}

/** p-adic L function **/

/* W an msinit, xpm the normalized modylar symbol attached to E/Q, D > 0.
 * Assume |D p^m| < MAX_ULONG, m > 0 */
static GEN
loopLpn(GEN W, GEN xpm, ulong D, ulong p, long m, long R, GEN q)
{
  pari_sp av;
  ulong a;
  GEN q1 = diviuexact(q,p);
  GEN Dq1= mului(D,q1), Dq = muliu(Dq1,p);
  GEN u = gen_0, u1 = gen_0, nc = icopy(gen_1);
  GEN c = mkfrac(nc, Dq), c1 = mkfrac(nc, Dq1);
  GEN C = R? initQplog(p, q, m): NULL;
  ulong A = itou(shifti(Dq,-1));

  av = avma;
  for (a = 1; a <= A; a++)
  {
    GEN logpR, x,x1;
    long s;
    if (a % p == 0 || !(s = krouu(D,a))) continue;
    nc[2] = (long)a;
    x = Q_xpm(W,xpm, c); /* xpm(a / Dq) */
    x1= Q_xpm(W,xpm, c1);/* xpm(a / D(q/p)) */
    if (!signe(x) && !signe(x1)) continue;
    if (R)
    {
      logpR = logp(C, nc, p, q);
      if (R != 1) logpR = Fp_powu(logpR, R, q);
      x = mulii(x, logpR);
      x1= mulii(x1,logpR);
    }
    if (s < 0) { u = subii(u, x); u1= subii(u1,x1); }
    else       { u = addii(u, x); u1= addii(u1,x1); }
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"loopLp: a = %ld / %ld",a,A);
      gerepileall(av, 2, &u,&u1);
    }
  }
  return mkvec2(u,u1);
}

/* p \nmid ap, return unit root of x^2 - ap*x + p, accuracy p^n */
static GEN
unit_eigenvalue(GEN ap, GEN p, long n)
{
  GEN sqrtD, D = subii(sqri(ap), shifti(p,2));
  if (equaliu(p,2)) n++;
  sqrtD = Zp_sqrtlift(D, ap, p, n); /* congruent to ap mod p */
  return gmul2n(gadd(ap, cvtop(sqrtD,p,n)), -1);
}

/* TODO: C corresponds to Teichmuller, currently allways NULL */
GEN
ellpadicL(GEN E, GEN pp, long n, long r, GEN DD, GEN C)
{
  pari_sp av = avma;
  GEN ap, scale, L, W, xpm;
  ulong p, D;

  if (DD && !Z_isfundamental(DD))
    pari_err_DOMAIN("ellpadicL", "isfundamental(D)", "=", gen_0, DD);
  if (DD && signe(DD) <= 0) pari_err_DOMAIN("ellpadicL", "D", "<=", gen_0, DD);
  if (typ(pp) != t_INT) pari_err_TYPE("ellpadicL",pp);
  if (cmpis(pp,2) < 0) pari_err_PRIME("ellpadicL",pp);
  if (n <= 0) pari_err_DOMAIN("ellpadicL","precision","<=",gen_0,stoi(n));
  if (r < 0) pari_err_DOMAIN("ellpadicL","r","<",gen_0,stoi(r));

  (void)C; /* TODO */
  W = msfromell(E, 1);
  xpm = gel(W,2);
  W = gel(W,1);
  p = itou(pp);
  D = DD? itou(DD): 1;

  xpm = Q_primitive_part(xpm,&scale);
  if (!scale) scale = gen_1;
  n -= Q_pval(scale, pp);
  scale = cvtop(scale, pp, n);

  ap = ellap(E,pp);
  if (umodiu(ap,p))
  { /* ordinary */
    long N = n+2;
    GEN pn = powuu(p, N);
    GEN u,v, uv = loopLpn(W,xpm, D, p,N,r,pn); /* correct mod p^n */
    GEN al = ginv( unit_eigenvalue(ap, pp, n) );
    al = gel(al,4); /* lift to Z */
    u = modii(gel(uv,1), pn);
    v = modii(gel(uv,2), pn);
    L = Fp_sub(u, Fp_mul(al,v,pn), pn);
    L = Fp_mul(L, Fp_powu(al, N, pn), pn);
    if (!signe(L)) L = zeropadic_shallow(pp, n);
  }
  else
  { /* supersingular */
    GEN _0 = zeropadic_shallow(pp, n);
    long N = signe(ap)? 2*n+3: 2*n+1;
    GEN uv = loopLpn(W,xpm, D, p,N,r,powiu(pp,N)), u = gel(uv,1), v = gel(uv,2);
    GEN M = mkmat2(mkcol2(gen_0, gen_m1), gdivgs(mkcol2(gen_1,ap),p));
    L = RgV_RgM_mul(mkvec2(u,gdivgs(v,-p)), gpowgs(M,N));
    u = gadd(gel(L,1), _0);
    v = gadd(gel(L,2), _0);
    L = mkvec2(u,v);
  }
  return gerepileupto(av, gmul(L, gmul2n(scale,1)));
}
