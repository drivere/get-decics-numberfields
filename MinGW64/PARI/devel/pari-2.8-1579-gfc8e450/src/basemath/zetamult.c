/* Copyright (C) 2000  The PARI group.
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
/**                     MULTIPLE ZETA VALUES                       **/
/**                                                                **/
/** ALGORITHM DUE TO P. AKHILESH. DO NOT REPRODUCE UNTIL PUBLISHED **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

static GEN
la(long e, long f, GEN s)
{
  if (e == f) return gmul2n(s,1);
  return (e > f)? s: gmulgs(s,3);
}

static GEN
rev(GEN evec)
{
  long i, le = lg(evec);
  GEN res = cgetg(le, t_VECSMALL);
  for (i = 1; i < le; ++i) res[i] = 1 - evec[le-i];
  return res;
}

static GEN
etoa(GEN evec)
{
  long ct, a, ia, le = lg(evec) - 1;
  GEN avec;

  if (evec[le] != 1) pari_err_TYPE("zetamult",evec);
  avec = cgetg(le+1, t_VECSMALL);
  ct = 0; a = 0; ia = 1;
  while (ct < le)
  {
    ct++; a++;
    if (evec[ct] == 1) { avec[ia++] = a; a = 0; }
  }
  setlg(avec, ia); return avec;
}

static GEN
atoe(GEN avec)
{
  long i, j, l1 = lg(avec);
  GEN evec = cgetg(l1, t_VEC);
  for (i = 1; i < l1; ++i)
  {
    long a = avec[i];
    GEN e = cgetg(a+1, t_VECSMALL);
    for (j = 1; j < a; ++j) e[j] = 0;
    e[a] = 1;
    gel(evec,i) = e;
  }
  return shallowconcat1(evec);
}

/* phivec[i] contains phip(j,avec[i..r]) for 1<=j<=nlim > 2 */
static GEN
phip(long nlim, GEN avec, long prec)
{
  pari_sp av = avma;
  long i, j, ar, r = lg(avec) - 1;
  GEN u, r1, phivec = cgetg(r+1, t_VEC);

  ar = avec[r]; r1 = real_1(prec);
  gel(phivec, r) = u = cgetg(nlim, t_VEC);
  for (j = 1; j < nlim; ++j) gel(u,j) = divri(r1, powuu(j,ar));
  for (i = r-1; i >= 1; i--)
  {
    GEN t, phi = gel(phivec,i+1);
    ar = avec[i];
    gel(phivec, i) = u = cgetg(nlim, t_VEC);
    gel(u,1) = gen_0; t = gel(phi,1);
    gel(u,2) = gmul2n(t, -ar);
    for (j = 3; j < nlim; j++)
    {
      t = gadd(t, gel(phi,j-1));
      gel(u,j) = gdiv(t, powuu(j,ar));
    }
  }
  return gerepilecopy(av, phivec);
}

/* Return 1 if vec2 RHS of vec1, -1 if vec1 RHS of vec2, 0 else */
static long
isrhs(GEN v1, GEN v2)
{
  long s = 1, i, l1 = lg(v1), l2 = lg(v2);
  if (l1 < l2)
  {
    s = -1;
    swap(v1,v2);
    lswap(l1,l2);
  }
  for (i = l2-1; i >= 1; --i)
    if (v2[i] != v1[l1-l2+i]) return 0;
  return s;
}

static long
istruerhs(GEN v1, GEN v2)
{
  long i, l1 = lg(v1), l2 = lg(v2);
  if (l1 < l2) return 0;
  for (i = l2-1; i >= 1; --i)
    if (v2[i] != v1[l1-l2+i]) return 0;
  return l1-l2+1;
}

static GEN
isinphi(GEN v, GEN a, GEN phivec)
{
  long s, m, l1 = lg(v);
  for (m = 1; m < l1; m++)
  {
    s = istruerhs(gel(v,m), a);
    if (s) return gmael(phivec,m,s);
  }
  return NULL;
}

/* If v RHS of LR[i] for some i, return LR. If LR[i] RHS (strict) of v, replace
 * LR[i] by v. If none, add v to LR. */
static GEN
addevec(GEN LR, GEN v)
{
  long s, i, l1 = lg(LR);
  for (i = 1; i < l1; i++)
  {
    s = isrhs(gel(LR,i), v);
    if (s == 1) return LR;
    if (s == -1) { gel(LR,i) = v; return LR; }
  }
  return vec_append(LR,v);
}

GEN
zetamult(GEN avec, long prec)
{
  pari_sp ltop = avma;
  long k, n, i, j, nlim, l, bitprec, prec2;
  GEN binvec, S, LR, phiall, MA, MR, evec = gen_0;

  switch(typ(avec))
  {
    case t_INT: return gzeta(avec,prec);
    case t_VEC:
    case t_COL: avec = gtovecsmall(avec); break;
    default: pari_err_TYPE("zetamult",avec);
  }
  if (lg(avec) == 1) return gen_1;
  if (vecsmall_min(avec) <= 0) pari_err_TYPE("zetamult",avec);
  if (avec[1] == 1) pari_err_DOMAIN("zetamult", "s[1]", "=", gen_1, avec);
  evec = atoe(avec);
  k = lg(evec)-1; /* weight */
  bitprec = prec2nbits(prec) + 64*(1+(k>>5));
  prec2 = nbits2prec(bitprec);
  nlim = 5 + bitprec/2;
  binvec = cgetg(nlim+1, t_VEC);
  gel(binvec, 1) = gen_2;
  for (n = 2; n <= nlim; ++n)
    gel(binvec, n) = diviuexact(mului(4*n-2, gel(binvec, n-1)), n);
  LR = cgetg(1, t_VEC);
  MA = cgetg(k, t_VEC);
  MR = cgetg(k, t_VEC);
  for (i = 1; i < k; ++i)
  {
    gel(MA,i) = etoa(rev(vecslice(evec, 1, i)));
    gel(MR,i) = etoa(vecslice(evec, i+1, k));
    LR = addevec(addevec(LR, gel(MA,i)), gel(MR,i));
  }
  l = lg(LR);
  phiall = cgetg(l, t_VEC);
  for (j = 1; j < l; j++) gel(phiall,j) = phip(nlim+1, gel(LR,j), prec2);
  S = real_0(prec2);
  for (i = 1; i < k; i++)
  {
    GEN phi1 = isinphi(LR, gel(MA,i), phiall);
    GEN phi2 = isinphi(LR, gel(MR,i), phiall);
    GEN s = gmul2n(gmul(gel(phi1,1), gel(phi2,1)), -1);
    for (n = 2; n <= nlim; ++n)
      s = gadd(s, gdiv(gmul(gel(phi1,n), gel(phi2,n)), gel(binvec,n)));
    S = gadd(S, la(evec[i], evec[i+1], s));
  }
  return gerepilecopy(ltop, rtor(S,prec));
}

