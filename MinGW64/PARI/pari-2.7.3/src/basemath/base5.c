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
/*                          (continued 2)                          */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

/* must return a t_POL */
GEN
eltreltoabs(GEN rnfeq, GEN x)
{
  long i, k, v;
  pari_sp av = avma;
  GEN T, pol, teta, a, s;

  pol = gel(rnfeq,1);
  a = gel(rnfeq,2);
  k = itos(gel(rnfeq,3));
  T = gel(rnfeq,4);

  v = varn(pol);
  if (varncmp(gvar(x), v) > 0) x = scalarpol(x,v);
  x = RgX_nffix("eltreltoabs", T, x, 1);
  /* Mod(X - k a, pol(X)), a root of the polynomial defining base */
  teta = gadd(pol_x(v), gmulsg(-k,a));
  s = gen_0;
  for (i=lg(x)-1; i>1; i--)
  {
    GEN c = gel(x,i);
    if (typ(c) == t_POL) c = RgX_RgXQ_eval(c, a, pol);
    s = RgX_rem(gadd(c, gmul(teta,s)), pol);
  }
  return gerepileupto(av, s);
}
GEN
rnfeltreltoabs(GEN rnf,GEN x)
{
  const char *f = "rnfeltreltoabs";
  GEN pol;
  checkrnf(rnf);
  pol = rnf_get_polabs(rnf);
  switch(typ(x))
  {
    case t_INT: return icopy(x);
    case t_FRAC: return gcopy(x);
    case t_POLMOD:
      if (RgX_equal_var(gel(x,1), pol))
      { /* already in 'abs' form, unless possibly if nf = Q */
        if (rnf_get_nfdegree(rnf) == 1)
        {
          GEN y = gel(x,2);
          pari_sp av = avma;
          y = simplify_shallow(liftpol_shallow(y));
          return gerepilecopy(av, mkpolmod(y, pol));
        }
        return gcopy(x);
      }
      x = polmod_nffix(f,rnf,x,0);
      if (typ(x) == t_POLMOD) return rnfeltup(rnf,x);
      retmkpolmod(eltreltoabs(rnf_get_map(rnf), x), RgX_copy(pol));
    case t_POL:
      if (varn(x) == rnf_get_nfvarn(rnf)) return rnfeltup(rnf,x);
      retmkpolmod(eltreltoabs(rnf_get_map(rnf), x), RgX_copy(pol));
  }
  pari_err_TYPE(f,x); return NULL;
}

GEN
eltabstorel_lift(GEN rnfeq, GEN P)
{
  GEN k, T = gel(rnfeq,4), relpol = gel(rnfeq,5);
  if (is_scalar_t(typ(P))) return P;
  k = gel(rnfeq,3);
  P = lift_intern(P);
  if (signe(k)) P = RgXQX_translate(P, deg1pol_shallow(k, gen_0, varn(T)), T);
  P = RgXQX_rem(P, relpol, T);
  return QXQX_to_mod_shallow(P, T);
}
/* rnfeq = [pol,a,k,T,relpol], P a t_POL or scalar
 * Return Mod(P(x + k Mod(y, T(y))), pol(x)) */
GEN
eltabstorel(GEN rnfeq, GEN P)
{
  GEN T = gel(rnfeq,4), relpol = gel(rnfeq,5);
  return mkpolmod(eltabstorel_lift(rnfeq,P), QXQX_to_mod_shallow(relpol,T));
}
GEN
rnfeltabstorel(GEN rnf,GEN x)
{
  const char *f = "rnfeltabstorel";
  pari_sp av = avma;
  GEN pol, T, P;
  checkrnf(rnf);
  T = rnf_get_nfpol(rnf);
  P = rnf_get_pol(rnf);
  switch(typ(x))
  {
    case t_INT: return icopy(x);
    case t_FRAC: return gcopy(x);
    case t_POLMOD:
      if (RgX_equal_var(P, gel(x,1)))
      {
        x = polmod_nffix(f, rnf, x, 0);
        return gerepilecopy(av, mkpolmod(x,P));
      }
      if (RgX_equal_var(T, gel(x,1))) { x = Rg_nffix(f, T, x, 0); goto END; }
      pol = rnf_get_polabs(rnf);
      if (!RgX_equal_var(pol, gel(x,1))) pari_err_MODULUS(f, gel(x,1),pol);
      x = gel(x,2);
      switch(typ(x))
      {
        case t_INT: return icopy(x);
        case t_FRAC: return gcopy(x);
        case t_POL: break;
        default: pari_err_TYPE(f, x);
      }
      break;
    case t_POL:
      pol = rnf_get_polabs(rnf);
      break;
    default:
      pari_err_TYPE(f,x);
      return NULL;
  }
  if (!RgX_is_QX(x)) pari_err_TYPE(f,x);
  if (varn(x) != varn(pol))
  {
    if (varn(x) == varn(T)) { x = Rg_nffix(f,T,x,0); goto END; }
    pari_err_VAR(f, x,pol);
  }
  switch(lg(x))
  {
    case 2: avma = av; return gen_0;
    case 3: return gerepilecopy(av, gel(x,2));
  }
END:
  return gerepilecopy(av, eltabstorel(rnf_get_map(rnf), x));
}


/* x a t_VEC of rnf elements in 'alg' form (t_POL). Assume maximal rank or 0 */
static GEN
modulereltoabs(GEN rnf, GEN x)
{
  GEN W=gel(x,1), I=gel(x,2), rnfeq = rnf_get_map(rnf), polabs = gel(rnfeq,1);
  long i, j, k, m, N = lg(W)-1;
  GEN zknf, czknf, M;

  if (!N) return cgetg(1, t_VEC);
  rnf_get_nfzk(rnf, &zknf,&czknf);
  m = rnf_get_nfdegree(rnf);
  M = cgetg(N*m+1, t_VEC);
  for (k=i=1; i<=N; i++)
  {
    GEN c0, cid, w = gel(W,i), id = gel(I,i);

    if (lg(id) == 1) continue; /* must be a t_MAT */
    id = Q_primitive_part(id, &cid);
    w = Q_primitive_part(eltreltoabs(rnfeq,w), &c0);
    c0 = mul_content(c0, mul_content(cid,czknf));
    if (typ(id) == t_INT)
      for (j=1; j<=m; j++)
      {
        GEN z = RgX_rem(gmul(w, gel(zknf,j)), polabs);
        if (c0) z = RgX_Rg_mul(z, c0);
        gel(M,k++) = z;
      }
    else
      for (j=1; j<=m; j++)
      {
        GEN c, z = Q_primitive_part(RgV_RgC_mul(zknf,gel(id,j)), &c);
        z = RgX_rem(gmul(w, z), polabs);
        c = mul_content(c, c0); if (c) z = RgX_Rg_mul(z, c);
        gel(M,k++) = z;
      }
  }
  setlg(M, k); return M;
}

/* Z-basis for absolute maximal order, as a t_MAT */
GEN
rnf_basM(GEN rnf)
{
  GEN M, d, pol = rnf_get_polabs(rnf);
  long n = degpol(pol);
  /* t_VEC of t_POL */
  M = Q_remove_denom(modulereltoabs(rnf, rnf_get_zk(rnf)), &d);
  if (d)
  {
    M = ZM_hnfmodall(RgXV_to_RgM(M,n), d, hnf_MODID|hnf_CENTER);
    M = RgM_Rg_div(M, d);
  }
  else
    M = matid(n);
  return M;
}

/* only fill in nf[1,3,4,7,8,9] */
static GEN
makenfabs(GEN rnf)
{
  GEN nf = rnf_get_nf(rnf), pol = rnf_get_polabs(rnf), NF = zerovec(9);
  GEN M = rnf_basM(rnf);
  gel(NF,1) = pol;
  gel(NF,3) = mulii(powiu(nf_get_disc(nf), rnf_get_degree(rnf)),
                    idealnorm(nf, rnf_get_disc(rnf)));
  nf_set_multable(NF, M, NULL);
  gel(NF,4) = get_nfindex(nf_get_zk(NF));
  return NF;
}

static GEN
makenorms(GEN rnf)
{
  GEN f = rnf_get_index(rnf);
  return typ(f) == t_INT? gen_1: RgM_det_triangular(f);
}

#define NFABS 1
#define NORMS 2
GEN
check_and_build_nfabs(GEN rnf) {
  return obj_checkbuild(rnf, NFABS, &makenfabs);
}
GEN
check_and_build_norms(GEN rnf) {
  return obj_checkbuild(rnf, NORMS, &makenorms);
}

void
nf_nfzk(GEN nf, GEN rnfeq, GEN *zknf, GEN *czknf)
{
  GEN pol = gel(rnfeq,1), a = gel(rnfeq,2);
  GEN zk = QXV_QXQ_eval(nf_get_zk(nf), a, pol);
  *zknf = Q_primitive_part(zk, czknf);
  if (!*czknf) *czknf = gen_1;
}

GEN
rnfinit(GEN nf, GEN polrel)
{
  pari_sp av = avma;
  GEN rnf, bas, D,d,f, B, rnfeq, basnf,cobasnf;
  nf = checknf(nf);
  bas = rnfallbase(nf,&polrel, &D,&d, &f);
  B = matbasistoalg(nf,gel(bas,1));
  gel(bas,1) = lift_if_rational( RgM_to_RgXV(B,varn(polrel)) );
  rnfeq = nf_rnfeq(nf,polrel);
  nf_nfzk(nf, rnfeq, &basnf, &cobasnf);
  rnf = cgetg(13, t_VEC);
  gel(rnf,1) = polrel;
  gel(rnf,2) = mkvec2(basnf, cobasnf);
  gel(rnf,3) = mkvec2(D, d);
  gel(rnf,4) = f;
  gel(rnf,5) = cgetg(1, t_VEC); /* dummy */
  gel(rnf,6) = cgetg(1, t_VEC); /* dummy */
  gel(rnf,7) = bas;
  gel(rnf,8) = lift_if_rational( RgM_inv(B) );
  gel(rnf,9) = cgetg(1,t_VEC); /* dummy */
  gel(rnf,10)= nf;
  gel(rnf,11)= rnfeq;
  gel(rnf,12)= zerovec(2);
  return gerepilecopy(av, rnf);
}

GEN
rnfeltup(GEN rnf, GEN x)
{
  pari_sp av = avma;
  GEN zknf, czknf;
  checkrnf(rnf);
  if (typ(x) == t_POLMOD && RgX_equal_var(gel(x,1), rnf_get_polabs(rnf)))
    return gcopy(x);
  rnf_get_nfzk(rnf, &zknf, &czknf);
  x = nfeltup(rnf_get_nf(rnf), x, zknf, czknf);
  if (typ(x) == t_POL) x = mkpolmod(x, rnf_get_polabs(rnf));
  return gerepilecopy(av, x);
}

GEN
nfeltup(GEN nf, GEN x, GEN zknf, GEN czknf)
{
  GEN c;
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) != t_COL) return x;
  x = Q_primitive_part(x, &c);
  if (!RgV_is_ZV(x)) pari_err_TYPE("rnfeltup", x);
  c = mul_content(c, czknf);
  x = RgV_RgC_mul(zknf, x); if (c) x = RgX_Rg_mul(x, c);
  return x;
}

static void
fail(const char *f, GEN x)
{ pari_err_DOMAIN(f,"element","not in", strtoGENstr("the base field"),x); }
GEN
rnfeltdown(GEN rnf,GEN x)
{
  const char *f = "rnfeltdown";
  pari_sp av = avma;
  GEN z, T;
  long v;

  checkrnf(rnf);
  T = rnf_get_nfpol(rnf);
  v = varn(T);
  switch(typ(x))
  { /* directly belonging to base field ? */
    case t_INT: return icopy(x);
    case t_FRAC:return gcopy(x);
    case t_POLMOD:
      if (RgX_equal_var(gel(x,1), rnf_get_polabs(rnf))) break;
      x = polmod_nffix(f,rnf,x,0);
      /* x was defined mod the relative polynomial & non constant => fail */
      if (typ(x) == t_POL) fail(f,x);
      return gerepilecopy(av, x);

    case t_POL:
      if (varn(x) != v) break;
      x = Rg_nffix(f,T,x,0);
      return gerepilecopy(av, x);
  }
  /* x defined mod the absolute equation */
  z = rnfeltabstorel(rnf,x);
  switch(typ(z))
  {
    case t_INT:
    case t_FRAC: return z;
  }
  /* typ(z) = t_POLMOD, varn of both components is rnf_get_varn(rnf) */
  z = gel(z,2);
  if (typ(z) == t_POL)
  {
    if (lg(z) != 3) fail(f,x);
    z = gel(z,2);
  }
  return gerepilecopy(av, z);
}

/* vector of rnf elt -> matrix of nf elts */
static GEN
rnfV_to_nfM(GEN rnf, GEN x)
{
  long i, l = lg(x);
  GEN y = cgetg(l, t_MAT);
  for (i = 1; i < l; i++) gel(y,i) = rnfalgtobasis(rnf,gel(x,i));
  return y;
}

static GEN
rnfprincipaltohnf(GEN rnf,GEN x)
{
  pari_sp av = avma;
  GEN bas = rnf_get_zk(rnf), nf = rnf_get_nf(rnf);
  x = rnfbasistoalg(rnf,x);
  x = gmul(x, gmodulo(gel(bas,1), rnf_get_pol(rnf)));
  return gerepileupto(av, nfhnf(nf, mkvec2(rnfV_to_nfM(rnf,x), gel(bas,2))));
}

/* pseudo-basis for the 0 ideal */
static GEN
rnfideal0() { retmkvec2(cgetg(1,t_MAT),cgetg(1,t_VEC)); }

GEN
rnfidealhnf(GEN rnf, GEN x)
{
  GEN z, nf, bas;

  checkrnf(rnf); nf = rnf_get_nf(rnf);
  switch(typ(x))
  {
    case t_INT: case t_FRAC:
      if (isintzero(x)) return rnfideal0();
      bas = rnf_get_zk(rnf); z = cgetg(3,t_VEC);
      gel(z,1) = matid(rnf_get_degree(rnf));
      gel(z,2) = gmul(x, gel(bas,2)); return z;

    case t_VEC:
      if (lg(x) == 3 && typ(gel(x,1)) == t_MAT) return nfhnf(nf, x);
      return rnfidealabstorel(rnf, x);

    case t_POLMOD: case t_POL: case t_COL:
      return rnfprincipaltohnf(rnf,x);
  }
  pari_err_TYPE("rnfidealhnf",x);
  return NULL; /* not reached */
}

GEN
prodid(GEN nf, GEN I)
{
  long i, l = lg(I);
  GEN z;
  if (l == 1) return matid(nf_get_degree(nf));
  z = gel(I,1);
  for (i=2; i<l; i++) z = idealmul(nf, z, gel(I,i));
  return z;
}

static GEN
prodidnorm(GEN nf, GEN I)
{
  long i, l = lg(I);
  GEN z;
  if (l == 1) return gen_1;
  z = idealnorm(nf, gel(I,1));
  for (i=2; i<l; i++) z = gmul(z, idealnorm(nf, gel(I,i)));
  return z;
}

GEN
rnfidealnormrel(GEN rnf, GEN id)
{
  pari_sp av = avma;
  GEN nf, z = gel(rnfidealhnf(rnf,id), 2);
  if (lg(z) == 1) return cgetg(1, t_MAT);
  nf = rnf_get_nf(rnf); z = prodid(nf, z);
  return gerepileupto(av, idealmul(nf,z, rnf_get_index(rnf)));
}

GEN
rnfidealnormabs(GEN rnf, GEN id)
{
  pari_sp av = avma;
  GEN nf, z = gel(rnfidealhnf(rnf,id), 2);
  if (lg(z) == 1) return gen_0;
  nf = rnf_get_nf(rnf); z = prodidnorm(nf, z);
  return gerepileupto(av, gmul(z, check_and_build_norms(rnf)));
}

GEN
rnfidealreltoabs(GEN rnf,GEN x)
{
  pari_sp av = avma;
  long i, l;
  GEN w;

  x = rnfidealhnf(rnf,x);
  w = gel(x,1); l = lg(w); settyp(w, t_VEC);
  for (i=1; i<l; i++) gel(w,i) = lift_intern( rnfbasistoalg(rnf, gel(w,i)) );
  return gerepilecopy(av, modulereltoabs(rnf, x));
}

GEN
rnfidealabstorel(GEN rnf, GEN x)
{
  long N, j;
  pari_sp av = avma;
  GEN A, I, invbas;

  checkrnf(rnf);
  invbas = rnf_get_invzk(rnf);
  if (typ(x) != t_VEC) pari_err_TYPE("rnfidealabstorel",x);
  N = lg(x)-1;
  if (N != rnf_get_absdegree(rnf))
  {
    if (!N) return rnfideal0();
    pari_err_DIM("rnfidealabstorel");
  }
  A = cgetg(N+1,t_MAT);
  I = cgetg(N+1,t_VEC);
  for (j=1; j<=N; j++)
  {
    GEN t = lift_intern( rnfeltabstorel(rnf, gel(x,j)) );
    gel(A,j) = mulmat_pol(invbas, t);
    gel(I,j) = gen_1;
  }
  return gerepileupto(av, nfhnf(rnf_get_nf(rnf), mkvec2(A,I)));
}

GEN
rnfidealdown(GEN rnf,GEN x)
{
  pari_sp av = avma;
  GEN I;
  x = rnfidealhnf(rnf,x); I = gel(x,2);
  if (lg(I) == 1) { avma = av; return cgetg(1,t_MAT); }
  return gerepilecopy(av, gel(I,1));
}

/* lift ideal x to the relative extension, returns a Z-basis */
GEN
rnfidealup(GEN rnf,GEN x)
{
  pari_sp av = avma;
  long i, n;
  GEN nf, bas, bas2, I;

  checkrnf(rnf); nf = rnf_get_nf(rnf);
  n = rnf_get_degree(rnf);
  bas = rnf_get_zk(rnf); bas2 = gel(bas,2);

  (void)idealtyp(&x, &I); /* I is junk */
  I = cgetg(n+1,t_VEC);
  for (i=1; i<=n; i++) gel(I,i) = idealmul(nf,x,gel(bas2,i));
  return gerepilecopy(av, modulereltoabs(rnf, mkvec2(gel(bas,1), I)));
}

/* x a relative HNF => vector of 2 generators (relative polmods) */
GEN
rnfidealtwoelement(GEN rnf, GEN x)
{
  pari_sp av = avma;
  GEN y, cy, z, NF;

  y = rnfidealreltoabs(rnf,x);
  NF = check_and_build_nfabs(rnf);
  y = matalgtobasis(NF, y); settyp(y, t_MAT);
  y = Q_primitive_part(y, &cy);
  y = ZM_hnf(y);
  if (lg(y) == 1) { avma = av; return mkvec2(gen_0, gen_0); }
  y = idealtwoelt(NF, y);
  if (cy) y = RgV_Rg_mul(y, cy);
  z = rnfeltabstorel(rnf, coltoliftalg(NF, gel(y,2)));
  return gerepilecopy(av, mkvec2(gel(y,1), z));
}

GEN
rnfidealmul(GEN rnf,GEN x,GEN y)
{
  pari_sp av = avma;
  GEN nf, z, x1, x2, p1, p2, bas;

  y = rnfidealtwoelement(rnf,y);
  if (isintzero(gel(y,1))) { avma = av; return rnfideal0(); }
  nf = rnf_get_nf(rnf);
  bas = rnf_get_zk(rnf);
  x = rnfidealhnf(rnf,x);
  x1 = gmodulo(gmul(gel(bas,1), matbasistoalg(nf,gel(x,1))), rnf_get_pol(rnf));
  x2 = gel(x,2);
  p1 = gmul(gel(y,1), gel(x,1));
  p2 = rnfV_to_nfM(rnf, gmul(gel(y,2), x1));
  z = mkvec2(shallowconcat(p1, p2), shallowconcat(x2, x2));
  return gerepileupto(av, nfhnf(nf,z));
}

int
nfissquarefree(GEN nf, GEN x)
{
  pari_sp av = avma;
  GEN g, y = RgX_deriv(x);
  if (RgX_is_rational(x))
    g = QX_gcd(x, y);
  else
    g = nfgcd(x, y, nf, NULL);
  avma = av; return (degpol(g) == 0);
}

GEN
rnfequationall(GEN A, GEN B, long *pk, GEN *pLPRS)
{
  long lA, lB;
  GEN nf, C;

  A = get_nfpol(A, &nf); lA = lg(A);
  if (!nf) {
    if (lA<=3) pari_err_CONSTPOL("rnfequation");
    RgX_check_ZX(A,"rnfequation");
  }
  B = RgX_nffix("rnfequation", A,B,1); lB = lg(B);
  if (lB<=3) pari_err_CONSTPOL("rnfequation");
  B = Q_primpart(B);

  if (!nfissquarefree(A,B))
    pari_err_DOMAIN("rnfequation","issquarefree(B)","=",gen_0,B);

  *pk = 0; C = ZX_ZXY_resultant_all(A, B, pk, pLPRS);
  if (gsigne(leading_term(C)) < 0) C = RgX_neg(C);
  *pk = -*pk; return Q_primpart(C);
}

GEN
rnfequation0(GEN A, GEN B, long flall)
{
  pari_sp av = avma;
  GEN LPRS, C;
  long k;

  C = rnfequationall(A, B, &k, flall? &LPRS: NULL);
  if (flall)
  { /* a,b,c root of A,B,C = compositum, c = b + k a */
    GEN a, mH0 = RgX_neg(gel(LPRS,1)), H1 = gel(LPRS,2);
    a = RgXQ_mul(mH0, QXQ_inv(H1, C), C);
    C = mkvec3(C, mkpolmod(a, C), stoi(k));
  }
  return gerepilecopy(av, C);
}
GEN
rnfequation(GEN nf, GEN pol) { return rnfequation0(nf,pol,0); }
GEN
rnfequation2(GEN nf, GEN pol) { return rnfequation0(nf,pol,1); }
GEN
nf_rnfeq(GEN nf, GEN relpol)
{
  GEN pol, a, k, junk, eq;
  relpol = liftpol_shallow(relpol);
  eq = rnfequation2(nf, relpol);
  pol = gel(eq,1);
  a = gel(eq,2); if (typ(a) == t_POLMOD) a = gel(a,2);
  k = gel(eq,3);
  return mkvec5(pol,a,k,get_nfpol(nf, &junk),relpol);
}
/* only allow abstorel */
GEN
nf_rnfeqsimple(GEN nf, GEN relpol)
{
  long sa;
  GEN junk, pol = rnfequationall(nf, relpol, &sa, NULL);
  return mkvec5(pol,gen_0/*dummy*/,stoi(sa),get_nfpol(nf, &junk),relpol);
}

static GEN
nftau(long r1, GEN x)
{
  long i, l = lg(x);
  GEN s = r1? gel(x,1): gmul2n(real_i(gel(x,1)),1);
  for (i=2; i<=r1; i++) s = gadd(s, gel(x,i));
  for (   ; i < l; i++) s = gadd(s, gmul2n(real_i(gel(x,i)),1));
  return s;
}

static GEN
initmat(long l)
{
  GEN x = cgetg(l, t_MAT);
  long i;
  for (i = 1; i < l; i++) gel(x,i) = cgetg(l, t_COL);
  return x;
}

static GEN
nftocomplex(GEN nf, GEN x)
{
  GEN M = nf_get_M(nf);
  x = nf_to_scalar_or_basis(nf,x);
  if (typ(x) != t_COL) return const_col(nbrows(M), x);
  return RgM_RgC_mul(M, x);
}
/* assume x a square t_MAT, return a t_VEC of embeddings of its columns */
static GEN
mattocomplex(GEN nf, GEN x)
{
  long i,j, l = lg(x);
  GEN v = cgetg(l, t_VEC);
  for (j=1; j<l; j++)
  {
    GEN c = gel(x,j), b = cgetg(l, t_MAT);
    for (i=1; i<l; i++) gel(b,i) = nftocomplex(nf, gel(c,i));
    b = shallowtrans(b); settyp(b, t_COL);
    gel(v,j) = b;
  }
  return v;
}

static GEN
nf_all_roots(GEN nf, GEN x, long prec)
{
  long i, j, l = lg(x), ru = lg(nf_get_roots(nf));
  GEN y = cgetg(l, t_POL), v, z;

  x = RgX_to_nfX(nf, x);
  y[1] = x[1];
  for (i=2; i<l; i++) gel(y,i) = nftocomplex(nf, gel(x,i));
  i = gprecision(y); if (i && i <= 3) return NULL;

  v = cgetg(ru, t_VEC);
  z = cgetg(l, t_POL); z[1] = x[1];
  for (i=1; i<ru; i++)
  {
    for (j = 2; j < l; j++) gel(z,j) = gmael(y,j,i);
    gel(v,i) = cleanroots(z, prec);
  }
  return v;
}

static GEN
rnfscal(GEN m, GEN x, GEN y)
{
  long i, l = lg(m);
  GEN z = cgetg(l, t_COL);
  for (i = 1; i < l; i++)
    gel(z,i) = gmul(gconj(shallowtrans(gel(x,i))), gmul(gel(m,i), gel(y,i)));
  return z;
}

/* x ideal in HNF */
static GEN
findmin(GEN nf, GEN x, GEN muf)
{
  pari_sp av = avma;
  long e;
  GEN cx, y, m, M = nf_get_M(nf);

  x = Q_primitive_part(x, &cx);
  if (gequal1(gcoeff(x,1,1))) y = M;
  else
  {
    GEN G = nf_get_G(nf);
    m = lllfp(RgM_mul(G,x), 0.75, 0);
    if (typ(m) != t_MAT)
    {
      x = ZM_lll(x, 0.75, LLL_INPLACE);
      m = lllfp(RgM_mul(G,x), 0.75, 0);
      if (typ(m) != t_MAT) pari_err_PREC("rnflllgram");
    }
    x = ZM_mul(x, m);
    y = RgM_mul(M, x);
  }
  m = RgM_solve_realimag(y, muf);
  if (!m) return NULL; /* precision problem */
  if (cx) m = RgC_Rg_div(m, cx);
  m = grndtoi(m, &e);
  if (e >= 0) return NULL; /* precision problem */
  m = ZM_ZC_mul(x, m);
  if (cx) m = RgC_Rg_mul(m, cx);
  return gerepileupto(av, m);
}

static int
RED(long k, long l, GEN U, GEN mu, GEN MC, GEN nf, GEN I, GEN *Ik_inv)
{
  GEN x, xc, ideal;
  long i;

  if (!*Ik_inv) *Ik_inv = idealinv(nf, gel(I,k));
  ideal = idealmul(nf,gel(I,l), *Ik_inv);
  x = findmin(nf, ideal, gcoeff(mu,k,l));
  if (!x) return 0;
  if (gequal0(x)) return 1;

  xc = nftocomplex(nf,x);
  gel(MC,k) = gsub(gel(MC,k), vecmul(xc,gel(MC,l)));
  gel(U,k) = gsub(gel(U,k), gmul(coltoalg(nf,x), gel(U,l)));
  gcoeff(mu,k,l) = gsub(gcoeff(mu,k,l), xc);
  for (i=1; i<l; i++)
    gcoeff(mu,k,i) = gsub(gcoeff(mu,k,i), vecmul(xc,gcoeff(mu,l,i)));
  return 1;
}

static int
check_0(GEN B)
{
  long i, l = lg(B);
  for (i = 1; i < l; i++)
    if (gsigne(gel(B,i)) <= 0) return 1;
  return 0;
}

static int
do_SWAP(GEN I, GEN MC, GEN MCS, GEN h, GEN mu, GEN B, long kmax, long k,
        const long alpha, long r1)
{
  GEN p1, p2, muf, mufc, Bf, temp;
  long i, j;

  p1 = nftau(r1, gadd(gel(B,k),
                      gmul(gnorml2(gcoeff(mu,k,k-1)), gel(B,k-1))));
  p2 = nftau(r1, gel(B,k-1));
  if (gcmp(gmulsg(alpha,p1), gmulsg(alpha-1,p2)) > 0) return 0;

  swap(gel(MC,k-1),gel(MC,k));
  swap(gel(h,k-1), gel(h,k));
  swap(gel(I,k-1), gel(I,k));
  for (j=1; j<=k-2; j++) swap(gcoeff(mu,k-1,j),gcoeff(mu,k,j));
  muf = gcoeff(mu,k,k-1);
  mufc = gconj(muf);
  Bf = gadd(gel(B,k), vecmul(real_i(vecmul(muf,mufc)), gel(B,k-1)));
  if (check_0(Bf)) return 1; /* precision problem */

  p1 = vecdiv(gel(B,k-1),Bf);
  gcoeff(mu,k,k-1) = vecmul(mufc,p1);
  temp = gel(MCS,k-1);
  gel(MCS,k-1) = gadd(gel(MCS,k), vecmul(muf,gel(MCS,k-1)));
  gel(MCS,k) = gsub(vecmul(vecdiv(gel(B,k),Bf), temp),
                    vecmul(gcoeff(mu,k,k-1), gel(MCS,k)));
  gel(B,k) = vecmul(gel(B,k),p1);
  gel(B,k-1) = Bf;
  for (i=k+1; i<=kmax; i++)
  {
    temp = gcoeff(mu,i,k);
    gcoeff(mu,i,k) = gsub(gcoeff(mu,i,k-1), vecmul(muf, gcoeff(mu,i,k)));
    gcoeff(mu,i,k-1) = gadd(temp, vecmul(gcoeff(mu,k,k-1),gcoeff(mu,i,k)));
  }
  return 1;
}

static GEN
rel_T2(GEN nf, GEN pol, long lx, long prec)
{
  long ru, i, j, k, l;
  GEN T2, s, unro, roorder, powreorder;

  roorder = nf_all_roots(nf, pol, prec);
  if (!roorder) return NULL;
  ru = lg(roorder);
  unro = cgetg(lx,t_COL); for (i=1; i<lx; i++) gel(unro,i) = gen_1;
  powreorder = cgetg(lx,t_MAT); gel(powreorder,1) = unro;
  T2 = cgetg(ru, t_VEC);
  for (i = 1; i < ru; i++)
  {
    GEN ro = gel(roorder,i);
    GEN m = initmat(lx);
    for (k=2; k<lx; k++)
    {
      GEN c = cgetg(lx, t_COL); gel(powreorder,k) = c;
      for (j=1; j < lx; j++)
        gel(c,j) = gmul(gel(ro,j), gmael(powreorder,k-1,j));
    }
    for (l = 1; l < lx; l++)
      for (k = 1; k <= l; k++)
      {
        s = gen_0;
        for (j = 1; j < lx; j++)
          s = gadd(s, gmul(gconj(gmael(powreorder,k,j)),
                                 gmael(powreorder,l,j)));
        if (l == k)
          gcoeff(m, l, l) = real_i(s);
        else
        {
          gcoeff(m, k, l) = s;
          gcoeff(m, l, k) = gconj(s);
        }
      }
    gel(T2,i) = m;
  }
  return T2;
}

/* given a base field nf (e.g main variable y), a polynomial pol with
 * coefficients in nf    (e.g main variable x), and an order as output
 * by rnfpseudobasis, outputs a reduced order. */
GEN
rnflllgram(GEN nf, GEN pol, GEN order,long prec)
{
  pari_sp av = avma, lim = stack_lim(av,2);
  long j, k, l, kmax, r1, lx, count = 0;
  GEN M, I, h, H, mth, MC, MPOL, MCS, B, mu;
  const long alpha = 10, MAX_COUNT = 4;

  nf = checknf(nf); r1 = nf_get_r1(nf);
  check_ZKmodule(order, "rnflllgram");
  M = gel(order,1);
  I = gel(order,2); lx = lg(I);
  if (lx < 3) return gcopy(order);
  if (lx-1 != degpol(pol)) pari_err_DIM("rnflllgram");
  I = leafcopy(I);
  H = NULL;
  MPOL = matbasistoalg(nf, M);
  MCS = matid(lx-1); /* dummy for gerepile */
PRECNF:
  if (count == MAX_COUNT)
  {
    prec = precdbl(prec); count = 0;
    if (DEBUGLEVEL) pari_warn(warnprec,"rnflllgram",prec);
    nf = nfnewprec_shallow(nf,prec);
  }
  mth = rel_T2(nf, pol, lx, prec);
  if (!mth) { count = MAX_COUNT; goto PRECNF; }
  h = NULL;
PRECPB:
  if (h)
  { /* precision problem, recompute. If no progress, increase nf precision */
    if (++count == MAX_COUNT || RgM_isidentity(h)) {count = MAX_COUNT; goto PRECNF;}
    H = H? gmul(H, h): h;
    MPOL = gmul(MPOL, h);
  }
  h = matid(lx-1);
  MC = mattocomplex(nf, MPOL);
  mu = cgetg(lx,t_MAT);
  B  = cgetg(lx,t_COL);
  for (j=1; j<lx; j++)
  {
    gel(mu,j) = zerocol(lx - 1);
    gel(B,j) = gen_0;
  }
  if (DEBUGLEVEL) err_printf("k = ");
  gel(B,1) = real_i(rnfscal(mth,gel(MC,1),gel(MC,1)));
  gel(MCS,1) = gel(MC,1);
  kmax = 1; k = 2;
  do
  {
    GEN Ik_inv = NULL;
    if (DEBUGLEVEL) err_printf("%ld ",k);
    if (k > kmax)
    { /* Incremental Gram-Schmidt */
      kmax = k; gel(MCS,k) = gel(MC,k);
      for (j=1; j<k; j++)
      {
        gcoeff(mu,k,j) = vecdiv(rnfscal(mth,gel(MCS,j),gel(MC,k)),
                                gel(B,j));
        gel(MCS,k) = gsub(gel(MCS,k), vecmul(gcoeff(mu,k,j),gel(MCS,j)));
      }
      gel(B,k) = real_i(rnfscal(mth,gel(MCS,k),gel(MCS,k)));
      if (check_0(gel(B,k))) goto PRECPB;
    }
    if (!RED(k, k-1, h, mu, MC, nf, I, &Ik_inv)) goto PRECPB;
    if (do_SWAP(I,MC,MCS,h,mu,B,kmax,k,alpha, r1))
    {
      if (!B[k]) goto PRECPB;
      if (k > 2) k--;
    }
    else
    {
      for (l=k-2; l; l--)
        if (!RED(k, l, h, mu, MC, nf, I, &Ik_inv)) goto PRECPB;
      k++;
    }
    if (low_stack(lim, stack_lim(av,2)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"rnflllgram");
      gerepileall(av, H?10:9, &nf,&mth,&h,&MPOL,&B,&MC,&MCS,&mu,&I,&H);
    }
  }
  while (k < lx);
  MPOL = gmul(MPOL,h);
  if (H) h = gmul(H, h);
  if (DEBUGLEVEL) err_printf("\n");
  MPOL = RgM_to_nfM(nf,MPOL);
  h = RgM_to_nfM(nf,h);
  return gerepilecopy(av, mkvec2(mkvec2(MPOL,I), h));
}

GEN
rnfpolred(GEN nf, GEN pol, long prec)
{
  pari_sp av = avma;
  long i, j, n, v = varn(pol);
  GEN id, w, I, O, bnf, nfpol;

  if (typ(pol)!=t_POL) pari_err_TYPE("rnfpolred",pol);
  bnf = nf; nf = checknf(bnf);
  bnf = (nf == bnf)? NULL: checkbnf(bnf);
  if (degpol(pol) <= 1) { w = cgetg(2, t_VEC); gel(w,1) = pol_x(v); return w; }
  nfpol = nf_get_pol(nf);

  id = rnfpseudobasis(nf,pol);
  if (bnf && is_pm1( bnf_get_no(bnf) )) /* if bnf is principal */
  {
    GEN newI, newO;
    O = gel(id,1);
    I = gel(id,2); n = lg(I)-1;
    newI = cgetg(n+1,t_VEC);
    newO = cgetg(n+1,t_MAT);
    for (j=1; j<=n; j++)
    {
      GEN al = gen_if_principal(bnf,gel(I,j));
      gel(newI,j) = gen_1;
      gel(newO,j) = nfC_nf_mul(nf, gel(O,j), al);
    }
    id = mkvec2(newO, newI);
  }

  id = gel(rnflllgram(nf,pol,id,prec),1);
  O = gel(id,1);
  I = gel(id,2); n = lg(I)-1;
  w = cgetg(n+1,t_VEC);
  pol = lift(pol);
  for (j=1; j<=n; j++)
  {
    GEN newpol, L, a, Ij = gel(I,j);
    a = RgC_Rg_mul(gel(O,j), (typ(Ij) == t_MAT)? gcoeff(Ij,1,1): Ij);
    for (i=n; i; i--)
    {
      GEN c = gel(a,i);
      if (typ(c) == t_COL) gel(a,i) = coltoliftalg(nf, c);
    }
    a = RgV_to_RgX(a, v);
    newpol = RgXQX_red(RgXQ_charpoly(a, pol, v), nfpol);
    newpol = Q_primpart(newpol);

    (void)nfgcd_all(newpol, RgX_deriv(newpol), nfpol, nf_get_index(nf), &newpol);
    L = leading_term(newpol);
    gel(w,j) = (typ(L) == t_POL)? RgXQX_div(newpol, L, nfpol)
                                : RgX_Rg_div(newpol, L);
  }
  return gerepilecopy(av,w);
}
