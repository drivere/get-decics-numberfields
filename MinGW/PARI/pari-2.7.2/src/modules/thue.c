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

/********************************************************************/
/**                                                                **/
/**             THUE EQUATION SOLVER (G. Hanrot)                   **/
/**                                                                **/
/********************************************************************/
/* In all the forthcoming remarks, "paper" designs the paper "Thue Equations of
 * High Degree", by Yu. Bilu and G. Hanrot, J. Number Theory (1996). The numbering
 * of the constants corresponds to Hanrot's thesis rather than to the paper */

/* Check whether tnf is a valid structure */
static int
checktnf(GEN tnf)
{
  long l = lg(tnf);
  if (typ(tnf)!=t_VEC || (l!=8 && l!=3)) return 0;
  if (typ(gel(tnf,1)) != t_VEC) return 0;
  if (l != 8) return 1; /* S=0 */

  (void)checkbnf(gel(tnf,2));
  return (typ(gel(tnf,3)) == t_COL
       && typ(gel(tnf,4)) == t_COL
       && typ(gel(tnf,5)) == t_MAT
       && typ(gel(tnf,6)) == t_MAT
       && typ(gel(tnf,7)) == t_VEC);
}

static GEN
distoZ(GEN z)
{
  GEN t = gfrac(z);
  return gmin(t, gsubsg(1,t));
}

/* Compensates rounding errors for computation/display of the constants.
 * Round up if dir > 0, down otherwise */
static GEN
myround(GEN x, long dir)
{
  GEN eps = powis(stoi(dir > 0? 10: -10), -10);
  return gmul(x, gadd(gen_1, eps));
}

/* v a t_VEC/t_VEC */
static GEN
vecmax_shallow(GEN v) { return gel(v, vecindexmax(v)); }

static GEN
tnf_get_roots(GEN poly, long prec, long S, long T)
{
  GEN R0 = QX_complex_roots(poly, prec), R = cgetg(lg(R0), t_COL);
  long k;

  for (k=1; k<=S; k++) gel(R,k) = gel(R0,k);
  /* swap roots to get the usual order */
  for (k=1; k<=T; k++)
  {
    gel(R,k+S)  = gel(R0,2*k+S-1);
    gel(R,k+S+T)= gel(R0,2*k+S);
  }
  return R;
}

/* Computation of the logarithmic height of x (given by embeddings) */
static GEN
LogHeight(GEN x, long prec)
{
  long i, n = lg(x)-1;
  GEN LH = gen_1;
  for (i=1; i<=n; i++) LH = gmul(LH, gmax(gen_1, gabs(gel(x,i), prec)));
  return gdivgs(glog(LH,prec), n);
}

/* |x|^(1/n), x t_INT */
static GEN
absisqrtn(GEN x, long n, long prec)
{ GEN r = itor(x,prec); setabssign(r); return sqrtnr(r, n); }

static GEN
get_emb(GEN x, GEN r)
{
  long l = lg(r), i;
  GEN y;

  if (typ(x) == t_INT) return const_col(l-1, x);
  y = cgetg(l, t_COL);
  for (i=1; i<l; i++)
  {
    GEN e = poleval(x, gel(r,i));
    if (gequal0(e) || (typ(e) != t_INT && precision(e) == 3)) return NULL;
    gel(y,i) = e;
  }
  return y;
}

/* Computation of the conjugates (sigma_i(v_j)), and log. heights, of elts of v */
static GEN
Conj_LH(GEN v, GEN *H, GEN r, long prec)
{
  long j, l = lg(v);
  GEN e, M = cgetg(l,t_MAT);

  (*H) = cgetg(l,t_COL);
  for (j = 1; j < l; j++)
  {
    if (! (e = get_emb(gel(v,j), r)) ) return NULL; /* FAIL */
    gel(M,j) = e;
    gel(*H,j) = LogHeight(e, prec);
  }
  return M;
}

static GEN abslog(GEN x, long prec) { return gabs(glog(x,prec), prec); }
static GEN logabs(GEN x, long prec) { return glog(gabs(x,prec), prec); }

/* Computation of M, its inverse A and precision check (see paper) */
static GEN
T_A_Matrices(GEN MatFU, long r, GEN *eps5, long prec)
{
  GEN A, p1, m1, IntM, nia, eps3, eps2;
  long e = prec2nbits(prec);

  m1 = rowslice(vecslice(MatFU, 1,r), 1,r); /* minor order r */
  m1 = logabs(m1, 3);

  A = RgM_inv(m1); if (!A) pari_err_PREC("thue");
  IntM = RgM_Rg_add(RgM_mul(A,m1), gen_m1);

  eps2 = gadd(vecmax(gabs(IntM, 3)), real2n(-e, LOWDEFAULTPREC)); /* t_REAL */
  nia = vecmax(gabs(A, 3));
  if (typ(nia) != t_REAL) nia = gtofp(nia, LOWDEFAULTPREC);

  /* Check for the precision in matrix inversion. See paper, Lemma 2.4.2. */
  p1 = addrr(mulsr(r, gmul2n(nia, e)), eps2); /* t_REAL */
  if (expo(p1) < -2*r) pari_err_PREC("thue");

  p1 = addrr(mulsr(r, gmul2n(nia,-e)), eps2);
  eps3 = mulrr(mulsr(2*r*r,nia), p1);
  if (!signe(eps3))
    eps3 = real2n(expo(eps3), LOWDEFAULTPREC);
  else
    eps3 = myround(eps3, 1);

  if (DEBUGLEVEL>1) err_printf("epsilon_3 -> %Ps\n",eps3);
  *eps5 = mulur(r, eps3); return A;
}

/* Performs basic computations concerning the equation.
 * Returns a "tnf" structure containing
 *  1) the polynomial
 *  2) the bnf (used to solve the norm equation)
 *  3) roots, with presumably enough precision
 *  4) The logarithmic heights of units
 *  5) The matrix of conjugates of units
 *  6) its inverse
 *  7) a few technical constants */
static GEN
inithue(GEN P, GEN bnf, long flag, long prec)
{
  GEN MatFU, x0, tnf, tmp, gpmin, dP, csts, ALH, eps5, ro, c1, c2, Ind = gen_1;
  long k,j, n = degpol(P);
  long s,t, prec_roots;

  if (!bnf)
  {
    bnf = Buchall(P, nf_FORCE, DEFAULTPREC);
    if (flag) (void)bnfcertify(bnf);
    else
      Ind = floorr(mulru(bnf_get_reg(bnf), 5));
  }

  nf_get_sign(bnf_get_nf(bnf), &s, &t);
  prec_roots = prec;
  for(;;)
  {
    ro = tnf_get_roots(P, prec_roots, s, t);
    MatFU = Conj_LH(bnf_get_fu(bnf), &ALH, ro, prec);
    if (MatFU) break;
    prec_roots = precdbl(prec_roots);
    if (DEBUGLEVEL>1) pari_warn(warnprec, "inithue", prec_roots);
  }

  dP = ZX_deriv(P);
  c1 = NULL; /* min |P'(r_i)|, i <= s */
  for (k=1; k<=s; k++)
  {
    tmp = gabs(poleval(dP,gel(ro,k)),prec);
    if (!c1 || gcmp(tmp,c1) < 0) c1 = tmp;
  }
  c1 = gdiv(int2n(n-1), c1);
  c1 = gprec_w(myround(c1, 1), DEFAULTPREC);

  c2 = NULL; /* max |r_i - r_j|, i!=j */
  for (k=1; k<=n; k++)
    for (j=k+1; j<=n; j++)
    {
      tmp = gabs(gsub(gel(ro,j),gel(ro,k)), prec);
      if (!c2 || gcmp(c2,tmp) > 0) c2 = tmp;
    }
  c2 = gprec_w(myround(c2, -1), DEFAULTPREC);

  if (t==0)
    x0 = real_1(DEFAULTPREC);
  else
  {
    gpmin = NULL; /* min |P'(r_i)|, i > s */
    for (k=1; k<=t; k++)
    {
      tmp = gabs(poleval(dP,gel(ro,s+k)), prec);
      if (!gpmin || gcmp(tmp,gpmin) < 0) gpmin = tmp;
    }
    gpmin = gprec_w(gpmin, DEFAULTPREC);

    /* Compute x0. See paper, Prop. 2.2.1 */
    x0 = gmul(gpmin, vecmax_shallow(gabs(imag_i(ro), prec)));
    x0 = sqrtnr(gdiv(int2n(n-1), x0), n);
  }
  if (DEBUGLEVEL>1)
    err_printf("c1 = %Ps\nc2 = %Ps\nIndice <= %Ps\n", c1, c2, Ind);

  ALH = gmul2n(ALH, 1);
  tnf = cgetg(8,t_VEC); csts = cgetg(8,t_VEC);
  gel(tnf,1) = P;
  gel(tnf,2) = bnf;
  gel(tnf,3) = ro;
  gel(tnf,4) = ALH;
  gel(tnf,5) = MatFU;
  gel(tnf,6) = T_A_Matrices(MatFU, s+t-1, &eps5, prec);
  gel(tnf,7) = csts;
  gel(csts,1) = c1; gel(csts,2) = c2;   gel(csts,3) = LogHeight(ro, prec);
  gel(csts,4) = x0; gel(csts,5) = eps5; gel(csts,6) = utoipos(prec);
  gel(csts,7) = Ind;
  return tnf;
}

typedef struct {
  GEN c10, c11, c13, c15, bak, NE, ALH, Ind, hal, MatFU, ro, Hmu;
  GEN delta, lambda, inverrdelta;
  long r, iroot, deg;
} baker_s;

/* Compute Baker's bound c9 and B_0, the bound for the b_i's. See Thm 2.3.1 */
static GEN
Baker(baker_s *BS)
{
  const long prec = DEFAULTPREC;
  GEN tmp, B0, hb0, c9 = gen_1, ro = BS->ro, ro0 = gel(ro,BS->iroot);
  long k, i1, i2, r = BS->r;

  switch (BS->iroot) {
    case 1: i1=2; i2=3; break;
    case 2: i1=1; i2=3; break;
   default: i1=1; i2=2; break;
  }

  /* Compute h_1....h_r */
  for (k=1; k<=r; k++)
  {
    tmp = gdiv(gcoeff(BS->MatFU,i1,k), gcoeff(BS->MatFU,i2,k));
    tmp = gmax(gen_1, abslog(tmp,prec));
    c9 = gmul(c9, gmax(gel(BS->ALH,k), gdiv(tmp, BS->bak)));
  }

  /* Compute a bound for the h_0 */
  hb0 = gadd(gmul2n(BS->hal,2), gmul2n(gadd(BS->Hmu,mplog2(prec)), 1));
  tmp = gdiv(gmul(gsub(ro0, gel(ro,i2)), gel(BS->NE,i1)),
             gmul(gsub(ro0, gel(ro,i1)), gel(BS->NE,i2)));
  tmp = gmax(gen_1, abslog(tmp, prec));
  hb0 = gmax(hb0, gdiv(tmp, BS->bak));
  c9 = gmul(c9,hb0);
  /* Multiply c9 by the "constant" factor */
  c9 = gmul(c9, gmul(mulri(mulur(18,mppi(prec)), int2n(5*(4+r))),
                     gmul(gmul(mpfact(r+3), powiu(muliu(BS->bak,r+2), r+3)),
                          glog(muliu(BS->bak,2*(r+2)),prec))));
  c9 = gprec_w(myround(c9, 1), DEFAULTPREC);
  /* Compute B0 according to Lemma 2.3.3 */
  B0 = mulir(shifti(BS->Ind,1),
             divrr(addrr(mulrr(c9,mplog(divrr(mulir(BS->Ind, c9),BS->c10))),
                         mplog(mulir(BS->Ind, BS->c11))),
                   BS->c10));
  B0 = gmax(B0, dbltor(2.71828183));
  B0 = gmax(B0, mulrr(divir(BS->Ind, BS->c10),
                      mplog(divrr(mulir(BS->Ind, BS->c11),
                                  Pi2n(1, prec)))));

  if (DEBUGLEVEL>1) {
    err_printf("  B0  = %Ps\n",B0);
    err_printf("  Baker = %Ps\n",c9);
  }
  return B0;
}

/* || x d ||, x t_REAL, d t_INT */
static GEN
errnum(GEN x, GEN d)
{
  GEN dx = mulir(d, x), D = subri(dx, roundr(dx));
  setabssign(D); return D;
}

/* Try to reduce the bound through continued fractions; see paper. */
static int
CF_1stPass(GEN *B0, GEN kappa, baker_s *BS)
{
  GEN a, b, q, ql, qd, l0, denbound = mulri(*B0, kappa);

  if (cmprr(mulrr(dbltor(0.1),sqrr(denbound)), BS->inverrdelta) > 0)
    return -1;

  q = denom( bestappr(BS->delta, denbound) );
  qd = errnum(BS->delta, q);
  ql = errnum(BS->lambda,q);

  l0 = subrr(ql, addrr(mulrr(qd, *B0), divri(dbltor(0.1),kappa)));
  if (signe(l0) <= 0) return 0;

  if (BS->r > 1) {
    a = BS->c15; b = BS->c13;
  }
  else {
    a = BS->c11; b = BS->c10;
    l0 = mulrr(l0, Pi2n(1, DEFAULTPREC));
  }
  *B0 = divrr(mplog(divrr(mulir(q,a), l0)), b);
  if (DEBUGLEVEL>1) err_printf("    B0 -> %Ps\n",*B0);
  return 1;
}

static void
get_B0Bx(baker_s *BS, GEN l0, GEN *B0, GEN *Bx)
{
  GEN t = divrr(mulir(BS->Ind, BS->c15), l0);
  *B0 = divrr(mulir(BS->Ind, mplog(t)), BS->c13);
  *Bx = sqrtnr(shiftr(t,1), BS->deg);
}

static int
LLL_1stPass(GEN *pB0, GEN kappa, baker_s *BS, GEN *pBx)
{
  GEN B0 = *pB0, Bx = *pBx, lllmat, C, l0, l1, triv;
  long e;

  C = grndtoi(mulir(mulii(BS->Ind, kappa),
                    gpow(B0, dbltor(2.2), DEFAULTPREC)), &e);

  if (DEBUGLEVEL > 1) err_printf("C (bitsize) : %d\n", expi(C));
  lllmat = matid(3);
  if (cmpri(B0, BS->Ind) > 0)
  {
    gcoeff(lllmat, 1, 1) = grndtoi(divri(B0, BS->Ind), &e);
    triv = shiftr(sqrr(B0), 1);
  }
  else
    triv = addir(sqri(BS->Ind), sqrr(B0));

  gcoeff(lllmat, 3, 1) = roundr(negr(mulir(C, BS->lambda)));
  gcoeff(lllmat, 3, 2) = roundr(negr(mulir(C, BS->delta)));
  gcoeff(lllmat, 3, 3) = C;
  lllmat = ZM_lll(lllmat, 0.99, LLL_IM|LLL_INPLACE);

  l0 = gnorml2(gel(lllmat,1));
  l0 = subrr(divir(l0, dbltor(1.8262)), triv); /* delta = 0.99 */
  if (signe(l0) <= 0) return 0;

  l1 = shiftr(addri(shiftr(B0,1), BS->Ind), -1);
  l0 = divri(subrr(sqrtr(l0), l1), C);

  if (signe(l0) <= 0) return 0;

  get_B0Bx(BS, l0, &B0, &Bx);
  if (DEBUGLEVEL>=2)
  {
    err_printf("LLL_First_Pass successful\n");
    err_printf("B0 -> %Ps\n", B0);
    err_printf("x <= %Ps\n", Bx);
  }
  *pB0 = B0; *pBx = Bx; return 1;
}


/* Check whether a solution has already been found */
static int
new_sol(GEN z, GEN S)
{
  long i, l = lg(S);
  for (i=1; i<l; i++)
    if (ZV_equal(z,gel(S,i))) return 0;
  return 1;
}

/* add solution (x,y) if not already known */
static void
add_sol(GEN *pS, GEN x, GEN y)
{
  GEN u = mkvec2(x,y);
  if (new_sol(u, *pS)) *pS = shallowconcat(*pS, mkvec(u));
}
/* z = P(p,q), d = deg P, |z| = |rhs|. Check signs and (possibly)
 * add solutions (p,q), (-p,-q) */
static void
add_pm(GEN *pS, GEN p, GEN q, GEN z, long d, GEN rhs)
{
  if (signe(z) == signe(rhs))
  {
    add_sol(pS, p, q);
    if (!odd(d)) add_sol(pS, negi(p), negi(q));
  }
  else
    if (odd(d))  add_sol(pS, negi(p), negi(q));
}

/* Check whether a potential solution is a true solution. Return 0 if
 * truncation error (increase precision) */
static int
CheckSol(GEN *pS, GEN z1, GEN z2, GEN P, GEN rhs, GEN ro)
{
  GEN x, y, ro1 = gel(ro,1), ro2 = gel(ro,2);
  long e;

  y = grndtoi(real_i(gdiv(gsub(z2,z1), gsub(ro1,ro2))), &e);
  if (e > 0) return 0;
  if (!signe(y)) return 1; /* y = 0 taken care of in SmallSols */
  x = gadd(z1, gmul(ro1, y));
  x = grndtoi(real_i(x), &e);
  if (e > 0) return 0;
  if (e <= -13)
  { /* y != 0 and rhs != 0; check whether P(x,y) = rhs or P(-x,-y) = rhs */
    GEN z = poleval(RgX_rescale(P,y),x);
    if (absi_equal(z, rhs)) add_pm(pS, x,y, z, degpol(P), rhs);
  }
  return 1;
}

/* find q1,q2,q3 st q1 + b q2 + c q3 ~ 0 */
static GEN
GuessQi(GEN b, GEN c, GEN *eps)
{
  const long shift = 33;
  GEN Q, Lat, C = int2n(shift);

  Lat = matid(3);
  gcoeff(Lat,3,1) = ground(gmul2n(b, shift));
  gcoeff(Lat,3,2) = ground(gmul2n(c, shift));
  gcoeff(Lat,3,3) = C;

  Q = gel(lllint(Lat),1);
  if (gequal0(gel(Q,2))) return NULL; /* FAIL */

  *eps = gadd(gadd(gel(Q,3), gmul(gel(Q,1),b)), gmul(gel(Q,2),c));
  *eps = mpabs(*eps); return Q;
}

/* x a t_REAL */
static GEN
myfloor(GEN x) { return expo(x) > 30 ? ceil_safe(x): floorr(x); }

/* Check for not-so-small solutions. Return a t_REAL or NULL */
static GEN
MiddleSols(GEN *pS, GEN bound, GEN roo, GEN poly, GEN rhs, long s, GEN c1)
{
  long j, k, nmax, d;
  GEN bndcf;

  if (expo(bound) < 0) return bound;
  d = degpol(poly);
  bndcf = sqrtnr(shiftr(c1,1), d - 2);
  if (cmprr(bound, bndcf) < 0) return bound;
  /* divide by log((1+sqrt(5))/2)
   * 1 + ==> ceil
   * 2 + ==> continued fraction is normalized if last entry is 1
   * 3 + ==> start at a0, not a1 */
  nmax = 3 + (long)(gtodouble(logr_abs(bound)) / 0.4812118250596);
  bound = myfloor(bound);

  for (k = 1; k <= s; k++)
  {
    GEN t = contfrac0(real_i(gel(roo,k)), NULL, nmax);
    GEN pm1, qm1, p0, q0;

    pm1 = gen_0; p0 = gen_1;
    qm1 = gen_1; q0 = gen_0;

    for (j = 1; j < lg(t); j++)
    {
      GEN p, q, z, Q, R;
      p = addii(mulii(p0, gel(t,j)), pm1); pm1 = p0; p0 = p;
      q = addii(mulii(q0, gel(t,j)), qm1); qm1 = q0; q0 = q;
      if (cmpii(q, bound) > 0) break;
      if (DEBUGLEVEL >= 2) err_printf("Checking (+/- %Ps, +/- %Ps)\n",p, q);

      z = poleval(ZX_rescale(poly,q), p); /* = P(p/q) q^dep(P) */
      Q = dvmdii(rhs, z, &R);
      if (R != gen_0) continue;
      setabssign(Q);
      if (Z_ispowerall(Q, d, &Q))
      {
        if (!is_pm1(Q)) { p = mulii(p, Q); q = mulii(q, Q); }
        add_pm(pS, p, q, z, d, rhs);
      }
    }
    if (j == lg(t)) pari_err_BUG("Short continued fraction in thue");
  }
  return bndcf;
}

static void
check_y_root(GEN *pS, GEN P, GEN Y)
{
  GEN r = nfrootsQ(P);
  long j;
  for (j = 1; j < lg(r); j++)
    if (typ(gel(r,j)) == t_INT) add_sol(pS, gel(r,j), Y);
}

static void
check_y(GEN *pS, GEN P, GEN poly, GEN Y, GEN rhs)
{
  long j, l = lg(poly);
  GEN Yn = Y;
  gel(P, l-1) = gel(poly, l-1);
  for (j = l-2; j >= 2; j--)
  {
    gel(P,j) = mulii(Yn, gel(poly,j));
    if (j > 2) Yn = mulii(Yn, Y);
  }
  gel(P,2) = subii(gel(P,2), rhs); /* P = poly(Y/y)*y^deg(poly) - rhs */
  check_y_root(pS, P, Y);
}

/* Check for solutions under a small bound (see paper) */
static GEN
SmallSols(GEN S, GEN x3, GEN poly, GEN rhs)
{
  pari_sp av = avma, lim = stack_lim(av, 1);
  GEN X, P, rhs2;
  long j, l = lg(poly), n = degpol(poly);
  ulong y, By;

  x3 = myfloor(x3);

  if (DEBUGLEVEL>1) err_printf("* Checking for small solutions <= %Ps\n", x3);
  if (lgefint(x3) > 3)
    pari_err_OVERFLOW(stack_sprintf("thue (SmallSols): y <= %Ps", x3));
  By = itou(x3);
  /* y = 0 first: solve X^n = rhs */
  if (odd(n))
  {
    if (Z_ispowerall(absi(rhs), n, &X))
      add_sol(&S, signe(rhs) > 0? X: negi(X), gen_0);
  }
  else if (signe(rhs) > 0 && Z_ispowerall(rhs, n, &X))
  {
    add_sol(&S, X, gen_0);
    add_sol(&S, negi(X), gen_0);
  }
  rhs2 = shifti(rhs,1);
  /* y != 0 */
  P = cgetg(l, t_POL); P[1] = poly[1];
  for (y = 1; y <= By; y++)
  {
    pari_sp av2 = avma;
    long lS = lg(S);
    GEN Y = utoipos(y);
    /* try y */
    check_y(&S, P, poly, Y, rhs);
    /* try -y */
    for (j = l-2; j >= 2; j -= 2) togglesign( gel(P,j) );
    if (j == 0) gel(P,2) = subii(gel(P,2), rhs2);
    check_y_root(&S, P, utoineg(y));
    if (lS == lg(S)) { avma = av2; continue; } /* no solution found */

    if (low_stack(lim,stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"SmallSols");
      gerepileall(av, 2, &S, &rhs2);
      P = cgetg(l, t_POL); P[1] = poly[1];
    }
  }
  return S;
}

/* Computes [x]! */
static double
fact(double x)
{
  double ft = 1.0;
  x = floor(x); while (x>1) { ft *= x; x--; }
  return ft ;
}

static GEN
RgX_homogenize(GEN P, long v)
{
  GEN Q = leafcopy(P);
  long i, l = lg(P), d = degpol(P);
  for (i = 2; i < l; i++) gel(Q,i) = monomial(gel(Q,i), d--, v);
  return Q;
}

/* Compute all relevant constants needed to solve the equation P(x,y)=a given
 * the solutions of N_{K/Q}(x)=a (see inithue). */
GEN
thueinit(GEN pol, long flag, long prec)
{
  GEN POL, C, L, fa, tnf, bnf = NULL;
  pari_sp av = avma;
  long k, s, lfa, dpol;

  if (checktnf(pol)) { bnf = checkbnf(gel(pol,2)); pol = gel(pol,1); }
  if (typ(pol)!=t_POL) pari_err_TYPE("thueinit",pol);
  dpol = degpol(pol);
  if (dpol <= 0) pari_err_CONSTPOL("thueinit");
  RgX_check_ZX(pol, "thueinit");
  if (varn(pol)) { pol = leafcopy(pol); setvarn(pol, 0); }
  /* POL monic: POL(x) = C pol(x/L), L integer */
  POL = ZX_primitive_to_monic(Q_primpart(pol), &L);
  C = gdiv(powiu(L, dpol), gel(pol, dpol+2));
  pol = POL;

  fa = ZX_factor(pol);
  lfa = lgcols(fa);
  if (lfa > 2 || itos(gcoeff(fa,1,2)) > 1)
  { /* reducible polynomial */
    GEN P, Q, R, g, f = gcoeff(fa,1,1), E = gcoeff(fa,1,2);
    long e = itos(E);
    long vy = fetch_var();
    long va = fetch_var();
    long vb = fetch_var();
    if (e != 1)
    {
      if (lfa == 2) {
        tnf = mkvec2(mkvec3(pol,C,L), mkvec2(thueinit(f, flag, prec), E));
        delete_var(); delete_var(); delete_var();
        return gerepilecopy(av, tnf);
      }
      P = gpowgs(f,e);
    }
    else
      P = f;
    g = RgX_div(pol, P);
    P = RgX_Rg_sub(RgX_homogenize(f, vy), pol_x(va));
    Q = RgX_Rg_sub(RgX_homogenize(g, vy), pol_x(vb));
    R = polresultant0(P, Q, -1, 0);
    tnf = mkvec2(mkvec3(pol,C,L), mkvec2(mkvecsmall4(degpol(f), e, va,vb),  R));
    delete_var(); delete_var(); delete_var();
    return gerepilecopy(av, tnf);
  }

  if (dpol <= 2) pari_err_DOMAIN("thue", "degree","<=",gen_2,pol);
  s = sturm(pol);
  if (s)
  {
    long PREC, n = degpol(pol);
    double d, dr, dn = (double)n;

    dr = (double)((s+n-2)>>1); /* s+t-1 */
    d = dn*(dn-1)*(dn-2);
    /* Guess precision by approximating Baker's bound. The guess is most of
     * the time not sharp, ie 10 to 30 decimal digits above what is _really_
     * necessary. Note that the limiting step is the reduction. See paper. */
    PREC = nbits2prec((long)((5.83 + (dr+4)*5 + log(fact(dr+3)) + (dr+3)*log(dr+2) +
                     (dr+3)*log(d) + log(log(2*d*(dr+2))) + (dr+1))
                     /10.)*32+32);

    if (flag == 0) PREC = (long)(2.2 * PREC); /* Lazy, to be improved */
    if (PREC < prec) PREC = prec;
    if (DEBUGLEVEL >=2) err_printf("prec = %d\n", PREC);

    for (;;)
    {
      if (( tnf = inithue(pol, bnf, flag, PREC) )) break;
      PREC = precdbl(PREC);
      if (DEBUGLEVEL>1) pari_warn(warnprec,"thueinit",PREC);
      bnf = NULL; avma = av;
    }
  }
  else
  {
    GEN ro = roots(pol, DEFAULTPREC), c0 = imag_i(gel(ro,1));
    for (k=2; k<lg(ro); k++) c0 = mulrr(c0, imag_i(gel(ro,k)));
    c0 = invr( absr(c0) ); tnf = mkvec2(pol, c0);
  }
  gel(tnf,1) = mkvec3(gel(tnf,1), C, L);
  return gerepilecopy(av,tnf);
}

static void
init_get_B(long i1, long i2, GEN Delta, GEN Lambda, GEN eps5, baker_s *BS,
           long prec)
{
  GEN delta, lambda, inverrdelta;
  if (BS->r > 1)
  {
    delta = divrr(gel(Delta,i2),gel(Delta,i1));
    lambda = gdiv(gsub(gmul(gel(Delta,i2),gel(Lambda,i1)),
                       gmul(gel(Delta,i1),gel(Lambda,i2))),
                  gel(Delta,i1));
    inverrdelta = divrr(subrr(mpabs(gel(Delta,i1)),eps5),
                        mulrr(addsr(1,delta),eps5));
  }
  else
  { /* r == 1, single fundamental unit (i1 = s = t = 1) */
    GEN p1, Pi2 = Pi2n(1, prec);
    GEN fu = gel(BS->MatFU,1), ro = BS->ro;

    p1 = gdiv(gel(fu,2), gel(fu,3));
    delta = divrr(garg(p1,prec), Pi2);

    p1 = gmul(gdiv(gsub(gel(ro,1), gel(ro,2)),
                   gsub(gel(ro,1), gel(ro,3))),
              gdiv(gel(BS->NE,3), gel(BS->NE,2)));
    lambda = divrr(garg(p1,prec), Pi2);

    inverrdelta = shiftr(gabs(gel(fu,2),prec), prec2nbits(prec)-1);
  }
  if (DEBUGLEVEL>1) err_printf("  inverrdelta = %Ps\n",inverrdelta);
  BS->delta = delta;
  BS->lambda = lambda;
  BS->inverrdelta = inverrdelta;
}

static GEN
get_B0(long i1, GEN Delta, GEN Lambda, GEN eps5, long prec, baker_s *BS)
{
  GEN B0 = Baker(BS);
  long step = 0, i2 = (i1 == 1)? 2: 1;
  for(;;) /* i2 from 1 to r unless r = 1 [then i2 = 2] */
  {
    init_get_B(i1,i2, Delta,Lambda,eps5, BS, prec);
    if (DEBUGLEVEL>1) err_printf("  Entering CF...\n");
    /* Reduce B0 as long as we make progress: newB0 < oldB0 - 0.1 */
    for (;;)
    {
      GEN oldB0 = B0, kappa = utoipos(10);
      long cf;

      for (cf = 0; cf < 10; cf++, kappa = muliu(kappa,10))
      {
        int res = CF_1stPass(&B0, kappa, BS);
        if (res < 0) return NULL; /* prec problem */
        if (res) break;
        if (DEBUGLEVEL>1) err_printf("CF failed. Increasing kappa\n");
      }
      if (!step && cf == 10)
      { /* Semirational or totally rational case */
        GEN Q, ep, q, l0, denbound;

        if (! (Q = GuessQi(BS->delta, BS->lambda, &ep)) ) break;

        denbound = gadd(B0, absi(gel(Q,1)));
        q = denom( bestappr(BS->delta, denbound) );
        l0 = subrr(errnum(BS->delta, q), ep);
        if (signe(l0) <= 0) break;

        B0 = divrr(mplog(divrr(mulir(gel(Q,2), BS->c15), l0)),  BS->c13);
        if (DEBUGLEVEL>1) err_printf("Semirat. reduction: B0 -> %Ps\n",B0);
      }
      /* if no progress, stop */
      if (gcmp(oldB0, gadd(B0,dbltor(0.1))) <= 0) return gmin(oldB0, B0);
      else step++;
    }
    i2++; if (i2 == i1) i2++;
    if (i2 > BS->r) break;
  }
  pari_err_BUG("thue (totally rational case)");
  return NULL; /* not reached */
}

static GEN
get_Bx_LLL(long i1, GEN Delta, GEN Lambda, GEN eps5, long prec, baker_s *BS)
{
  GEN B0 = Baker(BS), Bx = NULL;
  long step = 0, i2 = (i1 == 1)? 2: 1;
  for(;;) /* i2 from 1 to r unless r = 1 [then i2 = 2] */
  {
    init_get_B(i1,i2, Delta,Lambda,eps5, BS, prec);
    if (DEBUGLEVEL>1) err_printf("  Entering LLL...\n");
    /* Reduce B0 as long as we make progress: newB0 < oldB0 - 0.1 */
    for (;;)
    {
      GEN oldBx = Bx, kappa = utoipos(10);
      const long cfMAX = 10;
      long cf;

      for (cf = 0; cf < cfMAX; cf++, kappa = muliu(kappa,10))
      {
        int res = LLL_1stPass(&B0, kappa, BS, &Bx);
        if (res) break;
        if (DEBUGLEVEL>1) err_printf("LLL failed. Increasing kappa\n");
      }

      /* FIXME: TO BE COMPLETED */
      if (!step && cf == cfMAX)
      { /* Semirational or totally rational case */
        GEN Q, ep, q, l0, denbound;

        if (! (Q = GuessQi(BS->delta, BS->lambda, &ep)) ) break;

        /* Beware Q[2]] = gen_0 */
        denbound = gadd(mulri(B0, absi(gel(Q,1))),
                        mulii(BS->Ind, absi(gel(Q,2))));
        q = denom( bestappr(BS->delta, denbound) );
        l0 = divri(subrr(errnum(BS->delta, q), ep), absi(gel(Q,2)));
        if (signe(l0) <= 0) break;

        get_B0Bx(BS, l0, &B0, &Bx);
        if (DEBUGLEVEL>1)
          err_printf("Semirat. reduction: B0 -> %Ps x <= %Ps\n",B0, Bx);
      }
      /* if no progress, stop */
      if (oldBx && gcmp(oldBx, Bx) <= 0) return oldBx; else step++;
    }
    i2++; if (i2 == i1) i2++;
    if (i2 > BS->r) break;
  }
  pari_err_BUG("thue (totally rational case)");
  return NULL; /* not reached */
}

static GEN
LargeSols(GEN P, GEN tnf, GEN rhs, GEN ne, GEN *pS)
{
  GEN Vect, ro, bnf, MatFU, A, csts, dP, vecdP, Bx;
  GEN c1,c2,c3,c4,c11,c14,c15, x0, x1, x2, x3, b, zp1, tmp, eps5;
  long iroot, ine, n, i, r, upb, bi1, Prec, prec, s,t;
  baker_s BS;
  pari_sp av = avma;

  bnf  = gel(tnf,2);
  csts = gel(tnf,7);
  if (!ne)
  {
    ne = bnfisintnorm(bnf, rhs);
    if (DEBUGLEVEL)
      if (!is_pm1(gel(csts, 7)) && !is_pm1(bnf_get_no(bnf)) && !is_pm1(rhs))
        pari_warn(warner, "The result returned by 'thue' is conditional on the GRH");
  }
  else if (typ(ne) != t_VEC) pari_err_TYPE("thue",ne);
  if (lg(ne)==1) return NULL;

  nf_get_sign(bnf_get_nf(bnf), &s, &t);
  BS.r = r = s+t-1; n = degpol(P);
  ro     = gel(tnf,3);
  BS.ALH = gel(tnf,4);
  MatFU  = gel(tnf,5);
  A      = gel(tnf,6);
  c1     = gel(csts,1); c1 = gmul(absi(rhs), c1);
  c2     = gel(csts,2);
  BS.hal = gel(csts,3);
  x0     = gel(csts,4);
  eps5   = gel(csts,5);
  Prec = gtolong(gel(csts,6));
  BS.Ind = gel(csts,7);
  BS.MatFU = MatFU;
  BS.bak = mulss(n, (n-1)*(n-2)); /* safe */
  BS.deg = n;

  if (t) x0 = gmul(x0, absisqrtn(rhs, n, Prec));
  tmp = divrr(c1,c2);
  c3 = mulrr(dbltor(1.39), tmp);
  c4 = mulur(n-1, c3);
  x1 = gmax(x0, sqrtnr(shiftr(tmp,1),n));

  Vect = gmul(gabs(A,DEFAULTPREC), const_col(r, gen_1));
  c14 = mulrr(c4, vecmax_shallow(Vect));
  x2 = gmax(x1, sqrtnr(mulur(10,c14), n));
  if (DEBUGLEVEL>1) {
    err_printf("x1 -> %Ps\n",x1);
    err_printf("x2 -> %Ps\n",x2);
    err_printf("c14 = %Ps\n",c14);
  }

  dP = ZX_deriv(P); vecdP = cgetg(s+1, t_VEC);
  for (i=1; i<=s; i++) gel(vecdP,i) = poleval(dP, gel(ro,i));

  zp1 = dbltor(0.01);
  x3 = gmax(x2, sqrtnr(shiftr(divrr(c14,zp1),1),n));

  b = cgetg(r+1,t_COL);
  for (iroot=1; iroot<=s; iroot++)
  {
    GEN Delta, MatNE, Hmu, c5, c7;

    Vect = const_col(r, gen_1);
    if (iroot <= r) gel(Vect,iroot) = stoi(1-n);
    Delta = RgM_RgC_mul(A,Vect);

    c5 = vecmax_shallow(gabs(Delta,Prec));
    c5  = myround(gprec_w(c5,DEFAULTPREC), 1);
    c7  = mulur(r,c5);
    BS.c10 = divur(n,c7);
    BS.c13 = divur(n,c5);
    if (DEBUGLEVEL>1) {
      err_printf("* real root no %ld/%ld\n", iroot,s);
      err_printf("  c10 = %Ps\n",BS.c10);
      err_printf("  c13 = %Ps\n",BS.c13);
    }

    prec = Prec;
    for (;;)
    {
      if (( MatNE = Conj_LH(ne, &Hmu, ro, prec) )) break;
      prec = precdbl(prec);
      if (DEBUGLEVEL>1) pari_warn(warnprec,"thue",prec);
      ro = tnf_get_roots(P, prec, s, t);
    }
    BS.ro    = ro;
    BS.iroot = iroot;

    for (ine=1; ine<lg(ne); ine++)
    {
      pari_sp av2 = avma;
      GEN Lambda, B0, c6, c8;
      GEN NE = gel(MatNE,ine), Vect2 = cgetg(r+1,t_COL);
      long k, i1;

      if (DEBUGLEVEL>1) err_printf("  - norm sol. no %ld/%ld\n",ine,lg(ne)-1);
      for (k=1; k<=r; k++)
      {
        if (k == iroot)
          tmp = gdiv(rhs, gmul(gel(vecdP,k), gel(NE,k)));
        else
          tmp = gdiv(gsub(gel(ro,iroot),gel(ro,k)), gel(NE,k));
        gel(Vect2,k) = glog(gabs(tmp,prec), prec);
      }
      Lambda = RgM_RgC_mul(A,Vect2);

      c6 = addrr(dbltor(0.1), vecmax_shallow(gabs(Lambda,DEFAULTPREC)));
      c6 = myround(c6, 1);
      c8 = addrr(dbltor(1.23), mulur(r,c6));
      c11= mulrr(shiftr(c3,1) , mpexp(divrr(mulur(n,c8),c7)));
      c15= mulrr(shiftr(c14,1), mpexp(divrr(mulur(n,c6),c5)));

      if (DEBUGLEVEL>1) {
        err_printf("  c6  = %Ps\n",c6);
        err_printf("  c8  = %Ps\n",c8);
        err_printf("  c11 = %Ps\n",c11);
        err_printf("  c15 = %Ps\n",c15);
      }
      BS.c11 = c11;
      BS.c15 = c15;
      BS.NE = NE;
      BS.Hmu = gel(Hmu,ine);

      i1 = vecindexmax(gabs(Delta,prec));
      if (is_pm1(BS.Ind))
      {
        if (! (B0 = get_B0(i1, Delta, Lambda, eps5, prec, &BS)) ) goto PRECPB;
      }
      else
      {
        if (! (Bx = get_Bx_LLL(i1, Delta, Lambda, eps5, prec, &BS)) ) goto PRECPB;
        x3 = gerepileupto(av2, gmax(Bx, x3));
        continue;
      }
     /* For each possible value of b_i1, compute the b_i's
      * and 2 conjugates of z = x - alpha y. Then check. */
      upb = gtolong(gceil(B0));
      for (bi1=-upb; bi1<=upb; bi1++)
      {
        GEN z1, z2;
        for (i=1; i<=r; i++)
        {
          gel(b,i) = gdiv(gsub(gmul(gel(Delta,i), stoi(bi1)),
                               gsub(gmul(gel(Delta,i),gel(Lambda,i1)),
                                    gmul(gel(Delta,i1),gel(Lambda,i)))),
                          gel(Delta,i1));
          if (gcmp(distoZ(gel(b,i)), zp1) > 0) break;
        }
        if (i <= r) continue;

        z1 = z2 = gen_1;
        for(i=1; i<=r; i++)
        {
          GEN c = ground(gel(b,i));
          z1 = gmul(z1, powgi(gcoeff(MatFU,1,i), c));
          z2 = gmul(z2, powgi(gcoeff(MatFU,2,i), c));
        }
        z1 = gmul(z1, gel(NE,1));
        z2 = gmul(z2, gel(NE,2));
        if (!CheckSol(pS, z1,z2,P,rhs,ro)) goto PRECPB;
      }
    }
  }
  return gmax(x0, MiddleSols(pS, x3, ro, P, rhs, s, c1));

PRECPB:
  ne = gerepilecopy(av, ne);
  prec += 5 * (DEFAULTPREC-2);
  if (DEBUGLEVEL>1) pari_warn(warnprec,"thue",prec);
  tnf = inithue(P, bnf, 0, prec);
  return LargeSols(P, tnf, rhs, ne, pS);
}

/* restrict to solutions (x,y) with L | x, replacing each by (x/L, y) */
static GEN
filter_sol_x(GEN S, GEN L)
{
  long i, k, l;
  if (is_pm1(L)) return S;
  l = lg(S); k = 1;
  for (i = 1; i < l; i++)
  {
    GEN s = gel(S,i), r;
    gel(s,1) = dvmdii(gel(s,1), L, &r);
    if (r == gen_0) gel(S, k++) = s;
  }
  setlg(S, k); return S;
}

static GEN
sol_0(void)
{ GEN S = cgetg(2, t_VEC); gel(S,1) = mkvec2(gen_0,gen_0); return S; }

/* Given a tnf structure as returned by thueinit, a RHS and
 * optionally the solutions to the norm equation, returns the solutions to
 * the Thue equation F(x,y)=a */
GEN
thue(GEN tnf, GEN rhs, GEN ne)
{
  pari_sp av = avma;
  GEN POL, C, L, x3, S;

  if (typ(tnf) == t_POL) tnf = thueinit(tnf, 0, DEFAULTPREC);
  if (!checktnf(tnf)) pari_err_TYPE("thue [please apply thueinit()]", tnf);
  if (typ(rhs) != t_INT) pari_err_TYPE("thue",rhs);

  /* solve P(x,y) = rhs <=> POL(L x, y) = C rhs, with POL monic in Z[X] */
  POL = gel(tnf,1);
  C = gel(POL,2); rhs = gmul(C, rhs);
  if (typ(rhs) != t_INT) { avma = av; return cgetg(1, t_VEC); }
  L = gel(POL,3);
  POL = gel(POL,1);

  S = cgetg(1,t_VEC);
  if (lg(tnf) == 8)
  {
    if (!signe(rhs)) { avma = av; return sol_0(); }
    x3 = LargeSols(POL, tnf, rhs, ne, &S);
    if (!x3) { avma = (pari_sp)S; return S; }
    S = SmallSols(S, x3, POL, rhs);
  }
  else if (typ(gel(tnf,2)) == t_REAL)
  { /* Case s=0. All solutions are "small". */
    GEN c0 = gel(tnf,2); /* t_REAL */
    if (!signe(rhs)) { avma = av; return sol_0(); }
    x3 = sqrtnr(mulir(absi(rhs),c0), degpol(POL));
    x3 = addrr(x3, dbltor(0.1)); /* guard from round-off errors */
    S = SmallSols(S, x3, POL, rhs);
  }
  else if (typ(gmael(tnf,2,1)) == t_VEC) /* reducible case, pure power*/
  {
    long e;
    tnf = gel(tnf,2);
    e = itos( gel(tnf,2) );
    if (!signe(rhs)) { avma = av; return sol_0(); }

    if (!Z_ispowerall(rhs, e, &rhs)) { avma = av; return cgetg(1, t_VEC); }
    tnf = gel(tnf,1);
    S = thue(tnf, rhs, NULL);
    if (odd(e)) S = shallowconcat(S, thue(tnf, negi(rhs), NULL));
  }
  else if (typ(gel(tnf,2)) == t_VEC) /* other reducible cases */
  { /* solve f^e * g = rhs, f irreducible factor of smallest degree */
    GEN P, D, v = gmael(tnf, 2, 1), R = gmael(tnf, 2, 2);
    long i, l, degf = v[1], e = v[2], va = v[3], vb = v[4];
    if (!signe(rhs)) {
      if (degf == 1) pari_err_DOMAIN("thue","#sols","=",strtoGENstr("oo"),rhs);
      avma = av; return cgetg(1, t_VEC);
    }
    P = cgetg(lg(POL), t_POL); P[1] = POL[1];
    D = divisors(rhs); l = lg(D);
    for (i = 1; i < l; i++)
    {
      GEN Rab, ry, df = gel(D,i), dg = diviiexact(rhs, df);
      long k;

      if (e > 1 && !Z_ispowerall(df, e, &df)) continue;
      /* Rab: univariate polynomial in Z[Y], whose roots are the possible y. */
      /* Here and below, Rab != 0 */
      Rab = gsubst(gsubst(R, va, df), vb, dg);
      ry = nfrootsQ(Rab);
      for (k = 1; k < lg(ry); k++)
        if (typ(gel(ry,k)) == t_INT) check_y(&S, P, POL, gel(ry,k), rhs);
      if (odd(e)) {
        Rab = gsubst(gsubst(R, va, negi(df)), vb, negi(dg));
        ry = nfrootsQ(Rab);
        for (k = 1; k < lg(ry); k++)
          if (typ(gel(ry,k)) == t_INT) check_y(&S, P, POL, gel(ry,k), rhs);
      }
    }
  }
  return gerepilecopy(av, filter_sol_x(S, L));
}

/********************************************************************/
/**                                                                **/
/**                      BNFISINTNORM (K. Belabas)                 **/
/**                                                                **/
/********************************************************************/
struct sol_abs
{
  GEN rel; /* Primes PR[i] above a, expressed on generators of Cl(K) */
  GEN partrel; /* list of vectors, partrel[i] = rel[1..i] * u[1..i] */
  GEN cyc;     /* orders of generators of Cl(K) given in bnf */

  long *f;     /* f[i] = f(PR[i]/p), inertia degree */
  long *n;     /* a = prod p^{ n_p }. n[i]=n_p if PR[i] divides p */
  long *next;  /* index of first P above next p, 0 if p is last */
  long *S;     /* S[i] = n[i] - sum_{ 1<=k<=i } f[k]*u[k] */
  long *u;     /* We want principal ideals I = prod PR[i]^u[i] */
  GEN  normsol;/* lists of copies of the u[] which are solutions */

  long nPR;    /* length(T->rel) = #PR */
  long sindex, smax; /* current index in T->normsol; max. index */
};

/* u[1..i] has been filled. Norm(u) is correct.
 * Check relations in class group then save it. */
static void
test_sol(struct sol_abs *T, long i)
{
  long k, l;
  GEN s;

  if (T->partrel && !ZV_dvd(gel(T->partrel, i),  T->cyc)) return;
  if (T->sindex == T->smax)
  { /* no more room in solution list: enlarge */
    long new_smax = T->smax << 1;
    GEN  new_normsol = new_chunk(new_smax+1);

    for (k=1; k<=T->smax; k++) gel(new_normsol,k) = gel(T->normsol,k);
    T->normsol = new_normsol; T->smax = new_smax;
  }
  gel(T->normsol, ++T->sindex) = s = cgetg_copy(T->u, &l);
  for (k=1; k <= i; k++) s[k] = T->u[k];
  for (   ; k < l;  k++) s[k] = 0;
  if (DEBUGLEVEL>2)
  {
    err_printf("sol = %Ps\n",s);
    if (T->partrel) err_printf("T->partrel = %Ps\n",T->partrel);
    err_flush();
  }
}
/* partrel[i] <-- partrel[i-1] + u[i] * rel[i] */
static void
fix_partrel(struct sol_abs *T, long i)
{
  pari_sp av = avma;
  GEN part1 = gel(T->partrel,i);
  GEN part0 = gel(T->partrel,i-1);
  GEN rel = gel(T->rel, i);
  ulong u = T->u[i];
  long k, l = lg(part1);
  for (k=1; k < l; k++)
    affii(addii(gel(part0,k), muliu(gel(rel,k), u)), gel(part1,k));
  avma = av;
}

/* Recursive loop. Suppose u[1..i] has been filled
 * Find possible solutions u such that, Norm(prod PR[i]^u[i]) = a, taking
 * into account:
 *  1) the relations in the class group if need be.
 *  2) the factorization of a. */
static void
isintnorm_loop(struct sol_abs *T, long i)
{
  if (T->S[i] == 0) /* sum u[i].f[i] = n[i], do another prime */
  {
    long k, next = T->next[i];
    if (next == 0) { test_sol(T, i); return; } /* no primes left */

    /* some primes left */
    if (T->partrel) gaffect(gel(T->partrel,i), gel(T->partrel, next-1));
    for (k=i+1; k < next; k++) T->u[k] = 0;
    i = next-1;
  }
  else if (i == T->next[i]-2 || i == T->nPR-1)
  { /* only one Prime left above prime; change prime, fix u[i+1] */
    long q;
    if (T->S[i] % T->f[i+1]) return;
    q = T->S[i] / T->f[i+1];
    i++; T->u[i] = q;
    if (T->partrel) fix_partrel(T,i);
    if (T->next[i] == 0) { test_sol(T,i); return; }
  }

  i++; T->u[i] = 0;
  if (T->partrel) gaffect(gel(T->partrel,i-1), gel(T->partrel,i));
  if (i == T->next[i-1])
  { /* change prime */
    if (T->next[i] == i+1 || i == T->nPR) /* only one Prime above p */
    {
      T->S[i] = 0;
      T->u[i] = T->n[i] / T->f[i]; /* we already know this is exact */
      if (T->partrel) fix_partrel(T, i);
    }
    else T->S[i] = T->n[i];
  }
  else T->S[i] = T->S[i-1]; /* same prime, different Prime */
  for(;;)
  {
    isintnorm_loop(T, i);
    T->S[i] -= T->f[i]; if (T->S[i] < 0) break;
    T->u[i]++;
    if (T->partrel) {
      pari_sp av = avma;
      gaffect(ZC_add(gel(T->partrel,i), gel(T->rel,i)), gel(T->partrel,i));
      avma = av;
    }
  }
}

static int
get_sol_abs(struct sol_abs *T, GEN bnf, GEN a, GEN *ptPR)
{
  GEN nf = bnf_get_nf(bnf);
  GEN fact = absi_factor(a), P = gel(fact,1), E = gel(fact,2), PR;
  long N = nf_get_degree(nf), nP = lg(P)-1, Ngen, max, nPR, i, j;

  max = nP*N; /* upper bound for T->nPR */
  T->f = new_chunk(max+1);
  T->n = new_chunk(max+1);
  T->next = new_chunk(max+1);
  *ptPR = PR = cgetg(max+1, t_VEC); /* length to be fixed later */

  nPR = 0;
  for (i = 1; i <= nP; i++)
  {
    GEN L = idealprimedec(nf, gel(P,i));
    long lL = lg(L), gcd, k, v;
    ulong vn = itou(gel(E,i));

    /* check that gcd_{P | p} f_P  divides  n_p */
    gcd = pr_get_f(gel(L,1));
    for (j=2; gcd > 1 && j < lL; j++) gcd = ugcd(gcd, pr_get_f(gel(L,j)));
    if (gcd > 1 && vn % gcd)
    {
      if (DEBUGLEVEL>2)
      { err_printf("gcd f_P  does not divide n_p\n"); err_flush(); }
      return 0;
    }
    v = (i==nP)? 0: nPR + lL;
    for (k = 1; k < lL; k++)
    {
      GEN pr = gel(L,k);
      gel(PR, ++nPR) = pr;
      T->f[nPR] = pr_get_f(pr) / gcd;
      T->n[nPR] = vn / gcd;
      T->next[nPR] = v;
    }
  }
  T->nPR = nPR;
  setlg(PR, nPR + 1);

  T->u = cgetg(nPR+1, t_VECSMALL);
  T->S = new_chunk(nPR+1);
  T->cyc = bnf_get_cyc(bnf);
  Ngen = lg(T->cyc)-1;
  if (Ngen == 0)
    T->rel = T->partrel = NULL; /* trivial Cl(K), no relations to check */
  else
  {
    int triv = 1;
    T->partrel = new_chunk(nPR+1);
    T->rel = new_chunk(nPR+1);
    for (i=1; i <= nPR; i++)
    {
      GEN c = isprincipal(bnf, gel(PR,i));
      gel(T->rel,i) = c;
      if (triv && !ZV_equal0(c)) triv = 0; /* non trivial relations in Cl(K)*/
    }
    /* triv = 1: all ideals dividing a are principal */
    if (triv) T->rel = T->partrel = NULL;
  }
  if (T->partrel)
  {
    long B = ZV_max_lg(T->cyc) + 3;
    for (i = 0; i <= nPR; i++)
    { /* T->partrel[0] also needs to be initialized */
      GEN c = cgetg(Ngen+1, t_COL); gel(T->partrel,i) = c;
      for (j=1; j<=Ngen; j++)
      {
        GEN z = cgeti(B); gel(c,j) = z;
        z[1] = evalsigne(0)|evallgefint(B);
      }
    }
  }
  T->smax = 511;
  T->normsol = new_chunk(T->smax+1);
  T->S[0] = T->n[1];
  T->next[0] = 1;
  T->sindex = 0;
  isintnorm_loop(T, 0); return 1;
}

/* Look for unit of norm -1. Return 1 if it exists and set *unit, 0 otherwise */
static long
get_unit_1(GEN bnf, GEN *unit)
{
  GEN v, nf = bnf_get_nf(bnf);
  long i, n = nf_get_degree(nf);

  if (DEBUGLEVEL > 2) err_printf("looking for a fundamental unit of norm -1\n");
  if (odd(n)) { *unit = gen_m1; return 1; }
  v = nfsign_units(bnf, NULL, 0);
  for (i = 1; i < lg(v); i++)
    if ( Flv_sum( gel(v,i), 2) ) { *unit = gel(bnf_get_fu(bnf), i); return 1; }
  return 0;
}

GEN
bnfisintnormabs(GEN bnf, GEN a)
{
  struct sol_abs T;
  GEN nf, res, PR;
  long i;

  if (typ(a) != t_INT) pari_err_TYPE("bnfisintnormabs",a);
  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf);
  if (!signe(a)) return mkvec(gen_0);
  if (is_pm1(a)) return mkvec(gen_1);

  if (!get_sol_abs(&T, bnf, a, &PR)) return cgetg(1, t_VEC);
  /* |a| > 1 => T.nPR > 0 */
  res = cgetg(T.sindex+1, t_VEC);
  for (i=1; i<=T.sindex; i++)
  {
    GEN x = vecsmall_to_col( gel(T.normsol,i) );
    x = isprincipalfact(bnf, NULL, PR, x, nf_FORCE | nf_GEN_IF_PRINCIPAL);
    gel(res,i) = coltoliftalg(nf, x); /* x solution, up to sign */
  }
  return res;
}

GEN
bnfisintnorm(GEN bnf, GEN a)
{
  pari_sp av = avma;
  GEN nf = checknf(bnf), T = nf_get_pol(nf), unit = NULL;
  GEN z = bnfisintnormabs(bnf, a);
  long sNx, i, j, N = degpol(T), l = lg(z), sa = signe(a);
  long norm_1 = 0; /* gcc -Wall */

  /* update z in place to get correct signs: multiply by unit of norm -1 if
   * it exists, otherwise delete solution with wrong sign */
  for (i = j = 1; i < l; i++)
  {
    GEN x = gel(z,i);
    int xpol = (typ(x) == t_POL);

    if (xpol) sNx = signe(ZX_resultant(T, Q_primpart(x)));
    else      sNx = gsigne(x) < 0 && odd(N) ? -1 : 1;
    if (sNx != sa)
    {
      if (! unit) norm_1 = get_unit_1(bnf, &unit);
      if (!norm_1)
      {
        if (DEBUGLEVEL > 2) err_printf("%Ps eliminated because of sign\n",x);
        continue;
      }
      if (xpol) x = (unit == gen_m1)? RgX_neg(x): RgXQ_mul(unit,x,T);
      else      x = (unit == gen_m1)? gneg(x): RgX_Rg_mul(unit,x);
    }
    gel(z,j++) = x;
  }
  setlg(z, j);
  return gerepilecopy(av, z);
}
