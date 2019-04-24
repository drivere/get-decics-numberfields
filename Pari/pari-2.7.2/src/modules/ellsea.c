/* Copyright (C) 2008  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* This file is a C version by Bill Allombert of the 'ellsea' GP package
 * whose copyright statement is as follows:
Authors:
  Christophe Doche   <cdoche@math.u-bordeaux.fr>
  Sylvain Duquesne <duquesne@math.u-bordeaux.fr>

Universite Bordeaux I, Laboratoire A2X
For the AREHCC project, see http://www.arehcc.com/

Contributors:
  Karim Belabas (code cleanup and package release, faster polynomial arithmetic)

'ellsea' is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER. */

/* Extension to non prime finite fields by Bill Allombert 2012 */

#include "pari.h"
#include "paripriv.h"

static GEN modular_eqn;

void
pari_init_seadata(void)  { modular_eqn = NULL; }
void
pari_close_seadata(void) { if (modular_eqn) gunclone(modular_eqn); }

static int
FqX_equal(GEN x, GEN y) { return gequal(x,y); }

static int
FlxX_equal(GEN x, GEN y) { return gequal(x,y); }

static char *
seadata_filename(ulong ell)
{ return stack_sprintf("%s/seadata/sea%ld", pari_datadir, ell); }

static GEN
get_seadata(ulong ell)
{
  pari_sp av=avma;
  GEN eqn;
  char *s = seadata_filename(ell);
  pariFILE *F = pari_fopengz(s);
  if (!F) return NULL;
  if (ell==0)
  {
    eqn = gp_readvec_stream(F->file);
    pari_fclose(F);
    modular_eqn = gclone(eqn);
    avma=av;
    return gen_0;
  } else {
    eqn = gp_read_stream(F->file);
    pari_fclose(F);
    return eqn;
  }
}

/*Builds the modular equation corresponding to the vector list. Shallow */
static GEN
list_to_pol(GEN list, long vx, long vy)
{
  long i, l = lg(list);
  GEN P = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN L = gel(list,i);
    if (typ(L) == t_VEC) L = RgV_to_RgX_reverse(L, vy);
    gel(P, i) = L;
  }
  return RgV_to_RgX_reverse(P, vx);
}

struct meqn { char type; GEN eq; };

static int
get_modular_eqn(struct meqn *M, ulong ell, long vx, long vy)
{
  GEN eqn;
  long idx = uprimepi(ell)-1;
  if (!modular_eqn && !get_seadata(0)) pari_err_PACKAGE("seadata");
  if (idx && idx<lg(modular_eqn))
    eqn = gel(modular_eqn, idx);
  else
    eqn = get_seadata(ell);
  if (!eqn) return 0;
  M->type = *GSTR(gel(eqn, 2));
  M->eq = list_to_pol(gel(eqn, 3), vx, vy);
  return 1;
}

static void
err_modular_eqn(long ell)
{ pari_err_FILE("seadata file", seadata_filename(ell)); }

GEN
ellmodulareqn(long ell, long vx, long vy)
{
  pari_sp av = avma;
  struct meqn meqn;
  if (vx<0) vx=0;
  if (vy<0) vy=fetch_user_var("y");
  if (varncmp(vx,vy)>=0)
    pari_err_PRIORITY("ellmodulareqn", pol_x(vx), ">=", vy);
  if (ell < 0 || !uisprime(ell))
    pari_err_PRIME("ellmodulareqn (level)", stoi(ell));

  if (!get_modular_eqn(&meqn, ell, vx, vy))
    err_modular_eqn(ell);
  return gerepilecopy(av,mkvec2(meqn.eq, stoi(meqn.type=='A')));
}

/*Gives the first precS terms of the Weierstrass series related to */
/*E: y^2 = x^3 + a4x + a6.  Assumes (precS-2)*(2precS+3) < ULONG_MAX, i.e.
 * precS < 46342 in 32-bit machines */
static GEN
find_coeff(GEN a4, GEN a6, GEN T, GEN p, long precS)
{
  GEN res = cgetg(precS+1, t_VEC);
  long k, h;
  if (precS == 0) return res;
  gel(res, 1) = Fq_div(a4, stoi(-5), T, p);
  if (precS == 1) return res;
  gel(res, 2) = Fq_div(a6, stoi(-7), T, p);
  for (k = 3; k <= precS; ++k)
  {
    pari_sp btop = avma;
    GEN a = gen_0;
    for (h = 1; h <= k-2; h++)
      a = Fq_add(a, Fq_mul(gel(res, h), gel(res, k-1-h), T, p), T, p);
    a = Fq_div(Fq_mulu(a, 3, T, p), utoi((k-2) * (2*k + 3)), T, p);
    gel(res, k) = gerepileupto(btop, a);
  }
  return res;
}

/* Given power series s1 and s2, finds a polynomial P such that s2 = P(s1) */
static GEN
find_transformation(GEN s2, GEN s1)
{
  pari_sp ltop = avma, btop, st_lim;
  long i, vx = varn(s1), vs1 = valp(s1), vs2 = valp(s2), degP = vs2/vs1;
  GEN invs1coeff = ginv(gel(s1, 2)), P = gen_0, s1pl = cgetg(degP+1, t_VEC);

  gel(s1pl, 1) = s1;
  for (i = 2; i <= degP; i++) gel(s1pl, i) = gmul(s1, gel(s1pl, i-1));
  btop = avma; st_lim = stack_lim(btop, 1);
  for (i = 0; i < degP; i++)
  {
    GEN Pcoeff = gmul(gel(s2,2), invs1coeff);
    P = gadd(P, gmul(Pcoeff, monomial(gen_1, degP-i, vx)));
    s2 = gsub(s2, gmul(Pcoeff, gel(s1pl, degP-i)));
    if (low_stack(st_lim, stack_lim(btop, 1))) gerepileall(btop, 2, &P, &s2);
  }
  P = gadd(P, gmul(gel(s2,2), invs1coeff));
  return gerepileupto(ltop, P);
}

static GEN
compute_W(GEN a4, GEN a6, GEN T, GEN p, long vx, long precS)
{
  pari_sp ltop = avma;
  GEN c  = find_coeff(a4, a6, T, p, precS);
  GEN s  = RgX_inflate(RgV_to_RgX(c,vx), 2);
  GEN z2 = monomial(gen_1, 2, vx);
  s = gadd(gadd(ginv(z2), gmul(s, z2)), zeroser(vx, 2*precS));
  return gerepileupto(ltop, s);
}

/*Finds numerator phi of the isogeny between Eb and Ec whose denominator is h*/
static GEN
find_numerator_isogeny(GEN Eba4, GEN Eba6, GEN Eca4, GEN Eca6, GEN h, GEN T, GEN p,
                       long precS)
{
  pari_sp ltop = avma;
  GEN mod1p = gmodulsg(1,p);
  GEN mod = T ? gmodulo(mod1p, gmul(get_FpX_mod(T), mod1p)): mod1p;
  GEN WEb = gmul(compute_W(Eba4, Eba6, T, p, varn(h), precS), mod);
  GEN WEc = gmul(compute_W(Eca4, Eca6, T, p, varn(h), precS), mod);
  GEN den = poleval(h, WEb);
  return gerepileupto(ltop, find_transformation(gmul(gsqr(den), WEc), WEb));
}

/****************************************************************************/
/*               SIMPLE ELLIPTIC CURVE OVER Fq                              */
/****************************************************************************/

static GEN
Fq_ellj(GEN a4, GEN a6, GEN T, GEN p)
{
  pari_sp ltop=avma;
  GEN a43 = Fq_mulu(Fq_powu(a4, 3, T, p), 4, T, p);
  GEN j   = Fq_div(Fq_mulu(a43, 1728, T, p),
                   Fq_add(a43, Fq_mulu(Fq_sqr(a6, T, p), 27, T, p), T, p), T, p);
  return gerepileupto(ltop, j);
}

/****************************************************************************/
/*                              EIGENVALUE                                  */
/****************************************************************************/

struct eigen_ellinit
{
  GEN a4, h, T, p;
  GEN RHS, DRHS, X12, Gr, nGr,O;
  ulong pp;
};

static void
init_eigen(struct eigen_ellinit *Edat, GEN a4, GEN a6, GEN h, GEN T, GEN p)
{
  pari_sp ltop = avma;
  GEN RHS  = FqX_rem(mkpoln(4, gen_1, gen_0, a4, a6), h, T, p);
  GEN DRHS = FqX_rem(mkpoln(3, utoi(3), gen_0, a4), h, T, p);
  GEN lambda = FqXQ_div(DRHS, FqX_mulu(RHS, 4, T, p), h, T, p);
  GEN C = FqX_sub(FqXQ_mul(lambda, DRHS, h, T, p), monomial(gen_2,1,0), T, p);
  GEN D = FqXQ_mul(FqX_mulu(lambda, 2, T, p),FqX_sub(pol_x(0), C, T, p), h, T, p);
  GEN X12 = mkvec2(C, FqX_Fq_add(D, gen_m1, T, p));
  GEN Gr = T ? FpXQXQ_halfFrobenius(RHS, h, T, p):
               FpXQ_pow(RHS, shifti(p, -1), h, p);
  GEN nGr = FqX_neg(Gr, T, p);
  gerepileall(ltop, 5, &RHS, &DRHS, &X12, &Gr, &nGr);
  Edat->a4    = gcopy(a4);
  Edat->h     = gcopy(h);
  Edat->T     = T;
  Edat->p     = p;
  Edat->pp    = 0;
  Edat->RHS   = RHS;
  Edat->DRHS  = DRHS;
  Edat->X12   = X12;
  Edat->Gr    = Gr;
  Edat->nGr   = nGr;
  Edat->O     = mkvec2(pol_x(0), pol_1(0));
}

static void
init_eigenu(struct eigen_ellinit *Edat, GEN a4, GEN a6, GEN h, GEN T, ulong p)
{
  pari_sp ltop = avma;
  long vT = get_Flx_var(T);
  GEN g1 = pol1_Flx(vT), g0 = pol0_Flx(vT);
  GEN RHS  = FlxqX_rem(mkpoln(4, g1, g0, a4, a6), h, T, p);
  GEN DRHS = FlxqX_rem(mkpoln(3, Fl_to_Flx(3, T[1]), g0, a4), h, T, p);
  GEN lambda = FlxqXQ_div(DRHS, FlxX_Fl_mul(RHS, 4, p), h, T, p);
  GEN C = FlxX_sub(FlxqXQ_mul(lambda, DRHS, h, T, p), monomial(Fl_to_Flx(2,vT),1,0), p);
  GEN D = FlxqXQ_mul(FlxX_double(lambda, p),FlxX_sub(pol_x(0), C, p), h, T, p);
  GEN X12 = mkvec2(C, FlxX_Flx_add(D, Fl_to_Flx(p-1,vT), p));
  GEN Gr = FlxqXQ_halfFrobenius(RHS,h,T,p);
  GEN nGr = FlxX_neg(Gr, p);
  GEN O = mkvec2(monomial(g1,1,0), monomial(g1,0,0));
  gerepileall(ltop, 6, &RHS, &DRHS, &X12, &Gr, &nGr, &O);
  Edat->a4    = gcopy(a4);
  Edat->h     = gcopy(h);
  Edat->T     = T;
  Edat->p     = NULL;
  Edat->pp    = p;
  Edat->RHS   = RHS;
  Edat->DRHS  = DRHS;
  Edat->X12   = X12;
  Edat->Gr    = Gr;
  Edat->nGr   = nGr;
  Edat->O     = O;
}
static GEN
eigen_elldbl(void *E, GEN P)
{
  pari_sp ltop = avma;
  struct eigen_ellinit *Edat=(struct eigen_ellinit *)E;
  GEN T = Edat->T, p = Edat->p, h = Edat->h, x, y;
  if (ell_is_inf(P)) return gcopy(P);
  x = gel(P,1), y = gel(P,2);
  if (FqX_equal(x, pol_x(0)) && FqX_equal(y, pol_1(0)))
    return Edat->X12;
  else
  {
    GEN t1 = FqX_Fq_add(FqX_mulu(FqXQ_sqr(x,h,T,p),3,T, p), Edat->a4, T, p);
    GEN t2 = FqXQ_mul(FqX_mulu(y, 2, T, p), Edat->RHS, h, T, p);
    GEN lambda = FqXQ_div(t1, t2, h, T, p);
    GEN C = FqX_sub(FqXQ_mul(FqXQ_sqr(lambda, h, T, p), Edat->RHS, h, T, p),
                    FqX_mulu(x, 2, T, p), T, p);
    GEN D = FqX_sub(FqXQ_mul(lambda, FqX_sub(x, C, T, p), h, T, p), y, T, p);
    return gerepilecopy(ltop, mkvec2(C,D));
  }
}

/* Returns the addition of [P[1], P[2]*Y] and of [Q[1], Q[2]*Y]
 * Computations are done modulo Y^2 - (X^3 + a4X + a6)
 * An inversion is equivalent to 4M, so that this function requires about 7M
 * which is the same as with the method using ell-division polynomials
 * Working in mixed projective coordinates would require 11M */
static GEN
eigen_elladd(void *E, GEN P, GEN Q)
{
  pari_sp ltop = avma;
  struct eigen_ellinit *Edat=(struct eigen_ellinit *)E;
  GEN Px, Py, Qx, Qy;
  GEN T = Edat->T, p = Edat->p, h = Edat->h, lambda, C, D;
  if (ell_is_inf(P)) return gcopy(Q);
  if (ell_is_inf(Q)) return gcopy(P);
  Px = gel(P,1); Py = gel(P,2);
  Qx = gel(Q,1); Qy = gel(Q,2);
  if (FqX_equal(Px, Qx))
  {
    if (FqX_equal(Py, Qy))
      return eigen_elldbl(E, P);
    else
      return ellinf();
  }
  lambda = FqXQ_div(FqX_sub(Py, Qy, T, p), FqX_sub(Px, Qx, T, p), h, T, p);
  C = FqX_sub(FqX_sub(FqXQ_mul(FqXQ_sqr(lambda, h, T, p), Edat->RHS, h, T, p), Px, T, p), Qx, T, p);
  D = FqX_sub(FqXQ_mul(lambda, FqX_sub(Px, C, T, p), h, T, p), Py, T, p);
  return gerepilecopy(ltop, mkvec2(C,D));
}

static GEN
eigenu_elldbl(void *E, GEN P)
{
  pari_sp ltop = avma;
  struct eigen_ellinit *Edat=(struct eigen_ellinit *)E;
  GEN T = Edat->T, h = Edat->h, x, y;
  long vT = get_Flx_var(T);
  ulong p = Edat->pp;
  if (ell_is_inf(P)) return gcopy(P);
  x = gel(P,1), y = gel(P,2);
  if (FlxX_equal(x, monomial(pol1_Flx(vT),1,0)) && FlxX_equal(y, monomial(pol1_Flx(vT),0,0)))
    return Edat->X12;
  else
  {
    GEN t1 = FlxX_Flx_add(FlxX_triple(FlxqXQ_sqr(x,h,T,p),p), Edat->a4, p);
    GEN t2 = FlxqXQ_mul(FlxX_double(y, p), Edat->RHS, h, T, p);
    GEN lambda = FlxqXQ_div(t1, t2, h, T, p);
    GEN C = FlxX_sub(FlxqXQ_mul(FlxqXQ_sqr(lambda, h, T, p), Edat->RHS, h, T, p),
                     FlxX_double(x, p), p);
    GEN D = FlxX_sub(FlxqXQ_mul(lambda, FlxX_sub(x, C, p), h, T, p), y, p);
    return gerepilecopy(ltop, mkvec2(C,D));
  }
}

/* Returns the addition of [P[1], P[2]*Y] and of [Q[1], Q[2]*Y]
 * Computations are done modulo Y^2 - (X^3 + a4X + a6)
 * An inversion is equivalent to 4M, so that this function requires about 7M
 * which is the same as with the method using ell-division polynomials
 * Working in mixed projective coordinates would require 11M */
static GEN
eigenu_elladd(void *E, GEN P, GEN Q)
{
  pari_sp ltop = avma;
  struct eigen_ellinit *Edat=(struct eigen_ellinit *)E;
  GEN Px, Py, Qx, Qy;
  GEN T = Edat->T, h = Edat->h, lambda, C, D;
  ulong p = Edat->pp;
  if (ell_is_inf(P)) return gcopy(Q);
  if (ell_is_inf(Q)) return gcopy(P);
  Px = gel(P,1); Py = gel(P,2);
  Qx = gel(Q,1); Qy = gel(Q,2);
  if (FlxX_equal(Px, Qx))
  {
    if (FlxX_equal(Py, Qy))
      return eigenu_elldbl(E, P);
    else
      return ellinf();
  }
  lambda = FlxqXQ_div(FlxX_sub(Py, Qy, p), FlxX_sub(Px, Qx, p), h, T, p);
  C = FlxX_sub(FlxX_sub(FlxqXQ_mul(FlxqXQ_sqr(lambda, h, T, p), Edat->RHS, h, T, p), Px, p), Qx, p);
  D = FlxX_sub(FlxqXQ_mul(lambda, FlxX_sub(Px, C, p), h, T, p), Py, p);
  return gerepilecopy(ltop, mkvec2(C,D));
}

static GEN
eigen_ellmulu(struct eigen_ellinit *E, GEN z, ulong n)
{
  pari_sp av = avma;
  if (!n || ell_is_inf(z)) return mkvec(gen_0);
  if (n == 1) return gcopy(z);
  if (E->pp)
    return gerepileupto(av, gen_powu(z, n, E, &eigenu_elldbl, &eigenu_elladd));
  else
    return gerepileupto(av, gen_powu(z, n, E, &eigen_elldbl, &eigen_elladd));
}

/*Finds the eigenvalue of the Frobenius given E, ell odd prime, h factor of the
 *ell-division polynomial, p and tr the possible values for the trace
 *(useful for primes with one root)*/
static ulong
find_eigen_value(GEN a4, GEN a6, ulong ell, GEN h, GEN T, GEN p, GEN tr)
{
  pari_sp ltop = avma;
  GEN BP, Dr;
  ulong t;
  struct eigen_ellinit Edat;
  ulong pp = T ?itou_or_0(p): 0;
  if (pp)
    init_eigenu(&Edat, ZX_to_Flx(a4,pp), ZX_to_Flx(a6,pp),
                       ZXX_to_FlxX(h,pp, get_FpX_var(T)), ZXT_to_FlxT(T,pp), pp);
  else
    init_eigen(&Edat, a4, a6, h, T, p);
  Dr = BP = Edat.O;
  /*[0,Gr], BP, Dr are not points on the curve. */
  /*To obtain the corresponding points, multiply the y-coordinates by Y */
  if (!tr || lg(tr)==1)
  {
    pari_sp btop = avma;
    for (t = 1; t <= (ell>>1); t++)
    {
      if (gequal(gel(Dr,2), Edat.Gr))  { avma = ltop; return t; }
      if (gequal(gel(Dr,2), Edat.nGr)) { avma = ltop; return ell-t; }
      Dr = pp ? eigenu_elladd(&Edat, Dr, BP): eigen_elladd(&Edat, Dr, BP);
      Dr = gerepileupto(btop, Dr);
    }
    pari_err_BUG("find_eigen_value");
    return 0; /* NOT REACHED */
  }
  else
  {
    t = Fl_div(tr[1], 2, ell);
    if (t < (ell>>1)) t = ell - t;
    Dr = eigen_ellmulu(&Edat, BP, t);
    if (!gequal(gel(Dr,2), Edat.Gr)) t = ell - t;
    avma = ltop; return t;
  }
}

/*Finds the eigenvalue of the Frobenius modulo ell^k given E, ell, k, h factor
 *of the ell-division polynomial, lambda the previous eigen value and p */
static ulong
find_eigen_value_power(GEN a4, GEN a6, ulong ell, long k, GEN h, ulong lambda, GEN T, GEN p)
{
  pari_sp ltop = avma;
  pari_sp btop, st_lim;
  struct eigen_ellinit Edat;
  GEN BP, Dr, Gr, nGr;
  /*[0,Gr], BP, Dr are not points on the curve. */
  /*To obtain the corresponding points, multiply the y-coordinates by Y */
  ulong t, ellk1 = upowuu(ell, k-1), ellk = ell*ellk1;
  ulong pp = T ?itou_or_0(p): 0;
  if (pp)
    init_eigenu(&Edat, ZX_to_Flx(a4,pp), ZX_to_Flx(a6,pp),
        ZXX_to_FlxX(h, pp, get_FpX_var(T)), ZXT_to_FlxT(T,pp), pp);
  else
    init_eigen(&Edat, a4, a6, h, T, p);
  BP = eigen_ellmulu(&Edat, Edat.O, ellk1);
  Dr = eigen_ellmulu(&Edat, Edat.O, lambda);
  Gr = Edat.Gr; nGr = Edat.nGr;

  btop = avma; st_lim = stack_lim(btop, 1);
  for (t = 0; t < ellk; t += ellk1)
  {
    if (gequal(gel(Dr,2), Gr))  { avma = ltop; return t+lambda; }
    if (gequal(gel(Dr,2), nGr)) { avma = ltop; return ellk-(t+lambda); }
    Dr = pp ? eigenu_elladd(&Edat, Dr, BP): eigen_elladd(&Edat, Dr, BP);
    if (low_stack(st_lim, stack_lim(btop, 1)))
      Dr = gerepileupto(btop, Dr);
  }
  pari_err_BUG("find_eigen_value_power");
  return 0; /* NOT REACHED */
}

/*Finds the kernel polynomial h, dividing the ell-division polynomial from the
  isogenous curve Eb and trace term pp1. Uses CCR algorithm and returns h.
  Return NULL if E and Eb are *not* isogenous. */
static GEN
find_kernel(GEN a4, GEN a6, ulong ell, GEN a4t, GEN a6t, GEN pp1, GEN T, GEN p)
{
  const long ext = 2;
  pari_sp ltop = avma;
  GEN M, N, V, K, K1, K2, v, tlist, res;
  long i, j, k;
  long deg = (ell - 1)/2, dim = deg + ext;
  GEN Coeff  = find_coeff(a4, a6, T, p, dim);
  GEN Coefft = find_coeff(a4t, a6t, T, p, dim);
  GEN psi2  = mkpoln(4, utoi(4), gen_0, Fq_mulu(a4, 4, T, p), Fq_mulu(a6, 4, T, p));
  GEN list  = cgetg(dim+1, t_VEC);
  GEN Dpsi2 = mkpoln(3, utoi(6), gen_0, Fq_mulu(a4, 2, T, p));
  gel(list, 1) = Dpsi2;
  for (k = 2; k <= dim; k++)
  {
    pari_sp btop = avma;
    GEN tsil = gel(list, k-1);
    GEN r = FqX_Fq_mul(Dpsi2, gel(tsil,3), T, p);
    for (j = 4; j < lg(tsil); j++)
    {
      long o = j - 2;
      GEN D = FqX_add(RgX_shift_shallow(Dpsi2, 1), FqX_mulu(psi2, o-1, T, p), T, p);
      GEN E = FqX_Fq_mul(D, Fq_mulu(gel(tsil, j), o, T, p), T, p);
      r = FqX_add(r, RgX_shift_shallow(E, o-2), T, p);
    }
    gel(list, k) = gerepileupto(btop, r);
  }
  for (k = 2; k <= dim; k++)
  {
     GEN C = Fq_inv(shifti(mpfact(2*k),-1), T, p);
     gel(list, k) = FqX_Fq_mul(gel(list, k), C, T, p);
  }
  M = shallowtrans(RgXV_to_RgM(list, dim+2));
  N = vecslice(M, 1, dim);
  V = FqC_sub(Coefft, Coeff, T, p);
  v = shallowconcat(FqM_FqC_gauss(N, V, T, p), mkcol2(gen_0, gen_0));
  K = FqM_ker(M, T, p);
  if (lg(K) != 3) pari_err_BUG("trace not determined in a unique way");
  K1 = FqC_Fq_mul(gel(K,1), Fq_inv(gcoeff(K,1,1), T, p), T, p);
  K2 = FqC_sub(gel(K,2), FqC_Fq_mul(K1, gcoeff(K,1,2), T, p), T, p);
  K2 = FqC_Fq_mul(K2, Fq_inv(gel(K2,2), T, p), T, p);
  K1 = FqC_sub(K1, FqC_Fq_mul(K2, gel(K1,2), T, p), T, p);
  v = FqC_add(v, FqC_Fq_mul(K1, Fq_sub(utoi(deg), gel(v,1), T, p), T, p), T, p);
  v = FqC_add(v, FqC_Fq_mul(K2, Fq_sub(pp1, gel(v,2), T, p), T, p), T, p);
  tlist = cgetg(dim+2, t_VEC);
  gel(tlist, dim+1) = gen_1;
  for (k = 1; k <= dim; k++)
  {
    pari_sp btop = avma;
    GEN s = gel(v, k+1);
    for (i = 1; i < k; i++)
      s = Fq_add(s, Fq_mul(gel(tlist, dim-i+1), gel(v, k-i+1), T, p), T, p);
    gel(tlist, dim-k+1) = gerepileupto(btop, Fq_div(s, stoi(-k), T, p));
  }
  for (i = 1; i <= ext; i++)
    if (signe(gel(tlist, i))) { avma = ltop; return NULL; }
  res = vecslice(tlist, ext+1, dim+1);

  return RgV_to_RgX(res, 0);
}

static GEN
compute_u(GEN gprime, GEN Dxxg, GEN DxJg, GEN DJJg, GEN j, GEN pJ, GEN px, ulong q, GEN E4, GEN E6, GEN T, GEN p)
{
  pari_sp ltop = avma;
  GEN dxxgj = FqX_eval(Dxxg, j, T, p);
  GEN dxJgj = FqX_eval(DxJg, j, T, p);
  GEN dJJgj = FqX_eval(DJJg, j, T, p);
  GEN E42 = Fq_sqr(E4, T, p), E6ovE4 = Fq_div(E6, E4, T, p);
  GEN a = Fq_mul(gprime, dxxgj, T, p);
  GEN b = Fq_mul(Fq_mul(Fq_mulu(j,2*q, T, p), dxJgj, T, p), E6ovE4, T, p);
  GEN c = Fq_mul(Fq_div(Fq_sqr(E6ovE4, T, p), gprime, T, p), j, T, p);
  GEN d = Fq_mul(Fq_mul(c,sqru(q), T, p), Fq_add(pJ, Fq_mul(j, dJJgj, T, p), T, p), T, p);
  GEN e = Fq_sub(Fq_div(E6ovE4,utoi(3), T, p), Fq_div(E42, Fq_mulu(E6,2,T, p), T, p), T, p);
  GEN f = Fq_sub(Fq_sub(b,a,T,p), d, T, p);
  return gerepileupto(ltop, Fq_add(Fq_div(f,px,T,p), Fq_mulu(e,q,T,p), T, p));
}

/* Finds the isogenous EC, and the sum of the x-coordinates of the points in
 * the kernel of the isogeny E -> Eb
 * E: elliptic curve, ell: a prime, meqn: Atkin modular equation
 * g: root of meqn defining isogenous curve Eb. */
static GEN
find_isogenous_from_Atkin(GEN a4, GEN a6, long ell, GEN meqn, GEN g, GEN T, GEN p)
{
  pari_sp ltop = avma, btop;
  GEN Roots, gprime, u1;
  long k, vx = 0, vJ = MAXVARN;
  GEN E4 = Fq_div(a4, stoi(-3), T, p);
  GEN E6 = Fq_mul(a6, shifti(p, -1), T, p);
  GEN E42 = Fq_sqr(E4, T, p);
  GEN E43 = Fq_mul(E4, E42, T, p);
  GEN E62 = Fq_sqr(E6, T, p);
  GEN delta = Fq_div(Fq_sub(E43, E62, T, p), utoi(1728), T, p);
  GEN j = Fq_div(E43, delta, T, p);
  GEN Dx = deriv(meqn, vx);
  GEN DJ = deriv(meqn, vJ);
  GEN Dxg = FpXY_Fq_evaly(Dx, g, T, p, vJ);
  GEN px = FqX_eval(Dxg, j, T, p), dx = Fq_mul(px, g, T, p);
  GEN DJg = FpXY_Fq_evaly(DJ, g, T, p, vJ);
  GEN pJ = FqX_eval(DJg, j, T, p), dJ = Fq_mul(pJ, j, T, p);
  GEN Dxx = deriv(Dx, vx);
  GEN DxJg = FqX_deriv(Dxg, T, p);

  GEN Dxxg = FpXY_Fq_evaly(Dxx, g, T, p, vJ);
  GEN DJJg = FqX_deriv(DJg, T, p);

  GEN a = Fq_mul(dJ, Fq_mul(g, E6, T, p), T, p);
  GEN b = Fq_mul(E4, dx, T, p);
  if (!signe(a) || !signe(b))
  { /* TODO: understand what this means and use the information */
    if (DEBUGLEVEL)
      err_printf("find_isogenous_from_Atkin: division by zero at prime %ld", ell);
    avma = ltop; return NULL;
  }
  gprime = Fq_div(a, b, T, p);

  u1 = compute_u(gprime, Dxxg, DxJg, DJJg, j, pJ, px, 1, E4, E6, T, p);
  Roots = FqX_roots(FpXY_Fq_evaly(meqn, g, T, p, vJ), T, p);
  btop = avma;
  for (k = lg(Roots)-1; k >= 1; k--, avma = btop)
  {
    GEN jt = gel(Roots, k);
    GEN pxstar = FqX_eval(Dxg, jt, T, p);
    GEN dxstar = Fq_mul(pxstar, g, T, p);
    GEN pJstar = FqX_eval(DJg, jt, T, p);
    GEN dJstar = Fq_mul(Fq_mulu(jt, ell, T, p), pJstar, T, p);
    GEN u = Fq_mul(Fq_mul(dxstar, dJ, T, p), E6, T, p);
    GEN v = Fq_mul(Fq_mul(dJstar, dx, T, p), E4, T, p);
    GEN E4t = Fq_div(Fq_mul(Fq_sqr(u, T, p), jt, T, p), Fq_mul(Fq_sqr(v, T, p), Fq_sub(jt, utoi(1728), T, p), T, p), T, p);
    GEN E6t = Fq_div(Fq_mul(u, E4t, T, p), v, T, p);
    GEN u2 = compute_u(gprime, Dxxg, DxJg, DJJg, jt, pJstar, pxstar, ell, E4t, E6t, T, p);
    GEN pp1 = Fq_mulu(Fq_sub(u1, u2, T, p), 3*ell, T, p);
    GEN a4t = Fq_mul(mulsi(-3, powuu(ell,4)), E4t, T, p);
    GEN a6t = Fq_mul(mulsi(-2, powuu(ell,6)), E6t, T, p);
    GEN h = find_kernel(a4, a6, ell, a4t, a6t, pp1, T, p);
    if (h) return gerepilecopy(ltop, mkvec3(a4t, a6t, h));
  }
  pari_err_BUG("find_isogenous_from_Atkin, kernel not found");
  return NULL;
}

/* Finds E' ell-isogenous to E and the trace term p1 from canonical modular
 *   equation meqn
 * E: elliptic curve, ell: a prime, meqn: canonical modular equation
 * g: root of meqn defining isogenous curve Eb. */
static GEN
find_isogenous_from_canonical(GEN a4, GEN a6, long ell, GEN meqn, GEN g, GEN T, GEN p)
{
  pari_sp ltop = avma;
  long vx = 0, vJ = MAXVARN;
  GEN h;
  GEN E4 = Fq_div(a4, stoi(-3), T, p);
  GEN E6 = Fq_mul(a6, shifti(p, -1), T, p);
  GEN E42 = Fq_sqr(E4, T, p);
  GEN E43 = Fq_mul(E4, E42, T, p);
  GEN E62 = Fq_sqr(E6, T, p);
  GEN delta = Fq_div(Fq_sub(E43, E62, T, p), utoi(1728), T, p);
  GEN j = Fq_div(E43, delta, T, p);
  GEN Dx = deriv(meqn, vx);
  GEN DJ = deriv(meqn, vJ);
  GEN Dxg = FpXY_Fq_evaly(Dx, g, T, p, vJ);
  GEN px  = FqX_eval(Dxg, j, T, p), dx  = Fq_mul(px, g, T, p);
  GEN DJg = FpXY_Fq_evaly(DJ, g, T, p, vJ);
  GEN pJ = FqX_eval(DJg, j, T, p), dJ = Fq_mul(j, pJ, T, p);
  GEN Dxx = deriv(Dx, vx);
  GEN DxJg = FqX_deriv(Dxg, T, p);

  GEN ExJ = FqX_eval(DxJg, j, T, p);
  ulong tis = ugcd(12, ell-1), is = 12 / tis;
  GEN itis = Fq_inv(stoi(-tis), T, p);
  GEN deltal = Fq_div(Fq_mul(delta, Fq_powu(g, tis, T, p), T, p), powuu(ell, 12), T, p);
  GEN E4l, E6l, a4tilde, a6tilde, p_1;
  if (signe(dJ)==0)
  {
    GEN jl;
    if (DEBUGLEVEL) err_printf("Division by zero for prime %Ps\n", T, p);
    E4l = Fq_div(E4, sqru(ell), T, p);
    jl  = Fq_div(Fq_powu(E4l, 3, T, p), deltal, T, p);
    E6l = Fq_sqrt(Fq_mul(Fq_sub(jl, utoi(1728), T, p), deltal, T, p), T, p);
    p_1 = gen_0;
  }
  else
  {
    GEN jl, f, fd, Dgs, Djs, jld;
    GEN E2s = Fq_div(Fq_mul(Fq_neg(Fq_mulu(E6, 12, T, p), T, p), dJ, T, p), Fq_mul(Fq_mulu(E4, is, T, p), dx, T, p), T, p);
    GEN gd = Fq_mul(Fq_mul(E2s, itis, T, p), g, T, p);
    GEN jd = Fq_div(Fq_mul(Fq_neg(E42, T, p), E6, T, p), delta, T, p);
    GEN E0b = Fq_div(E6, Fq_mul(E4, E2s, T, p), T, p);
    GEN Dxxgj = FqXY_eval(Dxx, g, j, T, p);
    GEN Dgd = Fq_add(Fq_mul(gd, px, T, p), Fq_mul(g, Fq_add(Fq_mul(gd, Dxxgj, T, p), Fq_mul(jd, ExJ, T, p), T, p), T, p), T, p);
    GEN DJgJj = FqX_eval(FqX_deriv(DJg, T, p), j, T, p);
    GEN Djd = Fq_add(Fq_mul(jd, pJ, T, p), Fq_mul(j, Fq_add(Fq_mul(jd, DJgJj, T, p), Fq_mul(gd, ExJ, T, p), T, p), T, p), T, p);
    GEN E0bd = Fq_div(Fq_sub(Fq_mul(Dgd, itis, T, p), Fq_mul(E0b, Djd, T, p), T, p), dJ, T, p);
    E4l = Fq_div(Fq_sub(E4, Fq_mul(E2s, Fq_sub(Fq_sub(Fq_add(Fq_div(Fq_mulu(E0bd, 12, T, p), E0b, T, p), Fq_div(Fq_mulu(E42, 6, T, p), E6, T, p), T, p), Fq_div(Fq_mulu(E6, 4, T, p), E4, T, p), T, p), E2s, T, p), T, p), T, p), sqru(ell), T, p);
    jl = Fq_div(Fq_powu(E4l, 3, T, p), deltal, T, p);
    f =  Fq_div(powuu(ell, is), g, T, p);
    fd = Fq_neg(Fq_mul(Fq_mul(E2s, f, T, p), itis, T, p), T, p);
    Dgs = FqXY_eval(Dx, f, jl, T, p);
    Djs = FqXY_eval(DJ, f, jl, T, p);
    jld = Fq_div(Fq_mul(Fq_neg(fd, T, p), Dgs, T, p), Fq_mulu(Djs, ell, T, p), T, p);
    E6l = Fq_div(Fq_mul(Fq_neg(E4l, T, p), jld, T, p), jl, T, p);
    p_1 = Fq_mul(Fq_mulu(E2s, ell, T, p), shifti(p, -1), T, p);
  }
  a4tilde = Fq_mul(Fq_mul(stoi(-3), powuu(ell,4), T, p), E4l, T, p);
  a6tilde = Fq_mul(Fq_mul(stoi(-2), powuu(ell,6), T, p), E6l, T, p);
  h = find_kernel(a4, a6, ell, a4tilde, a6tilde, p_1, T, p);
  return gerepilecopy(ltop, mkvec3(a4tilde, a6tilde, h));
}

static GEN
find_isogenous(GEN a4, GEN a6, long ell, struct meqn *MEQN, GEN g, GEN T, GEN p)
{
  return (MEQN->type == 'C')
    ? find_isogenous_from_canonical(a4, a6, ell, MEQN->eq, g, T, p)
    : find_isogenous_from_Atkin(a4, a6, ell, MEQN->eq, g, T, p);
}

static GEN
find_kernel_power(GEN Eba4, GEN Eba6, GEN Eca4, GEN Eca6, ulong ell, struct meqn *MEQN, GEN kpoly, GEN Ib, GEN T, GEN p)
{
  pari_sp ltop = avma, btop;
  GEN a4t, a6t, gtmp;
  GEN num_iso = find_numerator_isogeny(Eba4, Eba6, Eca4, Eca6, kpoly, T, p, ell+1);
  GEN mpoly = FqXY_evalx(MEQN->eq, Fq_ellj(Eca4, Eca6, T, p), T, p);
  GEN tmp, mroots = FqX_roots(mpoly, T, p);
  long i, vx = 0, l1 = lg(mroots);
  btop = avma;
  for (i = 1; i < l1; i++)
  {
    GEN kpoly2, h;
    tmp = find_isogenous(Eca4, Eca6, ell, MEQN, gel(mroots, i), T, p);
    if (!tmp) { avma = ltop; return NULL; }
    a4t =  gel(tmp, 1);
    a6t =  gel(tmp, 2);
    gtmp = gel(tmp, 3);

    /*check that the kernel kpoly is the good one */
    kpoly2 = FqX_sqr(kpoly, T, p);
    h = liftall_shallow(numer(gsubst(gtmp, vx, gdiv(num_iso, kpoly2))));
    if (signe(Fq_elldivpolmod(Eba4, Eba6, ell, h, T, p)))
    {
      GEN Ic = gdiv(gsubst(num_iso, vx, Ib), gsqr(gsubst(kpoly, vx, Ib)));
      GEN kpoly_new = liftall_shallow(numer(gsubst(gtmp, vx, Ic)));
      return gerepilecopy(ltop, mkvecn(5, a4t, a6t, kpoly_new, gtmp, Ic));
    }
    avma = btop;
  }
  pari_err_BUG("failed to find kernel polynomial");
  return NULL; /*NOT REACHED*/
}

/****************************************************************************/
/*                                  TRACE                                   */
/****************************************************************************/
enum mod_type {MTpathological, MTAtkin, MTElkies, MTone_root, MTroots};

static GEN
Flxq_study_eqn(long ell, GEN mpoly, GEN T, ulong p, long *pt_dG, long *pt_r)
{
  GEN Xq = FlxqX_Frobenius(mpoly, T, p);
  GEN G  = FlxqX_gcd(FlxX_sub(Xq, pol_x(0), p), mpoly, T, p);
  *pt_dG = degpol(G);
  if (!*pt_dG)
  {
    GEN L = FlxqXQ_matrix_pow(Xq, ell+1, ell+1, mpoly, T, p);
    long vT = get_Flx_var(T);
    long s = ell + 1 - FlxqM_rank(FlxM_Flx_add_shallow(L, Fl_to_Flx(p-1, vT), p), T, p);
    *pt_r = (ell + 1)/s;
    return NULL;
  }
  return G;
}

static GEN
Fp_study_eqn(long ell, GEN mpoly, GEN p, long *pt_dG, long *pt_r)
{
  GEN XP = FpXQ_pow(pol_x(0), p, mpoly, p);
  GEN G  = FpX_gcd(FpX_sub(XP, pol_x(0), p), mpoly, p);
  *pt_dG = degpol(G);
  if (!*pt_dG)
  {
    GEN L = FpXQ_matrix_pow(XP, ell+1, ell+1, mpoly, p);
    long s = ell + 1 - FpM_rank(RgM_Rg_add_shallow(L, gen_m1), p);
    *pt_r = (ell + 1)/s;
    return NULL;
  }
  return FpX_oneroot(G, p);
}

static GEN
FpXQ_study_eqn(long ell, GEN mpoly, GEN T, GEN p, long *pt_dG, long *pt_r)
{
  GEN G;
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    GEN Tp = ZXT_to_FlxT(T,pp);
    GEN mpolyp = ZXX_to_FlxX(mpoly,pp,get_FpX_var(T));
    G = Flxq_study_eqn(ell, mpolyp, Tp, pp, pt_dG, pt_r);
    if (!G) return NULL;
    G = FlxX_to_ZXX(G);
  }
  else
  {
    GEN Xq = FpXQX_Frobenius(mpoly, T, p);
    G  = FpXQX_gcd(FpXX_sub(Xq, pol_x(0), p), mpoly, T, p);
    *pt_dG = degpol(G);
    if (!*pt_dG)
    {
      GEN L = FpXQXQ_matrix_pow(Xq, ell+1, ell+1, mpoly, T, p);
      long s = ell + 1 - FqM_rank(RgM_Rg_add(L, gen_m1), T, p);
      *pt_r = (ell + 1)/s;
      return NULL;
    }
  }
  return gel(FqX_roots(G, T, p), 1);
}

/* Berlekamp variant */
static GEN
study_modular_eqn(long ell, GEN mpoly, GEN T, GEN p, enum mod_type *mt, long *ptr_r)
{
  pari_sp ltop = avma;
  GEN g = gen_0;
  *ptr_r = 0; /*gcc -Wall*/
  if (degpol(FqX_gcd(mpoly, FqX_deriv(mpoly, T, p), T, p)) > 0)
    *mt = MTpathological;
  else
  {
    long dG;
    g = T ? FpXQ_study_eqn(ell, mpoly, T, p, &dG, ptr_r)
            : Fp_study_eqn(ell, mpoly, p, &dG, ptr_r);
    switch(dG)
    {
      case 0:  *mt = MTAtkin; break;
      case 1:  *mt = MTone_root; break;
      case 2:  *mt = MTElkies;   break;
      default: *mt = (dG == ell + 1)? MTroots: MTpathological;
    }
  }
  if (DEBUGLEVEL) switch(*mt)
  {
    case MTone_root: err_printf("One root\t"); break;
    case MTElkies: err_printf("Elkies\t"); break;
    case MTroots: err_printf("l+1 roots\t"); break;
    case MTAtkin: err_printf("Atkin\t"); break;
    case MTpathological: err_printf("Pathological\n"); break;
  }
  return g ? gerepilecopy(ltop, g): NULL;
}

/*Returns the trace modulo ell^k when ell is an Elkies prime */
static GEN
find_trace_Elkies_power(GEN a4, GEN a6, ulong ell, long k, struct meqn *MEQN, GEN g, GEN tr, GEN q, GEN T, GEN p, ulong smallfact, pari_timer *ti)
{
  pari_sp ltop = avma, btop, st_lim;
  GEN tmp, Eba4, Eba6, Eca4, Eca6, Ib, kpoly;
  ulong lambda, ellk = upowuu(ell, k), pellk = umodiu(q, ellk);
  long cnt;

  if (DEBUGLEVEL) { err_printf("Trace mod %ld", ell); }
  Eba4 = a4;
  Eba6 = a6;
  tmp = find_isogenous(a4,a6, ell, MEQN, g, T, p);
  if (!tmp) { avma = ltop; return NULL; }
  Eca4 =  gel(tmp, 1);
  Eca6 =  gel(tmp, 2);
  kpoly = gel(tmp, 3);
  Ib = pol_x(0);
  lambda = find_eigen_value(a4, a6, ell, kpoly, T, p, tr);
  if (DEBUGLEVEL>1) err_printf(" [%ld ms]", timer_delay(ti));
  if (smallfact && ell>smallfact)
  {
    ulong pell = pellk%ell;
    ulong ap = Fl_add(lambda, Fl_div(pell, lambda, ell), ell);
    if (Fl_sub(pell, ap, ell)==ell-1) { avma = ltop; return mkvecsmall(ap); }
  }
  btop = avma; st_lim = stack_lim(btop, 1);
  for (cnt = 2; cnt <= k; cnt++)
  {
    GEN tmp;
    if (DEBUGLEVEL) err_printf(", %Ps", powuu(ell, cnt));
    tmp = find_kernel_power(Eba4, Eba6, Eca4, Eca6, ell, MEQN, kpoly, Ib, T, p);
    if (!tmp) { avma = ltop; return NULL; }
    lambda = find_eigen_value_power(a4, a6, ell, cnt, gel(tmp,3), lambda, T, p);
    Eba4 = Eca4;
    Eba6 = Eca6;
    Eca4 = gel(tmp,1);
    Eca6 = gel(tmp,2);
    kpoly = gel(tmp,4);
    Ib = gel(tmp, 5);
    if (low_stack(st_lim, stack_lim(btop, 1)))
      gerepileall(btop, 6, &Eba4, &Eba6, &Eca4, &Eca6, &kpoly, &Ib);
    if (DEBUGLEVEL>1) err_printf(" [%ld ms]", timer_delay(ti));
  }
  avma = ltop;
  return mkvecsmall(Fl_add(lambda, Fl_div(pellk, lambda, ellk), ellk));
}

/*Returns the possible values of the trace when ell is an Atkin prime, */
/*given r the splitting degree of the modular equation at J = E.j */
static GEN
find_trace_Atkin(ulong ell, long r, GEN q)
{
  pari_sp ltop = avma;
  long nval = 0;
  ulong teta, pell = umodiu(q, ell), invp = Fl_inv(pell, ell);
  GEN val_pos = cgetg(1+ell, t_VECSMALL), P = gel(factoru(r), 1);
  GEN S = mkvecsmall4(0, pell, 0, 1);
  GEN U = mkvecsmall3(0, ell-1, 0);
  pari_sp btop = avma;
  if (r==2 && krouu(ell-pell, ell) < 0)
    val_pos[++nval] = 0;
  for (teta = 1; teta < ell; teta++, avma = btop)
  {
    ulong disc = Fl_sub(Fl_sqr(teta,ell), Fl_mul(4UL,pell,ell), ell);
    GEN a;
    if (krouu(disc, ell) >= 0) continue;
    S[3] = Fl_neg(teta, ell);
    U[3] = Fl_mul(invp, teta, ell);
    a = Flxq_powu(U, r/P[1], S, ell);
    if (!Flx_equal1(a) && Flx_equal1(Flxq_powu(a, P[1], S, ell)))
    {
      pari_sp av = avma;
      long i, l=lg(P);
      for (i = 2; i < l; i++, avma = av)
        if (Flx_equal1(Flxq_powu(U, r/P[i], S, ell))) break;
      if (i==l) val_pos[++nval] = teta;
    }
  }
  return gerepileupto(ltop, vecsmall_shorten(val_pos, nval));
}

/*Returns the possible traces when there is only one root */
static GEN
find_trace_one_root(ulong ell, GEN q)
{
  ulong a = Fl_double(Fl_sqrt(umodiu(q,ell), ell), ell);
  return mkvecsmall2(a, ell - a);
}

static GEN
find_trace_lp1_roots(long ell, GEN q)
{
  ulong ell2 = ell * ell, pell = umodiu(q, ell2);
  ulong a  = Fl_sqrt(pell%ell, ell);
  ulong pa = Fl_add(Fl_div(pell, a, ell2), a, ell2);
  return mkvecsmall2(pa, ell2 - pa);
}

/*trace modulo ell^k: [], [t] or [t1,...,td] */
static GEN
find_trace(GEN a4, GEN a6, ulong ell, GEN q, GEN T, GEN p, long *ptr_kt, ulong smallfact)
{
  pari_sp ltop = avma;
  GEN g, meqnj, tr, tr2;
  long k = 1, kt, r;
  enum mod_type mt;
  struct meqn MEQN;
  pari_timer ti;

  if (ell <= 13)
  {
    long lp = expi(q);
    switch(ell)
    {
      case 3: k = 3 + (lp > 160) + (lp > 350); break;
      case 5: k = 2 + (lp > 260); break;
      case 7: k = 2 + (lp > 390); break;
      default:k = 1 + (lp > 260);
    }
  }
  kt = k;
  if (!get_modular_eqn(&MEQN, ell, 0, MAXVARN)) err_modular_eqn(ell);
  if (DEBUGLEVEL)
  { err_printf("Process prime %5ld. ", ell); timer_start(&ti); }
  meqnj = FqXY_evalx(MEQN.eq, Fq_ellj(a4, a6, T, p), T, p);
  g = study_modular_eqn(ell, meqnj, T, p, &mt, &r);
  /* If l is an Elkies prime, search for a factor of the l-division polynomial.
  * Then deduce the trace by looking for eigenvalues of the Frobenius by
  * computing modulo this factor */
  switch (mt)
  {
  case MTone_root:
    tr2 = find_trace_one_root(ell, q);
    kt = k = 1;
    /* Must take k = 1 because we can't apply Hensel: no guarantee that a
     * root mod ell^2 exists */
    tr = find_trace_Elkies_power(a4,a6,ell, k, &MEQN, g, tr2, q, T, p, smallfact, &ti);
    if (!tr) tr = tr2;
    break;
  case MTElkies:
    /* Contrary to MTone_root, may look mod higher powers of ell */
    tr = find_trace_Elkies_power(a4,a6,ell, k, &MEQN, g, NULL, q, T, p, smallfact, &ti);
    if (!tr) { avma = ltop; return NULL; }
    break;
  case MTroots:
    tr = find_trace_lp1_roots(ell, q);
    kt = 2;
    break;
  case MTAtkin:
    tr = find_trace_Atkin(ell, r, q);
    if (lg(tr)==1) pari_err_PRIME("ellsea",p);
    kt = 1;
    break;
  default: /* case MTpathological: */
    avma = ltop; return NULL;
  }
  if (DEBUGLEVEL) {
    long n = lg(tr)-1;
    if (n > 1 || mt == MTAtkin)
    {
      err_printf("%3ld trace(s)",n);
      if (DEBUGLEVEL>1) err_printf(" [%ld ms]", timer_delay(&ti));
    }
    err_printf("\n");
  }
  *ptr_kt = kt;
  return gerepileupto(ltop, tr);
}

/* A partition of compile_atkin in baby and giant is represented as the binary
   developpement of an integer; if the i-th bit is 1, the i-th prime in
   compile-atkin is a baby. The optimum is obtained when the ratio between
   the number of possibilities for traces modulo giants (p_g) and babies (p_b)
   is near 3/4. */
static long
separation(GEN cnt)
{
  pari_sp btop, st_lim;
  long k = lg(cnt)-1, l = (1L<<k)-1, best_i, i, j;
  GEN best_r, P, P3, r;

  P = gen_1;
  for (j = 1; j <= k; ++j) P = mulis(P, cnt[j]);
  /* p_b * p_g = P is constant */
  P3 = mulsi(3, P);
  btop = avma; st_lim = stack_lim(btop, 1);
  best_i = 0;
  best_r = P3;
  for (i = 1; i < l; i++)
  {
    /* scan all possibilities */
    GEN p_b = gen_1;
    for (j = 0; j < k; j++)
      if (i & (1L<<j)) p_b = mulis(p_b, cnt[1+j]);
    r = subii(shifti(sqri(p_b), 2), P3); /* (p_b/p_g - 3/4)*4*P */
    if (!signe(r)) { best_i = i; break; }
    if (absi_cmp(r, best_r) < 0) { best_i = i; best_r = r; }
    if (low_stack(st_lim, stack_lim(btop, 1)))
      best_r = gerepileuptoint(btop, best_r);
  }
  return best_i;
}

/* x VEC defined modulo P (= *P), y VECSMALL modulo q, (q,P) = 1. */
/* Update in place:
 *   x to vector mod q P congruent to x mod P (resp. y mod q). */
/*   P ( <-- qP ) */
static void
multiple_crt(GEN x, GEN y, GEN q, GEN P)
{
  pari_sp ltop = avma, av;
  long i, j, k, lx = lg(x)-1, ly = lg(y)-1;
  GEN  a1, a2, u, v, A2X;
  (void)bezout(P,q,&u,&v);
  a1 = mulii(P,u);
  a2 = mulii(q,v); A2X = ZC_Z_mul(x, a2);
  av = avma; affii(mulii(P,q), P);
  for (i = 1, k = 1; i <= lx; i++, avma = av)
  {
    GEN a2x = gel(A2X,i);
    for (j = 1; j <= ly; ++j)
    {
      GEN t = Fp_add(Fp_mulu(a1, y[j], P), a2x, P);
      affii(t, gel(x, k++));
    }
  }
  setlg(x, k); avma = ltop;
}

/****************************************************************************/
/*                              MATCH AND SORT                              */
/****************************************************************************/

static GEN
possible_traces(GEN compile, GEN mask, GEN *P, int larger)
{
  GEN V, Pfinal = gen_1, C = shallowextract(compile, mask);
  long i, lfinal = 1, lC = lg(C), lP;
  pari_sp av = avma;

  for (i = 1; i < lC; i++)
  {
    GEN c = gel(C,i), t;
    Pfinal = mulii(Pfinal, gel(c,1));
    t = muluu(lfinal, lg(gel(c,2))-1);
    lfinal = itou(t);
  }
  Pfinal = gerepileuptoint(av, Pfinal);
  if (larger)
    lP = lgefint(shifti(Pfinal,1));
  else
    lP = lgefint(Pfinal);
  lfinal++;
  /* allocate room for final result */
  V = cgetg(lfinal, t_VEC);
  for (i = 1; i < lfinal; i++) gel(V,i) = cgeti(lP);

  {
    GEN c = gel(C,1), v = gel(c,2);
    long l = lg(v);
    for (i = 1; i < l; i++) affsi(v[i], gel(V,i));
    setlg(V, l); affii(gel(c,1), Pfinal); /* reset Pfinal */
  }
  for (i = 2; i < lC; i++)
  {
    GEN c = gel(C,i);
    multiple_crt(V, gel(c,2), gel(c,1), Pfinal); /* Pfinal updated! */
  }
  *P = Pfinal; return V;
}

static GEN
cost(long mask, GEN cost_vec)
{
  pari_sp ltop = avma;
  long i;
  GEN c = gen_1;
  for (i = 1; i < lg(cost_vec); i++)
    if (mask&(1L<<(i-1)))
      c = mulis(c, cost_vec[i]);
  return gerepileuptoint(ltop, c);
}

static GEN
value(long mask, GEN atkin, long k)
{
  pari_sp ltop = avma;
  long i;
  GEN c = gen_1;
  for (i = 1; i <= k; i++)
    if (mask&(1L<<(i-1)))
      c = mulii(c, gmael(atkin, i, 1));
  return gerepileuptoint(ltop, c);
}

static void
set_cost(GEN B, long b, GEN cost_vec, long *pi)
{
  pari_sp av = avma;
  GEN costb = cost(b, cost_vec);
  long i = *pi;
  while (cmpii(costb, cost(B[i], cost_vec)) < 0) --i;
  B[++i] = b;
  *pi = i; avma = av;
}

static GEN
get_lgatkin(GEN compile_atkin, long k)
{
  GEN v = cgetg(k+1, t_VECSMALL);
  long j;
  for (j = 1; j <= k; ++j) v[j] = lg(gmael(compile_atkin, j, 2))-1;
  return v;
}

static GEN
champion(GEN atkin, long k, GEN bound_champ)
{
  const long two_k = 1L<<k;
  pari_sp ltop = avma;
  long i, j, n, i1, i2;
  GEN B, Bp, cost_vec, res = NULL;

  cost_vec = get_lgatkin(atkin, k);
  if (k == 1) return mkvec2(gen_1, utoipos(cost_vec[1]));

  B  = zero_zv(two_k);
  Bp = zero_zv(two_k);
  Bp[2] = 1;
  for (n = 2, j = 2; j <= k; j++)
  {
    long b;
    i = 1;
    for (i1 = 2, i2 = 1; i1 <= n; )
    {
      pari_sp av = avma;
      long b1 = Bp[i1], b2 = Bp[i2]|(1L<<(j-1));
      if (cmpii(value(b1, atkin, k), value(b2, atkin, k)) < 0)
        { b = b1; i1++; } else { b = b2; i2++; }
      avma = av;
      set_cost(B, b, cost_vec, &i);
    }
    for ( ; i2 <= n; i2++)
    {
      b = Bp[i2]|(1L<<(j-1));
      set_cost(B, b, cost_vec, &i);
    }
    n = i;
    for (i = 1; i <= n; i++)
      Bp[i] = B[i];
  }
  for (i = 1; i <= two_k; i++)
    if (B[i])
    {
      GEN b = cost (B[i], cost_vec);
      GEN v = value(B[i], atkin, k);
      if (cmpii(v, bound_champ) <=0) continue;
      if (res && gcmp(b, gel(res, 2)) >=0) continue;
      res = mkvec2(utoi(B[i]), b);
    }
  return gerepilecopy(ltop, res);
}

static GEN
compute_diff(GEN v)
{
  pari_sp av = avma;
  long i, l = lg(v) - 1;
  GEN diff = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) gel(diff, i) = subii(gel(v, i+1), gel(v, i));
  return gerepileupto(av, ZV_sort_uniq(diff));
}

static int
cmp_atkin(void*E, GEN a, GEN b)
{
  long ta=typ(a)==t_INT, tb=typ(b)==t_INT, c;
  (void) E;
  if (ta || tb) return ta-tb;
  c = lg(gel(a,2)) - lg(gel(b,2));
  if (c) return c;
  return cmpii(gel(b,1), gel(a,1));
}

static void
add_atkin(GEN atkin, GEN trace, long *nb)
{
  long l = lg(atkin)-1;
  long i, k = gen_search(atkin, trace, 1, NULL, cmp_atkin);
  if (k==0 || k > l) return;
  for (i = l; i > k; i--)
    gel(atkin,i) = gel(atkin,i-1);
  if (typ(gel(atkin,l))==t_INT) (*nb)++;
  gel(atkin,k) = trace;
}

/* V = baby / giant, P = Pb / Pg */
static GEN
BSGS_pre(GEN *pdiff, GEN V, GEN P, void *E, const struct bb_group *grp)
{
  GEN diff = compute_diff(V);
  GEN pre = cgetg(lg(diff), t_VEC);
  long i, l = lg(diff);
  gel(pre, 1) = grp->pow(E, P, gel(diff, 1));
  /* what we'd _really_ want here is a hashtable diff[i] -> pre[i]  */
  for (i = 2; i < l; i++)
  {
    pari_sp av = avma;
    GEN d = subii(gel(diff, i), gel(diff, i-1));
    GEN Q = grp->mul(E, gel(pre, i-1), grp->pow(E, P, d));
    gel(pre, i) = gerepilecopy(av, Q);
  }
  *pdiff = diff; return pre;
}

/* u = trace_elkies, Mu = prod_elkies. Let caller collect garbage */
/* Match & sort: variant from Lercier's thesis, section 11.2.3 */
/* baby/giant/table updated in place: this routines uses
 *   size(baby)+size(giant)+size(table)+size(table_ind) + O(log p)
 * bits of stack */
static GEN
match_and_sort(GEN compile_atkin, GEN Mu, GEN u, GEN q, void *E, const struct bb_group *grp)
{
  pari_sp av1, av2, lim;
  GEN baby, giant, SgMb, Mb, Mg, den, Sg, dec_inf, div, pp1 = addis(q,1);
  GEN P, Pb, Pg, point, diff, pre, table, table_ind;
  long best_i, i, lbaby, lgiant, k = lg(compile_atkin)-1;
  pari_timer ti;

  if (k == 1)
  { /*only one Atkin prime, check the cardinality with random points */
    GEN r = gel(compile_atkin, 1), r1 = gel(r,1), r2 = gel(r,2);
    long l = lg(r2);
    GEN card = cgetg(l, t_VEC), Cs2, C, U;
    Z_chinese_pre(Mu, r1, &C,&U, NULL);
    Cs2 = shifti(C, -1);
    for (i = 1; i < l; i++)
    {
      GEN t = Z_chinese_post(u, stoi(r2[i]), C, U, NULL);
      gel(card, i) = subii(pp1, Fp_center(t, C, Cs2));
    }
    return gen_select_order(card, E, grp);
  }
  if (DEBUGLEVEL>=2) timer_start(&ti);
  av1 = avma;
  best_i = separation( get_lgatkin(compile_atkin, k) );
  avma = av1;

  baby  = possible_traces(compile_atkin, stoi(best_i), &Mb, 1);
  giant = possible_traces(compile_atkin, subis(int2n(k), best_i+1), &Mg, 0);
  lbaby = lg(baby);
  lgiant = lg(giant);
  den = Fp_inv(Fp_mul(Mu, Mb, Mg), Mg);
  av2 = avma;
  for (i = 1; i < lgiant; i++, avma = av2)
    affii(Fp_mul(gel(giant,i), den, Mg), gel(giant,i));
  gen_sort_inplace(giant, (void*)&cmpii, &cmp_nodata, NULL);
  Sg = Fp_mul(negi(u), den, Mg);
  den = Fp_inv(Fp_mul(Mu, Mg, Mb), Mb);
  dec_inf = divii(mulii(Mb,addii(Mg,shifti(Sg,1))), shifti(Mg,1));
  togglesign(dec_inf); /* now, dec_inf = ceil(- (Mb/2 + Sg Mb/Mg) ) */
  div = mulii(truedivii(dec_inf, Mb), Mb);
  av2 = avma;
  for (i = 1; i < lbaby; i++, avma = av2)
  {
    GEN b = addii(Fp_mul(Fp_sub(gel(baby,i), u, Mb), den, Mb), div);
    if (cmpii(b, dec_inf) < 0) b = addii(b, Mb);
    affii(b, gel(baby,i));
  }
  gen_sort_inplace(baby, (void*)&cmpii, &cmp_nodata, NULL);

  SgMb = mulii(Sg, Mb);
  P = grp->rand(E);
  point = grp->pow(E,P, Mu);
  Pb = grp->pow(E,point, Mg);
  Pg = grp->pow(E,point, Mb);
  /* Precomputation for babies */
  pre = BSGS_pre(&diff, baby, Pb, E, grp);

  /*Now we compute the table of babies, this table contains only the */
  /*lifted x-coordinate of the points in order to use less memory */
  table = cgetg(lbaby, t_VECSMALL);
  av1 = avma; lim = stack_lim(av1,3);
  /* (p+1 - u - Mu*Mb*Sg) P - (baby[1]) Pb */
  point = grp->pow(E,P, subii(subii(pp1, u), mulii(Mu, addii(SgMb, mulii(Mg, gel(baby,1))))));
  table[1] = grp->hash(gel(point,1));
  for (i = 2; i < lbaby; i++)
  {
    GEN d = subii(gel(baby, i), gel(baby, i-1));
    point =  grp->mul(E, point, grp->pow(E, gel(pre, ZV_search(diff, d)), gen_m1));
    table[i] = grp->hash(gel(point,1));
    if (low_stack(lim, stack_lim(av1,3)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"match_and_sort, baby = %ld", i);
      point = gerepileupto(av1, point);
    }
  }
  avma = av1;
  /* Precomputations for giants */
  pre = BSGS_pre(&diff, giant, Pg, E, grp);

  /* Look for a collision among the x-coordinates */
  table_ind = vecsmall_indexsort(table);
  table = perm_mul(table,table_ind);

  av1 = avma; lim = stack_lim(av1,3);
  point = grp->pow(E, Pg, gel(giant, 1));
  for (i = 1; ; i++)
  {
    GEN d;
    long h = grp->hash(gel(point, 1));
    long s = zv_search(table, h);
    if (s) {
      while (table[s] == h && s) s--;
      for (s++; s < lbaby && table[s] == h; s++)
      {
        GEN B = gel(baby,table_ind[s]), G = gel(giant,i);
        GEN GMb = mulii(G, Mb), BMg = mulii(B, Mg);
        GEN Be = subii(subii(pp1, u), mulii(Mu, addii(SgMb, BMg)));
        GEN Bp = grp->pow(E,P, Be);
        /* p+1 - u - Mu (Sg Mb + GIANT Mb + BABY Mg) */
        if (gequal(gel(Bp,1),gel(point,1)))
        {
          GEN card = subii(Be, mulii(Mu, GMb));
          card = mkvec2(card, addii(card, mulii(mulsi(2,Mu), GMb)));
          if (DEBUGLEVEL>=2) timer_printf(&ti,"match_and_sort");
          return gen_select_order(card, E, grp);
        }
      }
    }
    if (i==lgiant-1) break;
    d = subii(gel(giant, i+1), gel(giant, i));
    point = grp->mul(E,point, gel(pre, ZV_search(diff, d)));
    if (low_stack(lim, stack_lim(av1,3)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"match_and_sort, giant = %ld", i);
      point = gerepileupto(av1, point);
    }
  }
  /* no match ? */
  pari_err_BUG("match_and_sort");
  return NULL; /* not reached */
}

static GEN
get_bound_bsgs(long lp)
{
  GEN B;
  if (lp <= 160)
    B = divru(powru(dbltor(1.048), lp), 9);
  else if (lp <= 192)
    B = divrr(powru(dbltor(1.052), lp), dbltor(16.65));
  else
    B = mulrr(powru(dbltor(1.035), minss(lp,307)), dbltor(1.35));
  return mulru(B, 1000000);
}

/*FIXME: the name of the function does not quite match what it does*/
static const struct bb_group *
get_FqE_group(void ** pt_E, GEN a4, GEN a6, GEN T, GEN p)
{
  if (!T) return get_FpE_group(pt_E,a4,a6,p);
  else if (lgefint(p)==3)
  {
    ulong pp=(ulong) p[2];
    return get_FlxqE_group(pt_E, ZX_to_Flx(a4,pp),ZX_to_Flx(a6,pp),ZXT_to_FlxT(T,pp),pp);
  }
  return get_FpXQE_group(pt_E,a4,a6,T,p);
}

/* E is an elliptic curve defined over Z or over Fp in ellinit format, defined
 * by the equation E: y^2 + a1*x*y + a2*y = x^3 + a2*x^2 + a4*x + a6
 * p is a prime number
 * set smallfact to stop whenever a small factor > smallfact of the order is
 * detected. Useful when searching for a good curve for cryptographic
 * applications */
GEN
Fq_ellcard_SEA(GEN a4, GEN a6, GEN q, GEN T, GEN p, long smallfact)
{
  const long MAX_ATKIN = 21;
  pari_sp ltop = avma, btop, st_lim;
  long ell, i, nb_atkin;
  GEN TR, TR_mod, compile_atkin, bound, bound_bsgs, champ;
  GEN prod_atkin = gen_1, max_traces = gen_0;
  double bound_gr = 1.;
  const double growth_factor = 1.26;
  forprime_t TT;
  void *E;

  if (!modular_eqn && !get_seadata(0)) return NULL;
  if (T && get_FpX_var(T)==0) /* 0 is used by the modular polynomial */
  {
    if (typ(T)==t_POL) { T  = shallowcopy(T); setvarn(T,1); }
    else T = gsubst(T,0,pol_x(1));
    a4 = shallowcopy(a4); setvarn(a4,1);
    a6 = shallowcopy(a6); setvarn(a6,1);
  }
  /*First compute the trace modulo 2 */
  switch(FqX_nbroots(mkpoln(4, gen_1, gen_0, a4, a6), T, p))
  {
  case 3: /* bonus time: 4 | #E(Fq) = q+1 - t */
    i = mod4(q)+1; if (i > 2) i -= 4;
    TR_mod = utoipos(4);
    TR = stoi(i); break;
  case 1:
    TR_mod = gen_2;
    TR = gen_0; break;
  default : /* 0 */
    TR_mod = gen_2;
    TR = gen_1; break;
  }
  if (smallfact == 1 && !mpodd(TR))
  {
    if (DEBUGLEVEL) err_printf("Aborting: #E(Fq) divisible by 2\n");
    avma = ltop; return gen_0;
  }

  /* compile_atkin is a vector containing informations about Atkin primes,
   * informations about Elkies primes lie in Mod(TR, TR_mod). */
  u_forprime_init(&TT, 3, 1000); /* way beyond what seadata provides */
  bound = sqrti(shifti(q, 4));
  bound_bsgs = get_bound_bsgs(expi(q));
  compile_atkin = zerovec(MAX_ATKIN); nb_atkin = 0;
  btop = avma; st_lim = stack_lim(btop, 1);
  while ( (ell = u_forprime_next(&TT)) )
  {
    long ellkt, kt = 1, nbtrace;
    GEN trace_mod;
    trace_mod = find_trace(a4, a6, ell, q, T, p, &kt, smallfact);
    if (!trace_mod) continue;

    nbtrace = lg(trace_mod) - 1;
    ellkt = (long)upowuu(ell, kt);
    if (nbtrace == 1)
    {
      long t_mod_ellkt = trace_mod[1];
      if (smallfact && ell > smallfact)
      { /* does ell divide q + 1 - t ? */
        long card_mod_ell = (umodiu(q,ell) + 1 - t_mod_ellkt) % ell ;
        if (!card_mod_ell)
        {
          if (DEBUGLEVEL)
            err_printf("\nAborting: #E(Fq) divisible by %ld\n",ell);
          avma = ltop; return gen_0;
        }
      }
      (void)Z_incremental_CRT(&TR, t_mod_ellkt, &TR_mod, ellkt);
    }
    else
    {
      add_atkin(compile_atkin, mkvec2(utoipos(ellkt), trace_mod), &nb_atkin);
      prod_atkin = value(-1, compile_atkin, nb_atkin);
    }
    if (cmpii(mulii(TR_mod, prod_atkin), bound) > 0)
    {
      GEN bound_tr;
      if (!nb_atkin) return gerepileuptoint(ltop, subii(addis(p,1),TR));
      bound_tr = mulrr(bound_bsgs, dbltor(bound_gr));
      bound_gr *= growth_factor;
      if (signe(max_traces))
      {
        max_traces = divis(muliu(max_traces,nbtrace), ellkt);
        if (DEBUGLEVEL>=3)
          err_printf("At least %Ps remaining possibilities.\n",max_traces);
      }
      if (cmpir(max_traces, bound_tr) < 0)
      {
        GEN bound_atkin = truedivii(bound, TR_mod);
        champ = champion(compile_atkin, nb_atkin, bound_atkin);
        max_traces = gel(champ,2);
        if (DEBUGLEVEL>=2)
          err_printf("%Ps remaining possibilities.\n", max_traces);
        if (cmpir(max_traces, bound_tr) < 0)
        {
          GEN res, cat = shallowextract(compile_atkin, gel(champ,1));
          const struct bb_group *grp;
          if (DEBUGLEVEL)
            err_printf("Match and sort for %Ps possibilities.\n", max_traces);
          grp = get_FqE_group(&E,a4,a6,T,p);
          res = match_and_sort(cat, TR_mod, TR, q, E, grp);
          return gerepileuptoint(ltop, res);
        }
      }
    }
    if (low_stack(st_lim, stack_lim(btop, 1)))
      gerepileall(btop,5, &TR,&TR_mod, &compile_atkin, &max_traces, &prod_atkin);
  }
  return NULL;/*not reached*/
}

GEN
Fp_ellcard_SEA(GEN a4, GEN a6, GEN p, long smallfact)
{
  return Fq_ellcard_SEA(a4, a6, p, NULL, p, smallfact);
}

GEN
ellsea(GEN E, GEN p, long smallfact)
{
  pari_sp av = avma;
  GEN a4 = modii(mulis(Rg_to_Fp(gel(E,10), p), -27), p);
  GEN a6 = modii(mulis(Rg_to_Fp(gel(E,11), p), -54), p);
  GEN card = Fp_ellcard_SEA(a4, a6, p, smallfact);
  if (!card) pari_err_PACKAGE("seadata");
  return gerepileuptoint(av, subii(addis(p,1),card));
}
