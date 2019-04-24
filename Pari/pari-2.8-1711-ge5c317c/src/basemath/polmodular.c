/* Copyright (C) 2014  The PARI group.

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

#define dbg_printf(lvl) if (DEBUGLEVEL >= (lvl)) err_printf

/**
 * START Code from AVSs "class_inv.h"
 */

/* actually just returns the square-free part of the level, which is all we care about */
long
inv_level(long inv)
{
  switch (inv) {
  case INV_J:
    return 1;
  case INV_G2:
    return 3;
  case INV_F:
    return 6;
  default:
    pari_err_BUG("inv_level");
  }
  return 0;
}

/* Where applicable, returns N=p1*p2 (possibly p2=1) s.t. two j's
 * related to the same f are N-isogenous, and 0 otherwise.  This is
 * often (but not necessarily) equal to the level. */
long
inv_degree(long *p1, long *p2, long inv)
{
  *p1 = 1;
  *p2 = 1;
  switch (inv) {
  case INV_J:
  case INV_G2:
  case INV_F:
    break;
  default:
    pari_err_BUG("inv_degree");
  }
  return 0;
}


double
inv_height_factor(long inv)
{
  switch (inv) {
  case INV_J:
    return 1.0;
  case INV_G2:
    return 3.0;
  case INV_F:
    return 72.0;
  default:
    pari_err_BUG("inv_height_factor");
  }
  return 0.0;
}


INLINE long
inv_sparse_factor(long inv)
{
  switch (inv) {
  case INV_J:
    return 1;
  case INV_G2:
    return 3;
  case INV_F:
    return 24;
  default:
    pari_err_BUG("inv_sparse_factor");
  }
  return 0;
}

#define IQ_FILTER_1MOD3 1
#define IQ_FILTER_2MOD3 2
#define IQ_FILTER_1MOD4 4
#define IQ_FILTER_3MOD4 8

INLINE long
inv_pfilter(long inv)
{
  switch (inv) {
  case INV_J:
    return 0;
  case INV_G2:
    return IQ_FILTER_1MOD3; /* ensure unique cube roots */
  case INV_F:
    /* also ensure at most two 4th/8th roots */
    return IQ_FILTER_1MOD3 | IQ_FILTER_1MOD4;
  default:
    pari_err_BUG("inv_pfilter");
  }
  return -1;
}

int
inv_good_discriminant(long D, long inv)
{
  switch (inv) {
  case INV_J:
    return 1;
  case INV_G2:
    return !!(D % 3);
  case INV_F:
    return (D % 3) && ((-D & 7) == 7);
  default:
    pari_err_BUG("inv_good_discriminant");
  }
  return 0;
}

/* Certain invariants require that D not have 2 in it's conductor, but
 * this doesn't apply to every invariant with even level so we handle
 * it separately */
INLINE int
inv_odd_conductor(long inv)
{
  switch (inv) {
  case INV_F:
    return 1;
  }
  return 0;
}

int
inv_good_prime(long p, long inv)
{
  switch (inv) {
  case INV_J:
    return 1;
  case INV_G2:
    return (p % 3) == 2;
  case INV_F:
    if ((p % 3) == 2)
      return (p & 3) != 1;
    return 0;
  default:
    pari_err_BUG("inv_good_prime");
  }
  return 0;
}
/* END Code from "class_inv.h" */


/**
 * SECTION: class group bb_group.
 */

INLINE GEN
mkqfis(long a, long b, long c)
{
  retmkqfi(stoi(a), stoi(b), stoi(c));
}

/**
 * SECTION: Fixed-length dot-product-like functions on Fl's with
 * precomputed inverse.
 */

/* Computes x0y1 + y0x1 (mod p); assumes p < 2^63. */
INLINE ulong
Fl_addmul2(
  ulong x0, ulong x1, ulong y0, ulong y1,
  ulong p, ulong pi)
{
  return Fl_addmulmul_pre(x0,y1,y0,x1,p,pi);
}


/* Computes x0y2 + x1y1 + x2y0 (mod p); assumes p < 2^62. */
INLINE ulong
Fl_addmul3(
  ulong x0, ulong x1, ulong x2, ulong y0, ulong y1, ulong y2,
  ulong p, ulong pi)
{
  ulong l0, l1, h0, h1;
  LOCAL_OVERFLOW;
  LOCAL_HIREMAINDER;
  l0 = mulll(x0, y2); h0 = hiremainder;
  l1 = mulll(x1, y1); h1 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  l0 = mulll(x2, y0); h0 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  return remll_pre(h1, l1, p, pi);
}


/* Computes x0y3 + x1y2 + x2y1 + x3y0 (mod p); assumes p < 2^62. */
INLINE ulong
Fl_addmul4(
  ulong x0, ulong x1, ulong x2, ulong x3,
  ulong y0, ulong y1, ulong y2, ulong y3,
  ulong p, ulong pi)
{
  ulong l0, l1, h0, h1;
  LOCAL_OVERFLOW;
  LOCAL_HIREMAINDER;
  l0 = mulll(x0, y3); h0 = hiremainder;
  l1 = mulll(x1, y2); h1 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  l0 = mulll(x2, y1); h0 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  l0 = mulll(x3, y0); h0 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  return remll_pre(h1, l1, p, pi);
}

/* Computes x0y4 + x1y3 + x2y2 + x3y1 + x4y0 (mod p); assumes p < 2^62. */
INLINE ulong
Fl_addmul5(
  ulong x0, ulong x1, ulong x2, ulong x3, ulong x4,
  ulong y0, ulong y1, ulong y2, ulong y3, ulong y4,
  ulong p, ulong pi)
{
  ulong l0, l1, h0, h1;
  LOCAL_OVERFLOW;
  LOCAL_HIREMAINDER;
  l0 = mulll(x0, y4); h0 = hiremainder;
  l1 = mulll(x1, y3); h1 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  l0 = mulll(x2, y2); h0 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  l0 = mulll(x3, y1); h0 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  l0 = mulll(x4, y0); h0 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  return remll_pre(h1, l1, p, pi);
}


INLINE GEN
zero_block(long len)
{
  GEN blk;
  long i;

  blk = cgetg_block(len + 1, t_VEC);
  for (i = 1; i <= len; ++i)
    gel(blk, i) = gen_0;
  return blk;
}

/*
 * A polmodular database for a given class invariant consists of a
 * t_VEC whose L-th entry is 0 or a GEN pointing to Phi_L.  This
 * function produces a pair of databases corresponding to the
 * j-invariant and inv.
 */
GEN
polmodular_db_init(long inv)
{
  GEN res, jdb, fdb;
  enum { DEFAULT_MODPOL_DB_LEN = 32 };

  res = cgetg_block(2 + 1, t_VEC);
  jdb = zero_block(DEFAULT_MODPOL_DB_LEN);
  gel(res, 1) = jdb;
  if (inv != INV_J) {
    fdb = zero_block(DEFAULT_MODPOL_DB_LEN);
    gel(res, 2) = fdb;
  } else {
    gel(res, 2) = gen_0;
  }
  return res;
}

void
polmodular_db_add_level(GEN *DB, long L, long inv)
{
  long max_L;
  GEN db;

  if (inv == INV_J) {
    db = gel(*DB, 1);
  } else {
    db = gel(*DB, 2);
    if ( db == gen_0)
      pari_err_BUG("polmodular_db_add_level");
  }

  max_L = lg(db) - 1;
  if (L > max_L) {
    GEN newdb;
    long i, newlen = 2 * L;

    newdb = cgetg_block(newlen + 1, t_VEC);
    for (i = 1; i <= max_L; ++i)
      gel(newdb, i) = gel(db, i);
    for (i = max_L + 1; i <= newlen; ++i)
      gel(newdb, i) = gen_0;
    killblock(db);
    /* NB: Uses the fact that INV_J == 0 */
    gel(*DB, 2 - !inv) = db = newdb;
  }
  if ( gel(db, L) == gen_0) {
    pari_sp av = avma;
    gel(db, L) = gclone(polmodular0_ZM(L, inv, NULL, NULL, 0, DB));
    avma = av;
  }
}


void
polmodular_db_add_levels(GEN *db, GEN levels, long inv)
{
  long i;
  for (i = 1; i < lg(levels); ++i)
    polmodular_db_add_level(db, levels[i], inv);
}

GEN
polmodular_db_for_inv(GEN db, long inv)
{
  if (inv == INV_J)
    return gel(db, 1);
  return gel(db, 2);
}

/* TODO: Also cache modpoly mod p for most recent p (avoid repeated
 * reductions in, for example, polclass.c:oneroot_of_classpoly(). */
GEN
polmodular_db_getp(GEN db, long L, ulong p)
{
  GEN f = gel(db, L);
  if (f == gen_0)
    pari_err_BUG("polmodular_db_getp");
  return ZM_to_Flm(f, p);
}


/**
 * SECTION: Table of discriminants to use.
 */
typedef struct {
  long L;        /* modpoly level */
  long D0;       /* fundamental discriminant */
  long D1;       /* chosen discriminant */
  long L0;       /* first generator norm */
  long L1;       /* second generator norm */
  long n1;       /* order of L0 in cl(D1) */
  long n2;       /* order of L0 in cl(D2) where D2 = L^2 D1 */
  long nprimes;  /* number of primes needed for D1 */
  long dl1;      /* m such that L0^m = L in cl(D1) */
  long dl2_0;    /* These two are (m, n) such that L0^m L1^n = form of norm L^2 in D2 */
  long dl2_1;    /* This n is always 1 or 0. */
  long cost;     /* cost to enumerate  subgroup of cl(L^2D): subgroup size is n2 if L1=0, 2*n2 o.w. */
  long bits;
  ulong *primes;
  ulong *traces;
  long inv;
} modpoly_disc_info;


static void
modpoly_disc_info_clear(modpoly_disc_info *dinfo)
{
  killblock((GEN) dinfo->primes);
  killblock((GEN) dinfo->traces);
}

#define MODPOLY_MAX_DCNT    64

static long
discriminant_with_classno_at_least(
  modpoly_disc_info Ds[MODPOLY_MAX_DCNT], long L, long inv);

/* NB: The actual table is included at the end of the file. */


/**
 * SECTION: Hard-coded evaluation functions for modular polynomials of
 * small level.
 */

/*
 * Based on phi2_eval_ff() in Sutherland's classpoly programme.
 * Calculates Phi_2(X, j) (mod p) with 6M+7A (4 reductions, not
 * counting those for Phi_2).
 */
INLINE GEN
Flm_Fl_phi2_evalx(GEN phi2, ulong j, ulong p, ulong pi)
{
  GEN res = cgetg(6, t_VECSMALL);
  ulong j2, t1;

  res[1] = 0; /* variable name */

  j2 = Fl_sqr_pre(j, p, pi);
  t1 = Fl_add(j, coeff(phi2, 3, 1), p);
  t1 = Fl_addmul2(j, j2, t1, coeff(phi2, 2, 1), p, pi);
  res[2] = Fl_add(t1, coeff(phi2, 1, 1), p);

  t1 = Fl_addmul2(j, j2, coeff(phi2, 3, 2), coeff(phi2, 2, 2), p, pi);
  res[3] = Fl_add(t1, coeff(phi2, 2, 1), p);

  t1 = Fl_mul_pre(j, coeff(phi2, 3, 2), p, pi);
  t1 = Fl_add(t1, coeff(phi2, 3, 1), p);
  res[4] = Fl_sub(t1, j2, p);

  res[5] = 1;
  return res;
}


/*
 * Based on phi3_eval_ff() in Sutherland's classpoly programme.
 * Calculates Phi_3(X, j) (mod p) with 13M+13A (6 reductions, not
 * counting those for Phi_3).
 */
INLINE GEN
Flm_Fl_phi3_evalx(GEN phi3, ulong j, ulong p, ulong pi)
{
  GEN res = cgetg(7, t_VECSMALL);
  ulong j2, j3, t1;

  res[1] = 0; /* variable name */

  j2 = Fl_sqr_pre(j, p, pi);
  j3 = Fl_mul_pre(j, j2, p, pi);

  t1 = Fl_add(j, coeff(phi3, 4, 1), p);
  res[2] = Fl_addmul3(j, j2, j3, t1,
                      coeff(phi3, 3, 1), coeff(phi3, 2, 1), p, pi);

  t1 = Fl_addmul3(j, j2, j3, coeff(phi3, 4, 2),
                  coeff(phi3, 3, 2), coeff(phi3, 2, 2), p, pi);
  res[3] = Fl_add(t1, coeff(phi3, 2, 1), p);

  t1 = Fl_addmul3(j, j2, j3, coeff(phi3, 4, 3),
                  coeff(phi3, 3, 3), coeff(phi3, 3, 2), p, pi);
  res[4] = Fl_add(t1, coeff(phi3, 3, 1), p);

  t1 = Fl_addmul2(j, j2, coeff(phi3, 4, 3), coeff(phi3, 4, 2), p, pi);
  t1 = Fl_add(t1, coeff(phi3, 4, 1), p);
  res[5] = Fl_sub(t1, j3, p);

  res[6] = 1;

  return res;
}


/*
 * Based on phi5_eval_ff() in Sutherland's classpoly programme.
 * Calculates Phi_5(X, j) (mod p) with 33M+31A (10 reductions, not
 * counting those for Phi_5).
 */
INLINE GEN
Flm_Fl_phi5_evalx(GEN phi5, ulong j, ulong p, ulong pi)
{
  GEN res = cgetg(9, t_VECSMALL);
  ulong j2, j3, j4, j5, t1;

  res[1] = 0; /* variable name */

  j2 = Fl_sqr_pre(j, p, pi);
  j3 = Fl_mul_pre(j, j2, p, pi);
  j4 = Fl_sqr_pre(j2, p, pi);
  j5 = Fl_mul_pre(j, j4, p, pi);

  t1 = Fl_add(j, coeff(phi5, 6, 1), p);
  t1 = Fl_addmul5(j, j2, j3, j4, j5, t1,
                  coeff(phi5, 5, 1), coeff(phi5, 4, 1),
                  coeff(phi5, 3, 1), coeff(phi5, 2, 1),
                  p, pi);
  res[2] = Fl_add(t1, coeff(phi5, 1, 1), p);

  t1 = Fl_addmul5(j, j2, j3, j4, j5,
                  coeff(phi5, 6, 2), coeff(phi5, 5, 2),
                  coeff(phi5, 4, 2), coeff(phi5, 3, 2), coeff(phi5, 2, 2),
                  p, pi);
  res[3] = Fl_add(t1, coeff(phi5, 2, 1), p);

  t1 = Fl_addmul5(j, j2, j3, j4, j5,
                  coeff(phi5, 6, 3), coeff(phi5, 5, 3),
                  coeff(phi5, 4, 3), coeff(phi5, 3, 3), coeff(phi5, 3, 2),
                  p, pi);
  res[4] = Fl_add(t1, coeff(phi5, 3, 1), p);

  t1 = Fl_addmul5(j, j2, j3, j4, j5,
                  coeff(phi5, 6, 4), coeff(phi5, 5, 4),
                  coeff(phi5, 4, 4), coeff(phi5, 4, 3), coeff(phi5, 4, 2),
                  p, pi);
  res[5] = Fl_add(t1, coeff(phi5, 4, 1), p);

  t1 = Fl_addmul5(j, j2, j3, j4, j5,
                  coeff(phi5, 6, 5), coeff(phi5, 5, 5),
                  coeff(phi5, 5, 4), coeff(phi5, 5, 3), coeff(phi5, 5, 2),
                  p, pi);
  res[6] = Fl_add(t1, coeff(phi5, 5, 1), p);

  t1 = Fl_addmul4(j, j2, j3, j4,
                  coeff(phi5, 6, 5), coeff(phi5, 6, 4),
                  coeff(phi5, 6, 3), coeff(phi5, 6, 2),
                  p, pi);
  t1 = Fl_add(t1, coeff(phi5, 6, 1), p);
  res[7] = Fl_sub(t1, j5, p);

  res[8] = 1;

  return res;
}

GEN
Flm_Fl_polmodular_evalx(GEN phi, long L, ulong j, ulong p, ulong pi)
{
  pari_sp av = avma;
  GEN j_powers, modpol;
  switch (L) {
  case 2:
    return Flm_Fl_phi2_evalx(phi, j, p, pi);
  case 3:
    return Flm_Fl_phi3_evalx(phi, j, p, pi);
  case 5:
    /* This is, very surprisingly, not obviously faster than the
     * original code. :(
    if ( ! coeff(phi, 1, 1))
      return Flm_Fl_phi5_s24_evalx(phi, j, p, pi);
    */
    return Flm_Fl_phi5_evalx(phi, j, p, pi);
  }
  j_powers = Fl_powers_pre(j, L + 1, p, pi);
  modpol = Flv_to_Flx(Flm_Flc_mul_pre(phi, j_powers, p, pi), 0);
  return gerepileupto(av, modpol);
}


INLINE GEN
Flm_Fl_phi2_qevalx(GEN phi, ulong a, ulong b, ulong p, ulong pi)
{
    ulong J0, J1, J2, t1;
    GEN f = cgetg(6, t_VECSMALL);

    f[1] = 0;

    t1 = Fl_sqr_pre(b, p, pi);
    J1 = Fl_mul_pre(t1, a, p, pi);
    J0 = Fl_mul_pre(t1, b, p, pi);
    t1 = Fl_sqr_pre(a, p, pi);
    J2 = Fl_mul_pre(t1, b, p, pi);

    f[2] = Fl_addmul4(J0, J1, J2, t1, a,
                      coeff(phi, 1, 3), coeff(phi, 1, 2), coeff(phi, 1, 1),
                      p, pi);
    f[3] = Fl_addmul3(J0, J1, J2,
                      coeff(phi, 2, 3), coeff(phi, 2, 2), coeff(phi, 2, 1),
                      p, pi);
    t1 = Fl_addmul2(J0, J1, coeff(phi, 3, 2), coeff(phi, 3, 1), p, pi);
    f[4] = Fl_sub(t1, J2, p);
    f[5] = J0;

    return f;
}


/* Get pointer to coeffs of f as a ulong*. */
#define Flx_coeffs(f) ((ulong *)((f) + 2))
/* Get coefficient of x^d in f, assuming f is nonzero. */
#define Flx_coeff(f, d) ((f)[(d) + 2])


/* Based on Sutherland's ffpolysmall.h:ff_poly_mgcd_linear_n_3().
 *
 * f and g are monic polynomials, f of degree greater than 3, g of
 * degree 3.
 */
INLINE GEN
Flx_mgcd_linear_n_3(GEN f, GEN g, ulong p, ulong pi)
{
  long i, d = degpol(f);
  ulong s0, s1, s2, t0, t1, t2, t3, t, u;
  GEN h = cgetg(4, t_VECSMALL);

  h[1] = 0;

  s0 = Flx_coeff(g, 0);
  s1 = Flx_coeff(g, 1);
  s2 = Flx_coeff(g, 2);
  /* NB: Sutherland's version also handles deg(f) = 3, but we don't
   * need it, since f will always be the evaluation of a modular
   * polynomial of level > 2, hence of degree > 3. */
  if (d == 4) {
    t3 = Fl_sub(Flx_coeff(f, 3), s2, p);
    t2 = Fl_sub(s1, Flx_coeff(f, 2), p);
    t = Fl_mul_pre(t3, s2, p, pi);
    t2 = Fl_add(t2, t, p);
    t1 = Fl_sub(Flx_coeff(f, 1), s0, p);
    t = Fl_mul_pre(t3, s1, p, pi);
    t1 = Fl_sub(t1, t, p);
    t = Fl_mul_pre(t3, s0, p, pi);
    t0 = Fl_sub(Flx_coeff(f, 0), t, p);

    t = Fl_mul_pre(t2, s2, p, pi);
    s2 = Fl_add(t, t1, p);
    t = Fl_mul_pre(t2, s1, p, pi);
    s1 = Fl_add(t, t0, p);
    Flx_coeff(h, 1) = Fl_addmul2(s1, s2, t1, t2, p, pi);
    t = Fl_mul_pre(t2, s0, p, pi);
    Flx_coeff(h, 0) = Fl_addmul2(t, s2, t0, t2, p, pi);
    return h;
  }

  t2 = Fl_sub(Flx_coeff(f, d - 1), s2, p);
  t1 = Fl_sub(Flx_coeff(f, d - 2), s1, p);
  t = Fl_mul_pre(t2, s2, p, pi);
  t1 = Fl_sub(t1, t, p);
  t0 = Fl_sub(Flx_coeff(f, d - 3), s0, p);
  t = Fl_addmul2(t1, t2, s1, s2, p, pi);
  t0 = Fl_sub(t0, t, p);
  for (i = d - 4; i > 1; --i) {
    t = Fl_addmul3(t0, t1, t2, s0, s1, s2, p, pi);
    t2 = t1;
    t1 = t0;
    t0 = Fl_sub(Flx_coeff(f, i), t, p);
  }
  t = Fl_addmul2(t1, t2, s0, s1, p, pi);
  t2 = Fl_neg(t0, p);
  u = Fl_mul_pre(t1, s0, p, pi);
  t1 = Fl_sub(Flx_coeff(f, 1), t, p);
  t0 = Fl_sub(Flx_coeff(f, 0), u, p);

  t = Fl_mul_pre(t2, s2, p, pi);
  s2 = Fl_add(t, t1, p);
  t = Fl_mul_pre(t2, s1, p, pi);
  s1 = Fl_add(t, t0, p);
  Flx_coeff(h, 1) = Fl_addmul2(s1, s2, t1, t2, p, pi);
  t = Fl_mul_pre(t2, s0, p, pi);
  Flx_coeff(h, 0) = Fl_addmul2(t, s2, t0, t2, p, pi);
  return h;
}


/* Based on Sutherland's ff_poly code,
 * ffpolysmall.h:ff_poly_gcd_linear_n_2() */
/* f deg d_f > 2, g deg 2, f monic, f and g are not
 * modified. */
INLINE GEN
Flx_gcd_linear_n_2(GEN f_, GEN g_, ulong p, ulong pi)
{
  long i;
  ulong s0, s1, s2, t0, t1, t, d = degpol(f_);
  ulong *f = Flx_coeffs(f_);
  ulong *g = Flx_coeffs(g_);
  GEN h = cgetg(4, t_VECSMALL);
  h[1] = 0;

  s0 = Fl_neg(g[0], p);
  s1 = Fl_neg(g[1], p);
  s2 = Fl_sqr_pre(g[2], p, pi);
  s0 = Fl_mul_pre(s0, g[2], p, pi);
  t1 = Fl_addmul_pre(g[2], f[d - 1], s1, p, pi);
  t0 = Fl_addmul2(s1, s2, f[d - 2], t1, p, pi);
  t0 = Fl_add(t0, s0, p);
  for (i = d - 3; i > 0; --i) {
    s2 = Fl_mul_pre(s2, g[2], p, pi);
    t = Fl_addmul3(s0, s1, s2, f[i], t0, t1, p, pi);
    t1 = t0;
    t0 = t;
  }
  h[3] = t0;
  s0 = Fl_neg(g[0], p);
  h[2] = Fl_addmul2(s0, s2, f[0], t1, p, pi);

  return h;
}

/* Computes s^2*g/(x-r/s) assuming g(r/s)=0 for a cubic g (not assumed
 * monic) Based on Sutherland's classpoly code,
 * phi_gcd.c:ff_poly_remove_qroot_3(). */
INLINE GEN
Flx_remove_cubic_qroot(GEN g, ulong r, ulong s, ulong p, ulong pi)
{
  ulong t1, t2;
  GEN f = cgetg(5, t_VECSMALL);

  f[1] = 0;

  t2 = Fl_sqr_pre(s, p, pi);
  t1 = Fl_addmul2(Flx_coeff(g, 2), Flx_coeff(g, 3), r, s, p, pi);
  Flx_coeff(f, 0) = Fl_addmul2(t1, t2, Flx_coeff(g, 1), r, p, pi);
  Flx_coeff(f, 1) = Fl_mul_pre(s, t1, p, pi);
  Flx_coeff(f, 2) = Fl_mul_pre(t2, Flx_coeff(g, 3), p, pi);

  return f;
}


/* Based on Sutherland's classpoly code,
 * phi_gcd.c:phi_surface_qgcd_cycle_2_p2().
 *
 * box must point to space for 2n ulongs, the first n of which must
 * point to a (surface) 2-cycle of length n, and box[n] and box[n+1]
 * should be L-isogenous to box[0] and box[1] (with box[1] correctly
 * oriented using gcds. */
static void
fill_parallel_path(
  ulong box[],
  long n, GEN phi_2, GEN phi_L, long L, ulong p, ulong pi)
{
  enum { BATCH_INVERTS = 128, E = 2 };
  long i, j;
  ulong d[BATCH_INVERTS + 2];
  ulong *twocycl = box, *ppath = box + n;

  i = 0;
  j = E;

  /* TODO: Handle avs' strange case "r == r2", I think for
   * enumerating surface elements */
  i = j;

  d[0] = 1;
  while (j < n) {
    long m, j0, k;
    d[1] = 1;
    m = minss(BATCH_INVERTS, n - j);
    j0 = j - 2;
    for (k = 2; k <= m + 1; ++i, ++j, ++k) {
      pari_sp av = avma;
      GEN f, g, h;
      f = Flm_Fl_polmodular_evalx(phi_L, L, twocycl[i], p, pi);
      g = Flm_Fl_phi2_qevalx(phi_2, ppath[j - 1], d[k - 1], p, pi);
      g = Flx_remove_cubic_qroot(g, ppath[j - 2], d[k - 2], p, pi);
      h = Flx_gcd_linear_n_2(f, g, p, pi);
      ppath[j] = Fl_neg(Flx_coeff(h, 0), p);
      d[k] = Flx_coeff(h, 1);
      avma = av;
    }
    /* Make &d[1] into a vecsmall of m elements. Calculates the
     * inverse of d[2] up to d[m + 2]. */
    d[1] = evaltyp(t_VECSMALL) | _evallg(m + 1);
    Flv_inv_pre_inplace((GEN)&d[1], p, pi);
    for (k = 2; k <= m + 1; ++k)
      ppath[j0 + k] = Fl_mul_pre(ppath[j0 + k], d[k], p, pi);
  }
}


/* Put the common neighbour of box[1] and box[r] into box[r+1] */
INLINE void
fill_corner(
  ulong box[], long r, long L, GEN phi_2, GEN phi_L, ulong p, ulong pi)
{
  ulong left = box[1], up = box[r];
  GEN f, g, h;
  f = Flm_Fl_polmodular_evalx(phi_L, L, left, p, pi);
  g = Flm_Fl_phi2_evalx(phi_2, up, p, pi);
  h = Flx_mgcd_linear_n_3(f, g, p, pi);
  if (degpol(h) != 1)
    pari_err_BUG("fill_corner: Wrong number of roots");
  box[r + 1] = Fl_neg(Flx_coeff(h, 0), p);
  if (Flx_coeff(h, 1) != 1)
    box[r + 1] = Fl_div(box[r + 1], Flx_coeff(h, 1), p);
}


/* d is the depth of the 2-volcano, r is the order of [2] in cl(O). */
INLINE void
fill_box(
  ulong box[], long L, long d2, long dL, long r,
  GEN fdb, ulong p, ulong pi)
{
  pari_sp av = avma;
  GEN phi_2 = polmodular_db_getp(fdb, 2, p);
  GEN phi_L = polmodular_db_getp(fdb, L, p);
  ulong *sidestep = (ulong *)new_chunk(2 + dL);

  walk_surface_path(box, phi_2, p, pi, 2, d2, r - 1);
  sidestep[0] = box[0];
  walk_surface_path(sidestep, phi_L, p, pi, L, dL, 1);
  box[r] = sidestep[1];
  fill_corner(box, r, L, phi_2, phi_L, p, pi);
  fill_parallel_path(box, r, phi_2, phi_L, L, p, pi);

  avma = av;
}


static GEN
enum_j_fast(
  ulong j0, long D, long L1, long d2, long dL, long r,
  GEN fdb, ulong p, ulong pi)
{
  enum { L0 = 2 };
  GEN res = cgetg(2 * r + 1, t_VECSMALL);
  if (4 * L0 * L0 * L1 * L1 > -D || d2 > r || dL + 2 > r)
    pari_err_BUG("enum_j_fast: invalid parameters");
  res[1] = j0;
  fill_box(zv_to_ulongptr(res), L1, d2, dL, r, fdb, p, pi);
  return res;
}


/**
 * SECTION: Velu's formula for the codmain curve in the case of small
 * prime base field.
 */

INLINE ulong
Fl_mul4(ulong x, ulong p)
{
  return Fl_double(Fl_double(x, p), p);
}

INLINE ulong
Fl_mul5(ulong x, ulong p)
{
  return Fl_add(x, Fl_mul4(x, p), p);
}

INLINE ulong
Fl_mul8(ulong x, ulong p)
{
  return Fl_double(Fl_mul4(x, p), p);
}

INLINE ulong
Fl_mul6(ulong x, ulong p)
{
  return Fl_sub(Fl_mul8(x, p), Fl_double(x, p), p);
}

INLINE ulong
Fl_mul7(ulong x, ulong p)
{
  return Fl_sub(Fl_mul8(x, p), x, p);
}

INLINE ulong
uQ_calc(ulong a4, ulong a6, ulong xQ, ulong p, ulong pi)
{
  /* uQ = 4 xQ^3 + b2 xQ^2 + 2 b4 xQ + b6
   *    = 4 xQ^3 + 4 a4 xQ + 4 a6
   *    = 4 ((xQ^2 + a4) xQ + a6)
   * (since b2 = 0, b4 = 2 a4 and b6 = 4 a6) */
  ulong t1 = Fl_add(Fl_sqr_pre(xQ, p, pi), a4, p);
  return Fl_mul4(Fl_add(Fl_mul_pre(t1, xQ, p, pi), a6, p), p);
}


/*
 * Given an elliptic curve E = [a4, a6] over F_p and a non-zero point
 * pt on E, return the quotient E' = E/<P> = [a4_img, a6_img].
 *
 * TODO: Compare with an apparently simpler version of this algorithm in
 * Sutherland 2012, Section 6.4.
 */
static void
Fle_quotient_from_kernel_generator(
  ulong *a4_img, ulong *a6_img, ulong a4, ulong a6, GEN pt, ulong p, ulong pi)
{
  pari_sp av = avma;
  ulong t = 0, w = 0;
  GEN Q;
  ulong xQ, tQ, uQ;

  Q = gcopy(pt);
  /* Note that, as L is odd, say L = 2n + 1, we necessarily have
   * [(L - 1)/2]P = [n]P = [n - L]P = -[n + 1]P = -[(L + 1)/2]P.  This is
   * what the condition Q[1] != xQ tests, so the loop will execute n times. */
  do {
    xQ = Q[1];
    /* tQ = 6 xQ^2 + b2 xQ + b4
     *    = 6 xQ^2 + 2 a4 (since b2 = 0 and b4 = 2 a4) */
    tQ = Fl_add(Fl_mul6(Fl_sqr_pre(xQ, p, pi), p), Fl_double(a4, p), p);
    t = Fl_add(t, tQ, p);

    uQ = uQ_calc(a4, a6, xQ, p, pi);
    /* w += uQ + tQ * xQ */
    w = Fl_add(w, Fl_add(uQ, Fl_mul_pre(tQ, xQ, p, pi), p), p);
    Q = Fle_add(pt, Q, a4, p);
  } while ((ulong)Q[1] != xQ);
  avma = av;
  /* a4_img = a4 - 5 * t */
  *a4_img = Fl_sub(a4, Fl_mul5(t, p), p);
  /* a6_img = a6 - b2 * t - 7 * w = a6 - 7 * w
   * (since a1 = a2 = 0 ==> b2 = 0) */
  *a6_img = Fl_sub(a6, Fl_mul7(w, p), p);
}


/**
 * SECTION: Calculation of modular polynomials.
 */

/*
 * Given an elliptic curve [a4, a6] over FF_p, try to find a
 * non-trivial L-torsion point on the curve by considering n times a
 * random point; val controls the maximum L-valuation expected of n
 * times a random point.
 */
static GEN
find_L_tors_point(
  ulong *ival,
  ulong a4, ulong a6, ulong p, ulong pi,
  ulong n, ulong L, ulong val)
{
  pari_sp av = avma;
  ulong i;
  GEN P, Q;
  do {
    Q = random_Flj_pre(a4, a6, p, pi);
    P = Flj_mulu_pre(Q, n, a4, p, pi);
  } while (P[3] == 0);

  for (i = 0; i < val; ++i) {
    Q = Flj_mulu_pre(P, L, a4, p, pi);
    if (Q[3] == 0)
      break;
    P = Q;
  }
  if (ival)
    *ival = i;
  return gerepilecopy(av, P);
}


static GEN
select_curve_with_L_tors_point(
  ulong *a4, ulong *a6,
  ulong L, ulong j, ulong n, ulong card, ulong val,
  norm_eqn_t ne)
{
  pari_sp av = avma;
  ulong A4, A4t, A6, A6t;
  ulong p = ne->p, pi = ne->pi;
  GEN P;
  if (card % L != 0) {
    pari_err_BUG("select_curve_with_L_tors_point: "
                 "Cardinality not divisible by L");
  }

  Fl_ellj_to_a4a6(j, p, &A4, &A6);
  Fl_elltwist_disc(A4, A6, ne->T, p, &A4t, &A6t);

  /* Either E = [a4, a6] or its twist has cardinality divisible by L
   * because of the choice of p and t earlier on.  We find out which
   * by attempting to find a point of order L on each.  See bot p16 of
   * Sutherland 2012. */
  while (1) {
    ulong i;
    P = find_L_tors_point(&i, A4, A6, p, pi, n, L, val);
    if (i < val)
      break;
    avma = av;
    lswap(A4, A4t);
    lswap(A6, A6t);
  }

  *a4 = A4;
  *a6 = A6;
  return gerepilecopy(av, P);
}


/*
 * Return 1 if the L-Sylow subgroup of the curve [a4, a6] (mod p) is
 * cyclic, return 0 if it is not cyclic with "high" probability (I
 * guess around 1/L^3 chance it is still cyclic when we return 0).
 *
 * NB: A return value of 1 means that [a4, a6] (mod p) is on the floor
 * of its L-volcano.
 *
 * This code is based on Sutherland's
 * velu.c:velu_verify_Sylow_cyclic() in classpoly-1.0.1.
 */
INLINE long
verify_L_sylow_is_cyclic(
  long e, ulong a4, ulong a6, ulong p, ulong pi)
{
  /* Number of times to try to find a point with maximal order in the
   * L-Sylow subgroup. */
  enum { N_RETRIES = 3 };
  pari_sp av = avma;
  long i, res = 0;
  GEN P;
  for (i = 0; i < N_RETRIES; ++i) {
    P = random_Flj_pre(a4, a6, p, pi);
    P = Flj_mulu_pre(P, e, a4, p, pi);
    if (P[3] != 0) {
      res = 1;
      break;
    }
  }
  avma = av;
  return res;
}


static ulong
find_noniso_L_isogenous_curve(
  ulong L, ulong n,
  norm_eqn_t ne, long e, ulong val, ulong a4, ulong a6, GEN init_pt)
{
  pari_sp ltop, av;
  ulong p = ne->p, pi = ne->pi, j_res = 0;
  GEN pt = init_pt;
  ltop = av = avma;
  while (1) {
    /* c. Use Velu to calculate L-isogenous curve E' = E/<P> */
    ulong a4_img, a6_img;
    ulong z2 = Fl_sqr_pre(pt[3], p, pi);
    pt = mkvecsmall2(Fl_div(pt[1], z2, p),
                     Fl_div(pt[2], Fl_mul_pre(z2, pt[3], p, pi), p));
    Fle_quotient_from_kernel_generator(&a4_img, &a6_img,
                                       a4, a6, pt, p, pi);

    /* d. If j(E') = j_res has a different endo ring to j(E), then
     *    return j(E').  Otherwise, go to b. */
    if (verify_L_sylow_is_cyclic(e, a4_img, a6_img, p, pi)) {
      j_res = Fl_ellj_pre(a4_img, a6_img, p, pi);
      break;
    }

    /* b. Generate random point P on E of order L */
    avma = av;
    pt = find_L_tors_point(0, a4, a6, p, pi, n, L, val);
  }

  avma = ltop;
  return j_res;
}

/*
 * Given a prime L and a j-invariant j (mod p), return the j-invariant
 * of a curve which has a different endomorphism ring to j and is
 * L-isogenous to j.
 */
INLINE ulong
compute_L_isogenous_curve(
  ulong L, ulong n, norm_eqn_t ne,
  ulong j, ulong card, ulong val)
{
  ulong a4, a6;
  long e;
  GEN pt;

  if (ne->p < 5 || j == 0 || j == 1728 % ne->p) {
    char *err = stack_sprintf("compute_L_isogenous_curve: "
                              "Invalid params j = %lu, p = %lu", j, ne->p);
    pari_err_BUG(err);
  }

  pt = select_curve_with_L_tors_point(&a4, &a6, L, j, n, card, val, ne);

  e = card / L;
  if (e * L != card) {
    char *err = stack_sprintf("compute_L_isogenous_curve: "
                              "L = %lu must divide p + 1 - t = %lu",
                              L, card);
    pari_err_BUG(err);
  }

  return find_noniso_L_isogenous_curve(L, n, ne, e, val, a4, a6, pt);
}

INLINE GEN
get_Lsqr_cycle(const modpoly_disc_info *dinfo)
{
  long i, n1 = dinfo->n1, L = dinfo->L;
  GEN cyc = cgetg(L, t_VECSMALL);
  cyc[1] = 0;
  for (i = 2; i <= L / 2; ++i)
    cyc[i] = cyc[i - 1] + n1;
  if ( ! dinfo->L1) {
    for ( ; i < L; ++i)
      cyc[i] = cyc[i - 1] + n1;
  } else {
    cyc[L - 1] = 2 * dinfo->n2 - n1 / 2;
    for (i = L - 2; i > L / 2; --i)
      cyc[i] = cyc[i + 1] - n1;
  }
  return cyc;
}

INLINE void
update_Lsqr_cycle(GEN cyc, const modpoly_disc_info *dinfo)
{
  long i, L = dinfo->L;
  for (i = 1; i < L; ++i)
    ++cyc[i];
  if (dinfo->L1 && cyc[L - 1] == 2 * dinfo->n2) {
    long n1 = dinfo->n1;
    for (i = L / 2 + 1; i < L; ++i)
      cyc[i] -= n1;
  }
}


static ulong
oneroot_of_classpoly(
  GEN hilb, GEN factu, norm_eqn_t ne, GEN jdb)
{
  pari_sp av = avma;
  ulong j0, p = ne->p, pi = ne->pi;
  long i, nfactors = lg(gel(factu, 1)) - 1;
  GEN hilbp = ZX_to_Flx(hilb, p);

  /* TODO: Work out how to use hilb with better invariant */
  j0 = Flx_oneroot_split(hilbp, p);
  if (j0 == p) {
    pari_err_BUG("oneroot_of_classpoly: "
                 "Didn't find a root of the class polynomial");
  }
  for (i = 1; i <= nfactors; ++i) {
    long L = gel(factu, 1)[i];
    long val = gel(factu, 2)[i];
    GEN phi = polmodular_db_getp(jdb, L, p);
    val += z_lval(ne->v, L);
    j0 = descend_volcano(phi, j0, p, pi, 0, L, val, val);
    avma = av;
  }
  avma = av;
  return j0;
}


INLINE GEN
enum_volcano_surface(
  const modpoly_disc_info *dinfo, norm_eqn_t ne, ulong j0, GEN fdb)
{
  pari_sp av = avma;
  GEN pcp = mkvec2(mkvecsmall(dinfo->L0), mkvecsmall(dinfo->n1));
  return gerepileupto(av, enum_j_with_endo_ring(j0, 1, ne, fdb, pcp, dinfo->n1));
}


INLINE GEN
enum_floor_curves(
  long L, norm_eqn_t ne, ulong j0_pr, GEN fdb,
  const modpoly_disc_info *dinfo)
{
  /* L^2 D is the discriminant for the order R = Z + L OO. */
  long DR = L * L * ne->D;
  long R_cond = L * ne->u; /* conductor(DR); */
  long w = R_cond * ne->v;
  if (dinfo->L0 == 2 && dinfo->L1 != 0) {
    /* TODO: Calculate these once and for all in polmodular0_ZM(). */
    long d2 = z_lval(w, 2);
    long dL = z_lval(w, dinfo->L1);
    return enum_j_fast(j0_pr, DR, dinfo->L1, d2, dL, dinfo->n2, fdb,
        ne->p, ne->pi);
  } else {
    pari_sp av = avma;
    /* TODO: Calculate these once and for all in polmodular0_ZM(). */
    GEN pcp;
    long max_elts;
    norm_eqn_t eqn;
    memcpy(eqn, ne, sizeof *ne);
    eqn->D = DR;
    eqn->u = R_cond;
    eqn->v = w;
    if (dinfo->L1) {
      pcp = mkvec2(
        mkvecsmall2(dinfo->L0, dinfo->L1),
        mkvecsmall2(dinfo->n2, 2));
      max_elts = 2 * dinfo->n2;
    } else {
      pcp = mkvec2(mkvecsmall(dinfo->L0), mkvecsmall(dinfo->n2));
      max_elts = dinfo->n2;
    }
    return gerepileupto(av, enum_j_with_endo_ring(j0_pr, 1, eqn, fdb, pcp, max_elts));
  }
}


INLINE long
carray_isin(long *arr, long n, long el)
{
  long i = 0;
  while (el != *arr++ && ++i < n)
    ;
  return i;
}

INLINE void
carray_reverse_inplace(long *arr, long n)
{
  long lim = n>>1, i;
  --n;
  for (i = 0; i < lim; i++)
    lswap(arr[i], arr[n - i]);
}

INLINE void
append_neighbours(GEN rts, GEN surface_js, long njs, long L, long m, long i)
{
  long r_idx = (((i - 1) + m) % njs) + 1; /* (i + m) % njs */
  long l_idx = smodss((i - 1) - m, njs) + 1; /* (i - m) % njs */
  rts[L] = surface_js[l_idx];
  rts[L + 1] = surface_js[r_idx];
}

INLINE GEN
roots_to_coeffs(GEN rts, ulong p, long L)
{
  pari_sp av;
  long i, k;
  GEN M = zero_Flm_copy(lg(rts) - 1, L + 2);
  av = avma;
  for (i = 1; i < lg(rts); ++i) {
    GEN modpol = Flv_roots_to_pol(gel(rts, i), p, 0);
    for (k = 1; k <= L + 2; ++k)
      coeff(M, i, k) = modpol[k + 1];
    avma = av;
  }
  return M;
}


/* NB: Assumes indices are offset at 0, not at 1 like in GENs;
 * i.e. indices[i] will pick out v[indices[i] + 1] from v. */
INLINE void
vecsmall_pick(GEN res, GEN v, GEN indices)
{
  long i;
  for (i = 1; i < lg(indices); ++i)
    res[i] = v[indices[i] + 1];
}


/* The first element of surface_js must lie above the first element of
 * floor_js.  Will reverse surface_js if it is not oriented in the
 * same direction as floor_js. */
INLINE GEN
root_matrix(
  long L, ulong p, const modpoly_disc_info *dinfo,
  long njinvs, GEN surface_js, GEN floor_js, ulong j1pr_rt)
{
  pari_sp av;
  long i, m = dinfo->dl1, njs = lg(surface_js) - 1;
  GEN rt_mat = zero_Flm_copy(L + 1, njinvs), rts, cyc;
  av = avma;

  /* i = 1 */
  cyc = get_Lsqr_cycle(dinfo);
  rts = gel(rt_mat, 1);
  vecsmall_pick(rts, floor_js, cyc);
  append_neighbours(rts, surface_js, njs, L, m, 1);

  /* i = 2 */
  update_Lsqr_cycle(cyc, dinfo);
  rts = gel(rt_mat, 2);
  vecsmall_pick(rts, floor_js, cyc);
  /* Fix orientation if necessary */
  /* TODO: Check if the second condition predicts whether we get the
   * correct coeff of X^L Y^L first time or not. */
  if (carray_isin(rts + 1, L - 1, j1pr_rt) == L - 1
      && (dinfo->inv != INV_F || carray_isin(rts + 1, L - 1, Fl_neg(j1pr_rt, p)) == L - 1))
    carray_reverse_inplace(surface_js + 2, lg(surface_js) - 2);
  append_neighbours(rts, surface_js, njs, L, m, 2);

  for (i = 3; i <= njinvs; ++i) {
    update_Lsqr_cycle(cyc, dinfo);
    rts = gel(rt_mat, i);
    vecsmall_pick(rts, floor_js, cyc);
    append_neighbours(rts, surface_js, njs, L, m, i);
  }
  avma = av;
  return rt_mat;
}


INLINE void
interpolate_coeffs(GEN phi_modp, ulong p, GEN j_invs, GEN coeff_mat)
{
  pari_sp av = avma;
  long i;
  GEN pols = Flv_FlvV_polint(j_invs, coeff_mat, p, 0);
  for (i = 1; i < lg(pols); ++i) {
    GEN pol = gel(pols, i);
    long k, maxk = lg(pol);
    for (k = 2; k < maxk; ++k)
      coeff(phi_modp, k - 1, i) = pol[k];
  }
  avma = av;
}


INLINE long
Flv_lastnonzero(GEN v)
{
  long i;
  for (i = lg(v) - 1; i > 0; --i)
    if (v[i])
      break;
  return i;
}


/*
 * Assuming the matrix of coefficients in phi corresponds to
 * polynomials phi_k^* satisfying Y^c phi_k^*(Y^s) for c in {0, 1,
 * ..., s} satisfying c + Lk = L + 1 (mod s), change phi so that the
 * coefficients are for the polynomials Y^c phi_k^*(Y^s) (s is the
 * sparsity factor).
 */
INLINE void
inflate_polys(GEN phi, long L, long s)
{
  long k, deg = L + 1;
  long maxr;
  maxr = nbrows(phi);
  for (k = 0; k <= deg; ) {
    long i, c = smodss(L * (1 - k) + 1, s);
    /* TODO: We actually know that the last non-zero element of
     * gel(phi, k) can't be later than index n + 1, where n is about
     * (L + 1)/s. */
    ++k;
    for (i = Flv_lastnonzero(gel(phi, k)); i > 0; --i) {
      long r = c + (i - 1) * s + 1;
      if (r > maxr) {
        coeff(phi, i, k) = 0;
        continue;
      }
      if (r != i) {
        coeff(phi, r, k) = coeff(phi, i, k);
        coeff(phi, i, k) = 0;
      }
    }
  }
}

INLINE int
safe_abs_sqrt(ulong *r, ulong x, ulong p, ulong pi)
{
  if (krouu(x, p) == -1) {
    if (p%4 == 1) return 0;
    x = Fl_neg(x, p);
  }
  *r = Fl_sqrt_pre(x, p, pi);
  return 1;
}

INLINE int
eighth_root(ulong *r, ulong x, ulong p, ulong pi)
{
  ulong s;
  if (krouu(x, p) == -1)
    return 0;
  s = Fl_sqrt_pre(x, p, pi);
  if ( ! safe_abs_sqrt(&s, s, p, pi))
    return 0;
  return safe_abs_sqrt(r, s, p, pi);
}


ulong
modfn_root(ulong j, norm_eqn_t ne, long inv)
{
  pari_sp av;
  GEN pol, rts;
  long i;
  ulong g2, f = 0, p = ne->p, pi = ne->pi;
  switch (inv) {
  case INV_J:
    return j;
  case INV_G2:
    return Fl_sqrtl_pre(j, 3, p, pi);
  case INV_F:
    av = avma;
    /* f^8 must be a root of X^3 - \gamma_2 X - 16 */
    g2 = Fl_sqrtl_pre(j, 3, p, pi);

    pol = mkvecsmall5(0UL, Fl_neg(16 % p, p), Fl_neg(g2, p), 0UL, 1UL);
    rts = Flx_roots(pol, p);
    for (i = 1; i < lg(rts); ++i) {
      if (eighth_root(&f, rts[i], p, pi))
        break;
    }
    if (i == lg(rts))
      pari_err_BUG("modfn_root");
    avma = av;
    return f;
  default:
    pari_err_BUG("modfn_root");
  }
  return ULONG_MAX;
}

INLINE ulong
modfn_preimage(ulong x, norm_eqn_t ne, long inv)
{
  ulong x24, p, pi;
  switch (inv) {
  case INV_J:
    return x;
  case INV_G2:
    return Fl_powu_pre(x, 3, ne->p, ne->pi);
  case INV_F:
    /* If x satisfies (X^24 - 16)^3 - X^24 * j = 0
     * then j = (x^24 - 16)^3 / x^24 */
    p = ne->p;
    pi = ne->pi;
    x24 = Fl_powu_pre(x, 24, p, pi);
    return Fl_div(Fl_powu_pre(Fl_sub(x24, 16 % p, p), 3, p, pi), x24, p);
  default:
    pari_err_BUG("modfn_preimage");
  }
  return ULONG_MAX;
}


INLINE void
Flv_powu_inplace_pre(GEN v, ulong n, ulong p, ulong pi)
{
  long i;
  for (i = 1; i < lg(v); ++i)
    v[i] = Fl_powu_pre(v[i], n, p, pi);
}

INLINE void
normalise_coeffs(GEN coeffs, GEN js, long L, long s, ulong p, ulong pi)
{
  pari_sp av = avma;
  long k;
  GEN pows, inv_js;
  if (s == 1)
    return;

  /* pows[i + 1] contains 1 / js[i + 1]^i for i = 0, ..., s - 1. */
  pows = cgetg(s + 1, t_VEC);
  gel(pows, 1) = const_vecsmall(lg(js) - 1, 1);
  inv_js = Flv_inv_pre(js, p, pi);
  gel(pows, 2) = inv_js;
  for (k = 3; k <= s; ++k) {
    gel(pows, k) = gcopy(inv_js);
    Flv_powu_inplace_pre(gel(pows, k), k - 1, p, pi);
  }

  /* For each column of coefficients coeffs[k] = [a0 .. an],
   *   replace ai by ai / js[i]^c.
   * Said in another way, normalise each row i of coeffs by
   * dividing through by js[i - 1]^c (where c depends on i). */
  for (k = 1; k < lg(coeffs); ++k) {
    long i, c = smodss(L * (1 - (k - 1)) + 1, s);
    GEN col = gel(coeffs, k), C = gel(pows, c + 1);
    for (i = 1; i < lg(col); ++i)
      col[i] = Fl_mul_pre(col[i], C[i], p, pi);
  }
  avma = av;
}

/*
 * This is Sutherland 2012, Algorithm 2.1, p16.
 */
static GEN
polmodular_split_p_Flm(
  ulong L, GEN hilb, GEN factu, norm_eqn_t ne, GEN db,
  const modpoly_disc_info *dinfo)
{
  pari_sp ltop = avma;
  ulong j0, j0_rt, j0pr, j0pr_rt, j1, j1pr, j1pr_rt;
  ulong n, card, val, p = ne->p, pi = ne->pi;
  long s = inv_sparse_factor(dinfo->inv);
  long nj_selected = ceil((L + 1)/(double)s) + 1;
  GEN surface_js, floor_js, rts;
  GEN phi_modp;
  GEN jdb, fdb;
  long switched_signs = 0;

  jdb = polmodular_db_for_inv(db, INV_J);
  fdb = polmodular_db_for_inv(db, dinfo->inv);

  /* Precomputation */
  card = p + 1 - ne->t;
  val = u_lvalrem(card, L, &n); /* n = card / L^{v_L(card)} */

  j0 = oneroot_of_classpoly(hilb, factu, ne, jdb);
  j0_rt = modfn_root(j0, ne, dinfo->inv);
  surface_js = enum_volcano_surface(dinfo, ne, j0_rt, fdb);
  j0pr = compute_L_isogenous_curve(L, n, ne, j0, card, val);
  j0pr_rt = modfn_root(j0pr, ne, dinfo->inv);
  floor_js = enum_floor_curves(L, ne, j0pr_rt, fdb, dinfo);

  /* NB: Not sure this is the correct way to orient the surface and
   * floor but it seems to work. */
  j1 = modfn_preimage(surface_js[2], ne, dinfo->inv);
  j1pr = compute_L_isogenous_curve(L, n, ne, j1, card, val);
  j1pr_rt = modfn_root(j1pr, ne, dinfo->inv);
  rts = root_matrix(L, p, dinfo, nj_selected, surface_js, floor_js, j1pr_rt);

  do {
    pari_sp btop = avma;
    long i;
    GEN coeffs, surf;

    coeffs = roots_to_coeffs(rts, p, L);
    surf = vecsmall_shorten(surface_js, nj_selected);
    if (s > 1) {
      normalise_coeffs(coeffs, surf, L, s, p, pi);
      Flv_powu_inplace_pre(surf, s, p, pi);
    }
    phi_modp = zero_Flm_copy(L + 2, L + 2);
    interpolate_coeffs(phi_modp, p, surf, coeffs);
    if (s > 1)
      inflate_polys(phi_modp, L, s);

    if (ucoeff(phi_modp, L + 1, L + 1) == p - 1)
      break;

    if (switched_signs)
      pari_err_BUG("polmodular_split_p_Flm");

    avma = btop;
    for (i = 1; i < lg(rts); ++i) {
      surface_js[i] = Fl_neg(surface_js[i], p);
      coeff(rts, L, i) = Fl_neg(coeff(rts, L, i), p);
      coeff(rts, L + 1, i) = Fl_neg(coeff(rts, L + 1, i), p);
    }
    switched_signs = 1;
  } while (1);
  dbg_printf(4)("  Phi_%lu(X, Y) (mod %lu) = %Ps\n", L, p, phi_modp);

  return gerepileupto(ltop, phi_modp);
}


INLINE void
norm_eqn_init(norm_eqn_t ne, long D, long u)
{
  memset(ne, 0, sizeof(*ne));
  ne->D = D;
  ne->u = u;
}


INLINE void
norm_eqn_update(norm_eqn_t ne, ulong t, ulong p, long L)
{
  long res;
  ulong vL_sqr, vL;

  ne->t = t;
  ne->p = p;
  ne->pi = get_Fl_red(p);

  vL_sqr = (4 * p - t * t) / -ne->D;
  res = uissquareall(vL_sqr, &vL);
  if ( ! res || vL % L)
    pari_err_BUG("norm_eqn_update");

  ne->v = vL;

  /* Select twisting parameter. */
  do
    ne->T = random_Fl(p);
  while (krouu(ne->T, p) != -1);
}

INLINE void
Flv_deriv_pre_inplace(GEN v, long deg, ulong p, ulong pi)
{
  long i, ln = lg(v), d = deg % p;
  for (i = ln - 1; i > 1; --i, --d)
    v[i] = Fl_mul_pre(v[i - 1], d, p, pi);
  v[1] = 0;
}

/* NB: Deliberately leave a dirty stack, since the result must be
 * gerepileupto'd straight away in any case. */
INLINE GEN
eval_modpoly_modp(
  GEN modpoly_modp, GEN j_powers, norm_eqn_t ne, int compute_derivs)
{
  ulong p = ne->p, pi = ne->pi;
  long L = lg(j_powers) - 3;
  GEN j_pows_p = ZV_to_Flv(j_powers, p);
  GEN tmp = cgetg(2 + 2 * compute_derivs, t_VEC);
  /* We wrap the result in this t_VEC modpoly_modp to trick the
   * ZM_*_CRT() functions into thinking it's a matrix. */
  gel(tmp, 1) = Flm_Flc_mul_pre(modpoly_modp, j_pows_p, p, pi);
  if (compute_derivs) {
    Flv_deriv_pre_inplace(j_pows_p, L + 1, p, pi);
    gel(tmp, 2) = Flm_Flc_mul_pre(modpoly_modp, j_pows_p, p, pi);
    Flv_deriv_pre_inplace(j_pows_p, L + 1, p, pi);
    gel(tmp, 3) = Flm_Flc_mul_pre(modpoly_modp, j_pows_p, p, pi);
  }
  return tmp;
}


/* The largest level of the "hand written" modular polynomials */
#define MAX_INTERNAL_MODPOLY_LEVEL 5

/* NB: Result not suitable for gerepileupto(). */
static GEN
sympol_to_ZM(GEN phi, long L)
{
  GEN res = zeromatcopy(L + 2, L + 2);
  long i, j, c = 1;
  for (i = 1; i <= L + 1; ++i) {
    for (j = 1; j <= i; ++j, ++c)
      gcoeff(res, i, j) = gcoeff(res, j, i) = gel(phi, c);
  }
  gcoeff(res, L + 2, 1) = gcoeff(res, 1, L + 2) = gen_1;
  return res;
}


static long
simple_find_disc(long L, long inv, long L0)
{
  pari_sp av = avma;
  long d;

  /* Need inv_N coprime to D. */
  for (d = 39; ; d += 4) { /* d = unextprime(d + 1)) { */
    long h;
    GEN D, H;
    if (kross(-d, L0) == 1 && kross(-d, L) == 1
        && unegisfundamental(d)
        && inv_good_discriminant(-d, inv)) {
      D = stoi(-d);
      H = classno(D);
      h = itos(H);
      /* Usually we'd want to limit how big h is, but this function is
       * only called for a few small L and it turns out that picking
       * the first h that's big enough works satisfactorily. */
      if (h >= L + 1) {
        long n = itos(qfi_order(redimag(primeform_u(D, L0)), H));
        if (n == h)
          break;
      }
    }
    avma = av;
  }
  avma = av;
  return -d;
}


static long select_L0(long, long, long);
static double modpoly_height_bound(long, long);
static long modpoly_pickD_primes(
  ulong *primes, ulong *traces, long max, ulong *xprimes, long xcnt, long *totbits, long minbits,
  modpoly_disc_info *Dinfo);

static GEN
pick_primes_no_pcp(long D, double ht, long L, long inv)
{
  pari_sp av = avma;
  double prime_bits = 0.0;
  ulong v;
  GEN res = vecsmalltrunc_init(ceil(ht / log2(-D)) + 1);
  for (v = 1; v < 100 && prime_bits < ht; ++v) {
    ulong t, m_vLsqr_D = v * v * L * L * (ulong)(-D);
    if ((v & 1) && (D & 7) == 1)
      continue;
    for (t = 2; prime_bits < ht; ++t) {
      ulong possible_4p = t * t + m_vLsqr_D;
      if (possible_4p % 4 == 0) {
        ulong p = possible_4p / 4;
        if (p > (1UL << (BITS_IN_LONG - 2)))
          break;
        if (inv_good_prime(p, inv) && uisprime(p)) {
          vecsmalltrunc_append(res, p);
          prime_bits += log2(p);
        }
      }
    }
  }
  if (prime_bits < ht)
    pari_err_BUG("pick_primes_level2: insufficient primes");

  return gerepileupto(av, res);
}

INLINE void
Flv_modfn_roots(GEN v, norm_eqn_t ne, long inv)
{
  long i, n = lg(v);
  for (i = 1; i < n; ++i)
    v[i] = modfn_root(v[i], ne, inv);
}

static GEN
polmodular0_generic_ZM(long L, long inv, GEN *db)
{
  pari_sp ltop = avma, av;
  long s, D, L0, nprimes, N;
  double ht;
  GEN mp, pol, P, H;

  GEN primes;
  L0 = select_L0(L, inv, 0);
  D = simple_find_disc(L, inv, L0);
  ht = modpoly_height_bound(L, inv);
  H = polclass0(D, INV_J, 0, db);
  mp = polmodular0_ZM(L, INV_J, 0, 0, 0, db);

  /* TODO: Use sparsity factor N = ceil((L + 1)/s) + 1 ?  Probably not
   * worth the increase in complexity. */
  N = L + 2;

  primes = pick_primes_no_pcp(D, ht, L, inv);
  nprimes = lg(primes);

  av = avma;
  pol = ZM_init_CRT(zero_Flm_copy(N, L + 2), 1);
  P = gen_1;
  for (s = 1; s < nprimes; ++s) {
    pari_sp av1, av2;
    ulong p = primes[s], pi = get_Fl_red(p);
    long i;
    GEN Hrts, Hp, Phip, coeff_mat, phi_modp;
    norm_eqn_t ne;
    ne->p = p;
    ne->pi = pi;

    phi_modp = zero_Flm_copy(N, L + 2);
    av1 = avma;
    Hp = ZX_to_Flx(H, p);
    Hrts = Flx_roots(Hp, p);
    Phip = ZM_to_Flm(mp, p);
    coeff_mat = zero_Flm_copy(N, L + 2);
    av2 = avma;
    for (i = 1; i <= N; ++i) {
      long k;
      GEN jpows, modpoly_at_ji, mprts;

      jpows = Fl_powers_pre(Hrts[i], L + 1, p, pi);
      modpoly_at_ji = Flm_Flc_mul_pre(Phip, jpows, p, pi);
      mprts = Flx_roots(Flv_to_Flx(modpoly_at_ji, 0), p);
      if (lg(mprts) != L + 2)
        pari_err_BUG("polmodular0_generic_ZM");

      Flv_modfn_roots(mprts, ne, inv);
      modpoly_at_ji = Flv_roots_to_pol(mprts, p, 0);

      for (k = 1; k <= L + 2; ++k)
        coeff(coeff_mat, i, k) = modpoly_at_ji[k + 1];
      avma = av2;
    }

    setlg(Hrts, N + 1);
    Flv_modfn_roots(Hrts, ne, inv);

    interpolate_coeffs(phi_modp, p, Hrts, coeff_mat);
    avma = av1;

    (void) ZM_incremental_CRT(&pol, phi_modp, &P, p);
    if (gc_needed(av, 2))
      gerepileall(av, 2, &pol, &P);
  }

  return gerepilecopy(ltop, pol);
}

static GEN
polmodular_small_ZM(long L, long inv, GEN *db);

GEN
polmodular0_ZM(
  long L, long inv, GEN J, GEN Q, int compute_derivs, GEN *db)
{
  pari_sp ltop = avma;
  long k, d, Dcnt, nprimes = 0;
  GEN modpoly, plist;
  modpoly_disc_info Ds[MODPOLY_MAX_DCNT];

  long lvl = inv_level(inv);
  if (cgcd(L, lvl) != 1) {
    pari_err_DOMAIN("polmodular0_ZM", "invariant",
                    "incompatible with", stoi(L), stoi(lvl));
  }

  dbg_printf(1)("Calculating modular polynomial of level %lu\n", L);
  if (L <= MAX_INTERNAL_MODPOLY_LEVEL)
    return polmodular_small_ZM(L, inv, db);

  Dcnt = discriminant_with_classno_at_least(Ds, L, inv);
  for (d = 0; d < Dcnt; ++d) nprimes += Ds[d].nprimes;
  modpoly = cgetg(nprimes+1, t_VEC);
  plist = cgetg(nprimes+1, t_VECSMALL);
  k=1;

  for (d = 0; d < Dcnt; ++d) {
    long D, DK, i;
    ulong cond;
    GEN j_powers, factu, hilb;
    norm_eqn_t ne;
    modpoly_disc_info *dinfo = &Ds[d];

    polmodular_db_add_level(db, dinfo->L0, inv);
    if (dinfo->L1)
      polmodular_db_add_level(db, dinfo->L1, inv);

    D = dinfo->D1;
    DK = dinfo->D0;
    cond = sqrt(D / DK);
    factu = factoru(cond);
    dbg_printf(1)("Selected discriminant D = %ld = %ld^2 * %ld.\n",
                  D, cond, DK);

    hilb = polclass0(DK, INV_J, 0, db);
    norm_eqn_init(ne, D, cond);

    if (cond > 1)
      polmodular_db_add_levels(db, gel(factu, 1), INV_J);

    dbg_printf(1)("D = %ld, L0 = %lu, L1 = %lu, ", dinfo->D1, dinfo->L0, dinfo->L1);
    dbg_printf(1)("n1 = %lu, n2 = %lu, dl1 = %lu, dl2_0 = %lu, dl2_1 = %lu\n",
          dinfo->n1, dinfo->n2, dinfo->dl1, dinfo->dl2_0, dinfo->dl2_1);

    j_powers = NULL;
    if (J) {
      compute_derivs = !!compute_derivs;
      j_powers = Fp_powers(J, L + 1, Q);
    }

    for (i = 0; i < dinfo->nprimes; ++i, k++) {
      pari_sp av = avma;
      ulong p = dinfo->primes[i];
      ulong t = dinfo->traces[i];
      GEN modpoly_modp;

      norm_eqn_update(ne, t, p, L);

      av = avma;
      modpoly_modp = polmodular_split_p_Flm(L, hilb, factu, ne, *db, dinfo);
      if (J) {
        modpoly_modp = eval_modpoly_modp(modpoly_modp, j_powers, ne, compute_derivs);
        modpoly_modp = gerepileupto(av, modpoly_modp);
      }
      gel(modpoly, k) = modpoly_modp;
      plist[k] = p;
    }
    modpoly_disc_info_clear(dinfo);
  }
  modpoly = nmV_chinese_center(modpoly, plist, NULL);
  if (J)
    return gerepileupto(ltop, FpM_red(modpoly, Q));
  return gerepileupto(ltop, modpoly);
}


GEN
polmodular_ZM(long L, long inv)
{
  GEN db, Phi;

  if (L < 2)
    pari_err_DOMAIN("polmodular_ZM", "L", "<", gen_2, stoi(L));

  /* TODO: Handle non-prime L.  This is Algorithm 1.1 and Corollary
   * 3.4 in Sutherland, "Class polynomials for nonholomorphic modular
   * functions". */
  if ( ! uisprime(L))
    pari_err_IMPL("composite level");

  db = polmodular_db_init(inv);
  Phi = polmodular0_ZM(L, inv, 0, 0, 0, &db);
  gunclone_deep(db);

  return Phi;
}


GEN
polmodular_ZXX(long L, long inv, long vx, long vy)
{
  pari_sp av = avma;
  GEN phi = polmodular_ZM(L, inv);

  if (vx < 0) vx = 0;
  if (vy < 0) vy = 1;
  if (varncmp(vx, vy) >= 0)
    pari_err_PRIORITY("polmodular_ZXX", pol_x(vx), "<=", vy);

  return gerepilecopy(av, RgM_to_RgXX(phi, vx, vy));
}

INLINE GEN
FpV_deriv(GEN v, long deg, GEN P)
{
  long i, ln = lg(v);
  GEN dv = cgetg(ln, t_VEC);
  for (i = ln - 1; i > 1; --i, --deg)
    gel(dv, i) = Fp_mulu(gel(v, i - 1), deg, P);
  gel(dv, 1) = gen_0;
  return dv;
}

GEN
Fp_polmodular_evalx(
  long L, long inv, GEN J, GEN P, long v, int compute_derivs)
{
  pari_sp av = avma;
  GEN db, phi;

  if (L <= MAX_INTERNAL_MODPOLY_LEVEL) {
    GEN tmp;
    GEN phi = RgM_to_FpM(polmodular_ZM(L, inv), P);
    GEN j_powers = Fp_powers(J, L + 1, P);
    GEN modpol = RgV_to_RgX(FpM_FpC_mul(phi, j_powers, P), v);
    if (compute_derivs) {
      tmp = cgetg(4, t_VEC);
      gel(tmp, 1) = modpol;
      j_powers = FpV_deriv(j_powers, L + 1, P);
      gel(tmp, 2) = RgV_to_RgX(FpM_FpC_mul(phi, j_powers, P), v);
      j_powers = FpV_deriv(j_powers, L + 1, P);
      gel(tmp, 3) = RgV_to_RgX(FpM_FpC_mul(phi, j_powers, P), v);
    } else {
      tmp = modpol;
    }
    return gerepilecopy(av, tmp);
  }

  db = polmodular_db_init(inv);
  phi = polmodular0_ZM(L, inv, J, P, compute_derivs, &db);
  phi = RgM_to_RgXV(phi, v);
  gunclone_deep(db);
  return gerepilecopy(av, compute_derivs ? phi : gel(phi, 1));
}

GEN
polmodular(long L, long inv, GEN x, long v, long compute_derivs)
{
  pari_sp av = avma;
  long tx;
  GEN J = NULL, P = NULL, res = NULL, one = NULL;

  if ( ! x || gequalX(x)) {
    long xv = 0;
    if (x)
      xv = varn(x);
    if (compute_derivs)
      pari_err_FLAG("polmodular");
    return polmodular_ZXX(L, inv, xv, v);
  }

  tx = typ(x);
  if (tx == t_INTMOD) {
    J = gel(x, 2);
    P = gel(x, 1);
    one = mkintmod(gen_1, P);
  } else if (tx == t_FFELT) {
    J = FF_to_FpXQ_i(x);
    if (degpol(J) > 0)
      pari_err_DOMAIN("polmodular", "x", "not in prime subfield ", gen_0, x);
    J = constant_term(J);
    P = FF_p_i(x);
    one = p_to_FF(P, 0);
  } else {
    pari_err_TYPE("polmodular", x);
  }

  if (v < 0) v = 1;
  res = Fp_polmodular_evalx(L, inv, J, P, v, compute_derivs);
  res = gmul(res, one);
  return gerepileupto(av, res);
}

/**
 * SECTION: Modular polynomials of level <= MAX_INTERNAL_MODPOLY_LEVEL.
 */

/*
 * These functions return a vector of unique coefficients of classical
 * modular polynomials \Phi_L(X, Y) of small level L.  The number of
 * such coefficients is (L + 1)(L + 2)/2 since \Phi is symmetric.
 * (Note that we omit the (common) coefficient of X^{L + 1} and Y^{L +
 * 1} since it is always 1.)  See sympol_to_ZM() for how to interpret
 * the coefficients, and use that function to get the corresponding
 * full (desymmetrised) matrix of coefficients.
 */

/*
 *  Phi2, the modular polynomial of level 2:
 *
 *  X^3
 *  + X^2 * (-Y^2 + 1488*Y - 162000)
 *  + X * (1488*Y^2 + 40773375*Y + 8748000000)
 *  + Y^3 - 162000*Y^2 + 8748000000*Y - 157464000000000
 *
 *  [[3, 0, 1],
 *   [2, 2, -1],
 *   [2, 1, 1488],
 *   [2, 0, -162000],
 *   [1, 1, 40773375],
 *   [1, 0, 8748000000],
 *   [0, 0, -157464000000000]],
 */

static GEN
phi2_ZV(void)
{
  GEN phi2 = cgetg(7, t_VEC);
  gel(phi2, 1) = uu32toi(36662, 1908994048);
  setsigne(gel(phi2, 1), -1);
  gel(phi2, 2) = uu32toi(2, 158065408);
  gel(phi2, 3) = stoi(40773375);
  gel(phi2, 4) = stoi(-162000);
  gel(phi2, 5) = stoi(1488);
  gel(phi2, 6) = gen_m1;
  return phi2;
}


/*
 * L = 3
 *
 * [4, 0, 1],
 * [3, 3, -1],
 * [3, 2, 2232],
 * [3, 1, -1069956],
 * [3, 0, 36864000],
 * [2, 2, 2587918086],
 * [2, 1, 8900222976000],
 * [2, 0, 452984832000000],
 * [1, 1, -770845966336000000],
 * [1, 0, 1855425871872000000000]
 * [0, 0, 0]
 *
 * X^4
 * + X^3 (-Y^3 + 2232*Y^2 - 1069956*Y + 36864000)
 * + X^2 (2232*Y^3 + 2587918086*Y^2 + 8900222976000*Y + 452984832000000)
 * + X (-1069956*Y^3 + 8900222976000*Y^2 - 770845966336000000*Y + 1855425871872000000000)
 * + Y^4 + 36864000*Y^3 + 452984832000000*Y^2 + 1855425871872000000000*Y
 *
 * 1855425871872000000000 == 2^32 * (100 * 2^32 + 2503270400)
 */
static GEN
phi3_ZV(void)
{
  GEN phi3 = cgetg(11, t_VEC);
  pari_sp av = avma;
  gel(phi3, 1) = gen_0;
  gel(phi3, 2) = gerepileupto(av, shifti(uu32toi(100, 2503270400UL), 32));
  gel(phi3, 3) = uu32toi(179476562, 2147483648UL);
  setsigne(gel(phi3, 3), -1);
  gel(phi3, 4) = uu32toi(105468, 3221225472UL);
  gel(phi3, 5) = uu32toi(2072, 1050738688);
  gel(phi3, 6) = utoi(2587918086UL);
  gel(phi3, 7) = stoi(36864000);
  gel(phi3, 8) = stoi(-1069956);
  gel(phi3, 9) = stoi(2232);
  gel(phi3, 10) = gen_m1;
  return phi3;
}


static GEN
phi5_ZV(void)
{
  GEN phi5 = cgetg(22, t_VEC);
  gel(phi5, 1) = mkintn(5, 0x18c2cc9cUL, 0x484382b2UL, 0xdc000000UL, 0x0UL, 0x0UL);
  gel(phi5, 2) = mkintn(5, 0x2638fUL, 0x2ff02690UL, 0x68026000UL, 0x0UL, 0x0UL);
  gel(phi5, 3) = mkintn(5, 0x308UL, 0xac9d9a4UL, 0xe0fdab12UL, 0xc0000000UL, 0x0UL);
  setsigne(gel(phi5, 3), -1);
  gel(phi5, 4) = mkintn(5, 0x13UL, 0xaae09f9dUL, 0x1b5ef872UL, 0x30000000UL, 0x0UL);
  gel(phi5, 5) = mkintn(4, 0x1b802fa9UL, 0x77ba0653UL, 0xd2f78000UL, 0x0UL);
  gel(phi5, 6) = mkintn(4, 0xfbfdUL, 0x278e4756UL, 0xdf08a7c4UL, 0x40000000UL);
  gel(phi5, 7) = mkintn(4, 0x35f922UL, 0x62ccea6fUL, 0x153d0000UL, 0x0UL);
  gel(phi5, 8) = mkintn(4, 0x97dUL, 0x29203fafUL, 0xc3036909UL, 0x80000000UL);
  setsigne(gel(phi5, 8), -1);
  gel(phi5, 9) = mkintn(3, 0x56e9e892UL, 0xd7781867UL, 0xf2ea0000UL);
  gel(phi5, 10) = mkintn(3, 0x5d6dUL, 0xe0a58f4eUL, 0x9ee68c14UL);
  setsigne(gel(phi5, 10), -1);
  gel(phi5, 11) = mkintn(3, 0x1100dUL, 0x85cea769UL, 0x40000000UL);
  gel(phi5, 12) = mkintn(3, 0x1b38UL, 0x43cf461fUL, 0x3a900000UL);
  gel(phi5, 13) = mkintn(3, 0x14UL, 0xc45a616eUL, 0x4801680fUL);
  gel(phi5, 14) = uu32toi(0x17f4350UL, 0x493ca3e0UL);
  gel(phi5, 15) = uu32toi(0x183UL, 0xe54ce1f8UL);
  gel(phi5, 16) = uu32toi(0x1c9UL, 0x18860000UL);
  gel(phi5, 17) = uu32toi(0x39UL, 0x6f7a2206UL);
  setsigne(gel(phi5, 17), -1);
  gel(phi5, 18) = stoi(2028551200);
  gel(phi5, 19) = stoi(-4550940);
  gel(phi5, 20) = stoi(3720);
  gel(phi5, 21) = gen_m1;
  return phi5;
}

static GEN
phi5_f_ZV(void)
{
  GEN phi5_f = const_vec(22, gen_0);
  gel(phi5_f, 3) = stoi(4);
  gel(phi5_f, 21) = gen_m1;
  return phi5_f;
}

typedef GEN (*phi_fn)(void);

static GEN
bad_level(void)
{
  return (GEN)0;
}

static const phi_fn INTERNAL_MODPOLY_DB[6][3] = {
  {   phi2_ZV,   phi3_ZV,   phi5_ZV }, /* INV_J */
  { bad_level, bad_level, phi5_f_ZV }, /* INV_F */
  { bad_level, bad_level,         0 }, /* INV_F2 */
  { bad_level, bad_level,         0 }, /* INV_F3 */
  { bad_level, bad_level,         0 }, /* INV_F4 */
  {         0, bad_level,         0 }  /* INV_G2 */
};

static GEN
polmodular_small_ZM(long L, long inv, GEN *db)
{
  pari_sp av = avma;
  phi_fn f = NULL;
  GEN mp = NULL;

  switch (L) {
  case 2:
    f = INTERNAL_MODPOLY_DB[inv][0]; break;
  case 3:
    f = INTERNAL_MODPOLY_DB[inv][1]; break;
  case 5:
    f = INTERNAL_MODPOLY_DB[inv][2]; break;
  default:
    pari_err_BUG("polmodular_small_ZM");
  }

  if (f == bad_level) {
    pari_err_BUG("polmodular_small_ZM");
  } else if (f == 0) {
    mp = polmodular0_generic_ZM(L, inv, db);
  } else {
    mp = sympol_to_ZM(f(), L);
  }

  return gerepilecopy(av, mp);
}


/**
 * SECTION: Select discriminant for given modpoly level.
 */

/* require an L1, useful for multi-threading */
#define MODPOLY_USE_L1    1
/* no bound on L1 other than the fixed bound MAX_L1 - needed to
 * handle small L for certain invariants (but not for j) */
#define MODPOLY_NO_MAX_L1 2
/* don't use any auxilliary primes - needed to handle small L for
 * certain invariants (but not for j) */
#define MODPOLY_NO_AUX_L  4

INLINE double
modpoly_height_bound(long L, long inv)
{
  double nbits, nbits2;
  double c;
  int hf;

  /* proven bound (in bits), derived from: 6l*log(l)+16*l+13*sqrt(l)*log(l) */
  nbits = 6.0*L*log2(L)+16/LOG2*L+8.0*sqrt(L)*log2(L);
  /* alternative proven bound (in bits), derived from: 6l*log(l)+17*l */
  nbits2 = 6.0*L*log2(L)+17/LOG2*L;
  if ( nbits2 < nbits ) nbits = nbits2;
  hf = inv_height_factor(inv);
  if (hf > 1.0) {
    /*
   *** Important *** when dividing by the height factor, we only want to reduce terms related
   to the bound on j (the roots of Phi_l(X,y)), not terms arising from binomial coefficients.
   These arise in lemmas 2 and 3 of the height bound paper, terms of (log 2)*L and 2.085*(L+1)
   which we convert here to binary logs.
    */
    /* this is a massive overestimate, if you care about speed,
     * determine a good height bound empirically as done for INV_F
     * below */
    nbits2 = nbits - 4.01*L -3.0;
    nbits = nbits2/hf + 4.01*L + 3.0;
  }

  if (inv == INV_F) {
    if (L < 30) c = 45;
    else if (L < 100) c = 36;
    else if (L < 300) c = 32;
    else if (L < 600) c = 26;
    else if (L < 1200) c = 24;
    else if (L < 2400) c = 22;
    else c = 20;
    nbits = (6.0*L*log2(L) + c*L)/hf;
  }

  return nbits;
}

/* small enough so we can write the factorization of a smooth in a BIL
 * bit integer */
#define SMOOTH_PRIMES  ((BITS_IN_LONG >> 1) - 1)


#define MAX_ATKIN 255

/* Must have primes at least up to MAX_ATKIN */
static const long PRIMES[] = {
    0,   2,   3,   5,   7,  11,  13,  17,  19,  23,
   29,  31,  37,  41,  43,  47,  53,  59,  61,  67,
   71,  73,  79,  83,  89,  97, 101, 103, 107, 109,
  113, 127, 131, 137, 139, 149, 151, 157, 163, 167,
  173, 179, 181, 191, 193, 197, 199, 211, 223, 227,
  229, 233, 239, 241, 251, 257, 263, 269, 271, 277
};

#define MAX_L1      255

typedef struct {
  ulong m;
  long D, h;
} D_entry;

/* Returns a form that generates the classes of norm p^2 in cl(p^2D)
 * (i.e. one with order p-1), where p is an odd prime that splits in D
 * and does not divide its conductor (but this is not verified) */
INLINE GEN
qform_primeform2(long p, long D)
{
  pari_sp ltop = avma, av;
  GEN M;
  register long k;

  M = factor_pn_1(stoi(p), 1);
  av = avma;
  for (k = D & 1; k <= p; k += 2)
  {
    GEN Q;
    long ord, a, b, c = (k * k - D) / 4;

    if (!(c % p)) continue;
    a = p * p;
    b = k * p;
    Q = redimag(mkqfis(a, b, c));
    /* TODO: How do we know that Q has order dividing p - 1? If we
     * don't, then the call to gen_order should be replaced with a
     * call to something with fastorder semantics (i.e. return 0 if
     * ord(Q) \ndiv M). */
    ord = itos(qfi_order(Q, M));
    if (ord == p - 1) {
      /* TODO: This check that gen_order returned the correct result
       * should be removed when gen_order is replaced with something
       * with fastorder semantics. */
      GEN tst = gpowgs(Q, p - 1);
      if (qfi_equal1(tst)) { avma = ltop; return mkqfis(a, b, c); }
        break;
    }
    avma = av;
  }
  avma = ltop; return NULL;
}

#define divides(a,b) (!((b) % (a)))

/* This gets around the fact that gen_PH_log returns garbage if g
 * doesn't have order n. */
INLINE GEN
discrete_log(GEN a, GEN g, long n)
{
  return qfi_Shanks(a, g, n);
}


/*
 * Output x such that [L0]^x = [L] in cl(D) where n = #cl(D).  Return
 * value indicates whether x was found or not.
 */
INLINE long
primeform_discrete_log(long *x, long L0, long L, long n, long D)
{
  GEN X, Q, R, DD;
  pari_sp av = avma;
  long res = 0;

  DD = stoi(D);
  Q = redimag(primeform_u(DD, L0));
  R = redimag(primeform_u(DD, L));
  X = discrete_log(R, Q, n);
  if (X) {
    *x = itos(X);
    res = 1;
  }
  avma = av;
  return res;
}


/*
 * Return the norm of a class group generator appropriate for a
 * discriminant that will be used to calculate the modular polynomial
 * of level L and invariant inv.  Don't consider norms less than
 * initial_L0.
 */
static long
select_L0(long L, long inv, long initial_L0)
{
  long inv_N;
  long L0 = unextprime(initial_L0 + 1);

  inv_N = inv_level(inv);
  if (divides(L, inv_N))
    pari_err_BUG("select_L0");

  /* inv_level(INV_F3) = 2, but L0=3 does not work properly for
   * INV_F3, so pick L0 = 5. */
  if (inv == INV_F3)
    return 5;

  /* I've no idea why 5 doesn't work for 19 and 29, nor why 7 and 11
   * don't work for 19 either. */
  if (inv == INV_F) {
    if (L == 19)
      return 13;
    else if (L == 29)
      return 7;
    return 5;
  }

  /* L0 is the smallest small prime different from L that doesn't divide inv_N. */
  for ( ; L0 == L || divides(L0, inv_N); L0 = unextprime(L0 + 1))
    ;
  return L0;
}


/*
 * Return the order of [L]^n in cl(D), where #cl(D) = ord.
 */
INLINE long
primeform_exp_order(long L, long n, long D, long ord)
{
  pari_sp av = avma;
  GEN Q = gpowgs(primeform_u(stoi(D), L), n);
  long m = itos(qfi_order(Q, Z_factor(stoi(ord))));
  avma = av;
  return m;
}

INLINE long
eql_elt(GEN P, GEN Q, long i)
{
  return gequal(gel(P, i), gel(Q, i));
}

/* If an ideal of norm inv_deg is equivalent to an ideal of
 * norm L0, we have an orientation ambiguity that we need to
 * avoid. Note that we need to check all the possibilities (up
 * to 8), but we can cheaply check inverses (so at most 2) */
static long
orientation_ambiguity(long D1, long L0, long inv_p1, long inv_p2, long inv_N)
{
  pari_sp av = avma;
  long ambiguity = 0;
  GEN D = stoi(D1);
  GEN Q1 = primeform_u(D, inv_p1), Q2 = NULL;

  if (inv_p2 > 1) {
    if (inv_p1 != inv_p2) {
      GEN P2 = primeform_u(D, inv_p2);
      GEN Q = gsqr(P2);
      GEN R = gsqr(Q1);
      /* check that p1^2 != p2^{+/-2}, since this leads to
       * ambiguities when converting j's to f's */
      if (eql_elt(Q, R, 1)
          && (eql_elt(Q, R, 2) || gequal(gel(Q, 2), gneg(gel(R, 2))))) {
        dbg_printf(3)("Bad D=%ld, a^2=b^2 problem between inv_p1=%ld and inv_p2=%ld\n",
                      D1, inv_p1, inv_p2);
        ambiguity = 1;
      } else {
        /* generate both p1*p2 and p1*p2^{-1} */
        Q2 = gmul(Q1, P2);
        P2 = ginv(P2);
        Q1 = gmul(Q1, P2);
      }
    } else {
      Q1 = gsqr(Q1);
    }
  }
  if ( ! ambiguity) {
    GEN P = gsqr(primeform_u(D, L0));
    if (eql_elt(P, Q1, 1)
        || (inv_p2 && inv_p1 != inv_p2 && eql_elt(P, Q2, 1))) {
      dbg_printf(3)("Bad D=%ld, a=b^{+/-2} problem between inv_N=%ld and L0=%ld\n",
                    D1, inv_N, L0);
      ambiguity = 1;
    }
  }
  avma = av;
  return ambiguity;
}

static long
check_generators(
  long *n1_, long *m_,
  long D, long h, long n, long subgrp_sz, long L0, long L1)
{
  long n1, m = primeform_exp_order(L0, n, D, h);
  if (m_)
    *m_ = m;
  n1 = n * m;
  if ( ! n1)
    pari_err_BUG("check_generators");
  *n1_ = n1;
  if (n1 < subgrp_sz/2 || ( ! L1 && n1 < subgrp_sz))  {
    dbg_printf(3)("Bad D1=%ld with n1=%ld, h1=%ld, L1=%ld: "
                  "L0 and L1 don't span subgroup of size d in cl(D1)\n",
                  D, n, h, L1);
    return 0;
  }
  if (n1 < subgrp_sz && ! (n1 & 1)) {
    int res;
    /* check whether L1 is generated by L0, using the fact that it has order 2 */
    pari_sp av = avma;
    GEN D1 = stoi(D);
    GEN Q = gpowgs(primeform_u(D1, L0), n1 / 2);
    res = gequal(Q, redimag(primeform_u(D1, L1)));
    avma = av;
    if (res) {
      dbg_printf(3)("Bad D1=%ld, with n1=%ld, h1=%ld, L1=%ld: "
                    "L1 generated by L0 in cl(D1)\n", D, n, h, L1);
      return 0;
    }
  }
  return 1;
}

#define MAX_VOLCANO_FLOOR_SIZE 100000000

static long
calc_primes_for_discriminants(modpoly_disc_info Ds[], long Dcnt, long L, long minbits)
{
  pari_sp av = avma;
  long i, j, k, m, n, D1, pcnt, totbits;
  ulong *primes, *Dprimes, *Dtraces;

  /* D1 is the discriminant with smallest absolute value among those we found */
  D1 = Ds[0].D1;
  for (i = 1; i < Dcnt; i++) {
    if (Ds[i].D1 > D1)
      D1 = Ds[i].D1;
  }

  /* n is an upper bound on the number of primes we might get. */
  n = ceil(minbits / (log2(L * L * (-D1)) - 2)) + 1;
  primes = (ulong *) stack_malloc(n * sizeof(*primes));
  Dprimes = (ulong *) stack_malloc(n * sizeof(*Dprimes));
  Dtraces = (ulong *) stack_malloc(n * sizeof(*Dtraces));
  for (i = 0, totbits = 0, pcnt = 0; i < Dcnt && totbits < minbits; i++) {
    Ds[i].nprimes = modpoly_pickD_primes(Dprimes, Dtraces, n, primes, pcnt,
                                         &Ds[i].bits, minbits - totbits, Ds + i);
    Ds[i].primes = (ulong *) newblock(Ds[i].nprimes);
    memcpy(Ds[i].primes, Dprimes, Ds[i].nprimes * sizeof(*Dprimes));

    Ds[i].traces = (ulong *) newblock(Ds[i].nprimes);
    memcpy(Ds[i].traces, Dtraces, Ds[i].nprimes * sizeof(*Dtraces));

    totbits += Ds[i].bits;
    pcnt += Ds[i].nprimes;

    if (totbits >= minbits || i == Dcnt - 1) {
      Dcnt = i + 1;
      break;
    }
    /* merge lists */
    for (j = pcnt - Ds[i].nprimes - 1, k = Ds[i].nprimes - 1, m = pcnt - 1; m >= 0; m--) {
      if (k >= 0) {
        if (j >= 0 && primes[j] > Dprimes[k])
          primes[m] = primes[j--];
        else
          primes[m] = Dprimes[k--];
      } else {
        primes[m] = primes[j--];
      }
    }
  }
  if (totbits < minbits) {
    dbg_printf(1)("Only obtained %ld of %ld bits using %ld discriminants\n",
                  totbits, minbits, Dcnt);
    Dcnt = 0;
  }
  avma = av;
  return Dcnt;
}

/*
 * Select discriminant(s) to use when calculating the modular
 * polynomial of level L and invariant inv.
 *
 * INPUT:
 * - L: level of modular polynomial (must be odd)
 * - inv: invariant of modular polynomial
 * - L0: result of select_L0(L, inv)
 * - minbits: height of modular polynomial
 * - flags: see below
 * - tab: result of scanD0(L0)
 * - tablen: length of tab
 *
 * OUTPUT:
 * - Ds: the selected discriminant(s)
 *
 * RETURN:
 * - the number of Ds found
 *
 * The flags parameter is constructed by ORing zero or more of the
 * following values:
 * - MODPOLY_USE_L1: force use of second class group generator
 * - MODPOLY_NO_AUX_L: don't use auxillary class group elements
 */
static long
modpoly_pickD(
  modpoly_disc_info Ds[MODPOLY_MAX_DCNT], long L, long inv, long L0, long max_L1, long minbits, long flags,
  D_entry *tab, long tablen)
{
  pari_sp ltop = avma, btop;
  D_entry D0_entry;
  modpoly_disc_info Dinfo;
  pari_timer T;
  long p, q, L1;
  long tmp, inv_p1, inv_p2;
  long inv_N, inv_deg, deg, use_L1, twofactor, pfilter, Dcnt;
  long how_many_D0s = 0;
  double D0_bits, p_bits, L_bits;
  long D0, D1, D2, m, h0, h1, h2, n0, n1, n2, dl1, dl2[2], d, cost, enum_cost, H_cost, best_cost, totbits;
  register long i, j, k;

  if ( !(L & 1))
    pari_err_BUG("modpoly_pickD");

  timer_start(&T);
  d = inv_sparse_factor(inv);
  /*d = ui_ceil_ratio(L + 1, d) + 1; */
  tmp = (L + 1) / d;
  d = ((tmp * d < (L + 1)) ? tmp + 1 : tmp);
  d += 1;
  inv_N = inv_level(inv);
  inv_deg = inv_degree(&inv_p1, &inv_p2, inv);
  pfilter = inv_pfilter(inv);

  /* Now set level to 0 unless we will need to compute N-isogenies */
  dbg_printf(1)("Using L0=%ld for L=%ld, d=%ld, inv_N=%ld, inv_deg=%ld\n",
                L0, L, d, inv_N, inv_deg);

  /* We use L1 if (L0|L) == 1 or if we are forced to by flags. */
  use_L1 = (kross(L0,L) > 0 || (flags & MODPOLY_USE_L1));

  Dcnt = 0;
  best_cost = 0;
  L_bits = log2(L);
  dbg_printf(3)("use_L1=%ld\n", use_L1);
  dbg_printf(3)("minbits = %ld\n", minbits);

  totbits = 0;

  /* Iterate over the fundamental discriminants for L0 */
  while (how_many_D0s < tablen) {
    D0_entry = tab[how_many_D0s];
    how_many_D0s++;
    /* extract D0 from D0_entry */
    D0 = D0_entry.D;

    if ( ! inv_good_discriminant(D0, inv))
      continue;
    /* extract class poly degree from D0_entry */
    deg = D0_entry.h;

    /* compute class number */
    h0 = ((D0_entry.m & 2) ? 2*deg : deg);
    dbg_printf(3)("D0=%ld\n", D0);

    /* don't allow either inv_p1 or inv_p2 to ramify */
    if (kross(D0, L) < 1
        || (inv_p1 > 1 && kross(D0, inv_p1) < 1)
        || (inv_p2 > 1 && kross(D0, inv_p2) < 1)) {
      dbg_printf(3)("Bad D0=%ld due to non-split L or ramified level\n", D0);
      continue;
    }

    /* (D0_entry.m & 1) is 1 if ord(L0) < h0, is 0 if ord(L0) == h0.
     * Hence (D0_entry.m & 1) + 1 is 2 if ord(L0) < h0 (hence ==
     * h0/2) and is 1 if ord(L0) == h0.  Hence n0 = ord(L0). */
    n0 = h0/((D0_entry.m & 1) + 1);

    /* Look for L1: for each smooth prime p */
    for (i = 1 ; i <= SMOOTH_PRIMES; i++) {
      /* If 1 + (D0 | p) == 1, i.e. if (D0 | p) == 0, i.e. if p | D0. */
      if (((D0_entry.m >> (2*i)) & 3) == 1) {
        /* set L1 = p if it's not L0, it's less than the maximum,
         * it doesn't divide inv_N, and (L1 | L) == -1. */
        /* XXX: Why do we want (L1 | L) == -1?  Presumably so (L^2 v^2 D0 | L1) == -1? */
        L1 = PRIMES[i];
        if (L1 != L0 && L1 <= max_L1 && (inv_N % L1) && kross(L1, L) < 0)
          break;
      }
    }
    /* Didn't find suitable L1... */
    if (i > SMOOTH_PRIMES) {
      if (n0 < h0 || use_L1) {
        /* ...though we needed one. */
        dbg_printf(3)("Bad D0=%ld because there is no good L1\n", D0);
        continue;
      }
      L1 = 0;
    }
    dbg_printf(3)("Good D0=%ld with L1=%ld, n0=%ld, h0=%ld, d=%ld\n",
                  D0, L1, n0, h0, d);

    /* We're finished if we have sufficiently many discriminants that satisfy
     * the cost requirement */
    if (totbits > minbits && best_cost && h0*(L-1) > 3*best_cost)
      break;

    D0_bits = log2(-D0);
    /* If L^2 D0 is too big to fit in a BIL bit integer, skip D0. */
    if (D0_bits + 2 * L_bits > (BITS_IN_LONG - 1))
      continue;

    /* m is the order of L0^n0 in L^2 D0? */
    m = primeform_exp_order(L0, n0, L * L * D0, n0 * (L - 1));
    if ( m < (L - 1)/2 ) {
      dbg_printf(3)("Bad D0=%ld because %ld is less than (L-1)/2=%ld\n",
                    D0, m, (L - 1)/2);
      continue;
    }
    /* Heuristic.  Doesn't end up contributing much. */
    H_cost = 2 * deg * deg;

    /* 7 = 2^3 - 1 = 0b111, so D0 & 7 == D0 (mod 8).
     * 0xc = 0b1100, so D0_entry.m & 0xc == 1 + (D0 | 2).
     * Altogether, we get:
     * if D0 = 5 (mod 8), then
     *   if (D0 | 2) == -1, twofactor = 3
     *   otherwise (i.e. (D0 | 2) == 0 or 1), twofactor = 1
     * otherwise
     *   twofactor is 0 */
    if ((D0 & 7) == 5)
      twofactor = ((D0_entry.m & 0xc) ? 1 : 3);
    else
      twofactor = 0;

    btop = avma;
    /* For each small prime... */
    for (i = 0; i <= SMOOTH_PRIMES; i++) {
      avma = btop;
      /* i = 0 corresponds to 1, which we do not want to skip! (i.e. DK = D) */
      if (i) {
        if (inv_odd_conductor(inv) && i == 1)
          continue;
        p = PRIMES[i];
        /* Don't allow large factors in the conductor. */
        if (p > max_L1)
          break;
        if (p == L0 || p == L1 || p == L || p == inv_p1 || p == inv_p2)
          continue;
        p_bits = log2(p);
        /* h1 is the class number of D1 = q^2 D0, where q = p^j (j defined in the loop below) */
        h1 = h0 * (p - ((D0_entry.m >> (2*i)) & 0x3) + 1);
        /* q is the smallest power of p such that h1 >= d ~ "L + 1". */
        for (j = 1, q = p; h1 < d; j++, q *= p, h1 *= p)
          ;
        D1 = q * q * D0;
        /* can't have D1 = 0 mod 16 and hope to get any primes congruent to 3 mod 4 */
        if ((pfilter & IQ_FILTER_1MOD4) && !(D1 & 0xF))
          continue;
      } else {
        /* i = 0, corresponds to "p = 1". */
        h1 = h0;
        D1 = D0;
        p = q = j = 1;
        p_bits = 0;
      }
      /* include a factor of 4 if D1 is 5 mod 8 */
      /* XXX: No idea why he does this. */
      if (twofactor && (q & 1)) {
        if (inv_odd_conductor(inv))
          continue;
        D1 *= 4;
        h1 *= twofactor;
      }
      /* heuristic early abort -- we may miss some good D1's, but this saves a *lot* of time */
      if (totbits > minbits && best_cost && h1*(L-1) > 2.2*best_cost)
        continue;

      /* log2(D0 * (p^j)^2 * L^2 * twofactor) > (BIL - 1) -- i.e. params too big. */
      if (D0_bits + 2*j*p_bits + 2*L_bits + (twofactor && (q & 1) ? 2.0 : 0.0) > (BITS_IN_LONG - 1))
        continue;

      if ( ! check_generators(&n1, 0, D1, h1, n0, d, L0, L1))
        continue;

      if (n1 < h1) {
        if ( ! primeform_discrete_log(&dl1, L0, L, n1, D1))
          continue;
      } else {
        dl1 = -1;   /* fill it in later, no point in wasting the effort right now */
      }
      dbg_printf(3)("Good D0=%ld, D1=%ld with q=%ld, L1=%ld, n1=%ld, h1=%ld\n",
                    D0, D1, q, L1, n1, h1);
      if (inv_deg && orientation_ambiguity(D1, L0, inv_p1, inv_p2, inv_N))
        continue;

      D2 = L * L * D1;
      h2 = h1 * (L-1);
      /* m is the order of L0^n1 in cl(D2) */
      if ( ! check_generators(&n2, &m, D2, h2, n1, d*(L - 1), L0, L1))
        continue;

      /* This restriction on m is not strictly necessary, but simplifies life later. */
      if (m < (L-1)/2 || (!L1 && m < L-1) ) {
        dbg_printf(3)("Bad D2=%ld for D1=%ld, D0=%ld, with n2=%ld, h2=%ld, L1=%ld, "
                      "order of L0^n1 in cl(D2) is too small\n", D2, D1, D0, n2, h2, L1);
        continue;
      }
      dl2[0] = n1;
      dl2[1] = 0;
      if (m < L - 1) {
        GEN Q1 = qform_primeform2(L, D1), Q2, X;
        if ( ! Q1)
          pari_err_BUG("modpoly_pickD");
        Q2 = primeform_u(stoi(D2), L1);
        Q2 = gmul(Q1, Q2); /* we know this element has order L-1 */
        Q1 = primeform_u(stoi(D2), L0);
        k = ((n2 & 1) ? 2*n2 : n2)/(L-1);
        Q1 = gpowgs(Q1, k);
        X = discrete_log(Q2, Q1, L - 1);
        if ( ! X) {
          dbg_printf(3)("Bad D2=%ld for D1=%ld, D0=%ld, with n2=%ld, h2=%ld, L1=%ld, "
              "form of norm L^2 not generated by L0 and L1\n",
              D2, D1, D0, n2, h2, L1);
          continue;
        }
        dl2[0] = itos(X) * k;
        dl2[1] = 1;
      }
      if ( ! (m < L-1 || n2 < d*(L-1)) && n1 >= d && ! use_L1)
        L1 = 0;  /* we don't need L1 */

      if ( ! L1 && use_L1) {
        dbg_printf(3)("not using D2=%ld for D1=%ld, D0=%ld, with n2=%ld, h2=%ld, L1=%ld, "
                   "because we don't need L1 but must use it\n",
                   D2, D1, D0, n2, h2, L1);
        continue;
      }
      /* don't allow zero dl2[1] with L1 for the moment, since
       * modpoly doesn't handle it - we may change this in the future */
      if (L1 && ! dl2[1])
        continue;
      dbg_printf(3)("Good D0=%ld, D1=%ld, D2=%ld with s=%ld^%ld, L1=%ld, dl2=%ld, n2=%ld, h2=%ld\n",
                 D0, D1, D2, p, j, L1, dl2[0], n2, h2);

      /* This is estimate is heuristic and fiddling with the
       * parameters 5 and 0.25 can change things quite a bit. */
      enum_cost = n2 * (5 * L0 * L0 + 0.25 * L1 * L1);
      cost = enum_cost + H_cost;
      if (best_cost && cost > 2.2*best_cost)
        break;
      if (best_cost && cost >= 0.99*best_cost)
        continue;

      Dinfo.L = L;
      Dinfo.D0 = D0;
      Dinfo.D1 = D1;
      Dinfo.L0 = L0;
      Dinfo.L1 = L1;
      Dinfo.n1 = n1;
      Dinfo.n2 = n2;
      Dinfo.dl1 = dl1;
      Dinfo.dl2_0 = dl2[0];
      Dinfo.dl2_1 = dl2[1];
      Dinfo.cost = cost;
      Dinfo.inv = inv;

      if ( ! modpoly_pickD_primes (0, 0, 0, 0, 0, &Dinfo.bits, minbits, &Dinfo))
        continue;
      dbg_printf(2)("Best D2=%ld, D1=%ld, D0=%ld with s=%ld^%ld, L1=%ld, "
                 "n1=%ld, n2=%ld, cost ratio %.2f, bits=%ld\n",
                 D2, D1, D0, p, j, L1, n1, n2,
                 (double)cost/(d*(L-1)), Dinfo.bits);
      /* Insert Dinfo into the Ds array.  Ds is sorted by ascending cost. */
      for (j = 0; j < Dcnt; j++)
        if (Dinfo.cost < Ds[j].cost)
          break;
      if (n2 > MAX_VOLCANO_FLOOR_SIZE && n2*(L1 ? 2 : 1) > 1.2* (d*(L-1)) ) {
        dbg_printf(3)("Not using D1=%ld, D2=%ld for space reasons\n", D1, D2);
        continue;
      }
      if (j == Dcnt && Dcnt == MODPOLY_MAX_DCNT)
        continue;
      totbits += Dinfo.bits;
      if (Dcnt == MODPOLY_MAX_DCNT)
        totbits -= Ds[Dcnt-1].bits;
      if (n2 > MAX_VOLCANO_FLOOR_SIZE)
        dbg_printf(3)("totbits=%ld, minbits=%ld\n", totbits, minbits);
      if (Dcnt < MODPOLY_MAX_DCNT)
        Dcnt++;
      for (k = Dcnt - 1; k > j; k--)
        Ds[k] = Ds[k - 1];
      Ds[k] = Dinfo;
      if (totbits > minbits)
        best_cost = Ds[Dcnt-1].cost;
      else
        best_cost = 0;
      /* if we were able to use D1 with s = 1, there is no point in
       * using any larger D1 for the same D0 */
      if ( ! i)
        break;
    } /* END FOR over small primes */
  } /* END WHILE over D0's */
  dbg_printf(2)("  checked %ld of %ld fundamental discriminants to find suitable "
                "discriminant (Dcnt = %ld)\n", how_many_D0s, tablen, Dcnt);
  if ( ! Dcnt) {
    dbg_printf(1)("failed completely for L=%ld\n", L);
    return 0;
  }

  Dcnt = calc_primes_for_discriminants(Ds, Dcnt, L, minbits);

  /* fill in any missing dl1's */
  for (i = 0 ; i < Dcnt; i++) {
    if (Ds[i].dl1 < 0) {
      long dl;
      if ( ! primeform_discrete_log(&dl, L0, L, Ds[i].n1, Ds[i].D1))
      {
        pari_err_BUG("modpoly_pickD");
        return -1; /* not reached */
      }
      Ds[i].dl1 = dl;
    }
  }
  if (DEBUGLEVEL > 1) {
    err_printf("Selected %ld discriminants using %ld msecs\n", Dcnt, timer_delay(&T));
    for (i = 0 ; i < Dcnt ; i++) {
      /* TODO: Reuse the calculation from the D_entry */
      GEN H = classno(stoi(Ds[i].D0));
      long h0 = itos(H);
      err_printf ("    D0=%ld, h(D0)=%ld, D=%ld, L0=%ld, L1=%ld, "
          "cost ratio=%.2f, enum ratio=%.2f,",
          Ds[i].D0, h0, Ds[i].D1, Ds[i].L0, Ds[i].L1,
          (double)Ds[i].cost/(d*(L-1)),
          (double)(Ds[i].n2*(Ds[i].L1 ? 2 : 1))/(d*(L-1)));
      err_printf (" %ld primes, %ld bits\n", Ds[i].nprimes, Ds[i].bits);
    }
  }
  avma = ltop;
  return Dcnt;
}

/*
 * Calculate solutions (p, t) to the norm equation
 *
 *   4 p = t^2 - v^2 L^2 D   (*)
 *
 * corresponding to the descriminant described by Dinfo.
 *
 * INPUT:
 * - max: length of primes and traces
 * - xprimes: p to exclude from primes (if they arise)
 * - xcnt: length of xprimes
 * - minbits: sum of log2(p) must be larger than this
 * - Dinfo: discriminant, invariant and L for which we seek solutions
 *   to (*)
 *
 * OUTPUT:
 * - primes: array of p in (*)
 * - traces: array of t in (*)
 * - totbits: sum of log2(p) for p in primes.
 *
 * RETURN:
 * - the number of primes and traces found (these are always the same).
 *
 * NOTE: Any of primes, traces and totbits can be zero, in which case
 * these values are discarded after calculation (however it is not
 * permitted for traces to be zero if primes is non-zero).  xprimes
 * can be zero, in which case it is treated as empty.
 */
static long
modpoly_pickD_primes(
  ulong *primes, ulong *traces, long max, ulong *xprimes, long xcnt,
  long *totbits, long minbits, modpoly_disc_info *Dinfo)
{
  double bits;
  long D, m, n, vcnt, pfilter, one_prime, inv;
  ulong maxp;
  register ulong a1, a2, v, t, p, a1_start, a1_delta, L0, L1, L, absD;
  /* FF_BITS = BITS_IN_LONG - NAIL_BITS (latter is 2 or 7) */
  ulong FF_BITS = BITS_IN_LONG - 2;

  D = Dinfo->D1;
  L0 = Dinfo->L0;
  L1 = Dinfo->L1;
  L = Dinfo->L;
  inv = Dinfo->inv;

  absD = -D;

  /* make sure pfilter and D don't preclude the possibility of p=(t^2-v^2D)/4 being prime */
  pfilter = inv_pfilter(inv);
  if ((pfilter & IQ_FILTER_1MOD3) && ! (D % 3))
    return 0;
  if ((pfilter & IQ_FILTER_1MOD4) && ! (D & 0xF))
    return 0;

  /* Naively estimate the number of primes satisfying 4p=t^2-L^2D
   * with t=2 mod L and pfilter using the PNT this is roughly #{t:
   * t^2 < max p and t=2 mod L} / pi(max p) * filter_density, where
   * filter_density is 1, 2, or 4 depending on pfilter.  If this
   * quantity is already more than twice the number of bits we need,
   * assume that, barring some obstruction, we should have no problem
   * getting enough primes.  In this case we just verify we can get
   * one prime (which should always be true, assumingly we chose D
   * properly). */
  one_prime = 0;
  if (totbits)
    *totbits = 0;
  if (max <= 1 && ! one_prime) {
    p = ((pfilter & IQ_FILTER_1MOD3) ? 2 : 1) * ((pfilter & IQ_FILTER_1MOD4) ? 2 : 1);
    one_prime = (1UL << ((FF_BITS+1)/2)) * (log2(L*L*(-D))-1)
        > p*L*minbits*FF_BITS*LOG2;
    if (one_prime && totbits)
      *totbits = minbits+1;   /* lie */
  }

  m = n = 0;
  bits = 0.0;
  maxp = 0;
  for (v = 1; v < 100 && bits < minbits; v++) {
    /* Don't allow v dividing the conductor. */
    if (ugcd(absD, v) != 1)
      continue;
    /* can't get odd p with D=1 mod 8 unless v is even */
    if ((v & 1) && (D & 7) == 1)
      continue;
    /* don't use v divisible by 4 for L0=2 (we could remove this restriction, for a cost) */
    if (L0 == 2 && !(v & 3))
      continue;
    /* can't get p=3mod4 if v^2D is 0 mod 16 */
    if ((pfilter & IQ_FILTER_1MOD4) && !((v*v*D) & 0xF))
      continue;
    if ((pfilter & IQ_FILTER_1MOD3) && !(v%3) )
      continue;
    /* avoid L0-volcanos with non-zero height */
    if (L0 != 2 && ! (v % L0))
      continue;
    /* ditto for L1 */
    if (L1 && !(v % L1))
      continue;
    vcnt = 0;
    if ((v*v*absD)/4 > (1L<<FF_BITS)/(L*L))
      break;
    if (((v*D) & 1)) {
      a1_start = 1;
      a1_delta = 2;
    } else {
      a1_start = (((v*v*D) & 7) ? 2 : 0 );
      a1_delta = 4;
    }
    for (a1 = a1_start; bits < minbits; a1 += a1_delta) {
      a2 = (a1*a1 + v*v*absD) >> 2;
      if ( !(a2 % L))
        continue;
      t = a1*L + 2;
      p = a2*L*L + t - 1;
      if ( !(p & 1))
        pari_err_BUG("modpoly_pickD_primes");
      /* double check calculation just in case of overflow or other weirdness */
      if (t*t + v*v*L*L*absD != 4*p)
        pari_err_BUG("modpoly_pickD_primes");
      if (p > (1UL<<FF_BITS))
        break;
      if (xprimes) {
        while (m < xcnt && xprimes[m] < p)
          m++;
        if (m < xcnt && p == xprimes[m]) {
          dbg_printf(1)("skipping duplicate prime %ld\n", p);
          continue;
        }
      }
      if ( ! uisprime(p))
        continue;
      if ( ! inv_good_prime(p, inv))
        continue;
      if (primes) {
        /* ulong vLp, vLm; */
        if (n >= max)
          goto done;
        /* TODO: Implement test to filter primes that lead to
         * L-valuation != 2 */
        primes[n] = p;
        traces[n] = t;
      }
      n++;
      vcnt++;
      bits += log2(p);
      if (p > maxp)
        maxp = p;
      if (one_prime)
        goto done;
    }
    if (vcnt)
      dbg_printf(3)("%ld primes with v=%ld, maxp=%ld (%.2f bits)\n",
                 vcnt, v, maxp, log2(maxp));
  }
done:
  if ( ! n) {
    dbg_printf(3)("check_primes failed completely for D=%ld\n", D);
    return 0;
  }
  dbg_printf(3)("D=%ld: Found %ld primes totalling %0.2f of %ld bits\n",
             D, n, bits, minbits);
  if (totbits && ! *totbits)
    *totbits = (long)bits;
  return n;
}

static int
_qsort_cmp(const void *a, const void *b)
{
  D_entry *x, *y;
  long u, v;

  x = (D_entry *)a;
  y = (D_entry *)b;
  /* u and v are the class numbers of x and y */
  u = x->h * (!!(x->m & 2) + 1);
  v = y->h * (!!(y->m & 2) + 1);
  /* Sort by class number */
  if (u < v)
    return -1;
  if (u > v)
    return 1;
  /* Sort by discriminant (which is < 0, hence the sign reversal) */
  if (x->D > y->D)
    return -1;
  if (x->D < y->D)
    return 1;
  return 0;
}

/*
 * Build a table containing fundamental discriminants less than maxd
 * whose class groups
 * - are cyclic generated by an element of norm L0
 * - have class number at most maxh
 * The table is ordered using _qsort_cmp above, which ranks the
 * discriminants by class number, then by absolute disciminant.
 *
 * INPUT:
 * - maxd: largest allowed discriminant
 * - maxh: largest allowed class number
 * - L0: norm of class group generator
 *
 * OUTPUT:
 * - tablelen: length of return value
 *
 * RETURN:
 * - array of {discriminant D, h(D), kronecker symbols for small p} where D
 *   satisfies the properties above
 */
static D_entry *
scanD0(long *tablelen, long *minD, long maxD, long maxh, long L0)
{
  GEN fact, DD, H, ordL, frm;
  pari_sp av;
  long *q, *e;
  D_entry *tab;
  ulong m, x;
  long h, d, D, n;
  long L1, cnt, i, j, k;

  if (maxD < 0)
    maxD = -maxD;

  /* NB: As seen in the loop below, the real class number of D can be */
  /* 2*maxh if cl(D) is cyclic. */
  if (maxh < 0)
    pari_err_BUG("scanD0");

  /* Not checked, but L0 should be 2, 3, 5 or 7. */

  tab = (D_entry *) stack_malloc((maxD/4)*sizeof(*tab)); /* Overestimate */
  cnt = 0;
  av = avma;

  /* d = 7, 11, 15, 19, 23, ... */
  for (d = *minD, cnt = 0; d <= maxD; d += 4) {
    D = -d;
    /* Check to see if (D | L0) = 1 */
    if (kross(D, L0) < 1)
      continue;

    /* [q, e] is the factorisation of d. */
    fact = factoru(d);
    q = zv_to_longptr(gel(fact, 1));
    e = zv_to_longptr(gel(fact, 2));
    k = lg(gel(fact, 1)) - 1;

    /* Check if the discriminant is square-free */
    for (i = 0; i < k; i++)
      if (e[i] > 1)
        break;
    if (i < k)
      continue;

    /* L1 is initially the first factor of d if small enough, otherwise ignored. */
    if (k > 1 && q[0] <= MAX_L1)
      L1 = q[0];
    else
      L1 = 0;

    /* restrict to possibly cyclic class groups */
    if (k > 2)
      continue;

    /* Check if h(D) is too big */
    DD = stoi(D);
    H = classno(DD);
    h = itos(H);
    if (h > 2*maxh || (!L1 && h > maxh))
      continue;

    /* Check if ord(q) is not big enough to generate at least half the
     * class group (where q is the L0-primeform). */
    frm = primeform_u(DD, L0);
    ordL = qfi_order(redimag(frm), H);
    n = itos(ordL);
    if (n < h/2 || (!L1 && n < h))
      continue;

    /* If q is big enough, great!  Otherwise, for each potential L1,
     * do a discrete log to see if it is NOT in the subgroup generated
     * by L0; stop as soon as such is found. */
    for (j = 0; ; j++) {
      if (n == h || (L1 && ! discrete_log(primeform_u(DD, L1), frm, n))) {
        dbg_printf(2)("D0=%ld good with L1=%ld\n", D, L1);
        break;
      }
      if ( ! L1) break;
      L1 = (j < k && k > 1 && q[j] <= MAX_L1 ? q[j] : 0);
    }

    /* NB: After all that, L1 is not used or saved for later. */

    /* The first bit of m indicates whether q generates a proper
     * subgroup of cl(D) (hence implying that we need L1) or if q
     * generates the whole class group. */
    m = (n < h ? 1 : 0);
    /* bits i and i+1 of m give the 2-bit number 1 + (D|p) where p is
     * the ith prime. */
    for (i = 1 ; i <= ((BITS_IN_LONG >> 1) - 1); i++) {
      x = (ulong) (1 + kross(D, PRIMES[i]));
      m |= x << (2*i);
    }

    /* Insert d, h and m into the table */
    tab[cnt].D = D;
    tab[cnt].h = h;
    tab[cnt].m = m;
    cnt++;
    avma = av;
  }

  /* Sort the table */
  qsort(tab, cnt, sizeof(*tab), _qsort_cmp);
  *tablelen = cnt;
  *minD = d;
  return tab;
}


/*
 * Populate Ds with discriminants (and associated data) that can be
 * used to calculate the modular polynomial of level L and invariant
 * inv.  Return the number of discriminants found.
 */
static long
discriminant_with_classno_at_least(
  modpoly_disc_info Ds[MODPOLY_MAX_DCNT], long L, long inv)
{
  enum { SMALL_L_BOUND = 101 };
  long max_max_D = 160000 * (inv ? 2 : 1);
  long minD, maxD, maxh, L0, max_L1, minbits, Dcnt, flags, s, d, h, i, tmp;
  D_entry *tab;
  long tablen;
  pari_sp av = avma;
  double eps, best_eps = -1.0, cost, best_cost = -1.0;
  modpoly_disc_info bestD[MODPOLY_MAX_DCNT];
  long best_cnt = 0;
  pari_timer T;
  timer_start(&T);

  s = inv_sparse_factor(inv);
  d = s;
  /*d = ui_ceil_ratio(L + 1, d) + 1; */
  tmp = (L + 1) / d;
  d = ((tmp * d < (L + 1)) ? tmp + 1 : tmp);
  d += 1;

  /* maxD of 10000 allows us to get a satisfactory discriminant in
   * under 250ms in most cases. */
  maxD = 10000;
  /* Allow the class number to overshoot L by 50%.  Must be at least
   * 1.1*L, and higher values don't seem to provide much benefit. */
  maxh = 1.5 * L;

  flags = 0;
  L0 = select_L0(L, inv, 0);
  max_L1 = L / 2 + 2;    /* for L=11 we need L1=7 for j */
  minbits = modpoly_height_bound(L, inv);
  minD = 7;

  while ( ! best_cnt) {
    while (maxD <= max_max_D) {
      /* TODO: Find a way to re-use tab when we need multiple modpolys */
      tab = scanD0(&tablen, &minD, maxD, maxh, L0);
      dbg_printf(1)("Found %ld potential fundamental discriminants\n", tablen);

      Dcnt = modpoly_pickD(Ds, L, inv, L0, max_L1, minbits, flags, tab, tablen);
      eps = 0.0;
      cost = 0.0;

      if (Dcnt) {
        long n1 = 0;
        for (i = 0; i < Dcnt; ++i) {
          n1 = maxss(n1, Ds[i].n1);
          cost += Ds[i].cost;
        }
        eps = (n1 * s - L) / (double)L;

        if (best_cost < 0.0 || cost < best_cost) {
          (void) memcpy(bestD, Ds, Dcnt * sizeof(modpoly_disc_info));
          best_cost = cost;
          best_cnt = Dcnt;
          best_eps = eps;
          /* We're satisfied if n1 is within 5% of L. */
          if (L / s <= SMALL_L_BOUND || eps < 0.05)
            break;
        }
      } else {
        if (log2(maxD) > BITS_IN_LONG - 2 * (log2(L) + 2))
          pari_err(e_ARCH, "modular polynomial of given level and invariant");
      }
      maxD *= 2;
      minD += 4;
      if (DEBUGLEVEL > 0) {
        err_printf("  Doubling discriminant search space (closest: %.1f%%, cost ratio: %.1f)...\n",
            eps*100, cost/(double)(d*(L-1)));
      }
    }
    max_max_D *= 2;
  }

  if (DEBUGLEVEL > 0) {
    err_printf("Found discriminant(s):\n");
    for (i = 0; i < best_cnt; ++i) {
      av = avma;
      h = itos(classno(stoi(bestD[i].D1)));
      avma = av;
      err_printf("  D = %ld, h = %ld, u = %ld, L0 = %ld, L1 = %ld, n1 = %ld, n2 = %ld, cost = %ld\n",
          bestD[i].D1, h, (long)sqrt(bestD[i].D1 / bestD[i].D0), bestD[i].L0, bestD[i].L1,
          bestD[i].n1, bestD[i].n2, bestD[i].cost);
    }
    err_printf("(off target by %.1f%%, cost ratio: %.1f)\n",
               best_eps*100, best_cost/(double)(d*(L-1)));
  }
  return best_cnt;
}
