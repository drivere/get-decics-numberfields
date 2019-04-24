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

#define dbg_printf0(lvl, fmt) \
  do { if ((lvl) <= DEBUGLEVEL) err_printf(fmt "\n"); } while (0)
#define dbg_printf1(lvl, fmt, a1) \
  do { if ((lvl) <= DEBUGLEVEL) err_printf(fmt "\n", (a1)); } while (0)
#define dbg_printf2(lvl, fmt, a1, a2) \
  do { if ((lvl) <= DEBUGLEVEL) err_printf(fmt "\n", (a1), (a2)); } while (0)
#define dbg_printf3(lvl, fmt, a1, a2, a3) \
  do { if ((lvl) <= DEBUGLEVEL) err_printf(fmt "\n", (a1), (a2), (a3)); } while (0)
#define dbg_printf4(lvl, fmt, a1, a2, a3, a4) \
  do { if ((lvl) <= DEBUGLEVEL) err_printf(fmt  "\n", (a1), (a2), (a3), (a4)); } while (0)
#define dbg_printf dbg_printf1
#define dbg_puts(lvl, str) dbg_printf0(lvl, str)

/**
 * SECTION: Fixed-length dot-product-like functions on Fl's with
 * precomuted inverse.
 */

/* Computes x0y1 + y0x1 (mod p); assumes p < 2^63. */
INLINE ulong
Fl_addmul2(
  ulong x0, ulong x1, ulong y0, ulong y1,
  ulong p, ulong pi)
{
  ulong l0, l1, h0, h1;
  LOCAL_OVERFLOW;
  LOCAL_HIREMAINDER;
  l0 = mulll(x0, y1); h0 = hiremainder;
  l1 = mulll(x1, y0); h1 = hiremainder;
  l0 = addll(l0, l1); h0 = addllx(h0, h1);
  return remll_pre(h0, l0, p, pi);
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

/*
 * A polmodular database consists of a t_VEC whose L-th entry is 0 or a
 * GEN pointing to Phi_L.  levels is a t_VECSMALL of levels to use to
 * populate the database.
 */
GEN
polmodular_db_init(GEN levels)
{
  pari_sp av = avma;
  long levellg, maxlevel, i;
  GEN res;

  levellg = levels ? lg(levels) : 0;
  maxlevel = levellg > 1 ? vecsmall_max(levels) : 0;
  res = cgetg_block(maxlevel + 1, t_VEC);

  for (i = 1; i <= maxlevel; ++i)
    gel(res, i) = 0;

  for (i = 1; i < levellg; ++i) {
    long L = levels[i];
    gel(res, L) = gclone(polmodular_ZM(L));
  }

  avma = av;
  return res;
}


void
polmodular_db_clear(GEN db)
{
  long i, dblg = lg(db);
  for (i = 1; i < dblg; ++i) {
    if (gel(db, i))
      gunclone(gel(db, i));
  }
  killblock(db);
}


GEN
polmodular_db_get(GEN *db, long L)
{
  pari_sp av = avma;
  long max_L = lg(*db) - 1;
  if (L > max_L) {
    GEN newdb = cgetg_block(L + 1, t_VEC);
    long i;
    for (i = 1; i <= max_L; ++i)
      gel(newdb, i) = gel(*db, i);
    for (i = max_L + 1; i <= L; ++i)
      gel(newdb, i) = 0;
    killblock(*db);
    *db = newdb;
  }
  /* NB: In principle, this call to polmodular_ZM could make use of db,
   * but in practice it would gain almost nothing, and only in very
   * rare cases.  */
  if (gel(*db, L) == 0)
    gel(*db, L) = gclone(polmodular_ZM(L));
  avma = av;
  return gel(*db, L);
}


/* NB: Unlike polmodular_db_get(), this function returns something on the
 * stack that the caller must clean up. */
GEN
polmodular_db_getp(GEN *db, long L, ulong p)
{
  return ZM_to_Flm(polmodular_db_get(db, L), p);
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
} modpoly_disc_info;

static const modpoly_disc_info *
discriminant_with_classno_at_least(long *D, ulong *u, ulong *v, ulong L);

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
  if (L == 2)
    return Flm_Fl_phi2_evalx(phi, j, p, pi);
  if (L == 3)
    return Flm_Fl_phi3_evalx(phi, j, p, pi);
  if (L == 5)
    return Flm_Fl_phi5_evalx(phi, j, p, pi);
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
/* f deg d_f > 2, g deg 2, neither need be monic, f and g are not
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
  t1 = Fl_addmul2(s1, g[2], f[d - 1], f[d], p, pi);
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

  /* FIXME: Handle avs' strange case "r == r2", I think for
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
  GEN *mpdb, ulong p, ulong pi)
{
  pari_sp av = avma;
  GEN phi_2 = polmodular_db_getp(mpdb, 2, p);
  GEN phi_L = polmodular_db_getp(mpdb, L, p);
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
enum_j_fast(ulong j0, long D, long L1, long d2, long dL, long r,
            GEN *mpdb, ulong p, ulong pi)
{
  GEN res = cgetg(2 * r + 1, t_VECSMALL);
  if (4 * 4 * L1 * L1 > -D || d2 > r || dL + 2 > r)
    pari_err_BUG("enum_j_fast: invalid parameters");
  res[1] = j0;
  fill_box((ulong *)&res[1], L1, d2, dL, r, mpdb, p, pi);
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
 * FIXME: There is an even simpler version of this algorithm in
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

/* These are the conditions that a prime is required to satisfy, if
 * set. */
#define FILTER_PRIME_1MOD3 1
#define FILTER_PRIME_2MOD3 2
#define FILTER_PRIME_1MOD4 4
#define FILTER_PRIME_3MOD4 8

INLINE int
passes_filter(ulong p, ulong filter)
{
  /* filter & 3 == 3 means FILTER_PRIME_1MOD3 and FILTER_PRIME_2MOD3
   * were both set.
   * filter & 12 == 12 means FILTER_PRIME_1MOD4 and
   * FILTER_PRIME_3MOD4 were both set. */
  if (DEBUGLEVEL && ((filter & 3) == 3 || (filter & 12) == 12)) {
    char *err = stack_sprintf("passes_filter: "
                              "got incoherent filter: %#lx", filter);
    pari_err_BUG(err);
  }
  if ((filter & FILTER_PRIME_1MOD3) && (p % 3 != 1))
    return 0;
  if ((filter & FILTER_PRIME_2MOD3) && (p % 3 != 2))
    return 0;
  if ((filter & FILTER_PRIME_1MOD4) && (p % 4 != 1))
    return 0;
  if ((filter & FILTER_PRIME_3MOD4) && (p % 4 != 3))
    return 0;
  return 1;
}

/*
 * Select primes suitable for modpoly CRT.  See Sutherland 2012,
 * Section 6.1.
 *
 * Result is a t_VECSMALL whose odd elements (starting at index 1) are
 * the primes, and whose even elements are the corresponding traces
 * (i.e. the t such that 4p = t^2 - v^2 L^2 D).  The sign of the trace
 * is *correct* in the sense that t = 2 (mod L) is satisfied.
 */
static GEN
select_modpoly_primes(
  ulong v, ulong L, long D, double min_prime_bits, ulong filter)
{
  double prime_bits = 0.0;
  ulong vsqr = v * v;
  /* Note that vsqr * L * L * -D is positive since D is negative */
  ulong m_vsqr_Lsqr_D = vsqr * L * L * -D;
  ulong lost_primes = 0;

  pari_sp av = avma;
  long *vec = (long *)avma, veclen;

  /* This funny business with abs_t, incr and other_incr provides a
   * way to iterate over the values of t which are congruent to 2
   * modulo L such that abs(t) is monotonically increasing (for L > 3,
   * and close enough for L = 3).  This is achieved by alternately
   * incrementing abs_t by 4 or L - 4.  The sequence of abs_t's we
   * obtain is:
   *
   *     t      abs_t   incr
   * ----------------------------
   *       2        2
   *   2 - L    L - 2   L - 4
   *   2 + L    L + 2   4
   *   2 - 2L  2L - 2   L - 4
   *   2 + 2L  2L + 2   4
   *   2 - 3L  3L - 2   L - 4
   *   2 + 2L  3L + 2   4
   */

  /* incr will be -1 if L = 3, but otherwise positive. */
  long incr = L - 4;
  long other_incr = 4;
  ulong abs_tr = 2;
  ulong max_tr = 2.0 * sqrt((1UL << (BITS_IN_LONG - 2)) - (m_vsqr_Lsqr_D >> 2));
  do {
    ulong possible_4p = abs_tr * abs_tr + m_vsqr_Lsqr_D;
    if (possible_4p % 4 == 0) {
      ulong possible_p = possible_4p / 4;
      if (passes_filter(possible_p, filter)
          && uisprime(possible_p)) {
        /* Note that we now have 4p = t^2 - v^2 L^2 D for a prime p =
         * possible_p.  Since t = 2 (mod L) by construction, we see
         * that, modulo L, we have
         *
         * p = (1/4) (t^2 - v^2 L^2 D) = t^2 / 4 = 1.
         *
         * From the table above we see that t = |t| iff incr = 4 was
         * added last time.  But the condition incr = 4 is negated
         * because we swapped incr and other_incr after adding incr to
         * abs_tr at the bottom of the loop. */
        int sign = incr != 4 ? 1 : -1;
        long tr = sign * abs_tr;
        ulong card = possible_p + 1 - tr;

        ulong vL = u_lval(card, L);
        if (vL == 0 || vL == 1) {
          pari_err_BUG("select_modpoly_primes: "
                       "Incorrect trace sign");
        }

        /* Exclude primes with vL > 2 to make searching for L-torsion
         * points faster in the function compute_L_isogenous_curve()
         * below.  We throw away (very roughly) between 1% and 3% of
         * our primes because of this. */
        if (vL == 2) {
          /* Append our new prime and its trace to the end of the
           * array. */
          *--vec = tr;
          *--vec = possible_p;

          prime_bits += log2(possible_p);
          /* Do we have sufficiently many primes? */
          if (prime_bits >= min_prime_bits)
            break;
        } else
          lost_primes++;
      }
    }
    abs_tr += incr;
    lswap(incr, other_incr);
  } while (abs_tr < max_tr);

  if (abs_tr >= max_tr) {
    char *err = stack_sprintf("modular polynomial of level %lu", L);
    pari_err(e_ARCH, err);
  }

  /* Add type information. */
  --vec;
  veclen = (av - (pari_sp)vec) / sizeof(long);
  if (veclen <= 1) {
    char *err = stack_sprintf("select_modpoly_primes: Didn't find any "
                              "primes for L = %lu and D = %ld", L, D);
    pari_err_BUG(err);
  }

  *vec = evaltyp(t_VECSMALL) | evallg(veclen);
  avma = (pari_sp)vec;
  dbg_printf(1, "Threw away %.2f%% of primes because of high L-valuation",
             100 * lost_primes / (double)(lost_primes + veclen));
  return (GEN)vec;
}


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
  Fl_elltwist(A4, A6, ne->T, p, &A4t, &A6t);

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


/*
 * Identify the cycle generated by form starting at index j_idx of
 * j_invs.
 */
static GEN
identify_L_sqr_cycle(const modpoly_disc_info *dinfo, GEN j_invs, ulong j_idx)
{
  long idx;
  long m;
  long j_exp_0, j_exp_1, e_0, e_1, i;
  long cyc_gen_0, cyc_gen_1, cyc_elt_0, cyc_elt_1;
  long L = dinfo->L;
  GEN res = cgetg(L, t_VECSMALL);

  m = dinfo->n2;
  cyc_gen_0 = dinfo->dl2_0;
  cyc_gen_1 = 1;
  cyc_elt_0 = dinfo->dl2_0;
  cyc_elt_1 = 1;

  j_idx -= 1;
  j_exp_1 = j_idx / m;
  j_exp_0 = j_idx - j_exp_1 * m;

  for (i = 1; i <= L - 1; ++i) {
    e_0 = (j_exp_0 + cyc_elt_0) % m;
    e_1 = (j_exp_1 + cyc_elt_1) % 2;

    idx = (e_0 + e_1 * m) + 1;
    res[i] = j_invs[idx];

    cyc_elt_0 += cyc_gen_0;
    cyc_elt_0 %= m;
    cyc_elt_1 += cyc_gen_1;
    cyc_elt_1 %= 2;
  }

  return res;
}


static ulong
oneroot_of_classpoly(
  GEN hilb, GEN factu, norm_eqn_t ne, GEN *mpdb)
{
  pari_sp av = avma;
  ulong j0, p = ne->p, pi = ne->pi;
  long i, nfactors = lg(gel(factu, 1)) - 1;
  GEN hilbp = ZX_to_Flx(hilb, p);

  j0 = Flx_oneroot_split(hilbp, p);
  if (j0 == p) {
    pari_err_BUG("oneroot_of_classpoly: "
                 "Didn't find a root of the class polynomial");
  }
  for (i = 1; i <= nfactors; ++i) {
    long L = gel(factu, 1)[i];
    long val = gel(factu, 2)[i];
    GEN phi = polmodular_db_getp(mpdb, L, p);
    j0 = descend_volcano(phi, j0, p, pi, 0, L, val, val);
    avma = av;
  }
  avma = av;
  return j0;
}


static GEN
polmodular_split_p_evalx_Flv(
  const modpoly_disc_info *dinfo, ulong pp,
  GEN j_invs, GEN j_pr_invs, GEN R_j_invs, ulong j_idx)
{
  pari_sp av = avma;
  GEN nhbrs_of_ji, j_ik, modpoly_at_ji, L2_cycle_containing_ji_pr;
  long k, l_idx, r_idx, njinvs = lg(j_invs) - 1;
  long m = dinfo->dl1;

  r_idx = (((j_idx - 1) + m) % njinvs) + 1; /* (j_idx + m) % njinvs */
  l_idx = smodss((j_idx - 1) - m, njinvs) + 1; /* (j_idx - m) % njinvs */
  nhbrs_of_ji = mkvecsmall2(j_invs[l_idx], j_invs[r_idx]);

  k = vecsmall_isin(R_j_invs, j_pr_invs[j_idx]);
  if ( ! k) {
    pari_err_BUG("polmodular_split_p_evalx_Flv: "
                 "Couldn't find j-invariant in list");
  }

  /* FIXME: I think I can avoid recalculating the cycle for each j_idx
   * and instead calculate it once and then "shift" the cycle forward
   * by 1 for each iteration (for this identify_cycle() should return
   * indices instead of j-invariants I guess). */
  /* FIXME: We can actually enumerate ker(\phi) very quickly using
   * essentially the same code as in form_of_norm_L_sqr().  The L2
   * cycle could then be obtained by applying each element of
   * ker(\phi) to ji.  It's not clear whether that would be faster
   * than just searching for a generator as we do now. */
  L2_cycle_containing_ji_pr
    = identify_L_sqr_cycle(dinfo, R_j_invs, k);

  j_ik = concat(nhbrs_of_ji, L2_cycle_containing_ji_pr);
  modpoly_at_ji = Flv_roots_to_pol(j_ik, pp, 0);
  dbg_printf4(3, "    Phi_%lu(X, %lu) (mod %lu) = %Ps\n",
              dinfo->L, j_invs[j_idx], pp, modpoly_at_ji);

  return gerepileupto(av, modpoly_at_ji);
}


INLINE GEN
enum_volcano_surface(
  const modpoly_disc_info *dinfo, norm_eqn_t ne, ulong j0, GEN *mpdb)
{
  pari_sp av = avma;
  GEN pcp = mkvec2(mkvecsmall(dinfo->L0), mkvecsmall(dinfo->n1));
  return gerepileupto(av, enum_j_with_endo_ring(j0, ne, mpdb, pcp, dinfo->n1));
}

INLINE GEN
find_floor_curves(ulong L, ulong  n, norm_eqn_t ne, GEN j_invs, ulong card,
                  ulong val)
{
  long i, l = L+2;
  GEN j_pr_invs = cgetg(l+1, t_VECSMALL);
  for (i = 1; i <= l; ++i)
    j_pr_invs[i] = compute_L_isogenous_curve(L, n, ne, j_invs[i], card, val);
  return j_pr_invs;
}

INLINE GEN
enum_floor_curves(
  long L, norm_eqn_t ne, ulong j0_pr, GEN *mpdb,
  const modpoly_disc_info *dinfo)
{
  /* L^2 D is the discriminant for the order R = Z + L OO. */
  long DR = L * L * ne->D;
  long R_cond = L * ne->u; /* conductor(DR); */
  /* FIXME: Is this still the right v? */
  long w = R_cond * ne->v;
  /* FIXME: Calculate these once and for all in polmodular0_ZM(). */
  long d2 = z_lval(w, 2);
  long dL = z_lval(w, dinfo->L1);
  return enum_j_fast(j0_pr, DR, dinfo->L1, d2, dL, dinfo->n2, mpdb,
                     ne->p, ne->pi);
}

INLINE GEN
evaluated_modpoly_coeffs(
  long L, ulong p, const modpoly_disc_info *dinfo,
  GEN j_invs, GEN j_pr_invs, GEN R_j_invs)
{
  pari_sp av;
  long i;
  GEN coeff_mat = zero_Flm_copy(L + 2, L + 2);
  av = avma;
  for (i = 1; i <= L + 2; ++i) {
    long k;
    GEN modpoly_at_ji =
      polmodular_split_p_evalx_Flv(dinfo, p, j_invs, j_pr_invs, R_j_invs, i);
    for (k = 1; k <= L + 2; ++k)
      coeff(coeff_mat, i, k) = modpoly_at_ji[k + 1];
    avma = av;
  }
  return coeff_mat;
}

INLINE void
interpolate_coeffs(
  GEN modpoly_modp, /* Return parameter */
  long L, ulong p, GEN j_invs, GEN coeff_mat)
{
  pari_sp av = avma;
  GEN pols = Flv_FlvV_polint(j_invs, coeff_mat, p, 0);
  long i;
  for (i = 1; i <= L + 2; ++i) {
    GEN pol = gel(pols, i);
    long k, maxk = lg(pol);
    for (k = 2; k < maxk; ++k)
      coeff(modpoly_modp, i, k - 1) = pol[k];
  }
  avma = av;
}

/*
 * This is Sutherland 2012, Algorithm 2.1, p16.
 */
static GEN
polmodular_split_p_Flm(
  ulong L, GEN hilb, GEN factu, norm_eqn_t ne, GEN *mpdb,
  const modpoly_disc_info *dinfo)
{
  ulong j0, n, card, val, p = ne->p;
  GEN j_invs, j_pr_invs, R_j_invs, coeff_mat;
  GEN modpoly_modp = zero_Flm_copy(L + 2, L + 2);
  pari_sp av = avma;

  /* Precomputation */
  card = p + 1 - ne->t;
  val = u_lvalrem(card, L, &n); /* n = card / L^{v_L(card)} */

  j0 = oneroot_of_classpoly(hilb, factu, ne, mpdb);
  j_invs = enum_volcano_surface(dinfo, ne, j0, mpdb);
  j_pr_invs = find_floor_curves(L, n, ne, j_invs, card, val);
  R_j_invs = enum_floor_curves(L, ne, j_pr_invs[1], mpdb, dinfo);
  coeff_mat = evaluated_modpoly_coeffs(L, p, dinfo,
                                       j_invs, j_pr_invs, R_j_invs);
  setlg(j_invs, L + 2 + 1);
  interpolate_coeffs(modpoly_modp, L, p, j_invs, coeff_mat);

  dbg_printf3(3, "  Phi_%lu(X, Y) (mod %lu) = %Ps\n",
             L, p, modpoly_modp);

  avma = av;
  return modpoly_modp;
}


INLINE void
norm_eqn_init(norm_eqn_t ne, long D, long u, long v, long L)
{
  memset(ne, 0, sizeof(*ne));
  ne->D = D;
  ne->u = u;
  ne->v = v * L;
  ne->w = ne->u * ne->v;
}


INLINE void
norm_eqn_update(norm_eqn_t ne, long t, ulong p)
{
  ne->t = t;
  ne->p = p;
  ne->pi = get_Fl_red(p);
  /* Select twisting parameter. */
  do
    ne->T = random_Fl(p);
  while (krouu(ne->T, p) != -1);
}

INLINE void
Flv_deriv_pre_inplace(GEN v, long deg, ulong p, ulong pi)
{
  long i, ln = lg(v);
  for (i = ln - 1; i > 1; --i, --deg)
    v[i] = Fl_mul_pre(v[i - 1], deg % p, p, pi);
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

static GEN
polmodular0_ZM(
  ulong L, double min_prime_bits, GEN J, GEN Q,
  int compute_derivs,
  int quit_on_first_stabilisation)
{
  pari_sp ltop = avma, btop, av;
  long D, DK;
  ulong cond, v;
  GEN mpdb;
  ulong filter;
  GEN pt_pairs;
  long i, pt_pairs_len;
  norm_eqn_t ne;
  GEN hilb, j_powers, modpoly, P;
  GEN factu;
  const modpoly_disc_info *dinfo;

  dbg_printf1(1, "Calculating modular polynomial of level %lu", L);
  dinfo = discriminant_with_classno_at_least(&D, &cond, &v, L);
  factu = factoru(cond);

  av = avma;
  mpdb = polmodular_db_init(0);

  dbg_printf2(1, "Selected discriminant D = %ld which has conductor u = %ld.",
              D, cond);

  filter = 0; /* Don't filter anything. */
  pt_pairs = select_modpoly_primes(v, L, D, min_prime_bits, filter);
  pt_pairs_len = lg(pt_pairs) - 1;

  dbg_printf3(1, "Selected %ld primes in [%ld, %ld]",
              pt_pairs_len / 2, pt_pairs[pt_pairs_len - 1], pt_pairs[1]);

  DK = D / (long)(cond * cond);
  hilb = polclass(stoi(DK), -1);

  norm_eqn_init(ne, D, cond, v, L);

  j_powers = 0;
  if (J) {
    compute_derivs = !!compute_derivs;
    j_powers = Fp_powers(J, L + 1, Q);
  }

  btop = avma;
  if (J)
    modpoly = ZM_init_CRT(zero_Flm(L + 2, compute_derivs ? 3 : 1), 1);
  else
    modpoly = ZM_init_CRT(zero_Flm(L + 2, L + 2), 1);
  /* P is the product of all the primes. */
  P = gen_1;
  for (i = 1; i <= pt_pairs_len; i += 2) {
    ulong p = pt_pairs[i];
    ulong t = pt_pairs[i + 1];
    GEN modpoly_modp;
    int stab = 0;

    norm_eqn_update(ne, t, p);

    av = avma;
    modpoly_modp = polmodular_split_p_Flm(L, hilb, factu, ne, &mpdb, dinfo);
    if (J) {
      modpoly_modp = eval_modpoly_modp(modpoly_modp, j_powers, ne, compute_derivs);
      modpoly_modp = gerepileupto(av, modpoly_modp);
    }
    stab = ZM_incremental_CRT(&modpoly, modpoly_modp, &P, p);

    if (gc_needed(btop, 2))
      gerepileall(btop, 2, &modpoly, &P);
    if (quit_on_first_stabilisation && stab)
      break;
  }

  polmodular_db_clear(mpdb);
  if (J)
    return gerepileupto(ltop, FpM_red(modpoly, Q));
  return gerepileupto(ltop, modpoly);
}


/* The largest level of the "hand written" modular polynomials */
#define MAX_INTERNAL_MODPOLY_LEVEL 7

/* The definitions of these functions are at the end of the file. */
static GEN phi2_ZV(void);
static GEN phi3_ZV(void);
static GEN phi5_ZV(void);
static GEN phi7_ZV(void);


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


GEN
polmodular_ZM(long L)
{
  double c, min_prime_bits;
  pari_sp av = avma;
  GEN mp = 0;

  /* Handle very small L separately. */
  switch (L) {
  case 2:
    mp = phi2_ZV(); break;
  case 3:
    mp = phi3_ZV(); break;
  case 5:
    mp = phi5_ZV(); break;
  case 7:
    mp = phi7_ZV(); break;
  }
  if (mp)
    return gerepilecopy(av, sympol_to_ZM(mp, L));

  if (L < 2)
    pari_err_DOMAIN("polmodular_ZM", "L", "<", gen_2, stoi(L));

  /* FIXME: Handle non-prime L.  This is Algorithm 1.1 and Corollary
   * 3.4 in Sutherland, "Class polynomials for nonholomorphic modular
   * functions". */
  if ( ! uisprime(L))
    pari_err_IMPL("composite level");

  /* Need \sum log2(p) >= |c|/log(2) + 2 where c = 6 * L * (log(L) +
   * 3) is an upper bound for the logarithmic height of \Phi_L.  For L
   * > 3187, we use the better bound c = 2 (3L + 7 sqrt(L)) log(L) +
   * 16L. See Sutherland "On the evaluation of modular polynomials",
   * p6. */
  c = (L <= 3187)
    ? 6 * L * (log(L) + 3)
    : 2 * (3 * L + 7 * sqrt(L)) * log(L) + 16 * L;
  min_prime_bits = c / LOG2 + 2;

  return polmodular0_ZM(L, min_prime_bits, 0, 0, 0, 0);
}


GEN
polmodular_ZXX(long L, long vx, long vy)
{
  pari_sp av = avma;
  GEN phi = polmodular_ZM(L);

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
  long L, GEN J, GEN P, long v, int compute_derivs)
{
  pari_sp av = avma;
  double c;
  GEN phi;

  if (L <= MAX_INTERNAL_MODPOLY_LEVEL) {
    GEN tmp;
    GEN phi = RgM_to_FpM(polmodular_ZM(L), P);
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

  /* The height bound is 6 L log(L) + 18 L + log(q) + 3 log(L + 2) + log(4).
   *                    = 3 (2L (log(L) + 3) + log(L + 2)) + log(q) + log(4) */
  c = 3 * (2 * L * log2(L) + log2(L + 2)) + 18 * L / LOG2
    + dbllog2r(itor(P, DEFAULTPREC)) + 2;
  phi = polmodular0_ZM(L, c, J, P, compute_derivs, 0);
  phi = RgM_to_RgXV(phi, v);
  return gerepilecopy(av, compute_derivs ? phi : gel(phi, 1));
}

GEN
polmodular(long L, GEN x, long v, int compute_derivs)
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
    return polmodular_ZXX(L, xv, v);
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
  res = Fp_polmodular_evalx(L, J, P, v, compute_derivs);
  res = gmul(res, one);
  return gerepileupto(av, res);
}

/**
 * SECTION: Modular polynomials of level <= MAX_INTERNAL_MODPOLY_LEVEL.
 */

/*
 * These functions return a vector of unique coefficients of classical
 * modular polynomials \Phi_L(X, Y) of small level L.  The number of
 * such coefficients is (L + 1)(L + 2)/2 since \Phi is symmetric.  The
 * i(i+1)/2-th through i(i+3)/2-th entries of the vector are the
 * coefficients of the coefficient of X^i considered as a polynomial
 * in Y (FIXME: this is not exactly correct).  Note that we omit the
 * (common) coefficient of X^{L + 1} and Y^{L + 1} since it is always 1.
 *
 * Use GEN ZV_to_Flv(GEN v, ulong p) to reduce the polynomial modulo p.
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
phi7_ZV(void)
{
  GEN phi7 = cgetg(37, t_VEC);
  gel(phi7, 1) = gen_0;
  gel(phi7, 2) = gen_0;
  gel(phi7, 3) = mkintn(7, 0xb98ef8aUL, 0x5da89820UL, 0x27fcaa10UL, 0xc337ec73UL, 0xe8000000UL, 0x0UL, 0x0UL);
  gel(phi7, 4) = mkintn(7, 0xde8a58bUL, 0xfbf60e2aUL, 0x25371391UL, 0x6b054e99UL, 0x54000000UL, 0x0UL, 0x0UL);
  gel(phi7, 5) = mkintn(7, 0x209d2UL, 0xd2dd3b42UL, 0xf208c229UL, 0xd3f6cd61UL, 0x5aa81000UL, 0x0UL, 0x0UL);
  setsigne(gel(phi7, 5), -1);
  gel(phi7, 6) = mkintn(7, 0x7UL, 0x6f2fd980UL, 0x822116beUL, 0x3dd5c31aUL, 0xc177b28aUL, 0x20000000UL, 0x0UL);
  setsigne(gel(phi7, 6), -1);
  gel(phi7, 7) = mkintn(7, 0x864UL, 0x1e548f80UL, 0x799513d5UL, 0xbd1bf6b2UL, 0xc0855000UL, 0x0UL, 0x0UL);
  gel(phi7, 8) = mkintn(7, 0x14UL, 0xa9082853UL, 0xf7daac9fUL, 0xd3ae375aUL, 0xb11a1708UL, 0xa0000000UL, 0x0UL);
  setsigne(gel(phi7, 8), -1);
  gel(phi7, 9) = mkintn(6, 0x2f287d2UL, 0xa017bd69UL, 0x4c5eb85aUL, 0xa496f0f2UL, 0x68dac000UL, 0x0UL);
  gel(phi7, 10) = mkintn(6, 0xe6dUL, 0x2818206dUL, 0x99adaa70UL, 0x1e05f921UL, 0x26c36d89UL, 0x80000000UL);
  setsigne(gel(phi7, 10), -1);
  gel(phi7, 11) = mkintn(6, 0x1affb90UL, 0x75076431UL, 0x92c2d298UL, 0x18ed8fe9UL, 0x70000000UL, 0x0UL);
  gel(phi7, 12) = mkintn(6, 0x5c6d2UL, 0xc60306c0UL, 0xd36aaa58UL, 0x1dc09f98UL, 0xccac000UL, 0x0UL);
  gel(phi7, 13) = mkintn(6, 0xd3UL, 0x3bee42d3UL, 0x193e211UL, 0x575981bcUL, 0xa77b12beUL, 0x80000000UL);
  gel(phi7, 14) = mkintn(5, 0x325e879UL, 0xcc292d75UL, 0x6086beceUL, 0x8c18673aUL, 0x993d0000UL);
  gel(phi7, 15) = mkintn(5, 0x102UL, 0xb7de9305UL, 0x26c5fde5UL, 0x122a579eUL, 0x7bad0c46UL);
  gel(phi7, 16) = mkintn(6, 0x1cUL, 0xf4fc37ccUL, 0xb61bee0cUL, 0x1aa43057UL, 0x85e38000UL, 0x0UL);
  gel(phi7, 17) = mkintn(5, 0x7209872UL, 0xa810ac3cUL, 0xaf82d027UL, 0x19b659f6UL, 0x0UL);
  setsigne(gel(phi7, 17), -1);
  gel(phi7, 18) = mkintn(5, 0x815eUL, 0xfad28592UL, 0xf33facf6UL, 0x10060813UL, 0x25580000UL);
  gel(phi7, 19) = mkintn(5, 0x2UL, 0xa6529211UL, 0xea123ef6UL, 0x7ad394d2UL, 0xabe49138UL);
  setsigne(gel(phi7, 19), -1);
  gel(phi7, 20) = mkintn(4, 0x2b58cUL, 0x1cbcbb65UL, 0x2ce001cfUL, 0x279429e0UL);
  gel(phi7, 21) = mkintn(3, 0x3b2214c4UL, 0xf2b5e5fbUL, 0x1f81b4ecUL);
  setsigne(gel(phi7, 21), -1);
  gel(phi7, 22) = mkintn(4, 0xb3a0UL, 0x57dd5903UL, 0x23f93a5cUL, 0xc0000000UL);
  gel(phi7, 23) = mkintn(4, 0x332eUL, 0x3435e075UL, 0xaa2299d4UL, 0x3a1e0000UL);
  gel(phi7, 24) = mkintn(4, 0x86UL, 0xddc49282UL, 0xb81e3f32UL, 0xb5d52a1cUL);
  gel(phi7, 25) = mkintn(3, 0x341ab0c9UL, 0x2a5aafc0UL, 0x5c470530UL);
  gel(phi7, 26) = mkintn(3, 0x3b0a4UL, 0x2ced66eaUL, 0x97d5e888UL);
  gel(phi7, 27) = mkintn(3, 0x9UL, 0x999bc197UL, 0x601617f0UL);
  gel(phi7, 28) = uu32toi(0x11c4eUL, 0x9c431839UL);
  gel(phi7, 29) = uu32toi(0x1736b97UL, 0xef4d0000UL);
  gel(phi7, 30) = uu32toi(0x7c5237UL, 0xf1971f08UL);
  setsigne(gel(phi7, 30), -1);
  gel(phi7, 31) = uu32toi(0x28efdUL, 0x46d450f0UL);
  gel(phi7, 32) = uu32toi(0x3b5UL, 0xe122f592UL);
  setsigne(gel(phi7, 32), -1);
  gel(phi7, 33) = uu32toi(0x2UL, 0x32877ba0UL);
  gel(phi7, 34) = stoi(-10246068);
  gel(phi7, 35) = stoi(5208);
  gel(phi7, 36) = gen_m1;
  return phi7;
}

/*
 * This data was generated using Sutherland's modpoly_pickD() function.
 */

#ifndef LONG_IS_64BIT
#define DISC_TABLE_LENGTH 24
#else
#define DISC_TABLE_LENGTH 429
#endif

/*   L         D0         D1   L0   L1      n1      n2   #P     dl1  dl2[0]  dl2[1] */
static const modpoly_disc_info DISC_TABLE[DISC_TABLE_LENGTH] = {
{    5,      -111,      -111,   2,   3,      8,     16,  12,      5,      4,   1 },
{    7,      -159,      -159,   2,   3,     10,     30,  16,      6,     25,   1 },
{   11,      -791,      -791,   2,   7,     16,     80,  21,     10,     56,   1 },
{   13,     -6295,     -6295,   2,   5,     24,    144,  29,     17,     84,   1 },
{   17,      -695,      -695,   2,   5,     24,    192,  34,      9,    156,   1 },
{   19,     -1191,     -1191,   2,   3,     24,    216,  39,     20,    156,   1 },
{   23,      -143,     -7007,   2,  11,     30,    330,  45,     18,    225,   1 },
{   29,     -4647,     -4647,   2,   3,     32,    448,  60,      7,    240,   1 },
{   31,     -2199,     -2199,   2,   3,     36,    540,  60,     24,    234,   1 },
{   37,     -1655,     -1655,   2,   5,     44,    792,  67,     11,    242,   1 },
{   41,     -1919,     -1919,   2,  19,     44,    880,  75,     37,    418,   1 },
{   43,       -39,     -6591,   2,   3,     52,   1092,  84,     16,    442,   1 },
{   47,       -15,    -10935,   2,   5,     54,   1242,  93,     15,    837,   1 },
{   53,     -2495,     -2495,   2,   5,     56,   1456,  96,     19,   1428,   1 },
{   59,    -14183,    -14183,   2,  13,     64,   1856, 114,     21,   1184,   1 },
{   61,    -12199,    -12199,   2,  11,     64,   1920, 117,     43,    608,   1 },
{   67,    -10551,    -10551,   2,   3,     72,   2376, 126,     54,   1260,   1 },
{   71,       -55,    -75295,   2,  11,     76,   2660, 135,     60,   1786,   1 },
{   73,     -4631,     -4631,   2,  11,     76,   2736, 128,     51,   2242,   1 },
{   79,    -16311,    -16311,   2,   3,     84,   3276, 148,     28,   1218,   1 },
{   83,     -7319,     -7319,   2,  13,     88,   3608, 147,     59,   1980,   1 },
{   89,    -13471,    -13471,   2,  19,     92,   4048, 167,     13,   2714,   1 },
{   97,    -10055,    -10055,   2,   5,    100,   4800, 172,     63,   3650,   1 },
{  101,    -20487,    -20487,   2,   3,    104,   5200, 184,     63,   3692,   1 }

#ifdef LONG_IS_64BIT
                                                                                  ,
{  103,    -10911,    -10911,   2,   3,    108,   5508, 182,     64,   4266,   1 },
{  107,     -7895,     -7895,   2,   5,    112,   5936, 185,     97,   5208,   1 },
{  109,    -32071,    -32071,   2,  13,    112,   6048, 203,     95,   3080,   1 },
{  113,    -13927,   -348175,   2,  19,    120,   6720, 215,     19,   2340,   1 },
{  127,    -40791,    -40791,   2,   3,    132,   8316, 232,    106,   7062,   1 },
{  131,      -407,   -296703,   2,  37,    144,   9360, 243,     61,   4248,   1 },
{  137,     -1263,   -213447,   2,   3,    140,   9520, 253,     89,   4270,   1 },
{  139,    -42199,    -42199,   2,  19,    144,   9936, 255,     36,   7848,   1 },
{  149,     -1119,   -135399,   2,   3,    160,  11840, 265,     21,  11440,   1 },
{  151,    -41079,    -41079,   2,   3,    156,  11700, 270,     88,   3822,   1 },
{  157,    -37295,    -37295,   2,   5,    160,  12480, 276,     23,   3920,   1 },
{  163,     -5007,   -605847,   2,   3,    180,  14580, 302,    120,   8730,   1 },
{  167,      -407,    -49247,   2,  37,    176,  14608, 296,     61,   2552,   1 },
{  173,     -5007,   -605847,   2,   3,    180,  15480, 319,     75,  13950,   1 },
{  179,    -43087,  -1077175,   2,  11,    192,  17088, 335,     38,   9120,   1 },
{  181,   -184927,   -184927,   2,  19,    188,  16920, 340,      9,   1598,   1 },
{  191,     -3959,   -320679,   2,  37,    204,  19380, 342,     51,   7242,   1 },
{  193,     -2959,  -1849375,   2,  11,    200,  19200, 347,     27,   8300,   1 },
{  197,     -4367,   -109175,   2,  11,    204,  19992, 333,    127,  19074,   1 },
{  199,     -1007,   -170183,   2,  19,    210,  20790, 341,    134,  16905,   1 },
{  211,    -33591,    -33591,   2,   3,    216,  22680, 363,     88,   7884,   1 },
{  223,      -327,   -447663,   2,   3,    228,  25308, 399,     74,  16986,   1 },
{  227,    -20095,  -7254295,   2,   5,    240,  27120, 404,     13,  23400,   1 },
{  229,    -43007,    -43007,   2,  29,    232,  26448, 393,    151,  25868,   1 },
{  233,    -14695,  -1778095,   2,   5,    240,  27840, 433,    101,  16440,   1 },
{  239,      -871,   -460759,   2,  13,    242,  28798, 423,    185,    121,   1 },
{  241,    -52679,    -52679,   2,  11,    244,  29280, 408,    111,  11102,   1 },
{  251,    -27607,   -690175,   2,  19,    264,  33000, 453,     26,   9372,   1 },
{  257,      -535,   -732415,   2,   5,    266,  34048, 463,    181,  19551,   1 },
{  263,     -3439,   -993871,   2,  19,    270,  35370, 474,    226,  19845,   1 },
{  269,   -116031,   -116031,   2,   3,    272,  36448, 472,     65,   7480,   1 },
{  271,     -2823,  -1493367,   2,   3,    286,  38610, 492,    190,  27599,   1 },
{  277,   -274207,   -274207,   2,  37,    280,  38640, 504,    241,  23380,   1 },
{  281,    -24383,  -1975023,   2,  37,    288,  40320, 514,    211,  11664,   1 },
{  283,   -105159,   -105159,   2,   3,    288,  40608, 496,     12,  30096,   1 },
{  293,    -10583,   -857223,   2,  19,    300,  43800, 523,    221,  32550,   1 },
{  307,   -190263,   -190263,   2,   3,    312,  47736, 545,     74,   8268,   1 },
{  311,    -24343,  -4113967,   2,  11,    322,  49910, 573,     70,   2093,   1 },
{  313,   -110255,   -110255,   2,   5,    316,  49296, 536,     85,  41554,   1 },
{  317,     -5455,  -1969255,   2,   5,    324,  51192, 576,     17,  16038,   1 },
{  331,   -131151,   -131151,   2,   3,    336,  55440, 574,     60,  19992,   1 },
{  337,    -22255,  -2692855,   2,   5,    340,  57120, 614,    249,  39950,   1 },
{  347,   -173695, -21017095,   2,   5,    360,  62280, 621,    127,  13140,   1 },
{  349,    -74591,    -74591,   2,  11,    352,  61248, 583,     93,  45584,   1 },
{  353,    -37703,   -942575,   2,  37,    366,  64416, 607,     89,  55083,   1 },
{  359,    -10231,  -2956759,   2,  13,    378,  67662, 651,     37,   3591,   1 },
{  367,    -18687,  -3158103,   2,   3,    392,  71736, 663,    358,  62524,   1 },
{  373,   -579895,   -579895,   2,   5,    376,  69936, 679,     69,  50572,   1 },
{  379,   -239079,   -239079,   2,   3,    384,  72576, 660,    288,  18240,   1 },
{  383,    -16535,  -1339335,   2,   5,    390,  74490, 676,    351,   1755,   1 },
{  389,   -112719,   -112719,   2,   3,    392,  76048, 662,    327,  61348,   1 },
{  397,   -136295,   -136295,   2,   5,    400,  79200, 669,    211,  10600,   1 },
{  401,      -871,  -1192399,   2,  13,    418,  83600, 700,    203,  79211,   1 },
{  409,    -20647, -17364127,   2,  11,    434,  88536, 731,    337,  47089,   1 },
{  419,    -25663,  -9264343,   2,  11,    432,  90288, 768,    412,  60696,   1 },
{  421,   -149279,   -149279,   2,  13,    424,  89040, 708,    349,  48548,   1 },
{  431,   -926863, -23171575,   2,   7,    438,  94170, 769,    270,  23871,   1 },
{  433,   -136967,   -136967,   2,  29,    436,  94176, 725,    299,  77390,   1 },
{  439,     -6879,  -1162551,   2,   3,    448,  98112, 759,    166,  48608,   1 },
{  443,    -89407,  -2235175,   2,  29,    456, 100776, 789,    385,  75924,   1 },
{  449,    -47063,  -3812103,   2,  19,    468, 104832, 801,    187,  48906,   1 },
{  457,    -41815,  -7066735,   2,   5,    462, 105336, 830,    217, 102795,   1 },
{  461,    -87663, -10607223,   2,   3,    468, 107640, 809,     63,  84942,   1 },
{  463,    -73207,  -8858047,   2,  19,    470, 108570, 844,    396,  30785,   1 },
{  467,     -3295,  -2771095,   2,   5,    480, 111840, 832,    161,  15600,   1 },
{  479,       -87,   -570807,   2,  29,    486, 116154, 843,    375,   2187,   1 },
{  487,     -4479,  -3766839,   2,   3,    490, 119070, 825,    412, 106085,   1 },
{  491,     -3743,  -1081727,   2,  19,    504, 123480, 829,    410,  21924,   1 },
{  499,   -283567, -47922823,   2,  23,    504, 125496, 886,    457, 102564,   1 },
{  503,     -4847,  -4076327,   2,  37,    518, 130018, 844,    465,  99715,   1 },
{  509,    -27703, -14654887,   2,  13,    528, 134112, 925,     21,  41976,   1 },
{  521,   -175199,   -175199,   2,  19,    524, 136240, 860,    273, 115542,   1 },
{  523,    -10119,  -1710111,   2,   3,    532, 138852, 903,     22, 118370,   1 },
{  541,   -270023,   -270023,   2,  13,    544, 146880, 904,    117,  24208,   1 },
{  547,    -63295, -60826495,   2,   5,    560, 152880, 957,    189,  58520,   1 },
{  557,    -13071,  -2208999,   2,   3,    560, 155680, 966,    517, 146440,   1 },
{  563,     -8495,  -3066695,   2,   5,    576, 161856, 970,     25, 156384,   1 },
{  569,    -12199, -16700431,   2,  11,    576, 163584, 995,    219, 126432,   1 },
{  571,    -27399,  -4630431,   2,   3,    588, 167580,1005,    548,   2058,   1 },
{  577,     -4511,  -3793751,   2,  13,    588, 169344, 951,    105, 162582,   1 },
{  587,       -39,  -3257319,   2,  13,    612, 179316,1021,    281,  44370,   1 },
{  593,    -10495, -10085695,   2,   5,    600, 177600,1067,     19, 127500,   1 },
{  599,    -28039,  -4738591,   2,  11,    602, 179998,1057,    310,   8127,   1 },
{  601,   -393623,   -393623,   2,  19,    604, 181200,1011,    595,  93922,   1 },
{  607,     -7311,  -1235559,   2,   3,    616, 186648,1022,    354, 105644,   1 },
{  613,   -136495, -16515895,   2,   5,    640, 195840,1105,    101, 105280,   1 },
{  617,    -91247,  -7391007,   2,  13,    624, 192192,1099,    271, 119496,   1 },
{  619,    -15231,  -1842951,   2,   3,    640, 197760,1053,    482, 168640,   1 },
{  631,     -8047, -11016343,   2,  13,    646, 203490,1135,    631,  72029,   1 },
{  641,    -10743,  -3878223,   2,   3,    666, 213120,1118,    425, 192141,   1 },
{  643,    -53247,  -6442887,   2,   3,    660, 211860,1132,    612, 152790,   1 },
{  647,   -121543, -20540767,   2,  19,    658, 212534,1171,    638, 159565,   1 },
{  653,     -1655,  -1391855,   2,   5,    660, 215160,1086,    601,  76890,   1 },
{  659,   -469423, -23001727,   2,  29,    672, 221088,1190,    115, 111216,   1 },
{  661,   -752687,   -752687,   2,  13,    664, 219120,1124,    305,  13612,   1 },
{  673,    -43567,  -5271607,   2,  19,    690, 231840,1183,    519,  52095,   1 },
{  677,    -31503,  -3811863,   2,   3,    680, 229840,1176,    201, 188020,   1 },
{  683,    -42383,  -2076767,   2,  11,    696, 237336,1149,     10,  78300,   1 },
{  691,     -7167,  -3791343,   2,   3,    704, 242880,1197,    394, 203104,   1 },
{  701,    -93999, -11373879,   2,   3,    708, 247800,1192,     41,  23718,   1 },
{  709,   -922727,   -922727,   2,  13,    712, 252048,1209,    361, 138484,   1 },
{  719,   -173063,  -4326575,   2,  11,    732, 262788,1230,    628, 178974,   1 },
{  727,   -154023, -55602303,   2,   3,    730, 264990,1277,    106, 138335,   1 },
{  733,   -130855, -15833455,   2,   5,    740, 270840,1313,    691, 226070,   1 },
{  739,    -29703, -15712887,   2,   3,    748, 276012,1319,    280, 268906,   1 },
{  743,      -143,  -2234375,   2,  13,    750, 278250,1238,    285,  50625,   1 },
{  751,     -2559,  -3503271,   2,   3,    760, 285000,1283,    498, 178220,   1 },
{  757,   -270695,   -270695,   2,   5,    760, 287280,1234,    403,  89300,   1 },
{  761,    -17439,  -9225231,   2,   3,    770, 292600,1334,     41,  58135,   1 },
{  769,    -91351, -11053471,   2,  13,    790, 303360,1356,    777, 210535,   1 },
{  773,   -102239,  -8281359,   2,  19,    780, 301080,1352,    455,  87750,   1 },
{  787,    -20495,  -2479895,   2,   5,    800, 314400,1310,    565,  62000,   1 },
{  797,   -486127, -12153175,   2,  29,    804, 319992,1409,    319, 224718,   1 },
{  809,     -5631,  -2978799,   2,   3,    814, 328856,1368,    297, 121693,   1 },
{  811,  -1057823,  -1057823,   2,  13,    816, 330480,1376,    625,  32232,   1 },
{  821,   -176671,  -8656879,   2,  11,    828, 339480,1433,    149, 237222,   1 },
{  823,    -15719,  -2656511,   2,  11,    826, 339486,1367,    298,  47495,   1 },
{  827,    -46711, -63947359,   2,   7,    836, 345268,1450,    213, 199386,   1 },
{  829,   -734831,   -734831,   2,  29,    832, 344448,1378,     85,  82784,   1 },
{  839,   -461527, -11538175,   2,  11,    852, 356988,1477,    440, 294366,   1 },
{  853,   -745295,   -745295,   2,   5,    856, 364656,1420,    621, 194740,   1 },
{  857,    -50223,  -6076983,   2,   3,    860, 368080,1481,    379, 193930,   1 },
{  859,    -66567, -11249823,   2,   3,    868, 372372,1506,    704, 207886,   1 },
{  863,    -92135,  -7462935,   2,   5,    870, 374970,1498,    103, 231855,   1 },
{  877,   -237295,-228040495,   2,   5,    880, 385440,1518,    275, 284680,   1 },
{  881,   -831639,   -831639,   2,   3,    884, 388960,1487,    377, 126854,   1 },
{  883,    -76863,  -9300423,   2,   3,    900, 396900,1539,    492, 127350,   1 },
{  887,     -6455,  -5428655,   2,   5,    900, 398700,1500,    557, 211050,   1 },
{  907,   -184495, -66602695,   2,   5,    920, 416760,1582,    607, 120980,   1 },
{  911,    -56647, -20449567,   2,  37,    918, 417690,1617,    347, 407133,   1 },
{  919,    -54543,  -9217767,   2,   3,    924, 424116,1597,    720,  30954,   1 },
{  929,    -10671,  -5644959,   2,   3,    946, 438944,1581,    865, 216161,   1 },
{  937,   -188095, -22759495,   2,   5,    960, 449280,1657,    105, 337440,   1 },
{  941,    -86367, -14596023,   2,   3,    952, 447440,1649,    343,  99484,   1 },
{  947,    -14471,  -2445599,   2,  29,    952, 450296,1554,    703, 412692,   1 },
{  953,    -62695,  -7586095,   2,   5,    960, 456960,1647,     75,  52320,   1 },
{  967,     -6639,  -3512031,   2,   3,    990, 478170,1617,    212, 145035,   1 },
{  971,     -8327, -11399663,   2,  11,    988, 479180,1668,    214, 250458,   1 },
{  977,    -75567, -12770823,   2,   3,    980, 478240,1703,    627, 143570,   1 },
{  983,     -8327, -11399663,   2,  11,    988, 485108,1687,    482, 376922,   1 },
{  991,    -45807, -38523687,   2,   3,    994, 492030,1703,    744, 128723,   1 },
{  997,     -5191, -81109375,   2,  29,   1000, 498000,1739,    127, 482500,   1 },
{ 1009,    -76999,  -9316879,   2,  13,   1030, 519120,1737,    977, 377495,   1 },
{ 1013,   -830647, -20766175,   2,  29,   1020, 516120,1786,    767, 350370,   1 },
{ 1019,   -116623, -33704047,   2,  13,   1044, 531396,1810,    391, 409770,   1 },
{ 1021,    -60463, -31984927,   2,  13,   1056, 538560,1815,    475, 307824,   1 },
{ 1031,   -210767,  -5269175,   2,  19,   1056, 543840,1723,    936, 144144,   1 },
{ 1033,   -183367, -30989023,   2,  29,   1036, 534576,1835,    791, 114478,   1 },
{ 1039,    -18831,  -9961599,   2,   3,   1056, 548064,1784,    202,  85008,   1 },
{ 1049,     -9903, -13557207,   2,   3,   1064, 557536,1817,    999, 442092,   1 },
{ 1051,    -60463, -31984927,   2,  13,   1056, 554400,1866,    145, 100848,   1 },
{ 1061,    -18647,  -3151343,   2,  29,   1064, 563920,1744,    575, 312284,   1 },
{ 1063,   -120031, -14523751,   2,  29,   1070, 568170,1850,    417, 400715,   1 },
{ 1069,    -31471, -58189879,   2,  11,   1452, 775368,1819,    445, 227238,   1 },
{ 1087,    -87319, -14756911,   2,  29,   1092, 592956,1893,    461, 410046,   1 },
{ 1091,   -233951, -18950031,   2,  37,   1116, 608220,1896,    771, 513918,   1 },
{ 1093,    -82255, -29694055,   2,   5,   1100, 600600,1859,    639, 472450,   1 },
{ 1097,    -18903,  -9999687,   2,   3,   1100, 602800,1879,    131, 158950,   1 },
{ 1103,    -88135, -14894815,   2,   5,   1106, 609406,1915,    353, 405349,   1 },
{ 1109,    -19823, -14450967,   2,  43,   1116, 618264,1923,    853, 215946,   1 },
{ 1117,   -288871,-180544375,   2,  11,   1120, 624960,1950,     53, 316400,   1 },
{ 1123,   -154855,-260311255,   2,   5,   1140, 639540,1917,    749, 440610,   1 },
{ 1129,    -44143, -60431767,   2,  11,   1140, 642960,2012,    813, 619590,   1 },
{ 1151,    -20423, -10803767,   2,  13,   1166, 670450,1943,    825, 622061,   1 },
{ 1153,   -435823,-157332103,   2,  37,   1210, 696960,2009,    925, 526955,   1 },
{ 1163,   -246055, -29772655,   2,   5,   1180, 685580,2042,    151, 166970,   1 },
{ 1171,   -201063, -33979647,   2,   3,   1176, 687960,2060,     68, 641508,   1 },
{ 1181,   -138847, -50123767,   2,  43,   1188, 700920,2098,    665, 486486,   1 },
{ 1187,    -67879,-149944711,   2,   7,   1196, 709228,2063,    124, 340262,   1 },
{ 1193,    -23559,  -8504799,   2,   3,   1206, 718776,2022,    847, 390141,   1 },
{ 1201,    -43087, -58986103,   2,  11,   1216, 729600,2134,   1181, 728992,   1 },
{ 1213,   -370255,-355815055,   2,   5,   1300, 787800,2086,    143, 480350,   1 },
{ 1217,    -55655,  -6734255,   2,   5,   1220, 741760,2020,    767, 735050,   1 },
{ 1223,    -23935, -23001535,   2,   5,   1230, 751530,2141,     95, 591015,   1 },
{ 1229,    -45791,  -7738679,   2,  29,   1232, 756448,2044,   1079, 461384,   1 },
{ 1231,    -11103, -24526527,   2,   3,   1242, 763830,2146,    656, 358317,   1 },
{ 1237,   -569095,-205443295,   2,   5,   1240, 766320,2156,   1005,  62620,   1 },
{ 1249,   -422647,-152575567,   2,  43,   1260, 786240,2177,    595, 423990,   1 },
{ 1259,   -148343, -12015783,   2,  13,   1272, 800088,2149,    601, 491628,   1 },
{ 1277,     -9903, -21875727,   2,   3,   1288, 821744,2208,    707, 611156,   1 },
{ 1279,    -23519,  -3974711,   2,  29,   1288, 823032,2080,    957, 146188,   1 },
{ 1283,    -72583,-160335847,   2,   7,   1288, 825608,2233,    403, 488796,   1 },
{ 1289,     -4791,  -6558879,   2,   3,   1292, 832048,2149,    779, 421838,   1 },
{ 1291,    -99543, -16822767,   2,   3,   1316, 848820,2220,    424,  40138,   1 },
{ 1297,    -73655,  -8912255,   2,   5,   1300, 842400,2162,    971, 229450,   1 },
{ 1301,    -28047, -14836863,   2,   3,   1320, 858000,2227,   1055,  73260,   1 },
{ 1303,   -249663, -30209223,   2,   3,   1320, 859320,2273,    758, 830940,   1 },
{ 1307,   -506543, -12663575,   2,  29,   1320, 861960,2205,     29,  21780,   1 },
{ 1319,     -8903, -12188207,   2,  29,   1330, 876470,2214,    809, 387695,   1 },
{ 1321,   -240103, -40577407,   2,  19,   1414, 933240,2320,   1327, 382487,   1 },
{ 1327,    -22615, -30959935,   2,   5,   1330, 881790,2319,    261, 629755,   1 },
{ 1361,    -66567, -35213943,   2,   3,   1364, 927520,2376,     17, 759066,   1 },
{ 1367,     -3935,  -7275815,   2,   5,   1386, 946638,2259,     17, 104643,   1 },
{ 1373,    -32455, -31189255,   2,   5,   1380, 946680,2391,    559, 531990,   1 },
{ 1381,    -33407, -61769543,   2,  11,   1428, 985320,2266,    127,   4998,   1 },
{ 1399,    -85551, -71948391,   2,   3,   1414, 988386,2380,    110, 687911,   1 },
{ 1409,   -192679, -32562751,   2,  19,   1414, 995456,2451,    377, 897183,   1 },
{ 1423,    -20039,  -3386591,   2,  29,   1428,1015308,2341,    473, 270606,   1 },
{ 1427,   -390895, -47298295,   2,   5,   1440,1026720,2505,    673,  48240,   1 },
{ 1429,    -68167, -93320623,   2,  11,   1596,1139544,2524,    983, 473214,   1 },
{ 1433,     -8207,  -5129375,   2,  29,   1440,1031040,2326,    677, 464400,   1 },
{ 1439,     -4631,  -6339839,   2,  11,   1444,1038236,2352,    808, 392046,   1 },
{ 1447,     -1983, -56636463,   2,   3,   1456,1052688,2540,    598,  69160,   1 },
{ 1451,   -337111, -56971759,   2,  23,   1456,1055600,2457,   1213,1035944,   1 },
{ 1453,   -375055,-315421255,   2,   5,   1460,1059960,2490,   1235, 898630,   1 },
{ 1459,    -24663, -54480567,   2,   3,   1472,1073088,2558,    226, 140576,   1 },
{ 1471,     -6999, -15460791,   2,   3,   1518,1115730,2484,    390, 820479,   1 },
{ 1481,    -26279, -19157391,   2,  11,   1494,1105560,2518,    979, 859797,   1 },
{ 1483,   -365727, -44252967,   2,   3,   1500,1111500,2577,    124, 261750,   1 },
{ 1487,   -142063, -41056207,   2,  19,   1494,1110042,2595,    158, 463887,   1 },
{ 1489,   -120031,-221937319,   2,  29,   1498,1114512,2538,    477, 250915,   1 },
{ 1493,     -2407, -37609375,   2,  29,   1500,1119000,2601,   1403, 489750,   1 },
{ 1499,   -299167,-107999287,   2,  11,   1512,1132488,2657,    604, 327348,   1 },
{ 1511,    -79607, -13453583,   2,  11,   1526,1152130,2518,    108, 997241,   1 },
{ 1523,   -273151, -46162519,   2,  29,   1540,1171940,2653,    117, 467390,   1 },
{ 1531,    -48567, -25691943,   2,   3,   1540,1178100,2631,    336, 476630,   1 },
{ 1543,     -6023,  -8245487,   2,  19,   1558,1201218,2538,   1278, 985435,   1 },
{ 1549,    -95903, -16207607,   2,  29,   1596,1235304,2586,    711,   8778,   1 },
{ 1553,    -73663, -46039375,   2,  19,   1560,1210560,2714,    125,  95940,   1 },
{ 1559,   -252367, -42650023,   2,  43,   1568,1221472,2716,    800, 513520,   1 },
{ 1567,   -104079, -12593559,   2,   3,   1580,1237140,2628,   1322,  60830,   1 },
{ 1571,    -94303,-174366247,   2,  11,   1584,1243440,2713,    716, 460152,   1 },
{ 1579,    -10551, -23307159,   2,   3,   1656,1306584,2685,    986, 348588,   1 },
{ 1583,     -1007,  -2828663,   2,  19,   1590,1257690,2619,     30,1194885,   1 },
{ 1597,   -107495, -90403295,   2,   5,   1600,1276800,2619,   1535, 815200,   1 },
{ 1601,   -279071, -22604751,   2,  13,   1608,1286400,2723,    505, 565212,   1 },
{ 1607,   -431215, -72875335,   2,   5,   1610,1292830,2821,    175, 900795,   1 },
{ 1609,   -145447,-408560623,   2,  37,   1612,1296048,2791,   1401, 895466,   1 },
{ 1613,    -37543,-105458287,   2,  11,   1620,1305720,2847,   1435, 859410,   1 },
{ 1619,   -180791, -14644071,   2,  13,   1632,1320288,2720,    493, 880464,   1 },
{ 1621,     -2279,  -6401711,   2,  43,   2968,2404080,2695,    499, 292348,   1 },
{ 1627,   -500095, -60511495,   2,   5,   1640,1333320,2848,    649, 394420,   1 },
{ 1637,    -42095, -15196295,   2,   5,   1656,1354608,2727,    419,1305756,   1 },
{ 1657,   -352855, -42695455,   2,   5,   1660,1374480,2874,     91,1010110,   1 },
{ 1663,   -119199, -20144631,   2,   3,   1680,1396080,2804,    782,1240680,   1 },
{ 1667,    -92695, -77956495,   2,   5,   1680,1399440,2926,    973, 435960,   1 },
{ 1669,   -160927, -85130383,   2,  13,   1804,1504536,2925,    459, 910118,   1 },
{ 1693,   -229855, -27812455,   2,   5,   1700,1438200,2901,    645,1199350,   1 },
{ 1697,    -56271,  -9509799,   2,   3,   1708,1448384,2806,    557, 313418,   1 },
{ 1699,    -56271,  -9509799,   2,   3,   1708,1450092,2806,    364, 393694,   1 },
{ 1709,   -380263,-703106287,   2,  13,   1716,1465464,2954,    563,  38610,   1 },
{ 1721,   -377807, -30602367,   2,  37,   1728,1486080,2945,     53, 616032,   1 },
{ 1723,   -325855, -39428455,   2,   5,   1740,1498140,2967,   1127,1144050,   1 },
{ 1733,    -69487, -43429375,   2,  11,   1740,1506840,2995,    631, 573330,   1 },
{ 1741,    -63751,-140825959,   2,  37,   3680,3201600,2966,   1737,1433360,   1 },
{ 1747,   -385527, -46648767,   2,   3,   1760,1536480,3019,     22,1371920,   1 },
{ 1753,    -73223, -12374687,   2,  37,   1778,1557528,2915,    643,1286383,   1 },
{ 1759,   -125679, -21239751,   2,   3,   1764,1550556,2972,   1024,1306242,   1 },
{ 1777,   -279655, -33838255,   2,   5,   1780,1580640,3048,   1465,  20470,   1 },
{ 1783,   -396327, -47955567,   2,   3,   1800,1603800,3081,    884, 917100,   1 },
{ 1787,    -27151, -26092111,   2,  19,   1800,1607400,3044,   1334, 706500,   1 },
{ 1789,   -143767, -76052743,   2,  13,   1804,1612776,3131,    891, 855998,   1 },
{ 1801,     -2407, -68746327,   2,  29,   1820,1638000,3140,    103, 452270,   1 },
{ 1811,  -2047687, -51192175,   2,  19,   1824,1650720,3138,    934,1489296,   1 },
{ 1823,    -11735, -11277335,   2,   5,   1830,1667130,3076,    473,1549095,   1 },
{ 1831,   -106719, -89750679,   2,   3,   1834,1678110,3080,   1076,1436939,   1 },
{ 1847,       -55, -50793655,   2,   5,   1860,1716780,3187,    511, 614730,   1 },
{ 1861,    -71159,-131572991,   2,  11,   1932,1796760,3101,    693,  28014,   1 },
{ 1867,   -925303,-156376207,   2,  29,   1876,1750308,3292,    145,1655570,   1 },
{ 1871,  -1019959, -49977991,   2,  29,   1884,1761540,3224,   1407,1557126,   1 },
{ 1873,   -640495,-538656295,   2,   5,   1904,1782144,3239,   1259, 855848,   1 },
{ 1877,   -286887, -34713327,   2,   3,   1880,1763440,3200,    845, 343100,   1 },
{ 1879,    -83863, -44363527,   2,  13,   1892,1776588,3233,    845,  12298,   1 },
{ 1889,    -35431, -48505039,   2,  11,   1900,1793600,3252,    933,1741350,   1 },
{ 1901,    -27399, -60524391,   2,   3,   1932,1835400,3275,    715,1625778,   1 },
{ 1907,    -15095, -14506295,   2,   5,   1920,1829760,3229,    251,1316160,   1 },
{ 1913,   -294535, -49776415,   2,   5,   1918,1833608,3297,   1279,1082711,   1 },
{ 1931,     -6383, -41878863,   2,  13,   1944,1875960,3303,   1001,1076004,   1 },
{ 1933,   -103655, -12542255,   2,   5,   1940,1874040,3287,    813, 623710,   1 },
{ 1949,   -195807, -23692647,   2,   3,   1960,1909040,3285,    113, 553700,   1 },
{ 1951,   -173487, -29319303,   2,   3,   1960,1911000,3303,    446, 510580,   1 },
{ 1973,    -31071, -16436559,   2,   3,   1980,1952280,3304,    765,1549350,   1 },
{ 1979,   -385799, -31249719,   2,  37,   1992,1970088,3346,   1881,1660332,   1 },
{ 1987,    -96095, -11627495,   2,   5,   2000,1986000,3377,    949,1669000,   1 },
{ 1993,   -126695, -15330095,   2,   5,   2000,1992000,3389,   1295,1381000,   1 },
{ 1997,    -96095, -11627495,   2,   5,   2000,1996000,3398,   1207,1361000,   1 },
{ 1999,   -222623, -37623287,   2,  19,   2002,1999998,3365,    430, 865865,   1 },
{ 2003,   -239695, -86529895,   2,   5,   2016,2018016,3486,   1033, 789264,   1 },
{ 2011,   -105159, -17771871,   2,   3,   2016,2026080,3382,   1624, 763056,   1 },
{ 2017,    -55135, -75479815,   2,   5,   2090,2106720,3491,   1763, 107635,   1 },
{ 2027,   -165895,-139517695,   2,   5,   2040,2066520,3552,   1995, 823140,   1 },
{ 2029,   -101047,-223212823,   2,  37,   2208,2238912,3569,    813,  51888,   1 },
{ 2039,     -1351,-176063671,   2,   7,   2052,2090988,3463,   1936,2020194,   1 },
{ 2053,    -97655, -11816255,   2,   5,   2060,2113560,3497,   1677,1305010,   1 },
{ 2063,   -198095, -23969495,   2,   5,   2080,2144480,3508,    925, 720720,   1 },
{ 2069,    -63191, -10679279,   2,  29,   2072,2142448,3518,   1493,1449364,   1 },
{ 2081,    -66407, -23972927,   2,  11,   2088,2171520,3538,    147, 232812,   1 },
{ 2083,   -258591, -43701879,   2,   3,   2100,2186100,3544,    278, 610050,   1 },
{ 2087,    -18823,-275587543,   2,   7,   2090,2179870,3584,    839,1054405,   1 },
{ 2089,   -266807, -32283647,   2,  37,   2100,2192400,3511,    311, 435750,   1 },
{ 2099,   -193999,-102625471,   2,  13,   2112,2215488,3651,   1525,2159520,   1 },
{ 2111,   -378991, -64049479,   2,  37,   2114,2230270,3639,   1993,2022041,   1 },
{ 2113,    -90215, -15246335,   2,   5,   2142,2261952,3610,    263, 328797,   1 },
{ 2129,    -38751, -20499279,   2,   3,   2134,2270576,3605,    319, 287023,   1 },
{ 2131,   -170319, -28783911,   2,   3,   2156,2296140,3581,    370,2239006,   1 },
{ 2137,   -163015, -27549535,   2,   5,   2142,2287656,3613,   1659,2209473,   1 },
{ 2141,   -597143, -48368583,   2,  37,   2148,2298360,3659,    363,1826874,   1 },
{ 2143,      -247, -32189287,   2,  13,   2166,2319786,3772,   1207,1762041,   1 },
{ 2153,   -170319, -28783911,   2,   3,   2156,2319856,3624,   1609, 527142,   1 },
{ 2161,    -52519,-147525871,   2,  29,   2184,2358720,3648,    683,2327052,   1 },
{ 2179,     -7271,  -9953999,   2,  11,   2204,2400156,3687,    752,2183062,   1 },
{ 2203,   -248511, -30069831,   2,   3,   2220,2444220,3723,    910, 926850,   1 },
{ 2207,  -2240743,-271129903,   2,  29,   2210,2437630,3881,    561,1963585,   1 },
{ 2213,   -538743, -65187903,   2,   3,   2220,2455320,3794,    291, 589410,   1 },
{ 2221,   -506623,-426069943,   2,  13,   2296,2548560,3817,   1551,2046884,   1 },
{ 2237,    -71751, -37956279,   2,   3,   2244,2508792,3773,   1031, 968286,   1 },
{ 2239,    -51159, -27063111,   2,   3,   2244,2511036,3809,    832,1132098,   1 },
{ 2243,  -1101503, -89221743,   2,  13,   2256,2528976,3866,   1183,   3384,   1 },
{ 2251,    -42791, -58580879,   2,   7,   2280,2565000,3816,   1803, 717060,   1 },
{ 2267,  -1564823,-126750663,   2,  13,   2280,2583240,3937,   1563,1346340,   1 },
{ 2269,    -84839, -30626879,   2,  43,   2400,2721600,3830,   1021, 632400,   1 },
{ 2273,    -89407, -55879375,   2,  29,   2280,2590080,3883,   2229,1145700,   1 },
{ 2281,    -96967, -51295543,   2,  13,   2288,2608320,3900,    523,2401256,   1 },
{ 2287,   -301503, -50954007,   2,   3,   2296,2624328,3890,   1592,1068788,   1 },
{ 2293,   -413047, -69804943,   2,  29,   2296,2631216,3944,    473, 790972,   1 },
{ 2297,    -51063, -31914375,   2,   3,   2310,2651880,3903,   1375,2569875,   1 },
{ 2309,   -572279, -46354599,   2,  37,   2316,2672664,3898,   1205,1075782,   1 },
{ 2311,    -56607,-125044863,   2,   3,   2346,2709630,4002,   2186,1709061,   1 },
{ 2333,    -40055, -38492855,   2,   5,   2340,2728440,4001,   1899,1664910,   1 },
{ 2339,   -372479, -30170799,   2,  37,   2352,2749488,3998,   2227,2070936,   1 },
{ 2341,   -319783,-169165207,   2,  29,   2508,2934360,4079,   1787,2097942,   1 },
{ 2347,    -39743, -54408167,   2,  11,   2356,2763588,3999,   1968,1294622,   1 },
{ 2351,   -205231, -74088391,   2,  13,   2358,2770650,4027,   1403, 173313,   1 },
{ 2357,  -1889263, -47231575,   2,  29,   2376,2798928,4007,   2133, 588060,   1 },
{ 2371,   -357303,-189013287,   2,   3,   2376,2815560,4130,   1800,1982772,   1 },
{ 2377,   -602815,-101875735,   2,   5,   2394,2844072,4107,    575,1897245,   1 },
{ 2381,  -1360823,-110226663,   2,  37,   2388,2841720,4104,    837,2410686,   1 },
{ 2383,    -74335,-101764615,   2,   5,   2394,2851254,4121,     97,2160585,   1 },
{ 2389,  -1544983,-557738863,   2,  11,   2400,2865600,4105,    593,2751600,   1 },
{ 2393,     -1943, -30359375,   2,  29,   2400,2870400,4122,    393,2634000,   1 },
{ 2399,   -519607,-187578127,   2,  11,   2412,2891988,4190,   1488, 334062,   1 },
{ 2411,   -331799, -26875719,   2,  13,   2424,2920920,4117,   2135,2461572,   1 },
{ 2417,    -73551, -38908479,   2,   3,   2420,2923360,4127,   1277,1692790,   1 },
{ 2423,      -815, -48124935,   2,   5,   2430,2942730,4134,   1957, 579555,   1 },
{ 2437,   -688039,-430024375,   2,  11,   2460,2996280,4180,    347,1578090,   1 },
{ 2441,   -139647, -73873263,   2,   3,   2464,3006080,4171,   1989, 582736,   1 },
{ 2447,  -1497463,-253071247,   2,  11,   2450,2996350,4287,   1872,2022475,   1 },
{ 2459,   -869999, -70469919,   2,  13,   2472,3038088,4177,   1527,1934340,   1 },
{ 2467,   -534063, -64621623,   2,   3,   2480,3057840,4199,   2082, 536920,   1 },
{ 2473,   -319783,-169165207,   2,  29,   2508,3099888,4306,   1067,   8778,   1 },
{ 2477,    -22759, -63930031,   2,  11,   2484,3075192,4219,    465,2301426,   1 },
{ 2503,   -329335, -55657615,   2,   5,   2506,3135006,4264,   1727,1254253,   1 },
{ 2521,    -96367,-131926423,   2,  29,   2622,3303720,4354,   1879, 667299,   1 },
{ 2531,  -1163807, -29095175,   2,  19,   2544,3218160,4361,   1804,2832744,   1 },
{ 2539,   -271191, -45831279,   2,   3,   2548,3233412,4354,   1876,2330146,   1 },
{ 2543,     -4303, -67234375,   2,  13,   2550,3241050,4334,    495,1521075,   1 },
{ 2549,   -132407, -47798927,   2,  11,   2556,3256344,4403,   1839,2651850,   1 },
{ 2551,   -292143, -49372167,   2,   3,   2576,3284400,4363,   2342,2721544,   1 },
{ 2557,     -5855, -29515055,   2,   5,   2660,3399480,4393,   2513,2288930,   1 },
{ 2579,     -6071, -39831831,   2,  13,   2592,3341088,4429,   1539,2938032,   1 },
{ 2591,  -3409303, -85232575,   2,  19,   2604,3372180,4444,   1038,3251094,   1 },
{ 2593,   -211895, -25639295,   2,   5,   2600,3369600,4450,   2155,1522300,   1 },
{ 2609,    -56247,-124249623,   2,   3,   2622,3419088,4488,   1055,1359507,   1 },
{ 2617,   -272591, -98405351,   2,  11,   2620,3426960,4445,   2395, 643210,   1 },
{ 2621,    -86567, -63107343,   2,  13,   2628,3442680,4504,     31,3023514,   1 },
{ 2633,   -939263, -76080303,   2,  13,   2640,3474240,4510,   1189,1904760,   1 },
{ 2647,  -1627567,-196935607,   2,  29,   2650,3505950,4610,    601, 128525,   1 },
{ 2657,   -158871, -26849199,   2,   3,   2660,3532480,4544,    131,2557590,   1 },
{ 2659,   -164687, -19927127,   2,  37,   2680,3561720,4544,   1219,1400300,   1 },
{ 2663,   -113927, -95812607,   2,  11,   2670,3553770,4588,   1570,1384395,   1 },
{ 2671,    -87231, -46145199,   2,   3,   2684,3583140,4587,   1194,1601006,   1 },
{ 2677,   -191623,-538269007,   2,  37,   3328,4452864,4543,   2209,2204800,   1 },
{ 2683,   -807655, -97726255,   2,   5,   2700,3620700,4601,    261,2965950,   1 },
{ 2687,    -68063, -93178247,   2,  29,   2698,3623414,4633,     31,   1349,   1 },
{ 2689,  -1892743,-683280223,   2,  29,   2710,3642240,4614,   2085,2163935,   1 },
{ 2693,     -7543,-117859375,   2,  19,   2700,3634200,4639,   1269, 687150,   1 },
{ 2699,    -47927,-134626943,   2,  11,   2704,3647696,4604,    106,3129880,   1 },
{ 2707,   -103655, -87173855,   2,   5,   2716,3674748,4601,    983,2934638,   1 },
{ 2711,   -175487, -63350807,   2,  13,   2718,3682890,4693,   1931, 775989,   1 },
{ 2713,   -575495, -69634895,   2,   5,   2720,3688320,4689,    527, 654160,   1 },
{ 2719,    -94551,-265593759,   2,   3,   2730,3710070,4611,   2684,  99645,   1 },
{ 2729,   -334927, -96793903,   2,  43,   2736,3731904,4670,   1957,3128616,   1 },
{ 2731,    -66583, -91152127,   2,  11,   2736,3734640,4682,   1782, 452808,   1 },
{ 2741,    -86159, -14560871,   2,  29,   2744,3759280,4700,   1551,3746932,   1 },
{ 2749,    -89687, -47444423,   2,  13,   2772,3808728,4754,   1181,2634786,   1 },
{ 2753,    -24807, -54798663,   2,   3,   2760,3797760,4720,   1107, 335340,   1 },
{ 2767,   -255287, -43143503,   2,  29,   2772,3833676,4777,    877,3782394,   1 },
{ 2777,    -84935, -81622535,   2,   5,   2790,3872520,4808,   2671,1315485,   1 },
{ 2789,   -311511, -52645359,   2,   3,   2800,3903200,4793,   1757,1281000,   1 },
{ 2791,   -180087, -95266023,   2,   3,   2794,3897630,4788,   2518,3605657,   1 },
{ 2797,    -81743,-229616087,   2,  43,   2808,3925584,4781,   1475,1818180,   1 },
{ 2801,    -36447, -80511423,   2,   3,   2806,3928400,4813,   1779,1042429,   1 },
{ 2803,   -447807, -54184647,   2,   3,   2820,3950820,4794,   2584,2096670,   1 },
{ 2819,   -350831, -28417311,   2,  13,   2832,3990288,4853,   1375,3575400,   1 },
{ 2833,   -414695, -50178095,   2,   5,   2840,4021440,4898,   2347,1574780,   1 },
{ 2837,   -414695, -50178095,   2,   5,   2840,4027120,4910,    231,1844580,   1 },
{ 2843,       -95, -12380495,   2,   5,   2888,4103848,4947,     87, 680124,   1 },
{ 2851,   -399783, -67563327,   2,   3,   2856,4069800,4890,   1272, 469812,   1 },
{ 2857,   -145151, -17563271,   2,  37,   2860,4084080,4899,    897,2555410,   1 },
{ 2861,    -9903,-2771265423,   2,   3,   3864,5525520,3552,   3823,3904572,   1 },
{ 2879,   -646207,-341843503,   2,  29,   2882,4147198,5032,    753,3491543,   1 },
{ 2887,  -1648207,-278546983,   2,  11,   2898,4181814,5030,   2012,1702575,   1 },
{ 2897,     -5583,-159456063,   2,   3,   2912,4216576,4981,   1227,2383472,   1 },
{ 2903,   -484255,-174816055,   2,   5,   2916,4231116,5011,   1811,2159298,   1 },
{ 2909,    -12407, -81402327,   2,  19,   2916,4239864,5032,   2551,2984526,   1 },
{ 2917,   -238895, -28906295,   2,   5,   2920,4257360,5025,   2405,4022300,   1 },
{ 2927,   -122735, -89473815,   2,   5,   2934,4292442,5062,   2061,1568223,   1 },
{ 2939,     -2279,  -6401711,   2,  43,   2968,4359992,5089,     42,1423156,   1 },
{ 2953,   -272215,-503325535,   2,   5,   2970,4383720,5047,   1531,3865455,   1 },
{ 2957,   -259599, -43872231,   2,   3,   2968,4386704,5069,   1509,4189332,   1 },
{ 2963,  -1660879, -81383071,   2,  11,   2976,4407456,5111,    384,2837616,   1 },
{ 2969,   -505623, -61180383,   2,   3,   2980,4422320,5089,    999,4346330,   1 },
{ 2971,    -26351, -74019959,   2,  13,   3016,4478760,5066,   1031,2740036,   1 },
{ 2999,   -118639, -62760031,   2,  29,   3014,4517986,5170,   2281,3117983,   1 },
{ 3001,   -295279,-248329639,   2,  19,   3010,4515000,5122,     77,3384745,   1 }
#endif
};

static const modpoly_disc_info *
get_disc_info_for_level(long L)
{
  long imin, imax, imid;
  if (L < 5)
    pari_err_BUG("get_disc_info_for_level");

  if (L > 3001)
    pari_err_IMPL("Do not yet have discriminants for L > 3001");

  /* Binary search for L. */
  imin = 0;
  imax = DISC_TABLE_LENGTH;
  while (imin < imax) {
    imid = (imin + imax) / 2;
    if (DISC_TABLE[imid].L < L)
      imin = imid + 1;
    else
      imax = imid;
  }
  if (imax != imin || DISC_TABLE[imin].L != L) {
    pari_err_BUG("get_disc_info_for_level: "
                 "Did not find given level in discriminant table "
                 "(are you sure it's prime?)");
  }
  return &DISC_TABLE[imin];
}


static const modpoly_disc_info *
discriminant_with_classno_at_least(
  long *D, ulong *u, ulong *v, /* GEN *alpha, GEN *beta, */ ulong L)
{
  const modpoly_disc_info *dinfo = 0;
  pari_sp av = avma;

  dinfo = get_disc_info_for_level(L);
  *D = dinfo->D1;

  (void) corediscs(*D, u);
  avma = av;

  *v = (-*D % 8 == 7) ? 2 : 1;
  dbg_printf2(2, "-D %% 8 == %lu, selecting vsqr = %lu",
              -*D % 8, *v * *v);
  return dinfo;
}
