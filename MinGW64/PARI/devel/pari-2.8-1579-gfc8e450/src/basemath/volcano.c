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

/* Is j = 0 or 1728 (mod p)? */
INLINE int
is_j_exceptional(ulong j, ulong p)
{
  return j == 0 || j == 1728 % p;
}


INLINE long
node_degree(GEN phi, long L, ulong j, ulong p, ulong pi)
{
  pari_sp av = avma;
  long n = Flx_nbroots(Flm_Fl_polmodular_evalx(phi, L, j, p, pi), p);
  avma = av;
  return n;
}


/*
 * Given an array path = [j0, j1] of length 2, return the polynomial
 *
 *   \Phi_L(X, j1) / (X - j0)
 *
 * where \Phi_L(X, Y) is the modular polynomial of level L.  An error
 * is raised if X - j0 does not divide \Phi_L(X, j1).
 */
INLINE GEN
nhbr_polynomial(ulong path[], GEN phi, ulong p, ulong pi, long L)
{
  pari_sp ltop = avma;
  GEN modpol = Flm_Fl_polmodular_evalx(phi, L, path[0], p, pi);

  /* Note that, if the discriminant of End(path[0]) is less than L^2,
   * then it's possible for path[0] to appear among the roots of
   * nhbr_pol.  This case should have been obviated by earlier
   * choices. */
  ulong rem = 0;
  GEN nhbr_pol = Flx_div_by_X_x(modpol, path[-1], p, &rem);
  if (rem)
    pari_err_BUG("nhbr_polynomial: invalid preceding j");
  return gerepileupto(ltop, nhbr_pol);
}

/* This function assumes the volcano is a 2-volcano of depth 1, with
 * path[0] and path[1] already on the surface. */
static long
walk_surface_of_2_volcano(
  ulong path[], GEN phi, GEN first_nhbr_pol, ulong p, ulong pi, long max_len)
{
  enum { L = 2 };
  pari_sp av = avma;
  long d = 1;
  GEN nhbr_pol = first_nhbr_pol;
  for ( ; d < max_len && path[0] != path[d]; ++d) {
    GEN rts = Flx_roots(nhbr_pol, p);
    if (lg(rts) != 3) {
      char *err = stack_sprintf("walk_surface_of_2_volcano: got %ld "
                                "roots but expected 2", lg(rts) - 1);
      pari_err_BUG(err);
    }
    path[d + 1] = rts[1];
    nhbr_pol = nhbr_polynomial(path + d + 1, phi, p, pi, L);
    if (Flx_nbroots(nhbr_pol, p) == 0) {
      path[d + 1] = rts[2];
      if (d + 1 < max_len)
        nhbr_pol = nhbr_polynomial(path + d + 1, phi, p, pi, L);
    }
    nhbr_pol = gerepileupto(av, nhbr_pol);
  }
  avma = av;
  return d;
}


/*
 * Assumes path is an array with space for at least max_len + 1
 * elements, whose first and second elements are the beginning of the
 * path.  I.e., the path starts
 *
 *   (path[0], path[1])
 *
 * If the result is less than max_len, then the last element of path
 * is definitely on the floor.  If the result equals max_len, then in
 * general it is unknown whether the last element of path is on the
 * floor or not.
 */
static long
extend_path(
  ulong path[], GEN phi, ulong p, ulong pi, long L, long max_len)
{
  pari_sp av = avma;
  long d = 1;
  for ( ; d < max_len; ++d) {
    ulong nhbr;
    GEN nhbr_pol;

    nhbr_pol = nhbr_polynomial(path + d, phi, p, pi, L);
    nhbr = Flx_oneroot(nhbr_pol, p);
    avma = av;
    /* Flx_oneroot didn't find a root; so we must be on the floor. */
    if (nhbr == p)
      break;
    path[d + 1] = nhbr;
  }
  return d;
}


/*
 * This is Sutherland 2009 Algorithm Ascend (p12).
 */
ulong
ascend_volcano(
  GEN phi, ulong j, ulong p, ulong pi, long level, long L,
  long depth, long steps)
{
  pari_sp ltop = avma, av;
  /* path will never hold more than max_len elements, and max_len <
   * depth always. */
  GEN path_g = cgetg(depth + 2, t_VECSMALL);
  ulong *path = (ulong *)&path_g[1];
  long max_len = depth - level;
  int first_iter = 1;

  if (steps <= 0 || max_len < 0)
    pari_err_BUG("ascend_volcano: bad params");

  av = avma;
  while (steps--) {
    GEN nhbr_pol = first_iter
      ? Flm_Fl_polmodular_evalx(phi, L, j, p, pi)
      : nhbr_polynomial(path + 1, phi, p, pi, L);
    GEN nhbrs = Flx_roots(nhbr_pol, p);
    long nhbrs_len = lg(nhbrs) - 1, i;
    pari_sp btop = avma;
    path[0] = j;
    first_iter = 0;

    j = nhbrs[nhbrs_len];
    for (i = 1; i < nhbrs_len; ++i) {
      ulong next_j = nhbrs[i], last_j;
      long len;
      if (is_j_exceptional(next_j, p)) {
        /* According to Fouquet & Morain, Section 4.3, if j = 0 or
         * 1728, then it is necessarily on the surface.  So we just
         * return it. */
        if (steps) {
          pari_err_BUG("ascend_volcano: "
                       "Got to the top with more steps to go!");
        }
        j = next_j;
        break;
      }
      path[1] = next_j;
      len = extend_path(path, phi, p, pi, L, max_len);
      last_j = path[len];
      if (len == max_len
          /* Ended up on the surface */
          && (is_j_exceptional(last_j, p)
              || node_degree(phi, L, last_j, p, pi) > 1)) {
        j = next_j;
        break;
      }
      avma = btop;
    }
    path[1] = j; /* For nhbr_polynomial() at the top. */

    ++max_len;
    avma = av;
  }
  avma = ltop;
  return j;
}


static void
random_distinct_neighbours_of(
  ulong *nhbr1, ulong *nhbr2,
  GEN phi, ulong j, ulong p, ulong pi, long L,
  long must_have_two_neighbours)
{
  pari_sp ltop = avma;
  GEN modpol = Flm_Fl_polmodular_evalx(phi, L, j, p, pi);
  ulong rem;
  *nhbr1 = Flx_oneroot(modpol, p);
  if (*nhbr1 == p) {
    /* Didn't even find one root! */
    char *err = stack_sprintf("random_distinct_neighbours_of: "
                              "No neighbours for j = %lu (mod %lu) "
                              "in %lu-volcano.", j, p, L);
    pari_err_BUG(err);
  }
  modpol = Flx_div_by_X_x(modpol, *nhbr1, p, &rem);
  *nhbr2 = Flx_oneroot(modpol, p);
  if (must_have_two_neighbours && *nhbr2 == p) {
    /* Didn't find distinct root! */
    char *err = stack_sprintf("random_distinct_neighbours_of: "
                              "Only one neighbour for j = %lu (mod %lu) "
                              "in %lu-volcano.", j, p, L);
    pari_err_BUG(err);
  }
  avma = ltop;
}


/*
 * This is Sutherland 2009 Algorithm Descend (p12).
 */
ulong
descend_volcano(
  GEN phi, ulong j, ulong p, ulong pi,
  long level, long L, long depth, long steps)
{
  pari_sp ltop = avma;
  GEN path_g;
  ulong *path, res;
  long max_len;

  if (steps <= 0 || level + steps > depth)
    pari_err_BUG("descend_volcano: bad params");

  max_len = depth - level;
  path_g = cgetg(max_len + 1 + 1, t_VECSMALL);
  path = (ulong *)&path_g[1];
  path[0] = j;
  /* level = 0 means we're on the volcano surface... */
  if ( ! level) {
    /* Look for any path to the floor.  One of j's first three
     * neighbours must lead to the floor, since at most two neighbours
     * are on the surface. */
    GEN nhbrs = Flx_roots(Flm_Fl_polmodular_evalx(phi, L, j, p, pi), p);
    long i;
    for (i = 1; i <= 3; ++i) {
      long len;
      path[1] = nhbrs[i];
      len = extend_path(path, phi, p, pi, L, max_len);
      /* If nhbrs[i] took us to the floor: */
      if (len < max_len || node_degree(phi, L, path[len], p, pi) == 1)
        break;
    }

    if (i > 3) {
      pari_err_BUG("descend_volcano: "
                   "None of three neighbours lead to the floor");
    }
  } else {
    ulong nhbr1, nhbr2;
    long len;
    random_distinct_neighbours_of(&nhbr1, &nhbr2, phi, j, p, pi, L, 1);
    path[1] = nhbr1;
    len = extend_path(path, phi, p, pi, L, max_len);
    /* If last j isn't on the floor */
    if (len == max_len   /* Ended up on the surface. */
        && (is_j_exceptional(path[len], p)
            || node_degree(phi, L, path[len], p, pi) != 1)) {
      /* The other neighbour leads to the floor */
      path[1] = nhbr2;
      (void) extend_path(path, phi, p, pi, L, steps);
    }
  }
  res = path[steps];
  avma = ltop;
  return res;
}


long
j_level_in_volcano(
  GEN phi, ulong j, ulong p, ulong pi, long L, long depth)
{
  pari_sp av = avma;
  GEN chunk;
  ulong *path1, *path2;
  long lvl;

  if (depth == 0 || is_j_exceptional(j, p)) {
    /* According to Fouquet & Morain, Section 4.3, if j = 0 or 1728,
     * then it is necessarily on the surface.  Also, if the volcano
     * depth is zero then j necessarily has level 0. */
    return 0;
  }

  chunk = new_chunk(2 * (depth + 1));
  path1 = (ulong *) &chunk[0];
  path2 = (ulong *) &chunk[depth + 1];

  path1[0] = path2[0] = j;

  random_distinct_neighbours_of(&path1[1], &path2[1],
                                phi, j, p, pi, L, 0);
  if (path2[1] == p) {
    /* Only found one neighbour, hence j is on the floor, hence
     * level == depth. */
    lvl = depth;
  } else {
    long path1_len = extend_path(path1, phi, p, pi, L, depth);
    long path2_len = extend_path(path2, phi, p, pi, L, path1_len);
    lvl = depth - path2_len;
  }
  avma = av;
  return lvl;
}


/*
 * path should have space for at least (d + max_len + 1) ulongs.  Its
 * first element should be the j-invariant at the start of the path.
 * Returns length of the path obtained (which may be less than
 * max_len; note that the path length is *one less* than the number of
 * elements in path).
 */
long
walk_surface_path(
  ulong path[], GEN phi, ulong p, ulong pi,
  long L, long depth, long max_len)
{
  pari_sp ltop = avma;
  GEN nhbrs, modpol;
  ulong *path_curr, *path_end;
  long nhbr_idx;
  if (max_len <= 0)
    pari_err_BUG("walk_surface_path: bad max_len");

  modpol = Flm_Fl_polmodular_evalx(phi, L, path[0], p, pi);
  nhbrs = Flx_roots(modpol, p);
  if (lg(nhbrs) == 1) {
    char *err = stack_sprintf("walk_surface_path: "
                              "No neighbours in %lu-volcano of j = %lu "
                              "(mod %lu)", L, path[0], p);
    pari_err_BUG(err);
  }

  path[1] = nhbrs[1];
  if (lg(nhbrs) == 2) {
    avma = ltop;
    return 1;
  }

  /* Handle frequently occurring special case.  Note that, if L = 2
   * (and (D|L) = 1 as usual), then necessarily depth > 0, since the
   * degree of \Phi_2(X, j1)/(X - j0) is 2 and both roots are either
   * rational or both not. */
  if (L == 2 && depth == 1) {
    long len;
    /* If we didn't pick the correct neighbour above, select the next
     * one. */
    modpol = nhbr_polynomial(path + 1, phi, p, pi, L);
    if (Flx_nbroots(modpol, p) == 0) {
      path[1] = nhbrs[2];
      modpol = nhbr_polynomial(path + 1, phi, p, pi, L);
      /* If the first two choices were incorrect, select the last one.
       * Note that the only way for the first two choices to have failed
       * is if there are 3 neighbours. */
      if (Flx_nbroots(modpol, p) == 0) {
        /* N.B. This should only occur when h(D) = 2, since then the
         * volcano looks like this: >-< It happens when D = -20 for
         * example. */
        path[1] = nhbrs[3];
        modpol = nhbr_polynomial(path + 1, phi, p, pi, L);
      }
    }
    len = walk_surface_of_2_volcano(path, phi, modpol, p, pi, max_len);
    avma = ltop;
    return len;
  }

  /* Invariant: *path_curr is the most recently found surface-dwelling
   * element. */
  path_curr = path;
  path_end = path + max_len;
  nhbr_idx = 1;
  while (1) {
    /* Find a path that doesn't lead directly to the floor. */
    do {
      if (nhbr_idx == lg(nhbrs)) {
        char *err = stack_sprintf(
          "walk_surface_path: Can't find neighbour of %lu (mod "
          "%lu) that doesn't lead directly to the floor of its "
          "%lu-volcano", *path_curr, p, L);
        pari_err_BUG(err);
      }
      /* Select a new neighbour of path_curr. */
      path_curr[1] = nhbrs[nhbr_idx++];
      (void) extend_path(path_curr, phi, p, pi, L, depth);
    } while (node_degree(phi, L, path_curr[depth], p, pi) == 1);

    /* Finished if we get to max_len (i.e. path_end) or if we've come
     * back to the beginning. */
    if (path_curr + 1 == path_end || path_curr[1] == path[0])
      break;

    /* This extends path_curr+d by one element; i.e. it adds a
     * random neighbour.  We do this so that the access to
     * path_curr[depth] at the beginning of the next iteration is
     * valid. */
    if (depth && extend_path(path_curr + depth - 1, phi, p, pi, L, 2) != 2)
      pari_err_BUG("walk_surface_path: Failed to add a random element");

    ++path_curr;
    avma = ltop;
    nhbrs = Flx_roots(nhbr_polynomial(path_curr, phi, p, pi, L), p);
    nhbr_idx = 1;
  }
  avma = ltop;
  return path_curr - path + 1;
}
