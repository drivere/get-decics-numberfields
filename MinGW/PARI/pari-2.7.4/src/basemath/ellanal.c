/* Copyright (C) 2010  The PARI group.

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
/**                  L functions of elliptic curves                **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

/* Generic Buhler-Gross algorithm */

struct bg_data
{
  GEN E, N; /* ell, conductor */
  GEN bnd; /* t_INT; will need all an for n <= bnd */
  ulong rootbnd; /* sqrt(bnd) */
  GEN an; /* t_VECSMALL: cache of ap, n <= rootbnd */
  GEN ap; /* t_VECSMALL: cache of ap, p <= rootbnd */
  GEN p;  /* t_VECSMALL: primes <= rootbnd */
};

typedef void bg_fun(void*el, GEN *psum, GEN n, GEN a, long jmax);

/* a = a_n, where p = bg->pp[i] divides n, and lasta = a_{n/p}.
 * Call fun(E, psum, N, a_N, 0), for all N, n | N, P^+(N) <= p, a_N != 0,
 * i.e. assumes that fun accumulates psum += a_N * w(N) */
static void
gen_BG_add(void *E, bg_fun *fun, struct bg_data *bg, GEN *psum, GEN n, long i, GEN a, GEN lasta)
{
  pari_sp av = avma, lim = stack_lim(av,2);
  long j;
  ulong nn = itou_or_0(n);
  if (nn && nn <= bg->rootbnd) bg->an[nn] = itos(a);

  if (signe(a))
  {
    fun(E, psum, n, a, 0);
    j = 1;
  }
  else
    j = i;
  for(; j <= i; j++)
  {
    ulong p = bg->p[j];
    GEN nexta, pn = mului(p, n);
    if (cmpii(pn, bg->bnd) > 0) return;
    nexta = mulis(a, bg->ap[j]);
    if (i == j && umodiu(bg->N, p)) nexta = subii(nexta, mului(p, lasta));
    gen_BG_add(E, fun, bg, psum, pn, j, nexta, a);
    if (low_stack(lim, stack_lim(av,2)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"gen_BG_add, p=%lu",p);
      *psum = gerepilecopy(av, *psum);
    }
  }
}

static void
gen_BG_init(struct bg_data *bg, GEN E, GEN N, GEN bnd, GEN ap)
{
  pari_sp av;
  long i = 1, l;
  bg->E = E; bg->N = N;
  bg->bnd = bnd;
  bg->rootbnd = itou(sqrtint(bnd));
  bg->p = primes_upto_zv(bg->rootbnd);
  l = lg(bg->p);
  if (ap)
  { /* reuse known values */
    i = lg(ap);
    bg->ap = vecsmall_lengthen(ap, maxss(l,i)-1);
  }
  else bg->ap = cgetg(l, t_VECSMALL);
  av = avma;
  for (  ; i < l; i++, avma = av) bg->ap[i] = itos(ellap(E, utoipos(bg->p[i])));
  avma = av;
  bg->an = zero_zv(bg->rootbnd);
  bg->an[1] = 1;
}

static GEN
gen_BG_rec(void *E, bg_fun *fun, struct bg_data *bg, GEN sum0)
{
  long i, j, lp = lg(bg->p)-1, lim;
  GEN bndov2 = shifti(bg->bnd, -1);
  pari_sp av = avma, av2;
  GEN sum, p;
  forprime_t S;
  (void)forprime_init(&S, utoipos(bg->p[lp]+1), bg->bnd);
  av2 = avma; lim = stack_lim(av2,1);
  if(DEBUGLEVEL)
    err_printf("1st stage, using recursion for p <= %ld\n", bg->p[lp]);
  sum = gcopy(sum0);
  for (i = 1; i <= lp; i++)
  {
    ulong pp = bg->p[i];
    long ap = bg->ap[i];
    gen_BG_add(E, fun, bg, &sum, utoipos(pp), i, stoi(ap), gen_1);
    if (low_stack(lim, stack_lim(av2,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"ellL1, p=%lu",pp);
      sum = gerepileupto(av2, sum);
    }
  }
  if (DEBUGLEVEL) err_printf("2nd stage, looping for p <= %Ps\n", bndov2);
  while ( (p = forprime_next(&S)) )
  {
    long jmax;
    GEN ap = ellap(bg->E, p);
    if (!signe(ap)) continue;

    jmax = itou( divii(bg->bnd, p) ); /* 2 <= jmax <= el->rootbound */
    fun(E, &sum, p, ap, -jmax); /*Beware: create a cache on the stack */
    for (j = 2;  j <= jmax; j++)
    {
      long aj = bg->an[j];
      GEN a, n;
      if (!aj) continue;
      a = mulis(ap, aj);
      n = muliu(p, j);
      fun(E, &sum, n, a, j);
    }
    if (low_stack(lim, stack_lim(av2,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"ellL1, p=%Ps",p);
      sum = gerepilecopy(av2, sum);
    }
    if (absi_cmp(p, bndov2) >= 0) break;
  }
  if (DEBUGLEVEL) err_printf("3nd stage, looping for p <= %Ps\n", bg->bnd);
  while ( (p = forprime_next(&S)) )
  {
    GEN ap = ellap(bg->E, p);
    if (!signe(ap)) continue;
    fun(E, &sum, p, ap, 0);
    if (low_stack(lim, stack_lim(av2,1)))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"ellL1, p=%Ps",p);
      sum = gerepilecopy(av2, sum);
    }
  }
  return gerepileupto(av, sum);
}

/* Computing L-series derivatives */

/* Implementation by C. Delaunay and X.-F. Roblot
   after a GP script of Tom Womack and John Cremona
   and the corresponding section of Henri Cohen's book GTM 239
   Generic Buhler-Gross iteration and baby-step-giant-step implementation
   by Bill Allombert.
*/

/* used to compute exp((g*bgbnd + b) C) = baby[b] * giant[g] */
struct babygiant
{
  GEN baby, giant;
  ulong bgbnd;
};

struct ellld {
  GEN E, N; /* ell, conductor */
  GEN bnd; /* t_INT; will need all an for n <= bnd */
  ulong rootbnd; /* floor(sqrt(bnd)) */
  long r; /* we are computing L^{(r)}(1) */
  GEN X; /* t_REAL, 2Pi / sqrt(N) */
  GEN eX; /* t_REAL, exp(X) */
  GEN emX; /* t_REAL, exp(-X) */
  long epsbit;
  /* only if r > 1 */
  GEN alpha; /* t_VEC of t_REALs, except alpha[1] = gen_1 */
  GEN A; /* t_VEC of t_REALs, A[1] = 1 */
  /* only if r = 1 */
  GEN gcache, gjcache; /* t_VEC of t_REALs */
  /* only if r = 0 */
  struct babygiant BG[1];
};

static GEN
init_alpha(long m, long prec)
{
  GEN a, si, p1;
  GEN s = gadd(pol_x(0), zeroser(0, m+1));
  long i;

  si = s;
  p1 = gmul(mpeuler(prec), s);
  for (i = 2; i <= m; i++)
  {
    si = gmul(si, s); /* = s^i */
    p1 = gadd(p1, gmul(divru(szeta(i, prec), i), si));
  }
  p1 = gexp(p1, prec); /* t_SER of valuation = 0 */

  a = cgetg(m+2, t_VEC);
  for (i = 1; i <= m+1; i++) gel(a, i) = gel(p1, i+1);
  return a;
}

/* assume r >= 2, return a t_VEC A of t_REALs of length > 2.
 * NB: A[1] = 1 */
static GEN
init_A(long r, long m, long prec)
{
  const long l = m+1;
  long j, s, n;
  GEN A, B, ONE, fj;
  pari_sp av0, av;

  A = cgetg(l, t_VEC); /* will contain the final result */
  gel(A,1) = real_1(prec);
  for (j = 2; j < l; j++) gel(A,j) = cgetr(prec);
  av0 = avma;
  B = cgetg(l, t_VEC); /* scratch space */
  for (j = 1; j < l; j++) gel(B,j) = cgetr(prec);
  ONE = real_1(prec);
  av = avma;

  /* We alternate between two temp arrays A, B (initially virtually filled
   * ONEs = 1.), which are swapped after each loop.
   * After the last loop, we want A to contain the final array: make sure
   * we swap an even number of times */
  if (odd(r)) swap(A, B);

  /* s = 1 */
    for (n = 2; n <= m; n++)
    {
      GEN p3 = ONE; /* j = 1 */
      for (j = 2; j <= n; j++) p3 = addrr(p3, divru(ONE, j));
      affrr(p3, gel(B, n)); avma = av;
    }
  swap(A, B); /* B becomes the new A, old A becomes the new scratchspace */
  for (s = 2; s <= r; s++)
  {
    for (n = 2; n <= m; n++)
    {
      GEN p3 = ONE; /* j = 1 */
      for (j = 2; j <= n; j++) p3 = addrr(p3, divru(gel(A, j), j));
      affrr(p3, gel(B, n)); avma = av;
    }
    swap(A, B); /* B becomes the new A, old A becomes the new scratchspace */
  }

  /* leave A[1] (division by 1) alone */
  fj = ONE; /* will destroy ONE now */
  for (j = 2; j < l; j++)
  {
    affrr(mulru(fj, j), fj);
    affrr(divrr(gel(A,j), fj), gel(A,j));
    avma = av;
  }
  avma = av0; return A;
}

/* x > 0 t_REAL, M >= 2 */
static long
estimate_prec_Sx(GEN x, long M)
{
  GEN p1, p2;
  pari_sp av = avma;

  x = rtor(x, DEFAULTPREC);
  p1 = divri(powru(x, M-2), mpfact(M-1)); /* x^(M-2) / (M-1)! */
  if (expo(x) < 0)
  {
    p2 = divrr(mulrr(p1, powru(x,3)), mulur(M,subsr(1,x)));/* x^(M+1)/(1-x)M! */
    if (cmprr(p2,p1) < 0) p1 = p2;
  }
  avma = av; return expo(p1);
}

/* x a t_REAL */
static long
number_of_terms_Sx(GEN x, long epsbit)
{
  long M, M1, M2;
  M1 = (long)(epsbit * 7.02901423262); /* epsbit * log(2) / (log(3) - 1) */
  M2 = itos(ceil_safe(gmul2n(x,1))); /* >= 2x */
  if (M2 < 2) M2 = 2;
  M = M2;
  for(;;)
  {
    if (estimate_prec_Sx(x, M) < -epsbit) M1 = M; else M2 = M;
    M = (M1+M2+1) >> 1;
    if (M >= M1) return M1;
  }
}

/* X t_REAL, emX = exp(-X) t_REAL; return t_INT */
static GEN
cutoff_point(long r, GEN X, GEN emX, long epsbit, long prec)
{
  GEN M1 = ceil_safe(divsr(7*prec2nbits(prec)+1, X));
  GEN M2 = gen_2, M = M1;
  for(;;)
  {
    GEN c = divrr(powgi(emX, M), powru(mulri(X,M), r+1));
    if (expo(c) < -epsbit) M1 = M; else M2 = M;
    M = shifti(addii(M1, M2), -1);
    if (cmpii(M2, M) >= 0) return M;
  }
}

/* x "small" t_REAL, use power series expansion. Returns a t_REAL */
static GEN
compute_Gr_VSx(struct ellld *el, GEN x)
{
  pari_sp av = avma;
  long r = el->r, n;
  /* n = 2 */
  GEN p1 = divrs(sqrr(x), -2); /* (-1)^(n-1) x^n / n! */
  GEN p2 = x;
  GEN p3 = shiftr(p1, -r);
  for (n = 3; ; n++)
  {
    if (expo(p3) < -el->epsbit) return gerepilecopy(av, p2);
    p2 = addrr(p2, p3);
    p1 = divrs(mulrr(p1, x), -n); /* (-1)^(n-1) x^n / n! */
    p3 = divri(p1, powuu(n, r));
  }
  /* sum_{n = 1}^{oo} (-1)^(n-1) x^n / (n! n^r) */
}

/* t_REAL, assume r >= 2. m t_INT or NULL; Returns a t_REAL */
static GEN
compute_Gr_Sx(struct ellld *el, GEN m, ulong sm)
{
  pari_sp av = avma;
  const long thresh_SMALL = 5;
  long i, r = el->r;
  GEN x = m? mulir(m, el->X): mulur(sm, el->X);
  GEN logx = mplog(x), p4;
  /* i = 0 */
  GEN p3 = gel(el->alpha, r+1);
  GEN p2 = logx;
  for (i = 1; i < r; i++)
  { /* p2 = (logx)^i / i! */
    p3 = addrr(p3, mulrr(gel(el->alpha, r-i+1), p2));
    p2 = divru(mulrr(p2, logx), i+1);
  }
  /* i = r, use alpha[1] = 1 */
  p3 = addrr(p3, p2);

  if (cmprs(x, thresh_SMALL) < 0)
    p4 = compute_Gr_VSx(el, x); /* x "small" use expansion near 0 */
  else
  { /* x "large" use expansion at infinity */
    pari_sp av = avma, lim = stack_lim(av, 2);
    long M = lg(el->A);
    GEN xi = sqrr(x); /* x^2 */
    p4 = x; /* i = 1. Uses A[1] = 1; NB: M > 1 */
    for (i = 2; i < M; i++)
    {
      GEN p5 = mulrr(xi, gel(el->A, i));
      if (expo(p5) < -el->epsbit) break;
      p4 = addrr(p4, p5);
      xi = mulrr(xi, x); /* = x^i */
      if (low_stack(lim, stack_lim(av, 2)))
      {
        if (DEBUGMEM > 0) pari_warn(warnmem, "compute_Gr_Sx");
        gerepileall(av, 2, &xi, &p4);
      }
    }
    p4 = mulrr(p4, m? powgi(el->emX, m): powru(el->emX, sm));
  }
  return gerepileuptoleaf(av, odd(r)? subrr(p4, p3): subrr(p3, p4));
}

/* return G_r(X), cache values G(n*X), n < rootbnd.
 * If r = 0, G(x) = exp(-x), cache Baby/Giant struct in el->BG
 * If r >= 2, precompute the expansions at 0 and oo of G */
static GEN
init_G(struct ellld *el, long prec)
{
  if (el->r == 0)
  {
    ulong bnd = el->rootbnd+1;
    el->BG->bgbnd = bnd;
    el->BG->baby  = powruvec(el->emX, bnd);
    el->BG->giant = powruvec(gel(el->BG->baby,bnd), bnd);
    return gel(el->BG->baby, 1);
  }
  if (el->r == 1)
    el->gcache = mpveceint1(el->X, el->eX, el->rootbnd);
  else
  {
    long m, j, l = el->rootbnd;
    GEN G;
    m = number_of_terms_Sx(mulri(el->X, el->bnd), el->epsbit);
    el->alpha = init_alpha(el->r, prec);
    el->A = init_A(el->r, m, prec);
    G = cgetg(l+1, t_VEC);
    for (j = 1; j <= l; j++) gel(G,j) = compute_Gr_Sx(el, NULL, j);
    el->gcache = G;
  }
  return gel(el->gcache, 1);
}

/* r >= 2; sum += G(n*X) * a_n / n */
static void
ellld_L1(void *E, GEN *psum, GEN n, GEN a, long j)
{
  struct ellld *el = (struct ellld *)E;
  GEN G;
  (void)j;
  if (cmpiu(n, el->rootbnd) <= 0)
    G = gel(el->gcache, itou(n));
  else
    G = compute_Gr_Sx(el, n, 0);
  *psum = addrr(*psum, divri(mulir(a, G), n));
}
/* r = 1; sum += G(n*X) * a_n / n, where G = eint1.
 * If j < 0, cache values G(n*a*X), 1 <= a <= |j| in gjcache
 * If j > 0, assume n = N*j and retrieve G(N*j*X), from gjcache */
static void
ellld_L1r1(void *E, GEN *psum, GEN n, GEN a, long j)
{
  struct ellld *el = (struct ellld *)E;
  GEN G;
  if (j==0)
  {
    if (cmpiu(n, el->rootbnd) <= 0)
      G = gel(el->gcache, itou(n));
    else
      G = mpeint1(mulir(n,el->X), powgi(el->eX,n));
  }
  else if (j < 0)
  {
    el->gjcache = mpveceint1(mulir(n,el->X), powgi(el->eX,n), -j);
    G = gel(el->gjcache, 1);
  }
  else
    G = gel(el->gjcache, j);
  *psum = addrr(*psum, divri(mulir(a, G), n));
}

/* assume n / h->bgbnd fits in an ulong */
static void
get_baby_giant(struct babygiant *h, GEN n, GEN *b, GEN *g)
{
  ulong r, q = udiviu_rem(n, h->bgbnd, &r);
  *b = r? gel(h->baby,r): NULL;
  *g = q? gel(h->giant,q): NULL;
}
static void
ellld_L1r0(void *E, GEN *psum, GEN n, GEN a, long j)
{
  GEN b, g, G;
  get_baby_giant(((struct ellld*)E)->BG, n, &b, &g);
  (void)j;
  if (!b)      G = g;
  else if (!g) G = b;
  else         G = mulrr(b,g);
  *psum = addrr(*psum, divri(mulir(a, G), n));
}
static void
heegner_L1(void*E, GEN *psum, GEN n, GEN a, long jmax)
{
  long j, l = lg(*psum);
  GEN b, g, sum = cgetg(l, t_VEC);
  get_baby_giant((struct babygiant*)E, n, &b, &g);
  (void)jmax;
  for (j = 1; j < l; j++)
  {
    GEN G;
    if (!b)      G = real_i(gel(g,j));
    else if (!g) G = real_i(gel(b,j));
    else         G = mulreal(gel(b,j), gel(g,j));
    gel(sum, j) = addrr(gel(*psum,j), divri(mulir(a, G), n));
  }
  *psum = sum;
}

/* Basic data independent from r (E, N, X, eX, emX) already filled,
 * Returns a t_REAL */
static GEN
ellL1_i(struct ellld *el, struct bg_data *bg, long r, GEN ap, long prec)
{
  GEN sum;
  if (DEBUGLEVEL) err_printf("in ellL1 with r = %ld, prec = %ld\n", r, prec);
  el->r = r;
  el->bnd = cutoff_point(r, el->X, el->emX, el->epsbit, prec);
  gen_BG_init(bg,el->E,el->N,el->bnd,ap);
  el->rootbnd = bg->rootbnd;
  sum = init_G(el, prec);
  if (DEBUGLEVEL>=3) err_printf("el_bnd = %Ps, N=%Ps\n", el->bnd, el->N);
  sum = gen_BG_rec(el, r>=2? ellld_L1: (r==1? ellld_L1r1: ellld_L1r0), bg, sum);
  return mulri(shiftr(sum, 1), mpfact(r));
}

static void
init_el(struct ellld *el, GEN E, long *parity, long bitprec)
{
  GEN eX;
  long prec;

  el->E = E = ellanal_globalred(E, NULL);
  el->N = ellQ_get_N(E);
  prec = nbits2prec(bitprec+(expi(el->N)>>1));
  el->X = divrr(Pi2n(1, prec), sqrtr(itor(el->N, prec))); /* << 1 */
  eX = mpexp(el->X);
  if (realprec(eX) > prec) eX = rtor(eX, prec); /* avoid spurious accuracy increase */
  el->eX = eX;
  el->emX = invr(el->eX);
  el->epsbit = bitprec+1;
  *parity = (ellrootno_global(E) > 0)? 0: 1; /* rank parity */
}

static GEN
ellL1_bitprec(GEN E, long r, long bitprec)
{
  pari_sp av = avma;
  struct ellld el;
  struct bg_data bg;
  long parity;
  long prec = nbits2prec(bitprec)+1;
  if (r<0) pari_err_DOMAIN("ellL1","derivative order","<",gen_0,stoi(r));
  init_el(&el, E, &parity, bitprec);
  if (parity != (r & 1)) return gen_0;
  return gerepileuptoleaf(av, ellL1_i(&el, &bg, r, NULL, prec));
}

GEN
ellL1(GEN E, long r, long prec) { return ellL1_bitprec(E, r, prec2nbits(prec)); }

GEN
ellanalyticrank(GEN e, GEN eps, long prec)
{
  struct ellld el;
  struct bg_data bg;
  long rk;
  pari_sp av = avma, av2;
  GEN ap = NULL;
  pari_timer T;

  if (!eps)
    eps = real2n(-prec2nbits(prec)/2+1, DEFAULTPREC);
  else
    if (typ(eps) != t_REAL) {
      eps = gtofp(eps, DEFAULTPREC);
      if (typ(eps) != t_REAL) pari_err_TYPE("ellanalyticrank", eps);
    }
  init_el(&el, e, &rk, prec2nbits(prec)); /* set rk to rank parity (0 or 1) */
  if (DEBUGLEVEL) {
    err_printf("ellanalyticrank: rank is %s, eps=%Ps\n", rk? "odd": "even",eps);
    timer_start(&T);
  }
  av2 = avma;
  for(;; rk += 2)
  {
    GEN Lr1 = ellL1_i(&el, &bg, rk, ap, prec);
    if (DEBUGLEVEL) timer_printf(&T, "L^(%ld)=%Ps", rk, Lr1);
    if (absr_cmp(Lr1, eps) > 0) return gerepilecopy(av, mkvec2(stoi(rk), Lr1));
    ap = gerepilecopy(av2, bg.ap);
  }
}

/* This file is a C version by Bill Allombert of a GP script by
   Christophe Delaunay which was based on a GP script by John Cremona.
   Reference: Henri Cohen's book GTM 239.
*/

/* Return C, C[i][j] = Q[j]^i, i = 1..nb */
static GEN
fillstep(GEN Q, long nb)
{
  long i, k, l = lg(Q);
  GEN C = cgetg(nb+1,t_VEC);
  gel(C,1) = Q;
  for (i = 2; i<=nb; ++i)
  {
    gel(C,i) = cgetg(l, t_VEC);
    for (k = 1; k<l; ++k) gmael(C,i,k) = gmul(gel(Q,k),gmael(C,i-1,k));
  }
  return C;
}

/* ymin a t_REAL */
static GEN
heegner_psi(GEN E, GEN N, GEN ymin, GEN points, long bitprec)
{
  pari_sp av = avma;
  struct babygiant BG[1];
  struct bg_data bg;
  ulong bnd;
  long k, np = lg(points), prec = nbits2prec(bitprec)+1;
  GEN sum, Q, pi2 = Pi2n(1, prec);
  GEN B = ceilr(divrr(mulur(bitprec,mplog2(DEFAULTPREC)), mulrr(pi2, ymin)));
  gen_BG_init(&bg,E,N,B,NULL);
  bnd = bg.rootbnd + 1;
  BG->bgbnd = bnd;
  Q = cgetg(np, t_VEC);
  for (k = 1; k<np; ++k) gel(Q, k) = expIxy(pi2, gel(points, k), prec);
  BG->baby  = fillstep(Q, bnd);
  BG->giant = fillstep(gel(BG->baby, bnd), bnd);
  sum = gen_BG_rec((void*)BG, heegner_L1, &bg, real_i(Q));
  return gerepileupto(av, sum);
}

/*Returns lambda_bad list for one prime p, nv = localred(E, p) */
static GEN
lambda1(GEN E, GEN nv, GEN p, long prec)
{
  pari_sp av;
  GEN res, lp;
  long kod = itos(gel(nv, 2));
  if (kod==2 || kod ==-2) return cgetg(1,t_VEC);
  av = avma; lp = glog(p, prec);
  if (kod > 4)
  {
    long n = Z_pval(ell_get_disc(E), p);
    long j, m = kod - 4, nl = 1 + (m >> 1L);
    res = cgetg(nl, t_VEC);
    for (j = 1; j < nl; j++)
      gel(res, j) = gmul(lp, gsubgs(gdivgs(sqru(j), n), j)); /* j^2/n - j */
  }
  else if (kod < -4)
    res = mkvec2(negr(lp), divrs(mulrs(lp, kod), 4));
  else
  {
    const long lam[] = {8,9,0,6,0,0,0,3,4};
    long m = -lam[kod+4];
    res = mkvec(divrs(mulrs(lp, m), 6));
  }
  return gerepilecopy(av, res);
}

static GEN
lambdalist(GEN E, long prec)
{
  pari_sp ltop = avma;
  GEN glob = ellglobalred(E), plist = gmael(glob,4,1), L = gel(glob,5);
  GEN res, v, D = ell_get_disc(E);
  long i, j, k, l, m, n, np = lg(plist), lr = 1;
  v = cgetg(np, t_VEC);
  for (j = 1, i = 1 ; j < np; ++j)
  {
    GEN p = gel(plist, j);
    if (dvdii(D, sqri(p)))
    {
      GEN la = lambda1(E, gel(L,j), p, prec);
      gel(v, i++) = la;
      lr *= lg(la);
    }
  }
  np = i;
  res = cgetg(lr+1, t_VEC);
  gel(res, 1) = gen_0; n = 1; m = 1;
  for (j = 1; j < np; ++j)
  {
    GEN w = gel(v, j);
    long lw = lg(w);
    for (k = 1; k <= n; k++)
    {
      GEN t = gel(res, k);
      for (l = 1, m = n; l < lw; l++, m+=n)
        gel(res, k + m) = mpadd(t, gel(w, l));
    }
    n = m;
  }
  return gerepilecopy(ltop, res);
}

/* P a t_INT or t_FRAC, return its logarithmic height */
static GEN
heightQ(GEN P, long prec)
{
  long s;
  if (typ(P) == t_FRAC)
  {
    GEN a = gel(P,1), b = gel(P,2);
    P = absi_cmp(a,b) > 0 ? a: b;
  }
  s = signe(P);
  if (!s) return real_0(prec);
  if (s < 0) P = absi(P);
  return glog(P, prec);
}

/* t a t_INT or t_FRAC, returns max(1, log |t|), returns a t_REAL */
static GEN
logplusQ(GEN t, long prec)
{
  if (typ(t) == t_INT)
  {
    if (!signe(t)) return real_1(prec);
    if (signe(t) < 0) t = absi(t);
  }
  else
  {
    GEN a = gel(t,1), b = gel(t,2);
    if (absi_cmp(a, b) < 0) return real_1(prec);
    if (signe(a) < 0) t = gneg(t);
  }
  return glog(t, prec);
}

/* See GTM239, p532, Th 8.1.18
 * Return M such that h_naive <= M */
static GEN
hnaive_max(GEN ell, GEN ht)
{
  const long prec = LOWDEFAULTPREC; /* minimal accuracy */
  GEN b2     = ell_get_b2(ell), j = ell_get_j(ell);
  GEN logd   = glog(absi(ell_get_disc(ell)), prec);
  GEN logj   = logplusQ(j, prec);
  GEN hj     = heightQ(j, prec);
  GEN logb2p = signe(b2)? addrr(logplusQ(gdivgs(b2, 12),prec), mplog2(prec))
                        : real_1(prec);
  GEN mu     = addrr(divrs(addrr(logd, logj),6), logb2p);
  return addrs(addrr(addrr(ht, divrs(hj,12)), mu), 2);
}

static GEN
qfb_root(GEN Q, GEN vDi)
{
  GEN a2 = shifti(gel(Q, 1),1), b = gel(Q, 2);
  return mkcomplex(gdiv(negi(b),a2),divri(vDi,a2));
}

static GEN
qimag2(GEN Q)
{
  pari_sp av = avma;
  GEN z = gdiv(negi(qfb_disc(Q)), shifti(sqri(gel(Q, 1)),2));
  return gerepileupto(av, z);
}

/***************************************************/
/*Routines for increasing the imaginary parts using*/
/*Atkin-Lehner operators                           */
/***************************************************/

static GEN
qfb_mult(GEN Q, GEN M)
{
  GEN A = gel(Q, 1) , B = gel(Q, 2) , C = gel(Q, 3);
  GEN a = gcoeff(M, 1, 1), b = gcoeff(M, 1, 2);
  GEN c = gcoeff(M, 2, 1), d = gcoeff(M, 2, 2);
  GEN W1 = addii(addii(mulii(sqri(a), A), mulii(mulii(c, a), B)), mulii(sqri(c), C));
  GEN W2 = addii(addii(mulii(mulii(shifti(b,1), a), A),
                       mulii(addii(mulii(d, a), mulii(c, b)), B)),
                 mulii(mulii(shifti(d,1), c), C));
  GEN W3 = addii(addii(mulii(sqri(b), A), mulii(mulii(d, b), B)), mulii(sqri(d), C));
  GEN D = gcdii(W1, gcdii(W2, W3));
  if (!equali1(D)) {
    W1 = diviiexact(W1,D);
    W2 = diviiexact(W2,D);
    W3 = diviiexact(W3,D);
  }
  return qfi(W1, W2, W3);
}

#ifdef DEBUG
static void
best_point_old(GEN Q, GEN NQ, GEN f, GEN *u, GEN *v)
{
  long n, k;
  GEN U, c, d;
  GEN A = gel(f, 1);
  GEN B = gel(f, 2);
  GEN C = gel(f, 3);
  GEN q = qfi(mulii(NQ, C), negi(B), diviiexact(A, NQ));
  redimagsl2(q, &U);
  *u = c = gcoeff(U, 1, 1);
  *v = d = gcoeff(U, 2, 1);
  if (equali1(gcdii(mulii(*u, NQ), mulii(*v, Q))))
    return;
  for (n = 1; ; n++)
  {
    for (k = -n; k<=n; k++)
    {
      *u = addis(c, k); *v = addis(d, n);
      if (equali1(ggcd(mulii(*u, NQ), mulii(*v, Q))))
        return;
      *v= subis(d, n);
      if (equali1(ggcd(mulii(*u, NQ), mulii(*v, Q))))
        return;
      *u = addis(c, n); *v = addis(d, k);
      if (equali1(ggcd(mulii(*u, NQ), mulii(*v, Q))))
        return;
      *u = subis(c, n);
      if (equali1(ggcd(mulii(*u, NQ), mulii(*v, Q))))
        return;
    }
  }
}
/* q(x,y) = ax^2 + bxy + cy^2 */
static GEN
qfb_eval(GEN q, GEN x, GEN y)
{
  GEN a = gel(q,1), b = gel(q,2), c = gel(q,3);
  GEN x2 = sqri(x), y2 = sqri(y), xy = mulii(x,y);
  return addii(addii(mulii(a, x2), mulii(b,xy)), mulii(c, y2));
}
#endif

static long
nexti(long i) { return i>0 ? -i : 1-i; }

/* q0 + i q1 + i^2 q2 */
static GEN
qfmin_eval(GEN q0, GEN q1, GEN q2, long i)
{ return addii(mulis(addii(mulis(q2, i), q1), i), q0); }

/* assume a > 0, return gcd(a,b,c) */
static ulong
gcduii(ulong a, GEN b, GEN c)
{
  ulong d = a;
  d = ugcd(umodiu(b, d), d );
  if (d == 1) return 1;
  d = ugcd(umodiu(c, d), d );
  return d;
}

static void
best_point(GEN Q, GEN NQ, GEN f, GEN *pu, GEN *pv)
{
  GEN a = mulii(NQ, gel(f,3)), b = negi(gel(f,2)), c = diviiexact(gel(f,1), NQ);
  GEN D = absi( qfb_disc(f) );
  GEN U, qr = redimagsl2(qfi(a,b,c), &U);
  GEN A = gel(qr,1), B = gel(qr,2), A2 = shifti(A,1), AA4 = sqri(A2);
  GEN V, best;
  long y;

  /* 4A qr(x,y) = (2A x + By)^2 + D y^2
   * Write x = x0(y) + i, where x0 is an integer minimum
   * (the smallest in case of tie) of x-> qr(x,y), for given y.
   * 4A qr(x,y) = ((2A x0 + By)^2 + Dy^2) + 4A i (2A x0 + By) + 4A^2 i^2
   *            = q0(y) + q1(y) i + q2 i^2
   * Loop through (x,y), y>0 by (roughly) increasing values of qr(x,y) */

  /* We must test whether [X,Y]~ := U * [x,y]~ satisfy (X NQ, Y Q) = 1
   * This is equivalent to (X,Y) = 1 (note that (X,Y) = (x,y)), and
   * (X, Q) = (Y, NQ) = 1.
   * We have U * [x0+i, y]~ = U * [x0,y]~ + i U[,1] =: V0 + i U[,1] */

  /* try [1,0]~ = first minimum */
  V = gel(U,1); /* U *[1,0]~ */
  *pu = gel(V,1);
  *pv = gel(V,2);
  if (is_pm1(gcdii(*pu, Q)) && is_pm1(gcdii(*pv, NQ))) return;

  /* try [0,1]~ = second minimum */
  V = gel(U,2); /* U *[0,1]~ */
  *pu = gel(V,1);
  *pv = gel(V,2);
  if (is_pm1(gcdii(*pu, Q)) && is_pm1(gcdii(*pv, NQ))) return;

  /* (X,Y) = (1, \pm1) always works. Try to do better now */
  best = subii(addii(a, c), absi(b));
  *pu = gen_1;
  *pv = signe(b) < 0? gen_1: gen_m1;

  for (y = 1;; y++)
  {
    GEN Dy2, r, By, x0, q0, q1, V0;
    long i;
    if (y > 1)
    {
      if (gcduii(y, gcoeff(U,1,1),  Q) != 1) continue;
      if (gcduii(y, gcoeff(U,2,1), NQ) != 1) continue;
    }
    Dy2 = mulii(D, sqru(y));
    if (cmpii(Dy2, best) >= 0) break; /* we won't improve. STOP */
    By = muliu(B,y), x0 = truedvmdii(negi(By), A2, &r);
    if (cmpii(r, A) >= 0) { x0 = subis(x0,1); r = subii(r, A2); }
    /* (2A x + By)^2 + Dy^2, minimal at x = x0. Assume A2 > 0 */
    /* r = 2A x0 + By */
    q0 = addii(sqri(r), Dy2); /* minimal value for this y, at x0 */
    if (cmpii(q0, best) >= 0) continue; /* we won't improve for this y */
    q1 = shifti(mulii(A2, r), 1);

    V0 = ZM_ZC_mul(U, mkcol2(x0, utoipos(y)));
    for (i = 0;; i = nexti(i))
    {
      pari_sp av2 = avma;
      GEN x, N = qfmin_eval(q0, q1, AA4, i);
      if (cmpii(N , best) >= 0) break;
      x = addis(x0, i);
      if (ugcd(umodiu(x, y), y) == 1)
      {
        GEN u, v;
        V = ZC_add(V0, ZC_z_mul(gel(U,1), i)); /* [X, Y] */
        u = gel(V,1);
        v = gel(V,2);
        if (is_pm1(gcdii(u, Q)) && is_pm1(gcdii(v, NQ)))
        {
          *pu = u;
          *pv = v;
          best = N; break;
        }
      }
      avma = av2;
    }
  }
#ifdef DEBUG
  {
    GEN oldu, oldv, F = qfi(a,b,c);
    best_point_old(Q, NQ, f, &oldu, &oldv);
    if (!equalii(oldu, *pu) || !equalii(oldv, *pv))
    {
      if (!equali1(gcdii(mulii(*pu, NQ), mulii(*pv, Q))))
        pari_err_BUG("best_point (gcd)");
      if (cmpii(qfb_eval(F, *pu,*pv), qfb_eval(F, oldu, oldv)) > 0)
      {
        pari_warn(warner, "%Ps,%Ps,%Ps, %Ps > %Ps",
                          Q,NQ,f, mkvec2(*pu,*pv), mkvec2(oldu,oldv));
        pari_err_BUG("best_point (too large)");
      }
    }
  }
#endif
}

static GEN
best_lift(GEN N, GEN Q, GEN NQ, GEN f)
{
  GEN a,b,c,d,M;
  best_point(Q, NQ, f, &c, &d);
  (void)bezout(mulii(d, Q), mulii(NQ, c), &a, &b);
  M = mkmat2( mkcol2(mulii(d, Q), mulii(negi(N), c)),
              mkcol2(b, mulii(a, Q)));
  return qfb_mult(f, M);
}

static GEN
lift_points(GEN N, GEN listQ, GEN f, GEN *pt, GEN *pQ)
{
  pari_sp av = avma;
  GEN yf = gen_0, tf = NULL, Qf = NULL;
  long k, l = lg(listQ);
  for (k = 1; k < l; ++k)
  {
    GEN c = gel(listQ, k), Q = gel(c,1), NQ = gel(c,2);
    GEN t = best_lift(N, Q, NQ, f), y = qimag2(t);
    if (gcmp(y, yf) > 0) { yf = y; Qf = Q; tf = t; }
  }
  gerepileall(av, 3, &tf, &Qf, &yf);
  *pt = tf; *pQ = Qf; return yf;
}

/***************************/
/*         Twists          */
/***************************/

static GEN
twistcurve(GEN e, GEN D)
{
  GEN D2 = sqri(D);
  GEN a4 = mulii(mulsi(-27, D2), ell_get_c4(e));
  GEN a6 = mulii(mulsi(-54, mulii(D, D2)), ell_get_c6(e));
  return ellinit(mkvec2(a4,a6),NULL,0);
}

static GEN
ltwist1(GEN E, GEN d, long bitprec)
{
  pari_sp av = avma;
  GEN Ed = twistcurve(E, d);
  GEN z = ellL1_bitprec(Ed, 0, bitprec);
  obj_free(Ed); return gerepileuptoleaf(av, z);
}

/* Return O_re*c(E)/(4*O_vol*|E_t|^2) */

static GEN
heegner_indexmult(GEN om, long t, GEN tam, long prec)
{
  pari_sp av = avma;
  GEN Ovr = gabs(gimag(gel(om, 2)), prec); /* O_vol/O_re, t_REAL */
  return gerepileupto(av, divrs(divir(tam, Ovr), 4*t*t));
}


/* omega(gcd(D, N)), given faN = factor(N) */
static long
omega_N_D(GEN faN, ulong D)
{
  GEN P = gel(faN, 1);
  long i, l = lg(P), w = 0;
  for (i = 1; i < l; i++)
    if (dvdui(D, gel(P,i))) w++;
  return w;
}

static GEN
heegner_indexmultD(GEN faN, GEN a, long D, GEN sqrtD)
{
  pari_sp av = avma;
  GEN c;
  long w;
  switch(D)
  {
    case -3: w = 9; break;
    case -4: w = 4; break;
    default: w = 1;
  }
  c = shifti(stoi(w), omega_N_D(faN,-D)); /* (w(D)/2)^2 * 2^omega(gcd(D,N)) */
  return gerepileupto(av, mulri(mulrr(a, sqrtD), c));
}

static GEN
heegner_try_point(GEN E, GEN lambdas, GEN ht, GEN z, long prec)
{
  long l = lg(lambdas);
  long i, eps;
  GEN P = greal(pointell(E, z, prec)), x = gel(P,1);
  GEN rh = subrr(ht, shiftr(ellheightoo(E, P, prec),1));
  for (i = 1; i < l; ++i)
  {
    GEN logd = shiftr(gsub(rh, gel(lambdas, i)), -1);
    GEN d, approxd = gexp(logd, prec);
    if (DEBUGLEVEL > 1)
      err_printf("Trying lambda number %ld, logd=%Ps, approxd=%Ps\n", i, logd, approxd);
    d = grndtoi(approxd, &eps);
    if (signe(d) > 0 && eps<-10)
    {
      GEN X, ylist, d2 = sqri(d), approxn = mulir(d2, x);
      if (DEBUGLEVEL > 1) err_printf("approxn=%Ps  eps=%ld\n", approxn,eps);
      X = gdiv(ground(approxn), d2);
      ylist = ellordinate(E, X, prec);
      if (lg(ylist) > 1)
      {
        GEN P = mkvec2(X, gel(ylist, 1));
        GEN hp = ghell(E,P,prec);
        if (cmprr(hp, shiftr(ht,1)) < 0 && cmprr(hp, shiftr(ht,-1)) > 0)
          return P;
        if (DEBUGLEVEL > 0)
          err_printf("found non-Heegner point %Ps\n", P);
      }
    }
  }
  return NULL;
}

static GEN
heegner_find_point(GEN e, GEN om, GEN ht, GEN z1, long k, long prec)
{
  GEN lambdas = lambdalist(e, prec);
  pari_sp av = avma;
  long m;
  GEN Ore = gel(om, 1), Oim = gel(om, 2);
  for (m = 0; m < k; m++)
  {
    GEN P, z2 = divrs(addrr(z1, mulsr(m, Ore)), k);
    if (DEBUGLEVEL > 1)
      err_printf("Trying multiplier %ld\n",m);
    P = heegner_try_point(e, lambdas, ht, z2, prec);
    if (P) return P;
    if (signe(ell_get_disc(e)) > 0)
    {
      z2 = gadd(z2, gmul2n(Oim, -1));
      P = heegner_try_point(e, lambdas, ht, z2, prec);
      if (P) return P;
    }
    avma = av;
  }
  pari_err_BUG("ellheegner, point not found");
  return NULL; /* NOT REACHED */
}

/* N > 1, fa = factor(N), return factor(4*N) */
static GEN
fa_shift2(GEN fa)
{
  GEN P = gel(fa,1), E = gel(fa,2);
  if (equaliu(gcoeff(fa,1,1), 2))
  {
    E = shallowcopy(E);
    gel(E,1) = addis(gel(E,1), 2);
  }
  else
  {
    P = shallowconcat(gen_2, P);
    E = shallowconcat(gen_2, E);
  }
  return mkmat2(P, E);
}

/* P = prime divisors of N(E). Return the product of primes p in P, a_p != -1
 * HACK: restrict to small primes since large ones won't divide our C-long
 * discriminants */
static GEN
get_bad(GEN E, GEN P)
{
  long k, l = lg(P), ibad = 1;
  GEN B = cgetg(l, t_VECSMALL);
  for (k = 1; k < l; k++)
  {
    GEN p = gel(P,k);
    long pp = itos_or_0(p);
    if (!pp) break;
    if (! equalim1(ellap(E,p))) B[ibad++] = pp;
  }
  setlg(B, ibad); return ibad == 1? NULL: zv_prod_Z(B);
}

/* list of pairs [Q,N/Q], where Q | N and gcd(Q,N/Q) = 1 */
static GEN
find_div(GEN N, GEN faN)
{
  GEN listQ = divisors(faN);
  long j, k, l = lg(listQ);

  gel(listQ, 1) = mkvec2(gen_1, N);
  for (j = k = 2; k < l; ++k)
  {
    GEN Q = gel(listQ, k), NQ = diviiexact(N, Q);
    if (is_pm1(gcdii(Q,NQ))) gel(listQ, j++) = mkvec2(Q,NQ);
  }
  setlg(listQ, j); return listQ;
}

static long
testDisc(GEN bad, long d)
{ return !bad || ugcd(umodiu(bad, -d), -d) == 1; }
/* bad = product of bad primes. Return the NDISC largest fundamental
 * discriminants D < d such that (D,bad) = 1 and d is a square mod 4N */
static GEN
listDisc(GEN fa4N, GEN bad, long d)
{
  const long NDISC = 10;
  GEN v = cgetg(NDISC+1, t_VECSMALL);
  pari_sp av = avma;
  long j = 1;
  for(;;)
  {
    d -= odd(d)? 1: 3;
    if (testDisc(bad,d) && unegisfundamental(-d) && Zn_issquare(stoi(d), fa4N))
    {
      v[j++] = d;
      if (j > NDISC) break;
    }
    avma = av;
  }
  avma = av; return v;
}
/* L = vector of [q1,q2] or [q1,q2,q2']
 * cd = (b^2 - D)/(4N) */
static void
listfill(GEN N, GEN b, GEN c, GEN d, GEN L, long *s)
{
  long k, l = lg(L);
  GEN add, frm2, a = mulii(d, N), V = mkqfi(a,b,c), frm = redimag(V);
  for (k = 1; k < l; ++k)
  { /* Lk = [v,frm] or [v,frm,frm2] */
    GEN Lk = gel(L,k);
    long i;
    for (i = 2; i < lg(Lk); i++) /* 1 or 2 elements */
      if (gequal(frm, gel(Lk,i)))
      {
        GEN v = gel(Lk, 1);
        if (cmpii(a, gel(v,1)) < 0) gel(Lk,1) = V;
        return;
      }
  }
  frm2 = redimag( mkqfi(d, negi(b), mulii(c,N)) );
  add = gequal(frm, frm2)? mkvec2(V,frm): mkvec3(V,frm,frm2);
  vectrunc_append(L, add);
  *s += lg(add) - 2;
}
/* faN4 = factor(4*N) */
static GEN
listheegner(GEN N, GEN faN4, GEN listQ, GEN D)
{
  const long kmin = 30;
  long h = itos(gel(quadclassunit0(D, 0, NULL, DEFAULTPREC), 1));
  GEN ymin, b = Zn_sqrt(D, faN4), L = vectrunc_init(h+1);
  long l, k, s = 0;
  for (k = 0; k < kmin || s < h; k++)
  {
    GEN bk = addii(b, mulsi(2*k, N));
    GEN C = diviiexact(shifti(subii(sqri(bk), D), -2), N);
    GEN div = divisors(C);
    long i, l = lg(div);
    for (i = 1; i < l; i++)
    {
      GEN d = gel(div, i), c = gel(div, l-i); /* cd = C */
      listfill(N, bk, c, d, L, &s);
    }
  }
  l = lg(L); ymin = NULL;
  for (k = 1; k < l; k++)
  {
    GEN t, Q, Lk = gel(L,k), f = gel(Lk,1);
    GEN y = lift_points(N, listQ, f, &t, &Q);
    gel(L, k) = mkvec3(t, stoi(lg(Lk) - 2), Q);
    if (!ymin || gcmp(y, ymin) < 0) ymin = y;
  }
  return mkvec3(ymin, L, D);
}

/* Q | N, P = prime divisors of N, R[i] = local epsilon-factor at P[i].
 * Return \prod_{p | Q} R[i] */
static long
rootno(GEN Q, GEN P, GEN R)
{
  long s = 1, i, l = lg(P);
  for (i = 1; i < l; i++)
    if (dvdii(Q, gel(P,i))) s *= R[i];
  return s;
}

static void
heegner_find_disc(GEN *ymin, GEN *points, GEN *coefs, long *pind, GEN E,
                  GEN indmult, long prec)
{
  long d = 0;
  GEN faN4, bad, N, faN, listQ, listR;

  ellQ_get_Nfa(E, &N, &faN);
  faN4 = fa_shift2(faN);
  listQ = find_div(N, faN);
  bad = get_bad(E, gel(faN, 1));
  listR = gel(obj_check(E, Q_ROOTNO), 2);
  for(;;)
  {
    pari_sp av = avma;
    GEN list, listD = listDisc(faN4, bad, d);
    long k, l = lg(listD);
    if (DEBUGLEVEL) err_printf("List of discriminants...%Ps\n", listD);
    list = cgetg(l, t_VEC);
    for (k = 1; k < l; ++k)
      gel(list, k) = listheegner(N, faN4, listQ, stoi(listD[k]));
    list = vecsort0(list, gen_1, 0);
    for (k = l-1; k > 0; --k)
    {
      long bprec = 8;
      GEN Lk = gel(list,k), D = gel(Lk,3);
      GEN sqrtD = sqrtr_abs(itor(D, prec)); /* sqrt(|D|) */
      GEN indmultD = heegner_indexmultD(faN, indmult, itos(D), sqrtD);
      do
      {
        GEN mulf = ltwist1(E, D, bprec+expo(indmultD));
        GEN indr = mulrr(indmultD, mulf);
        if (DEBUGLEVEL>=1) err_printf("Disc = %Ps, Index^2 = %Ps\n", D, indr);
        if (signe(indr)>0 && expo(indr) >= -1) /* indr >=.5 */
        {
          long e, i, l;
          GEN pts, cfs, L, indi = grndtoi(sqrtr_abs(indr), &e);
          if (e > expi(indi)-7)
          {
            bprec++;
            pari_warn(warnprec, "ellL1",bprec);
            continue;
          }
          *pind = itos(indi);
          *ymin = gsqrt(gel(Lk, 1), prec);
          L = gel(Lk, 2); l = lg(L);
          pts = cgetg(l, t_VEC);
          cfs = cgetg(l, t_VECSMALL);
          for (i = 1; i < l; ++i)
          {
            GEN P = gel(L,i), z = gel(P,2), Q = gel(P,3); /* [1 or 2, Q] */
            long c;
            gel(pts, i) = qfb_root(gel(P,1), sqrtD);
            c = rootno(Q, gel(faN,1), listR);
            if (!equali1(z)) c *= 2;
            cfs[i] = c;
          }
          *coefs = cfs; *points = pts; return;
        }
      } while(0);
    }
    d = listD[l-1]; avma = av;
  }
}

static GEN
ell_apply_globalred_all(GEN e, GEN *N, GEN *cb, GEN *tam)
{
  GEN E = ellanal_globalred(e, cb), red = obj_check(E, Q_GLOBALRED);
  *N = gel(red, 1);
  *tam = gel(red,2);
  if (signe(ell_get_disc(E))>0) *tam = shifti(*tam,1);
  return E;
}

GEN
ellheegner(GEN E)
{
  pari_sp av = avma;
  GEN z, P, ht, points, coefs, ymin, s, om, indmult;
  long ind, lint, k, l, wtor, etor;
  long bitprec = 16, prec = nbits2prec(bitprec)+1;
  pari_timer T;
  GEN N, cb, tam, torsion;

  E = ell_apply_globalred_all(E, &N, &cb, &tam);
  if (ellrootno_global(E) == 1)
    pari_err_DOMAIN("ellheegner", "(analytic rank)%2","=",gen_0,E);
  torsion = elltors(E);
  wtor = itos( gel(torsion,1) ); /* #E(Q)_tor */
  etor = wtor > 1? itos(gmael(torsion, 2, 1)): 1; /* exponent of E(Q)_tor */
  while (1)
  {
    GEN hnaive, l1;
    long bitneeded;
    l1 = ellL1_bitprec(E, 1, bitprec);
    if (expo(l1) < 1 - bitprec/2)
      pari_err_DOMAIN("ellheegner", "analytic rank",">",gen_1,E);
    om = ellR_omega(E,prec);
    ht = divrr(mulru(l1, wtor * wtor), mulri(gel(om,1), tam));
    if (DEBUGLEVEL) err_printf("Expected height=%Ps\n", ht);
    hnaive = hnaive_max(E, ht);
    if (DEBUGLEVEL) err_printf("Naive height <= %Ps\n", hnaive);
    bitneeded = itos(gceil(divrr(hnaive, mplog2(prec)))) + 10;
    if (DEBUGLEVEL) err_printf("precision = %ld\n", bitneeded);
    if (bitprec>=bitneeded) break;
    bitprec = bitneeded;
    prec = nbits2prec(bitprec)+1;
  }
  indmult = heegner_indexmult(om, wtor, tam, prec);
  heegner_find_disc(&ymin, &points, &coefs, &ind, E, indmult, prec);
  if (DEBUGLEVEL == 1) err_printf("N = %Ps, ymin*N = %Ps\n",N,gmul(ymin,N));
  if (DEBUGLEVEL) timer_start(&T);
  s = heegner_psi(E, N, ymin, points, bitprec);
  if (DEBUGLEVEL) timer_printf(&T,"heegner_psi");
  l = lg(points);
  z = mulsr(coefs[1], gel(s, 1));
  for (k = 2; k < l; ++k) z = addrr(z, mulsr(coefs[k], gel(s, k)));
  if (DEBUGLEVEL) err_printf("z=%Ps\n", z);
  z = gsub(z, gmul(gel(om,1), ground(gdiv(z, gel(om,1)))));
  lint = wtor > 1 ? cgcd(ind, etor): 1;
  P = heegner_find_point(E, om, ht, gmulsg(2*lint, z), lint*2*ind, prec);
  if (DEBUGLEVEL) timer_printf(&T,"heegner_find_point");
  if (cb) P = ellchangepointinv(P, cb);
  return gerepilecopy(av, P);
}
