/* Copyright (C) 2009  The PARI group.

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

/************************************************************/
/*     Computation of all the extensions of a given         */
/*               degree of a p-adic field                   */
/* Xavier Roblot                                            */
/************************************************************/

#undef CHECK_EXTENSIONS

/* cf. Math. Comp, vol. 70, No. 236, pp. 1641-1659 for more details.
   Note that n is now e (since the e from the paper is always = 1) and l
   is now f */
/* Structure for a given type of extension */
typedef struct {
  GEN p;
  long e, f, j;
  long a, b, c;
  long v;     /* auxiliary variable */
  long r;     /* pr = p^r */
  GEN pr;     /* p-adic precision for poly. reduction */
  GEN q, qm1; /* p^f, q - 1 */
  GEN upl;    /* cyclotomic polynomial (in v) generating K^ur (mod pr) */
  GEN mv;     /* -v mod upl (mod pr) */
  GEN uplr;   /* upl reduced mod p */
  GEN frob;   /* Frobenius acting of the root of upl (mod pr) */
  GEN nbext;  /* number of extensions */
  GEN roottable; /* table of roots of polynomials over the residue field */
  GEN pk;     /* powers of p: [p^1, p^2, ..., p^c] */
} KRASNER_t;

/* Structure containing the field data (constructed with FieldData) */
typedef struct {
  GEN p;
  GEN top;  /* absolute polynomial with root zq + pi (mod pr) */
  GEN topr; /* absolute polynomial with root zq + pi (mod p) */
  GEN eis;  /* relative polynomial with root pi (mod pr) (y=zq) */
  GEN zq;   /* (q-1)-th root of unity (root of upl) (mod pr) (y=zq+pi) */
  GEN pi;   /* prime element (mod p) (y=zq+pi)*/
  GEN ipi;  /* p/pi (mod pr) (y=zq+pi) (used to divide by pi) */
  GEN pik;  /* [1, pi, ..., pi^(e-1), pi^e / p] (mod pr). Note the last one ! */
  long cj;  /* number of conjugate fields */
} FAD_t;

static long
ceildiv(ulong a, ulong b)
{
  long c = a/b;
  if (a%b) c++;
  return c;
}

/* Eval P(x) assuming P has positive coefficients and the result is a long */
static ulong
ZX_z_eval(GEN P, ulong x)
{
  long i, l = lg(P);
  ulong z;

  if (typ(P) == t_INT) return itou(P);
  if (l == 2) return 0;
  z = itou(gel(P, l-1));
  for (i = l-2; i > 1; i--) z = z*x + itou(gel(P,i));
  return z;
}

/* Eval P(x, y) assuming P has positive coefficients and the result is a long */
static ulong
ZXY_z_eval(GEN P, ulong x, ulong y)
{
  long i, l = lg(P);
  ulong z;

  if (l == 2) return 0;
  z = ZX_z_eval(gel(P, l-1), y);
  for (i = l-2; i > 1; i--) z = z*x + ZX_z_eval(gel(P, i), y);
  return z;
}

/* P an Fq[X], where Fq = Fp[Y]/(T(Y)), a an FpX representing the automorphism
 * y -> a(y). Return a(P), applying a() coefficientwise. */
static GEN
FqX_FpXQ_eval(GEN P, GEN a, GEN T, GEN p)
{
  long i, l;
  GEN Q = cgetg_copy(P, &l);

  Q[1] = P[1];
  for (i = 2; i < l; i++)
  {
    GEN cf = gel(P, i);
    if (typ(cf) == t_POL) {
      switch(degpol(cf))
      {
        case -1: cf = gen_0; break;
        case 0:  cf = gel(cf,2); break;
        default:
          cf = FpX_FpXQ_eval(cf, a, T, p);
          cf = simplify_shallow(cf);
          break;
      }
    }
    gel(Q, i) = cf;
  }

  return Q;
}

/* Sieving routines */
static GEN
InitSieve(long l) { return zero_F2v(l); }
static long
NextZeroValue(GEN sv, long i)
{
  for(; i <= sv[1]; i++)
    if (!F2v_coeff(sv, i)) return i;
  return 0; /* sieve is full or out of the sieve! */
}
static void
SetSieveValue(GEN sv, long i)
{ if (i >= 1 && i <= sv[1]) F2v_set(sv, i); }

/* return 1 if the data verify Ore condition and 0 otherwise */
static long
VerifyOre(GEN p, long e, long j)
{
  long nv, b, vb, nb;

  if (j < 0) return 0;
  nv = e * u_pval(e, p);
  b  = j%e;
  if (b == 0) return (j == nv);
  if (j > nv) return 0;
  /* j < nv */
  vb = u_pval(b, p);
  nb = vb*e;
  return (nb <= j);
}

/* Given [K:Q_p] = m and disc(K/Q_p) = p^d, return all decompositions K/K^ur/Q_p
 * as [e, f, j] with
 *   K^ur/Q_p unramified of degree f,
 *   K/K^ur totally ramified of degree e, and discriminant p^(e+j-1);
 * thus d = f*(e+j-1) and j > 0 iff ramification is wild */
static GEN
possible_efj_by_d(GEN p, long m, long d)
{
  GEN rep, div;
  long i, ctr, l;

  if (d == 0) return mkvec(mkvecsmall3(1, m, 0)); /* unramified */
  div = divisorsu(ugcd(m, d));
  l = lg(div); ctr = 1;
  rep = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    long f = div[i], e = m/f, j = d/f - e + 1;
    if (VerifyOre(p, e, j)) gel(rep, ctr++) = mkvecsmall3(e, f, j);
  }
  setlg(rep, ctr); return rep;
}

/* return the number of extensions corresponding to (e,f,j) */
static GEN
NumberExtensions(KRASNER_t *data)
{
  ulong pp, pa;
  long e, a, b;
  GEN p, q, s0, p1;

  e = data->e;
  p = data->p;
  q = data->q;
  a = data->a; /* floor(j/e) <= v_p(e), hence p^a | e */
  b = data->b; /* j % e */
  if (is_bigint(p)) /* implies a = 0 */
    return b == 0? utoipos(e): mulsi(e, data->qm1);

  pp = p[2];
  switch(a)
  {
    case 0:  pa = 1;  s0 = utoipos(e); break;
    case 1:  pa = pp; s0 = mului(e, powiu(q, e / pa)); break;
    default:
      pa = upowuu(pp, a); /* p^a */
      s0 = mulsi(e, powiu(q, (e / pa) * ((pa - 1) / (pp - 1))));
  }
  /* s0 = e * q^(e*sum(p^-i, i=1...a)) */
  if (b == 0) return s0;

  /* q^floor((b-1)/p^(a+1)) */
  p1 = powiu(q, sdivsi(b-1, muluu(pa, pp)));
  return mulii(mulii(data->qm1, s0), p1);
}

static GEN
get_topx(KRASNER_t *data, GEN eis)
{
  GEN p1, p2, rpl;
  long j;
  pari_sp av;
  /* top poly. is the minimal polynomial of root(pol) + root(upl) */
  rpl = FqX_translate(FqX_red(eis, data->upl, data->pr),
                      data->mv, data->upl, data->pr);
  p1 = p2 = rpl;
  av = avma;
  for (j = 1; j < data->f; j++)
  {
    p1 = FqX_FpXQ_eval(p1, data->frob, data->upl, data->pr);
    p2 = FqX_mul(p2, p1, data->upl, data->pr);
    if (gc_needed(av, 1)) gerepileall(av, 2, &p1, &p2);
  }
  return simplify_shallow(p2); /* ZX */
}

/* eis (ZXY): Eisenstein polynomial  over the field defined by upl.
 * topx (ZX): corresponding absolute equation.
 * Return the struct FAD corresponding to the field it defines (GENs created
 * as clones). Assume e > 1. */
static void
FieldData(KRASNER_t *data, FAD_t *fdata, GEN eis, GEN topx)
{
  GEN p1, zq, ipi, cipi, dipi, t, Q;

  fdata->p = data->p;
  t = leafcopy(topx); setvarn(t, data->v);
  fdata->top  = t;
  fdata->topr = FpX_red(t, data->pr);

  zq  = pol_x(data->v);
  /* FIXME: do as in CycloPol (not so easy) */
  for(;;)
  {
    GEN zq2 = zq;
    zq = Fq_pow(zq, data->q, fdata->top, data->pr);
    if (gequal(zq, zq2)) break;
  }
  fdata->zq  = zq;
  fdata->eis = eis;
  fdata->pi  = Fq_sub(pol_x(data->v), fdata->zq,
                      FpX_red(fdata->top, data->p), data->p);
  ipi = RgXQ_inv(fdata->pi, fdata->top);
  ipi = Q_remove_denom(ipi, &dipi);
  Q = mulii(data->pr, data->p);
  cipi = Fp_inv(diviiexact(dipi, data->p), Q);
  fdata->ipi = FpX_Fp_mul(ipi, cipi, Q); /* p/pi mod p^(pr+1) */

  /* Last one is in fact pi^e/p */
  p1 = FpXQ_powers(fdata->pi, data->e, fdata->topr, data->pr);
  gel(p1, data->e+1) = ZX_Z_divexact(gel(p1, data->e+1), data->p);
  fdata->pik  = p1;
}

/* return pol*ipi/p (mod top, pp) if it has integral coefficient, NULL
   otherwise. The result is reduced mod top, pp */
static GEN
DivideByPi(FAD_t *fdata, GEN pp, GEN ppp, GEN pol)
{
  GEN P;
  long i, l;
  pari_sp av = avma;

  /* "pol" is a t_INT or an FpX: signe() works for both */
  if (!signe(pol)) return pol;

  P = Fq_mul(pol, fdata->ipi, fdata->top, ppp); /* FpX */
  l  = lg(P);
  for (i = 2; i < l; i++)
  {
    GEN r;
    gel(P,i) = dvmdii(gel(P,i), fdata->p, &r);
    if (r != gen_0) { avma = av; return NULL; }
  }
  return FpX_red(P, pp);
}

/* return pol# = pol~/pi^vpi(pol~) mod pp where pol~(x) = pol(pi.x + beta)
 * has coefficients in the field defined by top and pi is a prime element */
static GEN
GetSharp(FAD_t *fdata, GEN pp, GEN ppp, GEN pol, GEN beta, long *pl)
{
  GEN p1, p2;
  long i, v, l, d = degpol(pol);
  pari_sp av = avma;

  if (!gequal0(beta))
    p1 = FqX_translate(pol, beta, fdata->topr, pp);
  else
    p1 = shallowcopy(pol);
  p2 = p1;
  for (v = 0;; v++)
  {
    for (i = 0; i <= v; i++)
    {
      GEN c = gel(p2, i+2);
      c = DivideByPi(fdata, pp, ppp, c);
      if (!c) break;
      gel(p2, i+2) = c;
    }
    if (i <= v) break;
    p1 = shallowcopy(p2);
  }
  if (!v) pari_err_BUG("GetSharp [no division]");

  for (l = v; l >= 0; l--)
  {
    GEN c = gel(p1, l+2);
    c = DivideByPi(fdata, pp, ppp, c);
    if (!c) { break; }
  }

  *pl = l; if (l < 2) return NULL;

  /* adjust powers */
  for (i = v+1; i <= d; i++)
    gel(p1, i+2) = Fq_mul(gel(p1, i+2),
                          gel(fdata->pik, i-v+1), fdata->topr, pp);

  return gerepilecopy(av, normalizepol(p1));
}

#ifdef CHECK_EXTENSIONS
static void
PrintValuations(GEN pol, GEN mod, GEN p)
{
  long i, d = degpol(pol);
  for (i = 0; i <= d; i++)
    err_printf("%d ", Z_pval(RgXQ_norm(gel(pol, i+2), mod), p));
}

/* Return the degree of pol mod the prime ideal of top */
static long
DegreeMod(FAD_t *fdata, GEN pp, GEN ppp, GEN pol)
{
  long d = degpol(pol); /* should be > 0 */
  pari_sp av = avma;

  do
  {
    GEN c = gel(pol, d+2);
    if (!gequal0(c) && !DivideByPi(fdata, pp, ppp, c))
      return d;
  }
  while (--d >= 1);
  avma = av; return 0;
}
#endif

/* Compute roots of pol in the residue field. Use table look-up if possible */
static GEN
Quick_FqX_roots(KRASNER_t *data, GEN pol)
{
  GEN rts;
  ulong ind = 0;

  pol = FpXQX_red(pol, data->uplr, data->p);

  if (data->roottable)
  {
    ind = ZXY_z_eval(pol, data->q[2], data->p[2]);
    if (gel(data->roottable, ind)) return gel(data->roottable, ind);
  }
  rts = FqX_roots(pol, data->uplr, data->p);

  if (ind) gel(data->roottable, ind) = gclone(rts);
  return rts;
}

static void
FreeRootTable(GEN T)
{
  if (T)
  {
    long j, l = lg(T);
    for (j = 1; j < l; j++)
      if (gel(T,j)) gunclone(gel(T,j));
  }
}

/* Return the number of roots of pol congruent to alpha modulo pi working
   modulo pp (all roots if alpha is NULL); if flag is non-zero, return 1
   as soon as a root is found. (Note: ppp = pp*p for DivideByPi) */
static long
RootCongruents(KRASNER_t *data, FAD_t *fdata, GEN pol, GEN alpha, GEN pp, GEN ppp, long sl, long flag)
{
  GEN R;
  long s, i;

  if (alpha)
  { /* FIXME: the data used in GetSharp is not reduced */
    long l;
    pol = GetSharp(fdata, pp, ppp, pol, alpha, &l);
    if (l <= 1) return l;
#ifdef CHECK_EXTENSIONS
    if (l != DegreeMod(fdata, pp, ppp, pol))
      pari_err_BUG("RootCongruents [degree mismatch in RCA]");
#endif
    /* decrease precision if sl gets bigger than a multiple of e */
    sl += l;
    if (sl >= data->e)
    {
      sl -= data->e;
      ppp = pp;
      pp = diviiexact(pp, data->p);
    }
  }

  R  = Quick_FqX_roots(data, pol);
  for (s = 0, i = 1; i < lg(R); i++)
  {
    s += RootCongruents(data, fdata, pol, gel(R, i), pp, ppp, sl, flag);
    if (flag && s) return 1;
  }
  return s;
}

/* pol is a ZXY defining a polynomial over the field defined by fdata
   If flag != 0, return 1 as soon as a root is found. Precision are done with
   a precision of pr. */
static long
RootCountingAlgorithm(KRASNER_t *data, FAD_t *fdata, GEN pol, long flag)
{
  long j, l, d;
  GEN P = cgetg_copy(pol, &l);

  P[1] = pol[1];
  d = l-3;
  for (j = 0; j < d; j++)
  {
    GEN cf = gel(pol, j+2);
    if (typ(cf) == t_INT)
      cf = diviiexact(cf, data->p);
    else
      cf = ZX_Z_divexact(cf, data->p);
    gel(P, j+2) = Fq_mul(cf, gel(fdata->pik, j+1), fdata->topr, data->pr);
  }
  gel(P, d+2) = gel(fdata->pik, d+1); /* pik[d] = pi^d/p */

  return RootCongruents(data, fdata, P, NULL, diviiexact(data->pr, data->p), data->pr, 0, flag);
}

/* Return non-zero if the field given by fdata defines a field isomorphic to
 * the one defined by pol */
static long
IsIsomorphic(KRASNER_t *data, FAD_t *fdata, GEN pol)
{
  long j, nb;
  pari_sp av = avma;

  if (RgX_is_ZX(pol)) return RootCountingAlgorithm(data, fdata, pol, 1);

  for (j = 1; j <= data->f; j++)
  {
    GEN p1 = FqX_FpXQ_eval(pol, fdata->zq, fdata->top, data->pr);
    nb = RootCountingAlgorithm(data, fdata, p1, 1);
    if (nb) { avma = av; return nb; }
    if (j < data->f)
      pol = FqX_FpXQ_eval(pol, data->frob, data->upl, data->pr);
  }
  avma = av; return 0;
}

/* Compute the number of conjugates fields of the field given by fdata */
static void
NbConjugateFields(KRASNER_t *data, FAD_t *fdata)
{
  GEN pol = fdata->eis;
  long j, nb;
  pari_sp av = avma;

  if (RgX_is_ZX(pol)) { /* split for efficiency; contains the case f = 1 */
    fdata->cj = data->e / RootCountingAlgorithm(data, fdata, pol, 0);
    avma = av; return;
  }

  nb = 0;
  for (j = 1; j <= data->f; j++)
  {
    GEN p1 = FqX_FpXQ_eval(pol, fdata->zq, fdata->top, data->pr);
    nb += RootCountingAlgorithm(data, fdata, p1, 0);
    if (j < data->f)
      pol = FqX_FpXQ_eval(pol, data->frob, data->upl, data->pr);
  }
  avma = av;
  fdata->cj = data->e * data->f / nb;
  return;
}

/* return a minimal list of polynomials generating all the totally
   ramified extensions of K^ur of degree e and discriminant
   p^{e + j - 1} in the tamely ramified case */
static GEN
TamelyRamifiedCase(KRASNER_t *data)
{
  long av = avma, g;
  GEN rep, p2, topx, m, eis, Xe = gpowgs(pol_x(0), data->e);

#ifdef CHECK_EXTENSIONS
  FAD_t fdata;
  long cnt = 0, nb, j;
  GEN vpl;
  err_printf("Number of extensions: %ld\n", itos(data->nbext));
#endif

  g   = ugcd(data->e, umodiu(data->qm1, data->e)); /* (e, q-1) */
  m   = stoi(data->e/g);
  rep = zerovec(g);

  eis = gadd(Xe, data->p);
  topx = get_topx(data, eis);
  p2 = mkvec2(topx, m);
  gel(rep, 1) = p2;
#ifdef CHECK_EXTENSIONS
  vpl = zerovec(g);
  gel(vpl, 1) = eis;
  if (data->e == 1)
    nb = 1;
  else
  {
    FieldData(data, &fdata, eis, topx);
    NbConjugateFields(data, &fdata);
    nb = fdata.cj;
  }
  err_printf("Found %ld field(s)\n", nb);
  cnt += nb;
#endif

  if (g > 1)
  {
    ulong pmodg = umodiu(data->p, g);
    long r = 1, ct = 1;
    GEN sv = InitSieve(g-1);
    while (r)
    {
      long gr;
      GEN p1 = FpXQ_powu(pol_x(data->v), r, data->uplr, data->p);
      eis = gadd(Xe, ZX_Z_mul(p1, data->p)); /* Adding a ZX and a ZY (cste coefficient) */
      ct++;
      topx = get_topx(data, eis);
      p2 = mkvec2(topx, m);
      gel(rep, ct) = p2;
#ifdef CHECK_EXTENSIONS
      gel(vpl, ct) = eis;
      FieldData(data, &fdata, eis, topx);
      for (j = 1; j < ct; j++)
        if (IsIsomorphic(data, &fdata, gel(vpl, j)))
          pari_err_BUG("TamelyRamifiedCase [isomorphic fields]");
      NbConjugateFields(data, &fdata);
      nb = fdata.cj;
      err_printf("Found %ld field(s)\n", nb);
      cnt += nb;
#endif
      gr = r;
      do
      {
        SetSieveValue(sv, gr);
        gr = Fl_mul(gr, pmodg, g);
      }
      while (gr != r);
      r  = NextZeroValue(sv, r);
    }
    setlg(rep, ct+1);
  }

#ifdef CHECK_EXTENSIONS
  if (!equaliu(data->nbext, cnt))
    pari_err_BUG("TamelyRamifiedCase [incorrect #fields]");
#endif

  return gerepilecopy(av, rep);
}

static long
function_l(GEN p, long a, long b, long i)
{
  long l = 1 + a - z_pval(i, p);
  if (i < b) l++;
  return (l < 1)? 1: l;
}

/* Structure of the coefficients set Omega. Each coefficient is [start, zr]
 * meaning all the numbers of the form:
 *   zeta_0 * p^start + ... + zeta_s * p^c (s = c - start)
 * with zeta_i roots of unity (powers of zq + zero), zeta_0 = 0 is
 * possible iff zr = 1 */
static GEN
StructureOmega(KRASNER_t *data, GEN *pnbpol)
{
  GEN nbpol, O = cgetg(data->e + 1, t_VEC);
  long i;

  /* i = 0 */
  gel(O, 1) = mkvecsmall2(1, 0);
  nbpol = mulii(data->qm1, powiu(data->q, data->c - 1));
  for (i = 1; i < data->e; i++)
  {
    long v_start, zero = 0;
    GEN nbcf, p1;
    v_start = function_l(data->p, data->a, data->b, i);
    p1 = powiu(data->q, data->c - v_start);
    if (i == data->b)
      nbcf = mulii(p1, data->qm1);
    else
    {
      nbcf = mulii(p1, data->q);
      zero = 1;
    }
    gel(O, i+1) = mkvecsmall2(v_start, zero);
    nbpol = mulii(nbpol, nbcf);
  }
  *pnbpol = nbpol; return O;
}

/* a random element of the finite field */
static GEN
RandomFF(KRASNER_t *data)
{
  long i, l = data->f + 2, p = itou(data->p);
  GEN c = cgetg(l, t_POL);
  c[1] = evalvarn(data->v);
  for (i = 2; i < l; i++) gel(c, i) = utoi(random_Fl(p));
  return ZX_renormalize(c, l);
}
static GEN
RandomPol(KRASNER_t *data, GEN Omega)
{
  long i, j, l = data->e + 3, end = data->c;
  GEN pol = cgetg(l, t_POL);
  pol[1] = evalsigne(1) | evalvarn(0);
  for (i = 1; i <= data->e; i++)
  {
    GEN c, cf = gel(Omega, i);
    long st = cf[1], zr = cf[2];
    /* c = sum_{st <= j <= end} x_j p^j, where x_j are random Fq mod (p,upl)
     * If (!zr), insist on x_st != 0 */
    for (;;) {
      c = RandomFF(data);
      if (zr || signe(c)) break;
    }
    for (j = 1; j <= end-st; j++)
      c = ZX_add(c, ZX_Z_mul(RandomFF(data), gel(data->pk, j)));
    c = ZX_Z_mul(c, gel(data->pk, st));
    c = FpX_red(c, data->pr);
    switch(degpol(c))
    {
      case -1: c = gen_0; break;
      case  0: c = gel(c,2); break;
    }
    gel(pol, i+1) = c;
  }
  gel(pol, i+1) = gen_1; /* monic */
  return pol;
}

static void
CloneFieldData(FAD_t *fdata)
{
 fdata->top = gclone(fdata->top);
 fdata->topr= gclone(fdata->topr);
 fdata->zq  = gclone(fdata->zq);
 fdata->eis = gclone(fdata->eis);
 fdata->pi  = gclone(fdata->pi);
 fdata->ipi = gclone(fdata->ipi);
 fdata->pik = gclone(fdata->pik);
}
static void
FreeFieldData(FAD_t *fdata)
{
  gunclone(fdata->top);
  gunclone(fdata->topr);
  gunclone(fdata->zq);
  gunclone(fdata->eis);
  gunclone(fdata->pi);
  gunclone(fdata->ipi);
  gunclone(fdata->pik);
}

static GEN
WildlyRamifiedCase(KRASNER_t *data)
{
  long nbext, ct, fd, nb = 0, j;
  GEN nbpol, rpl, rep, Omega;
  FAD_t **vfd;
  pari_timer T;
  pari_sp av = avma, av2;

  /* Omega = vector giving the structure of the set Omega */
  /* nbpol = number of polynomials to consider = |Omega| */
  Omega = StructureOmega(data, &nbpol);
  nbext = itos_or_0(data->nbext);
  if (!nbext || (nbext & ~LGBITS))
    pari_err_OVERFLOW("padicfields [too many extensions]");

  if (DEBUGLEVEL>0) {
    err_printf("There are %ld extensions to find and %Ps polynomials to consider\n", nbext, nbpol);
    timer_start(&T);
  }

  vfd = (FAD_t**)new_chunk(nbext);
  for (j = 0; j < nbext; j++) vfd[j] = (FAD_t*)new_chunk(sizeof(FAD_t));

  ct = 0;
  fd = 0;
  av2 = avma;

  while (fd < nbext)
  { /* Jump randomly among the polynomials : seems best... */
    rpl = RandomPol(data, Omega);
    if (DEBUGLEVEL>3) err_printf("considering polynomial %Ps\n", rpl);
#ifdef CHECK_EXTENSIONS
    {
      GEN disc = poldisc0(rpl, 0);
      long e = data->e, f = data->f, j = data->j;
      disc = RgXQ_norm(disc, data->upl);
      if (Z_pval(disc, data->p) != f*(e+j-1))
        pari_err_BUG("WildlyRamifiedCase [incorrect discriminant]");
    }
#endif

    for (j = 0; j < ct; j++)
    {
      nb = IsIsomorphic(data, vfd[j], rpl);
      if (nb) break;
    }
    if (!nb)
    {
      GEN topx = get_topx(data, rpl);
      FAD_t *fdata = (FAD_t*)vfd[ct];
      FieldData(data, fdata, rpl, topx);
      CloneFieldData(fdata);
      NbConjugateFields(data, fdata);
      nb = fdata->cj;
      fd += nb;
      ct++;
      if (DEBUGLEVEL>1)
        err_printf("%ld more extension%s\t(%ld/%ld, %ldms)\n",
                   nb, (nb == 1)? "": "s", fd, nbext, timer_delay(&T));
    }
    avma = av2;
  }

  rep = cgetg(ct+1, t_VEC);
  for (j = 0; j < ct; j++)
  {
    GEN topx = ZX_copy(((FAD_t*)vfd[j])->top);
    GEN p1;
    setvarn(topx, 0);
    p1 = mkvec2(topx, stoi(((FAD_t*)vfd[j])->cj));
    gel(rep, j+1) = p1;
    FreeFieldData((FAD_t*)vfd[j]);
  }
  FreeRootTable(data->roottable);
  return gerepileupto(av, rep);
}

/* return the minimal polynomial (mod pr) of an element nu of (F_q)^x
 * where q = p^f that is l-maximal for all primes l dividing g = (e,q-1). */
static GEN
CycloPol(KRASNER_t *d)
{
  long v = d->v, e = d->e;
  GEN T, z, fa, p = d->p;

  /* v - primroot(p) */
  if (d->f == 1)
    return deg1pol_shallow(gen_1, Fp_neg(pgener_Fp(p), d->pr), v);

  T = init_Fq(d->p, d->f, v);
  fa = factoru( ugcd(e, umodiu(d->qm1, e)) );
  z = gener_FpXQ_local(T, d->p, zv_to_ZV(gel(fa,1)));
  z = ZpXQ_sqrtnlift(scalarpol(gen_1,varn(T)), d->qm1, z, T, d->p, d->r);
  return FpX_red(ZXQ_charpoly(z, T, v), d->pr);
}

/* return [ p^1, p^2, ..., p^c ] */
static GEN
get_pk(KRASNER_t *data)
{
  long i, l = data->c + 1;
  GEN pk = cgetg(l, t_VEC), p = data->p;
  gel(pk, 1) = p;
  for (i = 2; i <= data->c; i++) gel(pk, i) = mulii(gel(pk, i-1), p);
  return pk;
}

/* Compute an absolute polynomial for all the totally ramified
   extensions of Q_p(z) of degree e and discriminant p^{e + j - 1}
   where z is a root of upl defining an unramified extension of Q_p */
/* See padicfields for the meaning of flag */
static GEN
GetRamifiedPol(GEN p, GEN efj, long flag)
{
  long e = efj[1], f = efj[2], j = efj[3], i, l;
  const long v = 1;
  GEN L, pols;
  KRASNER_t data;
  pari_sp av = avma;

  if (DEBUGLEVEL>1)
    err_printf("  Computing extensions with decomposition [e, f, j] = [%ld, %ld, %ld]\n", e,f,j);
  data.p   = p;
  data.e   = e;
  data.f   = f;
  data.j   = j;
  data.a   = j/e;
  data.b   = j%e;
  data.c   = (e+2*j)/e+1;
  data.q   = powiu(p, f);
  data.qm1 = subis(data.q, 1);
  data.v   = v;
  data.r   = 1 + ceildiv(2*j + 3, e); /* enough precision */
  data.pr  = powiu(p, data.r);
  data.nbext = NumberExtensions(&data);

  if (flag == 2) return data.nbext;

  data.upl   = CycloPol(&data);
  /* mv = -v mod upl. If f = 1, then upl = v + c, hence mv = c */
  data.mv    = f == 1? gel(data.upl, 2)
                     : FpX_neg(pol_x(v), data.pr);
  data.uplr  = FpX_red(data.upl, data.p);
  data.frob  = FpXQ_pow(pol_x(v), p, data.upl, data.pr);
  if (DEBUGLEVEL>1) err_printf("  Unramified part %Ps\n", data.upl);
  data.roottable = NULL;
  if (j)
  {
    if (lgefint(data.q) == 3)
    {
      ulong npol = upowuu(data.q[2], e+1);
      if (npol && npol < (1<<19)) data.roottable = const_vec(npol, NULL);
    }
    data.pk = get_pk(&data);
    L = WildlyRamifiedCase(&data);
  }
  else
    L = TamelyRamifiedCase(&data);

  pols = cgetg_copy(L, &l);
  if (flag == 1)
  {
    GEN E = utoipos(e), F = utoipos(f), D = utoi(f*(e+j-1));
    for (i = 1; i < l; i++)
    {
      GEN T = gel(L,i);
      gel(pols, i) = mkvec5(ZX_copy(gel(T, 1)), E,F,D, icopy(gel(T, 2)));
    }
  }
  else
  {
    for (i = 1; i < l; i++)
    {
      GEN T = gel(L,i);
      gel(pols, i) = ZX_copy(gel(T,1));
    }
  }
  return gerepileupto(av, pols);
}

static GEN
possible_efj(GEN p, long m)
{ /* maximal possible discriminant valuation d <= m * (1+v_p(m)) - 1 */
  /* 1) [j = 0, tame] d = m - f with f | m and v_p(f) = v_p(m), or
   * 2) [j > 0, wild] d >= m, j <= v_p(e)*e   */
  ulong m1, pve, pp = p[2]; /* pp used only if v > 0 */
  long ve, v = u_pvalrem(m, p, &m1);
  GEN L, D = divisorsu(m1);
  long i, taum1 = lg(D)-1, nb = 0;

  if (v) {
    for (pve = 1,ve = 1; ve <= v; ve++) { pve *= pp; nb += pve * ve; }
    nb = itos_or_0(muluu(nb, zv_sum(D)));
    if (!nb || is_bigint( mului(pve, sqru(v)) ) )
      pari_err_OVERFLOW("padicfields [too many ramification possibilities]");
  }
  nb += taum1; /* upper bound for the number of possible triples [e,f,j] */

  L = cgetg(nb + 1, t_VEC);
  /* 1) tame */
  for (nb=1, i=1; i < lg(D); i++)
  {
    long e = D[i], f = m / e;
    gel(L, nb++) = mkvecsmall3(e, f, 0);
  }
  /* 2) wild */
  /* Ore's condition: either
   * 1) j = v_p(e) * e, or
   * 2) j = a e + b, with 0 < b < e and v_p(b) <= a < v_p(e) */
  for (pve = 1, ve = 1; ve <= v; ve++)
  {
    pve *= pp; /* = p^ve */
    for (i = 1; i < lg(D); i++)
    {
      long a,b, e = D[i] * pve, f = m / e;
      for (b = 1; b < e; b++)
        for (a = u_lval(b, pp); a < ve; a++)
          gel(L, nb++) = mkvecsmall3(e, f,  a*e + b);
      gel(L, nb++) = mkvecsmall3(e, f, ve*e);
    }
  }
  setlg(L, nb); return L;
}

static GEN
pols_from_efj(pari_sp av, GEN EFJ, GEN p, long flag)
{
  long i, l;
  GEN L = cgetg_copy(EFJ, &l);
  if (l == 1) { avma = av; return flag == 2? gen_0: cgetg(1, t_VEC); }
  for (i = 1; i < l; i++) gel(L,i) = GetRamifiedPol(p, gel(EFJ,i), flag);
  if (flag == 2) return gerepileuptoint(av, ZV_sum(L));
  return gerepilecopy(av, shallowconcat1(L));
}

/* return a minimal list of polynomials generating all the extensions of
   Q_p of given degree N; if N is a t_VEC [n,d], return extensions of degree n
   and discriminant p^d. */
/* Return only the polynomials if flag = 0 (default), also the ramification
   degree, the residual degree and the discriminant if flag = 1 and only the
   number of extensions if flag = 2 */
GEN
padicfields0(GEN p, GEN N, long flag)
{
  pari_sp av = avma;
  long m = 0, d = -1;
  GEN L;

  if (typ(p) != t_INT) pari_err_TYPE("padicfields",p);
  /* be nice to silly users */
  if (!BPSW_psp(p)) pari_err_PRIME("padicfields",p);
  switch(typ(N))
  {
    case t_VEC:
      if (lg(N) != 3) pari_err_TYPE("padicfields",N);
      d = gtos(gel(N,2));
      N = gel(N,1); /* fall through */
    case t_INT:
      m = itos(N);
      if (m <= 0) pari_err_DOMAIN("padicfields", "degree", "<=", gen_0,N);
      break;
    default:
      pari_err_TYPE("padicfields",N);
  }
  if (d >= 0) return padicfields(p, m, d, flag);
  L = possible_efj(p, m);
  return pols_from_efj(av, L, p, flag);
}

GEN
padicfields(GEN p, long m, long d, long flag)
{
  long av = avma;
  GEN L = possible_efj_by_d(p, m, d);
  return pols_from_efj(av, L, p, flag);
}
