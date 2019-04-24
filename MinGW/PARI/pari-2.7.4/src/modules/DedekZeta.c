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
/*                     DEDEKIND ZETA FUNCTION                      */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"
static GEN
dirzetak0(GEN nf, ulong N)
{
  GEN vect, c, c2, T = nf_get_pol(nf), index = nf_get_index(nf);
  pari_sp av = avma, av2;
  const ulong SQRTN = (ulong)(sqrt(N) + 1e-3);
  ulong i, p, lx;
  long court[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};
  forprime_t S;

  (void)evallg(N+1);
  c  = cgetalloc(t_VECSMALL, N+1);
  c2 = cgetalloc(t_VECSMALL, N+1);
  c2[1] = c[1] = 1; for (i=2; i<=N; i++) c[i] = 0;
  u_forprime_init(&S, 2, N);
  av2 = avma;
  while ( (p = u_forprime_next(&S)) )
  {
    avma = av2;
    if (umodiu(index, p)) /* p does not divide index */
    {
      vect = gel(Flx_degfact(ZX_to_Flx(T,p), p),1);
      lx = lg(vect);
    }
    else
    {
      GEN P;
      court[2] = p; P = idealprimedec(nf,court);
      lx = lg(P); vect = cgetg(lx,t_VECSMALL);
      for (i=1; i<lx; i++) vect[i] = pr_get_f(gel(P,i));
    }
    if (p <= SQRTN)
      for (i=1; i<lx; i++)
      {
        ulong qn, q = upowuu(p, vect[i]); /* Norm P[i] */
        if (!q || q > N) break;
        memcpy(c2 + 2, c + 2, (N-1)*sizeof(long));
        /* c2[i] <- c[i] + sum_{k = 1}^{v_q(i)} c[i/q^k] for all i <= N */
        for (qn = q; qn <= N; qn *= q)
        {
          ulong k0 = N/qn, k, k2; /* k2 = k*qn */
          for (k = k0, k2 = k*qn; k > 0; k--, k2 -=qn) c2[k2] += c[k];
          if (q > k0) break; /* <=> q*qn > N */
        }
        swap(c, c2);
      }
    else /* p > sqrt(N): simpler */
      for (i=1; i<lx; i++)
      {
        ulong k, k2; /* k2 = k*p */
        if (vect[i] > 1) break;
        /* c2[i] <- c[i] + sum_{k = 1}^{v_q(i)} c[i/q^k] for all i <= N */
        for (k = N/p, k2 = k*p; k > 0; k--, k2 -= p) c[k2] += c[k];
      }
  }
  avma = av;
  pari_free(c2); return c;
}

GEN
dirzetak(GEN nf, GEN b)
{
  GEN z, c;
  long n;

  if (typ(b) != t_INT) pari_err_TYPE("dirzetak",b);
  if (signe(b) <= 0) return cgetg(1,t_VEC);
  nf = checknf(nf);
  n = itou_or_0(b); if (!n) pari_err_OVERFLOW("dirzetak");
  c = dirzetak0(nf, n);
  z = vecsmall_to_vec(c); pari_free(c); return z;
}

/* return a t_REAL */
GEN
zeta_get_limx(long r1, long r2, long bit)
{
  pari_sp av = avma;
  GEN p1, p2, c0, c1, A0;
  long r = r1 + r2, N = r + r2;

  /* c1 = N 2^(-2r2 / N) */
  c1 = mulrs(powrfrac(real2n(1, DEFAULTPREC), -2*r2, N), N);

  p1 = powru(Pi2n(1, DEFAULTPREC), r - 1);
  p2 = mulir(powuu(N,r), p1); shiftr_inplace(p2, -r2);
  c0 = sqrtr( divrr(p2, powru(c1, r+1)) );

  A0 = logr_abs( gmul2n(c0, bit) ); p2 = divrr(A0, c1);
  p1 = divrr(mulur(N*(r+1), logr_abs(p2)), addsr(2*(r+1), gmul2n(A0,2)));
  return gerepileuptoleaf(av, divrr(addrs(p1, 1), powruhalf(p2, N)));
}
/* N_0 = floor( C_K / limx ). Large */
long
zeta_get_N0(GEN C,  GEN limx)
{
  long e;
  pari_sp av = avma;
  GEN z = gcvtoi(gdiv(C, limx), &e); /* avoid truncation error */
  if (e >= 0 || is_bigint(z))
    pari_err_OVERFLOW("zeta_get_N0 [need too many primes]");
  if (DEBUGLEVEL>1) err_printf("\ninitzeta: N0 = %Ps\n", z);
  avma = av; return itos(z);
}

/* even i such that limx^i ( (i\2)! )^r1 ( i! )^r2 ~ B. Small. */
static long
get_i0(long r1, long r2, GEN B, GEN limx)
{
  long imin = 1, imax = 1400;
  while(imax - imin >= 4)
  {
    long i = (imax + imin) >> 1;
    GEN t = powru(limx, i);
    if (!r1)      t = mulrr(t, powru(mpfactr(i  , DEFAULTPREC), r2));
    else if (!r2) t = mulrr(t, powru(mpfactr(i/2, DEFAULTPREC), r1));
    else {
      GEN u1 = mpfactr(i/2, DEFAULTPREC);
      GEN u2 = mpfactr(i,   DEFAULTPREC);
      if (r1 == r2) t = mulrr(t, powru(mulrr(u1,u2), r1));
      else t = mulrr(t, mulrr(powru(u1,r1), powru(u2,r2)));
    }
    if (mpcmp(t, B) >= 0) imax = i; else imin = i;
  }
  return imax & ~1; /* make it even */
}

/* assume limx = zeta_get_limx(r1, r2, bit), a t_REAL */
long
zeta_get_i0(long r1, long r2, long bit, GEN limx)
{
  pari_sp av = avma;
  GEN B = gmul(sqrtr( divrr(powrs(mppi(DEFAULTPREC), r2-3), limx) ),
               gmul2n(powuu(5, r1), bit + r2));
  long i0 = get_i0(r1, r2, B, limx);
  if (DEBUGLEVEL>1) { err_printf("i0 = %ld\n",i0); err_flush(); }
  avma = av; return i0;
}

/* sum(j=1, r-k+1, A[j] * B[j]), assumes k <= r and A[j],B[j] are 'mp' */
INLINE GEN
sumprod(GEN A, GEN B, long r, long k)
{
  GEN s = signe(gel(A,1))? mpmul(gel(A,1), gel(B,1)): gen_0;
  long j;
  for (j=2; j<=r-k+1; j++)
    if (signe(gel(A,j))) s = mpadd(s, mpmul(gel(A,j), gel(B,j)));
  return s;
}

GEN
initzeta(GEN T, long prec)
{
  GEN znf, nf, bnf, gr2, gru, p1, p2, cst, coef;
  GEN limx, resi,zet,C,coeflog,racpi,aij,tabj,colzero, tabcstn, tabcstni;
  GEN c_even, ck_even, c_odd, ck_odd, serie_even, serie_odd, serie_exp;
  GEN VOID;
  long N0, i0, r1, r2, r, R, N, i, j, k, n, bit = prec2nbits(prec) + 6;
  pari_timer ti;

  pari_sp av, av2;
  long court[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};

  /*************** residue & constants ***************/
  T = get_bnfpol(T, &bnf, &nf);
  if (!nf) {
    bnf = Buchall(T, 0, prec);
    nf = bnf_get_nf(bnf);
  }
  else if (!bnf) {
    if (nf_get_prec(nf) < prec) nf = nfnewprec_shallow(nf, prec);
    bnf = Buchall(nf, 0, prec);
  } else if (nf_get_prec(bnf) < prec) {
    bnf = bnfnewprec(bnf, prec);
    nf = bnf_get_nf(bnf);
  }

  prec = precdbl(prec);
  racpi = sqrtr(mppi(prec));
  /* all the above left on stack for efficiency */

  /* class number & regulator */
  N = nf_get_degree(nf);
  nf_get_sign(nf, &r1, &r2);
  gr2 = gmael(nf,2,2);
  r = r1 + r2; R = r+2;

  znf = cgetg(10,t_VEC);
  VOID = cgetg(1, t_STR); /* unused value */
  av = avma;
  resi = gerepileupto(av,
           gdivgs(mpmul(shifti(bnf_get_no(bnf),r1), bnf_get_reg(bnf)),
                  bnf_get_tuN(bnf))); /* hr 2^r1 / w*/
  av = avma;
  p1 = sqrtr_abs(itor(nf_get_disc(nf), prec));
  p2 = gmul2n(powru(racpi,N), r2);
  cst = gerepileuptoleaf(av, divrr(p1,p2));

  /* N0, i0 */
  limx = zeta_get_limx(r1, r2, bit);
  N0 = zeta_get_N0(cst, limx);
  i0 = zeta_get_i0(r1, r2, bit + 4, limx);

  /* Array of i/cst (i=1..N0) */
  av = avma;
  tabcstn  = cgetg(N0+1,t_VEC);
  tabcstni = cgetg(N0+1,t_VEC);
  p1 = invr(cst);
  for (i=1; i<=N0; i++) gel(tabcstni,i) = gel(tabcstn,i) = mulur(i,p1);
  tabcstn  = gclone(tabcstn);
  tabcstni = gclone(tabcstni);

  /********** compute a(i,j) **********/
  if (DEBUGLEVEL>1) timer_start(&ti);
  zet = cgetg(R,t_VEC); gel(zet,1) = mpeuler(prec);
  for (i=2; i<R; i++) gel(zet,i) = szeta(i, prec);

  aij = cgetg(i0+1,t_VEC);
  for (i=1; i<=i0; i++) gel(aij,i) = cgetg(R,t_VEC);

  c_even = real2n(r1, prec);
  c_odd = gmul(c_even, powru(racpi,r1));
  if (r&1) c_odd = gneg_i(c_odd);
  ck_even = cgetg(R,t_VEC); ck_odd = cgetg(r2+2,t_VEC);
  for (k=1; k<R; k++)
  {
    GEN t = mulri(gel(zet,k), addis(shifti(gr2, k), r1));
    shiftr_inplace(t, -k);
    if (k&1) togglesign(t);
    gel(ck_even,k) = t;
  }
  gru = utoipos(r);
  for (k = 1; k <= r2+1; k++)
  {
    GEN t = mulri(gel(zet,k), subis(shifti(gru,k), r1));
    shiftr_inplace(t, -k);
    if (k&1) togglesign(t);
    gel(ck_odd,k) = addsr(r, t);
  }
  if (r1) gel(ck_odd,1) = subrr(gel(ck_odd,1), mulur(r1, mplog2(prec)));
  serie_even = cgetg(r+3,t_SER);
  serie_odd = cgetg(r2+3,t_SER);
  serie_even[1] = serie_odd[1] = evalsigne(1)|_evalvalp(1);
  i = 0;
  while (i < i0/2)
  {
    for (k=1; k<R; k++) gel(serie_even,k+1) = gdivgs(gel(ck_even,k),k);
    serie_exp = gmul(c_even, gexp(serie_even,0));
    p1 = gel(aij,2*i+1);
    for (j=1; j<R; j++) p1[j] = serie_exp[r+3-j];

    for (k=1; k<=r2+1; k++) gel(serie_odd,k+1) = gdivgs(gel(ck_odd,k),k);
    serie_exp = gmul(c_odd, gexp(serie_odd,0));
    p1 = gel(aij,2*i+2);
    for (j=1; j<=r2+1; j++) p1[j] = serie_exp[r2+3-j];
    for (   ; j<R; j++) gel(p1,j) = gen_0;
    i++;

    c_even = gdiv(c_even,gmul(powuu(i,r),powuu(2*i-1,r2)));
    c_odd  = gdiv(c_odd, gmul(powuu(i,r2),powuu(2*i+1,r)));
    c_even = gmul2n(c_even,-r2);
    c_odd  = gmul2n(c_odd,r1-r2);
    if (r1 & 1) { c_even = gneg_i(c_even); c_odd = gneg_i(c_odd); }
    p1 = gr2; p2 = gru;
    for (k=1; k<R; k++)
    {
      p1 = gdivgs(p1,2*i-1); p2 = gdivgs(p2,2*i);
      gel(ck_even,k) = gadd(gel(ck_even,k), gadd(p1,p2));
    }
    p1 = gru; p2 = gr2;
    for (k=1; k<=r2+1; k++)
    {
      p1 = gdivgs(p1,2*i+1); p2 = gdivgs(p2,2*i);
      gel(ck_odd,k) = gadd(gel(ck_odd,k), gadd(p1,p2));
    }
  }
  aij = gerepilecopy(av, aij);
  if (DEBUGLEVEL>1) timer_printf(&ti,"a(i,j)");
  gel(znf,1) = mkvecsmall2(r1,r2);
  gel(znf,2) = resi;
  gel(znf,5) = cst;
  gel(znf,6) = logr_abs(cst);
  gel(znf,7) = aij;

  /************* Calcul du nombre d'ideaux de norme donnee *************/
  coef = dirzetak0(nf,N0); tabj = cgetg(N0+1,t_MAT);
  if (DEBUGLEVEL>1) timer_printf(&ti,"coef");
  colzero = zerocol(r+1);
  for (i=1; i<=N0; i++)
    if (coef[i])
    {
      GEN t = cgetg(r+2,t_COL);
      p1 = logr_abs(gel(tabcstn,i)); togglesign(p1);
      gel(t,1) = utoi(coef[i]);
      gel(t,2) = mulur(coef[i], p1);
      for (j=2; j<=r; j++)
      {
        pari_sp av2 = avma;
        gel(t,j+1) = gerepileuptoleaf(av2, divru(mulrr(gel(t,j), p1), j));
      }
      gel(tabj,i) = t; /* tabj[n,j] = coef(n)*ln(c/n)^(j-1)/(j-1)! */
    }
    else
      gel(tabj,i) = colzero;
  if (DEBUGLEVEL>1) timer_printf(&ti,"a(n)");

  coeflog=cgetg(N0+1,t_VEC); gel(coeflog,1) = VOID;
  for (i=2; i<=N0; i++)
    if (coef[i])
    {
      court[2] = i; p1 = glog(court,prec);
      setsigne(p1, -1); gel(coeflog,i) = p1;
    }
    else gel(coeflog,i) = VOID;
  if (DEBUGLEVEL>1) timer_printf(&ti,"log(n)");

  gel(znf,3) = tabj;
  gel(znf,8) = vecsmall_copy(coef);
  gel(znf,9) = coeflog;

  /******************** Calcul des coefficients Cik ********************/
  C = cgetg(r+1,t_MAT);
  for (k=1; k<=r; k++) gel(C,k) = cgetg(i0+1,t_COL);
  av2 = avma;
  for (i=1; i<=i0; i++)
  {
    for (k=1; k<=r; k++)
    {
      GEN A = gel(aij,i) + k; /* A[j] = aij[i, j+k] */
      GEN t = sumprod(A, gel(tabj,1), r, k);
      /* n = 1 */
      if (i > 1 && signe(t)) t = mpmul(t, gel(tabcstni,1));
      for (n=2; n<=N0; n++)
        if (coef[n])
        { /* sum(j=1, r-k+1, aij[i,j+k] * tabj[n, j]) */
          GEN s = sumprod(A, gel(tabj,n), r, k);
          if (!signe(s)) continue;
          if (i > 1) s = mpmul(s, gel(tabcstni,n));
          t = mpadd(t,s);
        }
      togglesign(t);
      gcoeff(C,i,k) = gerepileuptoleaf(av2,t);
      av2 = avma;
    }
    if (i > 1 && i < i0) {
      for (n=1; n<=N0; n++)
        if (coef[n]) mpmulz(gel(tabcstni,n), gel(tabcstn,n), gel(tabcstni,n));
    }
  }
  gel(znf,4) = C;
  if (DEBUGLEVEL>1) timer_printf(&ti,"Cik");
  gunclone(tabcstn); gunclone(tabcstni);
  pari_free((void*)coef); return znf;
}

static void
znf_get_sign(GEN znf, long *r1, long *r2)
{ GEN v = gel(znf,1); *r1 = v[1]; *r2 = v[2]; }

/* s != 0,1 */
static GEN
slambdak(GEN znf, long s, long flag, long prec)
{
  GEN resi, C, cst, cstlog, coeflog, cs, coef;
  GEN lambd, gammas2, gammaunmoins2, var1, var2;
  GEN gar, val, valm, valk, valkm;
  long r1, r2, r, i0, i, k, N0;

  znf_get_sign(znf, &r1, &r2); r = r1+r2;
  resi   = gel(znf,2);
  C      = gel(znf,4);
  cst    = gel(znf,5);
  cstlog = gel(znf,6);
  coef   = gel(znf,8);
  coeflog= gel(znf,9);
  i0 = nbrows(C);
  N0 = lg(coef)-1;

  if (s < 0 && (r2 || !odd(s))) s = 1 - s;

  /* s >= 2 or s < 0 */
  lambd = gdiv(resi, mulss(s, s-1));
  gammas2 = ggamma(gmul2n(stoi(s),-1),prec);
  gar = gpowgs(gammas2,r1);
  cs = mpexp( mulrs(cstlog,s) );
  val = stoi(s); valm = stoi(1 - s);
  if (s < 0) /* r2 = 0 && odd(s) */
  {
    gammaunmoins2 = ggamma(gmul2n(valm,-1),prec); /* gamma((1-s) / 2) */
    var1 = var2 = gen_1;
    for (i=2; i<=N0; i++)
      if (coef[i])
      {
        GEN gexpro = mpexp(mulrs(gel(coeflog,i),s));
        var1 = gadd(var1, mulsr(coef[i],gexpro));
        var2 = gadd(var2, divsr(coef[i],mulsr(i,gexpro)));
      }
    lambd = gadd(lambd,gmul(gmul(var1,cs),gar));
    lambd = gadd(lambd,gmul(gmul(var2,gdiv(cst,cs)),
                            gpowgs(gammaunmoins2,r1)));
    var1 = gen_0;
    for (i=1; i<=i0; i+=2)
    {
      valk  = val;
      valkm = valm;
      for (k=1; k<=r; k++)
      {
        GEN c = gcoeff(C,i,k);
        var1 = mpadd(var1,mpdiv(c,valk )); valk  = mulii(val,valk);
        var1 = mpadd(var1,mpdiv(c,valkm)); valkm = mulii(valm,valkm);
      }
      val  = addis(val, 2);
      valm = addis(valm,2);
    }
  }
  else
  {
    GEN tabj = gel(znf,3), aij = gel(znf,7), A = gel(aij,s);
    long n;

    gar = gmul(gar,gpowgs(mpfactr(s-1,prec),r2)); /* x gamma(s)^r2 */
    /* n = 1 */
    var1 = gen_1;
    var2 = (s <= i0)? sumprod(A, gel(tabj,1), r, 0): gen_0;
    for (n=2; n<=N0; n++)
      if (coef[n])
      {
        GEN gexpro = mpexp( mulrs(gel(coeflog,n),s) );
        var1 = mpadd(var1, mulsr(coef[n],gexpro));
        if (s <= i0)
        {
          GEN t = sumprod(A, gel(tabj,n), r, 0);
          if (!signe(t)) continue;
          var2 = mpadd(var2, mpdiv(t, mulsr(n,gexpro)));
        }
      }
    lambd = gadd(lambd,gmul(gmul(var1,cs),gar));
    lambd = gadd(lambd,gmul(var2,gdiv(cst,cs)));
    var1 = gen_0;
    for (n=1; n<=i0; n++)
    {
      valk  = val;
      valkm = valm;
      if (n == s)
        for (k=1; k<=r; k++)
        {
          GEN c = gcoeff(C,n,k);
          var1 = mpadd(var1,mpdiv(c,valk)); valk = mulii(val,valk);
        }
      else
      for (k=1; k<=r; k++)
      {
          GEN c = gcoeff(C,n,k);
          var1 = mpadd(var1,mpdiv(c,valk )); valk  = mulii(val,valk);
          var1 = mpadd(var1,mpdiv(c,valkm)); valkm = mulii(valm,valkm);
      }
      val  = addis(val,1);
      valm = addis(valm,1);
    }
  }
  lambd = gadd(lambd, var1);
  if (!flag) lambd = gdiv(lambd,gmul(gar,cs)); /* zetak */
  return lambd;
}

/* s not an integer */
static GEN
cxlambdak(GEN znf, GEN s, long flag, long prec)
{
  GEN resi, C, cst, cstlog, coeflog, cs, coef;
  GEN lambd, gammas, gammaunmoins, gammas2, gammaunmoins2, var1, var2;
  GEN smoinun, unmoins, gar, val, valm, valk, valkm, Pi, sPi;
  long r1, r2, r, i0, i, k, N0, bigprec;

  znf_get_sign(znf, &r1, &r2);
  resi   = gel(znf,2);
  C      = gel(znf,4);
  cst    = gel(znf,5);
  cstlog = gel(znf,6);
  coef   = gel(znf,8);
  coeflog= gel(znf,9);
  r1 = mael(znf,1,1);
  r2 = mael(znf,1,2); r = r1+r2;
  i0 = nbrows(C);
  N0 = lg(coef)-1;
  bigprec = precision(cst);

  Pi = mppi(bigprec);
  s = gtofp(s, bigprec); sPi = gmul(s, Pi);
  smoinun = gsubgs(s,1);
  unmoins = gneg(smoinun);
  lambd = gdiv(resi,gmul(s,smoinun));
  gammas = ggamma(s,prec);
  gammas2= ggamma(gmul2n(s,-1),prec);
  gar = gmul(gpowgs(gammas,r2),gpowgs(gammas2,r1));
  cs = gexp(gmul(cstlog,s),prec);
  gammaunmoins = gdiv(Pi, gmul(gsin(sPi,prec),gammas));
  gammaunmoins2= gdiv(gmul(gmul(sqrtr(Pi),gpow(gen_2,smoinun,prec)),
                           gammas2),
                      gmul(gcos(gmul2n(sPi,-1),prec),gammas));
  var1 = var2 = gen_1;
  for (i=2; i<=N0; i++)
    if (coef[i])
    {
      GEN gexpro = gexp(gmul(gel(coeflog,i),s),bigprec);
      var1 = gadd(var1,gmulsg(coef[i], gexpro));
      var2 = gadd(var2,gdivsg(coef[i], gmulsg(i,gexpro)));
    }
  lambd = gadd(lambd,gmul(gmul(var1,cs),gar));
  lambd = gadd(lambd,gmul(gmul(gmul(var2,gdiv(cst,cs)),
                               gpowgs(gammaunmoins,r2)),
                          gpowgs(gammaunmoins2,r1)));
  val  = s;
  valm = unmoins;
  var1 = gen_0;
  for (i=1; i<=i0; i++)
  {
    valk  = val;
    valkm = valm;
    for (k=1; k<=r; k++)
    {
      GEN c = gcoeff(C,i,k);
      var1 = gadd(var1,gdiv(c,valk )); valk  = gmul(val, valk);
      var1 = gadd(var1,gdiv(c,valkm)); valkm = gmul(valm,valkm);
    }
    if (r2)
    {
      val  = gaddgs(val, 1);
      valm = gaddgs(valm,1);
    }
    else
    {
      val  = gaddgs(val, 2);
      valm = gaddgs(valm,2); i++;
    }
  }
  lambd = gadd(lambd, var1);
  if (!flag) lambd = gdiv(lambd,gmul(gar,cs)); /* zetak */
  return lambd;
}

GEN
gzetakall(GEN znf, GEN s, long flag, long prec)
{
  pari_sp av = avma;
  GEN z;

  if (typ(znf)!=t_VEC || lg(znf)!=10 || typ(gel(znf,1)) != t_VECSMALL)
    pari_err_TYPE("zetakall", znf);
  if (isint(s, &s))
  {
    long ss = itos(s), r1, r2;
    if (ss==1) pari_err_DOMAIN("zetak", "argument", "=", gen_1, s);
    znf_get_sign(znf, &r1, &r2);
    if (ss==0)
    {
      avma = av;
      if (flag) pari_err_DOMAIN("zetak", "argument", "=", gen_0, s);
      if (r1 + r2 > 1) return gen_0;
      return r1? mkfrac(gen_m1, gen_2): gneg(gel(znf, 2));
    }
    if (!flag && ss < 0 && (r2 || !odd(ss))) return gen_0;
    z = slambdak(znf, itos(s), flag, prec+EXTRAPRECWORD);
  }
  else
    z = cxlambdak(znf, s, flag, prec+EXTRAPRECWORD);
  if (gprecision(z) > prec) z = gprec_w(z, prec);
  return gerepileupto(av, z);
}
GEN
gzetak(GEN nfz, GEN s, long prec) { return gzetakall(nfz,s,0,prec); }
GEN
glambdak(GEN nfz, GEN s, long prec) { return gzetakall(nfz,s,1,prec); }
