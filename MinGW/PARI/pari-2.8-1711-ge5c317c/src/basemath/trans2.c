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
/**                   TRANSCENDENTAL FUNCTIONS                     **/
/**                          (part 2)                              **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

GEN
trans_fix_arg(long *prec, GEN *s0, GEN *sig, GEN *tau, pari_sp *av, GEN *res)
{
  GEN s, p1;
  long l;
  if (typ(*s0)==t_COMPLEX && gequal0(gel(*s0,2))) *s0 = gel(*s0,1);
  s = *s0;
  l = precision(s); if (!l) l = *prec;
  if (l < LOWDEFAULTPREC) l = LOWDEFAULTPREC;
  *res = cgetc(l); *av = avma;
  if (typ(s) == t_COMPLEX)
  { /* s = sig + i t */
    s = cxtofp(s, l+EXTRAPRECWORD);
    *sig = gel(s,1);
    *tau = gel(s,2);
  }
  else /* real number */
  {
    *sig = s = gtofp(s, l+EXTRAPRECWORD);
    *tau = gen_0;
    p1 = trunc2nr(s, 0);
    if (!signe(subri(s,p1))) *s0 = p1;
  }
  *prec = l; return s;
}

/********************************************************************/
/**                                                                **/
/**                          ARCTANGENT                            **/
/**                                                                **/
/********************************************************************/
static GEN
mpatan(GEN x)
{
  long l, l1, l2, n, m, i, lp, e, s, sx = signe(x);
  pari_sp av0, av;
  double alpha, beta, delta;
  GEN y, p1, p2, p3, p4, p5, unr;
  int inv;

  if (!sx) return real_0_bit(expo(x));
  l = lp = realprec(x);
  if (absrnz_equal1(x)) { /* |x| = 1 */
    y = Pi2n(-2, l+EXTRAPRECWORD); if (sx < 0) setsigne(y,-1);
    return y;
  }
  if (l > AGM_ATAN_LIMIT)
  {
    av = avma; y = logagmcx(mkcomplex(gen_1, x), l);
    return gerepileuptoleaf(av, gel(y,2));
  }

  e = expo(x); inv = (e >= 0); /* = (|x| > 1 ) */
  if (e > 0) lp += nbits2extraprec(e);

  y = cgetr(lp); av0 = avma;
  p1 = rtor(x, l+EXTRAPRECWORD); setabssign(p1); /* p1 = |x| */
  if (inv) p1 = invr(p1);
  e = expo(p1);
  if (e < -100)
    alpha = 1.65149612947 - e; /* log_2(Pi) - e */
  else
    alpha = log2(M_PI / atan(rtodbl(p1)));
  beta = (double)(prec2nbits(l)>>1);
  delta = 1 + beta - alpha/2;
  if (delta <= 0) { n = 1; m = 0; }
  else
  {
    double fi = alpha-2;
    if (delta >= fi*fi)
    {
      double t = 1 + sqrt(delta);
      n = (long)t;
      m = (long)(t - fi);
    }
    else
    {
      n = (long)(1+beta/fi);
      m = 0;
    }
  }
  l2 = l + nbits2extraprec(m);
  p2 = rtor(p1, l2); av = avma;
  for (i=1; i<=m; i++)
  {
    p5 = addsr(1, sqrr(p2)); setprec(p5,l2);
    p5 = addsr(1, sqrtr_abs(p5)); setprec(p5,l2);
    affrr(divrr(p2,p5), p2); avma = av;
  }
  p3 = sqrr(p2); l1 = minss(LOWDEFAULTPREC+EXTRAPRECWORD, l2); /* l1 increases to l2 */;
  unr = real_1(l2); setprec(unr,l1);
  p4 = cgetr(l2); setprec(p4,l1);
  affrr(divru(unr,2*n+1), p4);
  s = 0; e = expo(p3); av = avma;
  for (i = n; i > 1; i--) /* n >= 1. i = 1 done outside for efficiency */
  {
    setprec(p3,l1); p5 = mulrr(p4,p3);
    l1 += dvmdsBIL(s - e, &s); if (l1 > l2) l1 = l2;
    setprec(unr,l1); p5 = subrr(divru(unr,2*i-1), p5);
    setprec(p4,l1); affrr(p5,p4); avma = av;
  }
  setprec(p3, l2); p5 = mulrr(p4,p3); /* i = 1 */
  setprec(unr,l2); p4 = subrr(unr, p5);

  p4 = mulrr(p2,p4); shiftr_inplace(p4, m);
  if (inv) p4 = subrr(Pi2n(-1, lp), p4);
  if (sx < 0) togglesign(p4);
  affrr_fixlg(p4,y); avma = av0; return y;
}

GEN
gatan(GEN x, long prec)
{
  pari_sp av;
  GEN a, y;

  switch(typ(x))
  {
    case t_REAL: return mpatan(x);
    case t_COMPLEX: /* atan(x) = -i atanh(ix) */
      if (ismpzero(gel(x,2))) return gatan(gel(x,1), prec);
      av = avma; return gerepilecopy(av, mulcxmI(gatanh(mulcxI(x),prec)));
    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (valp(y) < 0) pari_err_DOMAIN("atan","valuation", "<", gen_0, x);
      if (lg(y)==2) return gerepilecopy(av, y);
      /* lg(y) > 2 */
      a = integser(gdiv(derivser(y), gaddsg(1,gsqr(y))));
      if (!valp(y)) a = gadd(a, gatan(gel(y,2),prec));
      return gerepileupto(av, a);
  }
  return trans_eval("atan",gatan,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                             ARCSINE                            **/
/**                                                                **/
/********************************************************************/
/* |x| < 1, x != 0 */
static GEN
mpasin(GEN x) {
  pari_sp av = avma;
  GEN z, a = sqrtr(subsr(1, sqrr(x)));
  if (realprec(x) > AGM_ATAN_LIMIT)
  {
    z = logagmcx(mkcomplex(a,x), realprec(x));
    z = gel(z,2);
  }
  else
    z = mpatan(divrr(x, a));
  return gerepileuptoleaf(av, z);
}

static GEN mpacosh(GEN x);
GEN
gasin(GEN x, long prec)
{
  long sx;
  pari_sp av;
  GEN a, y, p1;

  switch(typ(x))
  {
    case t_REAL: sx = signe(x);
      if (!sx) return real_0_bit(expo(x));
      if (absrnz_equal1(x)) { /* |x| = 1 */
        if (sx > 0) return Pi2n(-1, realprec(x)); /* 1 */
        y = Pi2n(-1, realprec(x)); setsigne(y, -1); return y; /* -1 */
      }
      if (expo(x) < 0) return mpasin(x);
      y = cgetg(3,t_COMPLEX);
      gel(y,1) = Pi2n(-1, realprec(x));
      gel(y,2) = mpacosh(x);
      if (sx < 0) togglesign(gel(y,1)); else togglesign(gel(y,2));
      return y;

    case t_COMPLEX: /* asin(z) = -i asinh(iz) */
      if (ismpzero(gel(x,2))) return gasin(gel(x,1), prec);
      av = avma;
      return gerepilecopy(av, mulcxmI(gasinh(mulcxI(x), prec)));
    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) return gerepilecopy(av, y);
      /* lg(y) > 2*/
      if (valp(y) < 0) pari_err_DOMAIN("asin","valuation", "<", gen_0, x);
      p1 = gsubsg(1,gsqr(y));
      if (gequal0(p1))
      {
        GEN t = Pi2n(-1,prec);
        if (gsigne(gel(y,2)) < 0) setsigne(t, -1);
        return gerepileupto(av, scalarser(t, varn(y), valp(p1)>>1));
      }
      p1 = gdiv(derivser(y), gsqrt(p1,prec));
      a = integser(p1);
      if (!valp(y)) a = gadd(a, gasin(gel(y,2),prec));
      return gerepileupto(av, a);
  }
  return trans_eval("asin",gasin,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                             ARCCOSINE                          **/
/**                                                                **/
/********************************************************************/
static GEN
acos0(long e) { return Pi2n(-1, nbits2prec(e<0? -e: 1)); }

/* |x| < 1, x != 0 */
static GEN
mpacos(GEN x)
{
  pari_sp av = avma;
  GEN z, a = sqrtr(subsr(1, sqrr(x)));
  if (realprec(x) > AGM_ATAN_LIMIT)
  {
    z = logagmcx(mkcomplex(x,a), realprec(x));
    z = gel(z,2);
  }
  else {
    z = mpatan(divrr(a, x));
    if (signe(x) < 0) z = addrr(mppi(realprec(z)), z);
  }
  return gerepileuptoleaf(av, z);
}

GEN
gacos(GEN x, long prec)
{
  long sx;
  pari_sp av;
  GEN a, y, p1;

  switch(typ(x))
  {
    case t_REAL: sx = signe(x);
      if (!sx) return acos0(expo(x));
      if (absrnz_equal1(x)) /* |x| = 1 */
        return sx > 0? real_0_bit( -(bit_prec(x)>>1) ) : mppi(realprec(x));
      if (expo(x) < 0) return mpacos(x);

      y = cgetg(3,t_COMPLEX); p1 = mpacosh(x);
      if (sx < 0) { gel(y,1) = mppi(realprec(x)); togglesign(p1); }
      else gel(y,1) = gen_0;
      gel(y,2) = p1; return y;

    case t_COMPLEX:
      if (ismpzero(gel(x,2))) return gacos(gel(x,1), prec);
      av = avma;
      p1 = gadd(x, mulcxI(gsqrt(gsubsg(1,gsqr(x)), prec)));
      y = glog(p1,prec); /* log(x + I*sqrt(1-x^2)) */
      return gerepilecopy(av, mulcxmI(y));
    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (valp(y) < 0) pari_err_DOMAIN("acos","valuation", "<", gen_0, x);
      if (lg(y) > 2)
      {
        p1 = gsubsg(1,gsqr(y));
        if (gequal0(p1)) { avma = av; return zeroser(varn(y), valp(p1)>>1); }
        p1 = integser(gdiv(gneg(derivser(y)), gsqrt(p1,prec)));
        /*y(t) = 1+O(t)*/
        if (gequal1(gel(y,2)) && !valp(y)) return gerepileupto(av, p1);
      }
      else p1 = y;
      a = (lg(y)==2 || valp(y))? Pi2n(-1, prec): gacos(gel(y,2),prec);
      return gerepileupto(av, gadd(a,p1));
  }
  return trans_eval("acos",gacos,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                            ARGUMENT                            **/
/**                                                                **/
/********************************************************************/

/* we know that x and y are not both 0 */
static GEN
mparg(GEN x, GEN y)
{
  long prec, sx = signe(x), sy = signe(y);
  GEN z;

  if (!sy)
  {
    if (sx > 0) return real_0_bit(expo(y) - expo(x));
    return mppi(realprec(x));
  }
  prec = realprec(y); if (prec < realprec(x)) prec = realprec(x);
  if (!sx)
  {
    z = Pi2n(-1, prec); if (sy < 0) setsigne(z,-1);
    return z;
  }

  if (expo(x)-expo(y) > -2)
  {
    z = mpatan(divrr(y,x)); if (sx > 0) return z;
    return addrr_sign(z, signe(z), mppi(prec), sy);
  }
  z = mpatan(divrr(x,y));
  return addrr_sign(z, -signe(z), Pi2n(-1, prec), sy);
}

static GEN
rfix(GEN x,long prec)
{
  switch(typ(x))
  {
    case t_INT: return itor(x, prec);
    case t_FRAC: return fractor(x, prec);
    case t_REAL: break;
    default: pari_err_TYPE("rfix (conversion to t_REAL)",x);
  }
  return x;
}

static GEN
cxarg(GEN x, GEN y, long prec)
{
  pari_sp av = avma;
  x = rfix(x,prec);
  y = rfix(y,prec); return gerepileuptoleaf(av, mparg(x,y));
}

GEN
garg(GEN x, long prec)
{
  if (gequal0(x)) pari_err_DOMAIN("arg", "argument", "=", gen_0, x);
  switch(typ(x))
  {
    case t_REAL: prec = realprec(x); /* fall through */
    case t_INT: case t_FRAC: return (gsigne(x)>0)? real_0(prec): mppi(prec);
    case t_COMPLEX: return cxarg(gel(x,1),gel(x,2),prec);
  }
  return trans_eval("arg",garg,x,prec);
}

/********************************************************************/
/**                                                                **/
/**                      HYPERBOLIC COSINE                         **/
/**                                                                **/
/********************************************************************/

static GEN
mpcosh(GEN x)
{
  pari_sp av;
  GEN z;

  if (!signe(x)) { /* 1 + x */
    long e = expo(x);
    return e >= 0? real_0_bit(e): real_1(nbits2prec(-e));
  }
  av = avma;
  z = mpexp(x); z = addrr(z, invr(z)); shiftr_inplace(z, -1);
  return gerepileuptoleaf(av, z);
}

GEN
gcosh(GEN x, long prec)
{
  pari_sp av;
  GEN y, p1;

  switch(typ(x))
  {
    case t_REAL: return mpcosh(x);
    case t_COMPLEX:
      if (isintzero(gel(x,1))) return gcos(gel(x,2),prec);
      /* fall through */
    case t_PADIC:
      av = avma; p1 = gexp(x,prec); p1 = gadd(p1, ginv(p1));
      return gerepileupto(av, gmul2n(p1,-1));
    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y) && valp(y) == 0) return gerepilecopy(av, y);
      p1 = gexp(y,prec); p1 = gadd(p1, ginv(p1));
      return gerepileupto(av, gmul2n(p1,-1));
  }
  return trans_eval("cosh",gcosh,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                       HYPERBOLIC SINE                          **/
/**                                                                **/
/********************************************************************/

static GEN
mpsinh(GEN x)
{
  pari_sp av;
  long ex = expo(x), lx;
  GEN z, res;

  if (!signe(x)) return real_0_bit(ex);
  lx = realprec(x); res = cgetr(lx); av = avma;
  if (ex < 1 - BITS_IN_LONG) x = rtor(x, lx + nbits2extraprec(-ex)-1);
  z = mpexp(x); z = subrr(z, invr(z)); shiftr_inplace(z, -1);
  affrr(z, res); avma = av; return res;
}

GEN
gsinh(GEN x, long prec)
{
  pari_sp av;
  GEN y, p1;

  switch(typ(x))
  {
    case t_REAL: return mpsinh(x);
    case t_COMPLEX:
      if (isintzero(gel(x,1))) retmkcomplex(gen_0, gsin(gel(x,2),prec));
      /* fall through */
    case t_PADIC:
      av = avma; p1 = gexp(x,prec); p1 = gsub(p1, ginv(p1));
      return gerepileupto(av, gmul2n(p1,-1));
    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y) && valp(y) == 0) return gerepilecopy(av, y);
      p1 = gexp(y, prec); p1 = gsub(p1, ginv(p1));
      return gerepileupto(av, gmul2n(p1,-1));
  }
  return trans_eval("sinh",gsinh,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                      HYPERBOLIC TANGENT                        **/
/**                                                                **/
/********************************************************************/

static GEN
mptanh(GEN x)
{
  long lx, s = signe(x);
  GEN y;

  if (!s) return real_0_bit(expo(x));
  lx = realprec(x);
  if (absr_cmp(x, stor(prec2nbits(lx), LOWDEFAULTPREC)) >= 0) {
    y = real_1(lx);
  } else {
    pari_sp av = avma;
    long ex = expo(x);
    GEN t;
    if (ex < 1 - BITS_IN_LONG) x = rtor(x, lx + nbits2extraprec(-ex)-1);
    t = exp1r_abs(gmul2n(x,1)); /* exp(|2x|) - 1 */
    y = gerepileuptoleaf(av, divrr(t, addsr(2,t)));
  }
  if (s < 0) togglesign(y); /* tanh is odd */
  return y;
}

GEN
gtanh(GEN x, long prec)
{
  pari_sp av;
  GEN y, t;

  switch(typ(x))
  {
    case t_REAL: return mptanh(x);
    case t_COMPLEX:
      if (isintzero(gel(x,1))) retmkcomplex(gen_0, gtan(gel(x,2),prec));
      /* fall through */
    case t_PADIC:
      av = avma;
      t = gexp(gmul2n(x,1),prec);
      t = gdivsg(-2, gaddgs(t,1));
      return gerepileupto(av, gaddsg(1,t));
    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) return gerepilecopy(av, y);
      t = gexp(gmul2n(y, 1),prec);
      t = gdivsg(-2, gaddgs(t,1));
      return gerepileupto(av, gaddsg(1,t));
  }
  return trans_eval("tanh",gtanh,x,prec);
}

static GEN
mpcotanh(GEN x)
{
  long lx, s = signe(x);
  GEN y;

  if (!s) pari_err_DOMAIN("cotan", "argument", "=", gen_0, x);

  lx = realprec(x);
  if (absr_cmp(x, stor(prec2nbits(lx), LOWDEFAULTPREC)) >= 0) {
    y = real_1(lx);
  } else {
    pari_sp av = avma;
    long ex = expo(x);
    GEN t;
    if (ex < 1 - BITS_IN_LONG) x = rtor(x, lx + nbits2extraprec(-ex)-1);
    t = exp1r_abs(gmul2n(x,1)); /* exp(|2x|) - 1 */
    y = gerepileuptoleaf(av, divrr(addsr(2,t), t));
  }
  if (s < 0) togglesign(y); /* cotanh is odd */
  return y;
}

GEN
gcotanh(GEN x, long prec)
{
  pari_sp av;
  GEN y, t;

  switch(typ(x))
  {
    case t_REAL: return mpcotanh(x);
    case t_COMPLEX:
      if (isintzero(gel(x,1))) retmkcomplex(gen_0, gcotan(gel(x,2),prec));
      /* fall through */
    case t_PADIC:
      av = avma;
      t = gexpm1(gmul2n(x,1),prec);
      return gerepileupto(av, gaddsg(1, gdivsg(2,t)));
    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) return gerepilecopy(av, y);
      t = gexpm1(gmul2n(y,1),prec);
      return gerepileupto(av, gaddsg(1, gdivsg(2,t)));
  }
  return trans_eval("cotanh",gcotanh,x,prec);
}

/********************************************************************/
/**                                                                **/
/**                     AREA HYPERBOLIC SINE                       **/
/**                                                                **/
/********************************************************************/

/* x != 0 */
static GEN
mpasinh(GEN x)
{
  GEN z, res;
  pari_sp av;
  long lx = realprec(x), ex = expo(x);

  res = cgetr(lx); av = avma;
  if (ex < 1 - BITS_IN_LONG) x = rtor(x, lx + nbits2extraprec(-ex)-1);
  z = logr_abs( addrr_sign(x,1, sqrtr_abs( addrs(sqrr(x), 1) ), 1) );
  if (signe(x) < 0) togglesign(z);
  affrr(z, res); avma = av; return res;
}

GEN
gasinh(GEN x, long prec)
{
  pari_sp av;
  GEN a, y, p1;

  switch(typ(x))
  {
    case t_REAL:
      if (!signe(x)) return rcopy(x);
      return mpasinh(x);

    case t_COMPLEX:
      if (ismpzero(gel(x,2))) return gasinh(gel(x,1), prec);
      av = avma;
      if (ismpzero(gel(x,1))) /* avoid cancellation */
        return gerepilecopy(av, mulcxI(gasin(gel(x,2), prec)));
      p1 = gadd(x, gsqrt(gaddsg(1,gsqr(x)), prec));
      y = glog(p1,prec); /* log (x + sqrt(1+x^2)) */
      return gerepileupto(av, y);
    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) return gerepilecopy(av, y);
      if (valp(y) < 0) pari_err_DOMAIN("asinh","valuation", "<", gen_0, x);
      p1 = gaddsg(1,gsqr(y));
      if (gequal0(p1))
      {
        GEN t = PiI2n(-1,prec);
        if ( gsigne(imag_i(gel(y,2))) < 0 ) setsigne(gel(t,2), -1);
        return gerepileupto(av, scalarser(t, varn(y), valp(p1)>>1));
      }
      p1 = gdiv(derivser(y), gsqrt(p1,prec));
      a = integser(p1);
      if (!valp(y)) a = gadd(a, gasinh(gel(y,2),prec));
      return gerepileupto(av, a);
  }
  return trans_eval("asinh",gasinh,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                     AREA HYPERBOLIC COSINE                     **/
/**                                                                **/
/********************************************************************/

/* |x| >= 1, return ach(|x|) */
static GEN
mpacosh(GEN x)
{
  pari_sp av = avma;
  GEN z;
  if (absrnz_equal1(x)) return real_0_bit(- bit_prec(x) >> 1);
  z = logr_abs( addrr_sign(x, 1, sqrtr( subrs(sqrr(x), 1) ), 1) );
  return gerepileuptoleaf(av, z);
}

GEN
gacosh(GEN x, long prec)
{
  pari_sp av;
  GEN y, p1;

  switch(typ(x))
  {
    case t_REAL: {
      long s = signe(x), e = expo(x);
      GEN a, b;
      if (s > 0 && e >= 0) return mpacosh(x);
      /* x < 1 */
      y = cgetg(3,t_COMPLEX); a = gen_0;
      if (s == 0) b = acos0(e);
      else if (e < 0) b = mpacos(x); /* -1 < x < 1 */
      else {
        if (!absrnz_equal1(x)) a = mpacosh(x);
        b = mppi(realprec(x));
      }
      gel(y,1) = a;
      gel(y,2) = b; return y;
    }
    case t_COMPLEX:
      if (ismpzero(gel(x,2))) return gacosh(gel(x,1), prec);
      av = avma;
      p1 = gadd(x, gsqrt(gaddsg(-1,gsqr(x)), prec));
      y = glog(p1,prec); /* log(x + sqrt(x^2-1)) */
      if (signe(real_i(y)) < 0) y = gneg(y);
      return gerepileupto(av, y);
    default: {
      GEN a;
      long v;
      av = avma; if (!(y = toser_i(x))) break;
      v = valp(y);
      if (v < 0) pari_err_DOMAIN("acosh","valuation", "<", gen_0, x);
      if (gequal0(y))
      {
        if (!v) return gerepilecopy(av, y);
        return gerepileupto(av, gadd(y, PiI2n(-1, prec)));
      }
      p1 = gsubgs(gsqr(y),1);
      if (gequal0(p1)) { avma = av; return zeroser(varn(y), valp(p1)>>1); }
      p1 = gdiv(derivser(y), gsqrt(p1,prec));
      a = integser(p1);
      if (v)
        p1 = PiI2n(-1, prec); /* I Pi/2 */
      else
      {
        p1 = gel(y,2); if (gequal1(p1)) return gerepileupto(av,a);
        p1 = gacosh(p1, prec);
      }
      return gerepileupto(av, gadd(p1,a));
    }
  }
  return trans_eval("acosh",gacosh,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                     AREA HYPERBOLIC TANGENT                    **/
/**                                                                **/
/********************************************************************/

/* |x| < 1, x != 0 */
static GEN
mpatanh(GEN x)
{
  pari_sp av = avma;
  long ex = expo(x);
  GEN z;
  if (ex < 1 - BITS_IN_LONG) x = rtor(x, realprec(x) + nbits2extraprec(-ex)-1);
  z = invr( subsr(1,x) ); shiftr_inplace(z, 1); /* 2/(1-x)*/
  z = logr_abs( addrs(z,-1) );
  shiftr_inplace(z, -1); return gerepileuptoleaf(av, z);
}

GEN
gatanh(GEN x, long prec)
{
  long sx;
  pari_sp av;
  GEN a, y, z;

  switch(typ(x))
  {
    case t_REAL:
      sx = signe(x);
      if (!sx) return real_0_bit(expo(x));
      if (expo(x) < 0) return mpatanh(x);

      y = cgetg(3,t_COMPLEX);
      av = avma;
      z = subrs(x,1);
      if (!signe(z)) pari_err_DOMAIN("atanh", "argument", "=", gen_1, x);
      z = invr(z); shiftr_inplace(z, 1); /* 2/(x-1)*/
      z = addrs(z,1);
      if (!signe(z)) pari_err_DOMAIN("atanh", "argument", "=", gen_m1, x);
      z = logr_abs(z);
      shiftr_inplace(z, -1); /* (1/2)log((1+x)/(x-1)) */
      gel(y,1) = gerepileuptoleaf(av, z);
      gel(y,2) = Pi2n(-1, realprec(x));
      if (sx > 0) togglesign(gel(y,2));
      return y;

    case t_COMPLEX: /* 2/(1-z) - 1 = (1+z) / (1-z) */
      if (ismpzero(gel(x,2))) return gatanh(gel(x,1), prec);
      av = avma; z = glog( gaddgs(gdivsg(2,gsubsg(1,x)),-1), prec );
      return gerepileupto(av, gmul2n(z,-1));

    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (valp(y) < 0) pari_err_DOMAIN("atanh","valuation", "<", gen_0, x);
      z = gdiv(derivser(y), gsubsg(1,gsqr(y)));
      a = integser(z);
      if (!valp(y)) a = gadd(a, gatanh(gel(y,2),prec));
      return gerepileupto(av, a);
  }
  return trans_eval("atanh",gatanh,x,prec);
}
/********************************************************************/
/**                                                                **/
/**               CACHE BERNOULLI NUMBERS B_2k                     **/
/**                                                                **/
/********************************************************************/
static GEN
bern(GEN B, long pr)
{
  if (typ(B) != t_REAL) return fractor(B, pr);
  if (realprec(B) < pr) return rtor(B,pr);
  return B;
}
static const long BERN_MINNB = 5;
/* need B[2..2*nb] at least prec accuracy. If prec = 0, compute exactly */
void
mpbern(long nb, long prec)
{
  const pari_sp av = avma;
  long n, pr, n_is_small = 1, lbern = 0;
  GEN B;
  pari_timer T;

  /* pr = accuracy for computation, prec = required accuracy for result */
  if (prec)
  {
    pr = prec;
    incrprec(pr);
  }
  else
    pr = prec = LONG_MAX; /* oo */
  if (nb < BERN_MINNB) nb = BERN_MINNB;
  if (bernzone)
  { /* don't recompute known Bernoulli */
    long i, min, max;
    lbern = lg(bernzone);
    if (lbern-1 < nb)
    { min = lbern-1; max = nb; }
    else
    { min = nb; max = lbern-1; }
    /* skip B_2, ..., B_{2*MINNB}, always included as t_FRAC */
    for (n = BERN_MINNB+1; n <= min; n++)
    {
      GEN c = gel(bernzone,n);
      /* also stop if prec = 0 (compute exactly) */
      if (typ(c) == t_REAL && realprec(c) < prec) break;
    }
    /* B[1..n-1] are OK */
    if (n > nb) return;
    B = cgetg_block(max+1, t_VEC);
    for (i = 1; i < n; i++) gel(B,i) = gel(bernzone,i);
    /* keep B[nb+1..max] */
    for (i = nb+1; i <= max; i++) gel(B,i) = gel(bernzone,i);
  }
  else
  {
    B = cgetg_block(nb+1, t_VEC);
    gel(B,1) = gclone(mkfrac(gen_1, utoipos(6)));
    gel(B,2) = gclone(mkfrac(gen_m1, utoipos(30)));
    gel(B,3) = gclone(mkfrac(gen_1, utoipos(42)));
    gel(B,4) = gel(B,2);
    gel(B,5) = gclone(mkfrac(utoipos(5), utoipos(66)));
    n = BERN_MINNB+1;
  }
  avma = av;
  if (DEBUGLEVEL) {
    err_printf("caching Bernoulli numbers 2 to 2*%ld, prec = %ld\n",
               nb, prec == LONG_MAX? 0: prec);
    timer_start(&T);
  }

  /* B_{2n} = (2n-1) / (4n+2) -
   * sum_{a = 1}^{n-1} (2n)...(2n+2-2a) / (2...(2a-1)2a) B_{2a} */
  n_is_small = 1;
  for (; n <= nb; n++, avma = av)
  { /* compute and store B[n] = B_{2n} */
    GEN S;
    if (n < lbern)
    {
      GEN b = gel(bernzone,n);
      if (typ(b)!=t_REAL || realprec(b)>=prec) { gel(B,n) = b; continue; }
    }
    /* Not cached, must compute */
    /* huge accuracy ? May as well compute exactly */
    if (n_is_small && (prec == LONG_MAX ||
                       2*n * log(2*n) < prec2nbits_mul(prec, LOG2)))
      S = bernfrac_using_zeta(2*n);
    else
    {
#ifdef LONG_IS_64BIT
      const ulong mul_overflow = 3037000500;
#else
      const ulong mul_overflow = 46341;
#endif
      ulong u = 8, v = 5, a = n-1, b = 2*n-3;
      n_is_small = 0;
      S = bern(gel(B,a), pr); /* B_2a */
      for (;;)
      { /* b = 2a-1, u = 2v-2, 2a + v = 2n+3 */
        if (a == 1) { S = mulri(S, muluu(u,v)); break; } /* a=b=1, v=2n+1, u=4n */
        /* beware overflow */
        S = (v <= mul_overflow)? mulru(S, u*v): mulri(S, muluu(u,v));
        S = (a <= mul_overflow)? divru(S, a*b): divri(S, muluu(a,b));
        u += 4; v += 2; a--; b -= 2;
        S = addrr(bern(gel(B,a), pr), S);
        if ((a & 127) == 0) S = gerepileuptoleaf(av, S);
      }
      S = divru(subsr(2*n, S), 2*n+1);
      shiftr_inplace(S, -2*n);
      if (realprec(S) != prec) S = rtor(S, prec);
    }
    gel(B,n) = gclone(S); /* S = B_2n */
  }
  if (DEBUGLEVEL) timer_printf(&T, "Bernoulli");
  swap(B, bernzone);
  if (B)
  { /* kill old non-reused values */
    for (n = lbern-1; n; n--)
    {
      if (gel(B,n) != gel(bernzone,n)) gunclone(gel(B,n));
    }
    killblock(B);
  }
  avma = av;
}

GEN
bernfrac(long n)
{
  long k;
  if (n < 0) pari_err_DOMAIN("bernfrac", "index", "<", gen_0, stoi(n));
  if (n == 0) return gen_1;
  if (n == 1) return mkfrac(gen_m1,gen_2);
  if (odd(n)) return gen_0;
  k = n >> 1;
  if (!bernzone && k <= BERN_MINNB) mpbern(BERN_MINNB, 0);
  if (bernzone && k < lg(bernzone))
  {
    GEN B = gel(bernzone, k), C;
    if (typ(B) != t_REAL) return B;
    C = bernfrac_using_zeta(n);
    gel(bernzone, k) = gclone(C);
    gunclone(B); return C;
  }
  return bernfrac_using_zeta(n);
}

/* mpbern as exact fractions */
static GEN
bernvec_old(long nb)
{
  long n, i;
  GEN y;

  if (nb < 0) return cgetg(1, t_VEC);
  if (nb > 46340 && BITS_IN_LONG == 32) pari_err_IMPL( "bernvec for n > 46340");

  y = cgetg(nb+2, t_VEC); gel(y,1) = gen_1;
  for (n = 1; n <= nb; n++)
  { /* compute y[n+1] = B_{2n} */
    pari_sp av = avma;
    GEN b = gmul2n(utoineg(2*n - 1), -1); /* 1 + (2n+1)B_1 = -(2n-1) /2 */
    GEN c = gen_1;
    ulong u1 = 2*n + 1, u2 = n, d1 = 1, d2 = 1;

    for (i = 1; i < n; i++)
    {
      c = diviiexact(muliu(c, u1*u2), utoipos(d1*d2));/*= binomial(2n+1, 2*i) */
      b = gadd(b, gmul(c, gel(y,i+1)));
      u1 -= 2; u2--; d1++; d2 += 2;
    }
    gel(y,n+1) = gerepileupto(av, gdivgs(b, -(1+2*n)));
  }
  return y;
}
GEN
bernvec(long nb)
{
  long i, l = nb+2;
  GEN y = cgetg(l, t_VEC);
  if (nb < 20) return bernvec_old(nb);
  for (i = 1; i < l; i++) gel(y,i) = bernfrac((i-1) << 1);
  return y;
}

/* x := pol_x(v); B_k(x) = \sum_{i=0}^k binomial(k, i) B_i x^{k-i} */
static GEN
bernpol_i(long k, long v)
{
  GEN B, C;
  long i;
  if (v < 0) v = 0;
  if (k < 0) pari_err_DOMAIN("bernpol", "index", "<", gen_0, stoi(k));
  mpbern(k >> 1, 0); /* cache B_2, ..., B_2[k/2] */
  C = vecbinome(k);
  B = cgetg(k + 3, t_POL);
  for (i = 0; i <= k; ++i) gel(B, k-i+2) = gmul(gel(C,i+1), bernfrac(i));
  B[1] = evalsigne(1) | evalvarn(v);
  return B;
}
GEN
bernpol(long k, long v) {
  pari_sp av = avma;
  return gerepileupto(av, bernpol_i(k, v));
}
/* x := pol_x(v); return 1^e + ... + x^e = x^e + (B_{e+1}(x) - B_{e+1})/(e+1) */
static GEN
faulhaber(long e, long v)
{
  GEN B;
  if (e == 0) return pol_x(v);
  B = RgX_integ(bernpol_i(e, v)); /* (B_{e+1}(x) - B_{e+1}) / (e+1) */
  gel(B,e+2) = gaddgs(gel(B,e+2), 1); /* add x^e, in place */
  return B;
}
/* sum_v T(v), T a polynomial expression in v */
GEN
sumformal(GEN T, long v)
{
  pari_sp av = avma, av2;
  long i, t, d;
  GEN R;

  T = simplify_shallow(T);
  t = typ(T);
  if (is_scalar_t(t))
    return gerepileupto(av, monomialcopy(T, 1, v < 0? 0: v));
  if (t != t_POL) pari_err_TYPE("sumformal [not a t_POL]", T);
  if (v < 0) v = varn(T);
  av2 = avma;
  R = gen_0;
  d = poldegree(T,v);
  for (i = d; i >= 0; i--)
  {
    GEN c = polcoeff0(T, i, v);
    if (gequal0(c)) continue;
    R = gadd(R, gmul(c, faulhaber(i, v)));
    if (gc_needed(av2,3))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"sumformal, i = %ld/%ld", i,d);
      R = gerepileupto(av2, R);
    }
  }
  return gerepileupto(av, R);
}

/********************************************************************/
/**                                                                **/
/**                         EULER'S GAMMA                          **/
/**                                                                **/
/********************************************************************/

/* x / (i*(i+1)) */
GEN
divrunu(GEN x, ulong i)
{
  if (i <= LOWMASK) /* i(i+1) < 2^BITS_IN_LONG*/
    return divru(x, i*(i+1));
  else
    return divru(divru(x, i), i+1);
}
/* x / (i*(i+1)) */
GEN
divgunu(GEN x, ulong i)
{
#ifdef LONG_IS_64BIT
  if (i < 3037000500L) /* i(i+1) < 2^63 */
#else
  if (i < 46341L) /* i(i+1) < 2^31 */
#endif
    return gdivgs(x, i*(i+1));
  else
    return gdivgs(gdivgs(x, i), i+1);
}

/* arg(s+it) */
double
darg(double s, double t)
{
  double x;
  if (!t) return (s>0)? 0.: M_PI;
  if (!s) return (t>0)? M_PI/2: -M_PI/2;
  x = atan(t/s);
  return (s>0)? x
              : ((t>0)? x+M_PI : x-M_PI);
}

void
dcxlog(double s, double t, double *a, double *b)
{
  *a = log(s*s + t*t) / 2; /* log |s| = Re(log(s)) */
  *b = darg(s,t);          /* Im(log(s)) */
}

double
dabs(double s, double t) { return sqrt( s*s + t*t ); }
double
dnorm(double s, double t) { return s*s + t*t; }

#if 0
/* x, z t_REAL. Compute unique x in ]-z,z] congruent to x mod 2z */
static GEN
red_mod_2z(GEN x, GEN z)
{
  GEN Z = gmul2n(z, 1), d = subrr(z, x);
  /* require little accuracy */
  if (!signe(d)) return x;
  setprec(d, nbits2prec(expo(d) - expo(Z)));
  return addrr(mulir(floorr(divrr(d, Z)), Z), x);
}
#endif

/* lngamma(1+z) = -Euler*z + sum_{i > 1} zeta(i)/i (-z)^i
 * at relative precision prec, |z| < 1 is small */
static GEN
lngamma1(GEN z, long prec)
{ /* sum_{i > l} |z|^(i-1) = |z|^l / (1-|z|) < 2^-B
   * for l > (B+1) / |log2(|z|)| */
  long i, l = ceil((bit_accuracy(prec) + 1) / - dbllog2(z));
  GEN zet, me = mpeuler(prec), s = gen_0;
  setsigne(me, -1); /* -Euler */
  if (l <= 1) return gmul(me, z);
  zet = veczeta(gen_1, gen_2, l-1, prec); /* z[i] = zeta(i+1) */
  for (i = l; i > 1; i--)
  {
    GEN c = divru(gel(zet,i-1), i);
    if (odd(i)) setsigne(c, -1);
    s = gadd(gmul(s,z), c);
  }
  return gmul(z, gadd(gmul(s,z), me));
}

static GEN
cxgamma(GEN s0, int dolog, long prec)
{
  GEN s, u, a, y, res, tes, sig, tau, invn2, p1, nnx, pi, pi2, sqrtpi2;
  long i, lim, nn, esig, et;
  pari_sp av, av2;
  int funeq = 0;
  pari_timer T;

  if (DEBUGLEVEL>5) timer_start(&T);
  s = trans_fix_arg(&prec,&s0,&sig,&tau,&av,&res);

  esig = expo(sig);
  et = signe(tau)? expo(tau): 0;
  if ((signe(sig) <= 0 || esig < -1) && et <= 16)
  { /* s <--> 1-s */
    funeq = 1; s = gsubsg(1, s); sig = real_i(s);
  }

  /* find "optimal" parameters [lim, nn] */
  if (esig > 300 || et > 300)
  { /* |s| is HUGE ! Play safe and avoid inf / NaN */
    GEN S, iS, l2, la, u;
    double logla, l;

    S = gprec_w(s,LOWDEFAULTPREC);
    /* l2 ~ |lngamma(s))|^2 */
    l2 = gnorm(gmul(S, glog(S, LOWDEFAULTPREC)));
    l = (prec2nbits_mul(prec, LOG2) - rtodbl(glog(l2,LOWDEFAULTPREC))/2) / 2.;
    if (l < 0) l = 0.;

    iS = imag_i(S);
    if (et > 0 && l > 0)
    {
      GEN t = gmul(iS, dbltor(M_PI / l)), logt = glog(t,LOWDEFAULTPREC);
      la = gmul(t, logt);
      if      (gcmpgs(la, 3) < 0)   { logla = log(3.); la = stoi(3); }
      else if (gcmpgs(la, 150) > 0) { logla = rtodbl(logt); la = t; }
      else logla = rtodbl(mplog(la));
    }
    else
    {
      logla = log(3.); la = stoi(3);
    }
    lim = (long)ceil(l / (1.+ logla));
    if (lim == 0) lim = 1;

    u = gmul(la, dbltor((lim-0.5)/M_PI));
    l2 = gsub(gsqr(u), gsqr(iS));
    if (signe(l2) > 0)
    {
      l2 = gsub(gsqrt(l2,3), sig);
      if (signe(l2) > 0) nn = itos( gceil(l2) ); else nn = 1;
    }
    else
      nn = 1;
  }
  else
  { /* |s| is moderate. Use floats  */
    double ssig = rtodbl(sig);
    double st = typ(s) == t_REAL? 0.0: rtodbl(imag_i(s));
    double la, l,l2,u,v, rlogs, ilogs;

    if (fabs(ssig-1) + fabs(st) < 0.0001)
    { /* s ~ 1: loggamma(1+u) ~ - Euler * u, cancellation */
      if (funeq) /* s0 ~ 0: use lngamma(s0)+log(s0) = lngamma(s0+1) */
        y = gsub(lngamma1(s0,prec), glog(s0,prec));
      else
      {
        if (isint1(s0)) { avma = av; return dolog? real_0(prec): real_1(prec); }
        y = lngamma1(gsubgs(s0,1),prec);
      }
      if (!dolog) y = gexp(y,prec);
      avma = av; return affc_fixlg(y, res);
    }
    dcxlog(ssig,st, &rlogs,&ilogs);
    /* Re (s - 1/2) log(s) */
    u = (ssig - 0.5)*rlogs - st * ilogs;
    /* Im (s - 1/2) log(s) */
    v = (ssig - 0.5)*ilogs + st * rlogs;
    /* l2 = | (s - 1/2) log(s) - s + log(2Pi)/2 |^2 ~ |lngamma(s))|^2 */
    u = u - ssig + log(2.*M_PI)/2;
    v = v - st;
    l2 = u*u + v*v;
    if (l2 < 0.000001) l2 = 0.000001;
    l = (prec2nbits_mul(prec, LOG2) - log(l2)/2) / 2.;
    if (l < 0) l = 0.;

    la = 3.; /* FIXME: heuristic... */
    if (st > 1 && l > 0)
    {
      double t = st * M_PI / l;
      la = t * log(t);
      if (la < 3) la = 3.;
      if (la > 150) la = t;
    }
    lim = (long)ceil(l / (1.+ log(la)));
    if (lim == 0) lim = 1;

    u = (lim-0.5) * la / M_PI;
    l2 = u*u - st*st;
    if (l2 > 0)
    {
      nn = (long)ceil(sqrt(l2) - ssig);
      if (nn < 1) nn = 1;
    }
    else
      nn = 1;
    if (DEBUGLEVEL>5) err_printf("lim, nn: [%ld, %ld], la = %lf\n",lim,nn,la);
  }
  incrprec(prec);

  av2 = avma;
  y = s;
  if (typ(s0) == t_INT)
  {
    if (signe(s0) <= 0)
      pari_err_DOMAIN("gamma","argument", "=",
                       strtoGENstr("non-positive integer"), s0);
    if (is_bigint(s0)) {
      for (i=1; i < nn; i++)
      {
        y = mulri(y, addis(s0, i));
        if (gc_needed(av2,3))
        {
          if(DEBUGMEM>1) pari_warn(warnmem,"gamma");
          y = gerepileuptoleaf(av2, y);
        }
      }
    } else {
      ulong ss = itou(s0);
      for (i=1; i < nn; i++)
      {
        y = mulru(y, ss + i);
        if (gc_needed(av2,3))
        {
          if(DEBUGMEM>1) pari_warn(warnmem,"gamma");
          y = gerepileuptoleaf(av2, y);
        }
      }
    }
    if (dolog) y = logr_abs(y);
  }
  else if (!dolog || typ(s) == t_REAL)
  { /* Compute lngamma mod 2 I Pi */
    for (i=1; i < nn; i++)
    {
      y = gmul(y, gaddgs(s,i));
      if (gc_needed(av2,3))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"gamma");
        y = gerepileupto(av2, y);
      }
    }
    if (dolog) y = logr_abs(y);
  }
  else
  { /* dolog && complex s: be careful with imaginary part */
    y = glog(y, prec);
    for (i=1; i < nn; i++)
    {
      y = gadd(y, glog(gaddgs(s,i), prec));
      if (gc_needed(av2,3))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"gamma");
        y = gerepileupto(av2, y);
      }
    }
  }
  if (DEBUGLEVEL>5) timer_printf(&T,"product from 0 to N-1");

  nnx = gaddgs(s, nn);
  a = ginv(nnx); invn2 = gsqr(a);
  av2 = avma;
  mpbern(lim,prec);
  tes = divrunu(bernreal(2*lim,prec), 2*lim-1); /* B2l / (2l-1) 2l*/
  if (DEBUGLEVEL>5) timer_printf(&T,"Bernoullis");
  for (i = 2*lim-2; i > 1; i -= 2)
  {
    u = divrunu(bernreal(i,prec), i-1); /* Bi / i(i-1) */
    tes = gadd(u, gmul(invn2,tes));
    if (gc_needed(av2,3))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"gamma");
      tes = gerepileupto(av2, tes);
    }
  }
  if (DEBUGLEVEL>5) timer_printf(&T,"Bernoulli sum");

  p1 = gsub(gmul(gsub(nnx, ghalf), glog(nnx,prec)), nnx);
  p1 = gadd(p1, gmul(tes, a));

  pi = mppi(prec); pi2 = shiftr(pi, 1); sqrtpi2 = sqrtr(pi2);

  if (dolog)
  {
    if (funeq)
    { /* (recall that s = 1 - s0) */

      /* We compute log(sin(Pi s0)) so that it has branch cuts along
      * (-oo, 0] and [1, oo).  To do this in a numerically stable way
      * we must compute the log first then mangle its imaginary part.
      * The rounding operation below is stable because we're rounding
      * a number which is already within 1/4 of an integer. */

      /* z = log( sin(Pi s0) / (sqrt(2Pi)/2) ) */
      GEN z = glog(gdiv(gsin(gmul(pi,s0),prec), shiftr(sqrtpi2,-1)), prec);
      /* b = (2 Re(s) - 1) / 4 */
      GEN b = shiftr(subrs(shiftr(sig, 1), 1), -2);
      y = gsub(y, z);
      if (gsigne(imag_i(s)) > 0) togglesign(b);
      /* z = 2Pi round( Im(z)/2Pi - b ) */
      z = gmul(roundr(gsub(gdiv(imag_i(z), pi2), b)), pi2);
      if (signe(z)) { /* y += I*z */
        if (typ(y) == t_COMPLEX)
          gel(y,2) = gadd(gel(y,2), z);
        else
          y = gadd(y, mkcomplex(gen_0, z));
      }
      p1 = gneg(p1);
    }
    else /* y --> sqrt(2Pi) / y */
      y = gsub(logr_abs(sqrtpi2), y);
    y = gadd(p1, y);
  }
  else
  {
    if (funeq)
    { /* y --> y Pi/(sin(Pi s) * sqrt(2Pi)) = y sqrt(Pi/2)/sin(Pi s) */
      y = gdiv(gmul(shiftr(sqrtpi2,-1),y), gsin(gmul(pi,s0), prec));
      /* don't use s above: sin(pi s0) = sin(pi s) and the former is
       * more accurate, esp. if s0 ~ 0 */
      p1 = gneg(p1);
    }
    else /* y --> sqrt(2Pi) / y */
      y = gdiv(sqrtpi2, y);
    y = gmul(gexp(p1, prec), y);
  }
  avma = av; return affc_fixlg(y, res);
}

/* Gamma((m+1) / 2) */
static GEN
gammahs(long m, long prec)
{
  GEN y = cgetr(prec), z;
  pari_sp av = avma;
  long ma = labs(m);

  if (ma > 200 + 50*(prec-2)) /* heuristic */
  {
    z = stor(m + 1, prec); shiftr_inplace(z, -1);
    affrr(cxgamma(z,0,prec), y);
    avma = av; return y;
  }
  z = sqrtr( mppi(prec) );
  if (m)
  {
    GEN p1 = mulu_interval(ma/2 + 1, ma);
    long v = vali(p1);
    p1 = shifti(p1, -v); v -= ma;
    if (m >= 0) z = mulri(z,p1);
    else
    {
      z = divri(z,p1); v = -v;
      if ((m&3) == 2) setsigne(z,-1);
    }
    shiftr_inplace(z, v);
  }
  affrr(z, y); avma = av; return y;
}
GEN
ggammah(GEN x, long prec)
{
  switch(typ(x))
  {
    case t_INT:
    {
      long k = itos(x);
      if (labs(k) > 962353) pari_err_OVERFLOW("gammah");
      return gammahs(k<<1, prec);
    }
    case t_REAL: case t_COMPLEX: case t_PADIC: case t_SER: {
      pari_sp av = avma;
      return gerepileupto(av, ggamma(gadd(x,ghalf), prec));
    }
  }
  return trans_eval("gammah",ggammah,x,prec);
}

/* find n such that n+v_p(n!)>=k p^2/(p-1)^2 */
static long
nboft(long k, long p)
{
  pari_sp av = avma;
  long s, n;

  if (k <= 0) return 0;
  k = itou( gceil(gdiv(mului(k, sqru(p)), sqru(p-1))) );
  avma = av;
  for (s=0, n=0; n+s < k; n++, s += u_lval(n, p));
  return n;
}

/* Using Dwork's expansion, compute \Gamma(px+1)=-\Gamma(px) with x a unit.
 * See p-Adic Gamma Functions and Dwork Cohomology, Maurizio Boyarsky
 * Transactions of the AMS, Vol. 257, No. 2. (Feb., 1980), pp. 359-369.
 * Inspired by a GP script by Fernando Rodriguez-Villegas */
static GEN
gadw(GEN x, long p)
{
  pari_sp ltop = avma;
  GEN s, t, u = cgetg(p+1, t_VEC);
  long j, k, kp, n = nboft(precp(x)+valp(x)+1, p);

  t = s = gaddsg(1, zeropadic(gel(x,2), n));
  gel(u, 1) = s;
  gel(u, 2) = s;
  for (j = 2; j < p; ++j)
    gel(u, j+1) = gdivgs(gel(u, j), j);
  for (k = 1, kp = p; k < n; ++k, kp += p) /* kp = k*p */
  {
    GEN c;
    gel(u, 1) = gdivgs(gadd(gel(u, 1), gel(u, p)), kp);
    for (j = 1; j < p; ++j)
      gel(u, j+1) = gdivgs(gadd(gel(u, j), gel(u, j+1)), kp + j);

    t = gmul(t, gaddgs(x, k-1));
    c = leafcopy(gel(u,1)); setvalp(c, valp(c) + k); /* c = u[1] * p^k */
    s = gadd(s, gmul(c, t));
    if ((k&0xFL)==0) gerepileall(ltop, 3, &u,&s,&t);
  }
  return gneg(s);
}

/*Use Dwork expansion*/
/*This is a O(p*e*log(pe)) algorithm, should be used when p small
 * If p==2 this is a O(pe) algorithm. */
static GEN
Qp_gamma_Dwork(GEN x, long p)
{
  pari_sp ltop = avma;
  long k = padic_to_Fl(x, p);
  GEN p1;
  long j;
  long px = precp(x);
  if (p==2 && px)
  {
    x = shallowcopy(x);
    setprecp(x, px+1);
    gel(x,3) = shifti(gel(x,3),1);
  }
  if (k)
  {
    GEN x_k = gsubgs(x,k);
    x = gdivgs(x_k, p);
    p1 = gadw(x, p); if (!odd(k)) p1 = gneg(p1);
    for (j = 1; j < k; ++j) p1 = gmul(p1, gaddgs(x_k, j));
  }
  else
    p1 = gneg(gadw(gdivgs(x, p), p));
  return gerepileupto(ltop, p1);
}

/* Compute Qp_gamma using the definition. This is a O(x*M(log(pe))) algorithm.
 * This should be used if x is very small. */
static GEN
Qp_gamma_Morita(long n, GEN p, long e)
{
  pari_sp ltop=avma;
  GEN p2 = gaddsg((n&1)?-1:1, zeropadic(p, e));
  long i;
  long pp=is_bigint(p)? 0: itos(p);
  for (i = 2; i < n; i++)
    if (!pp || i%pp)
    {
      p2 = gmulgs(p2, i);
      if ((i&0xFL) == 0xFL)
        p2 = gerepileupto(ltop, p2);
    }
  return gerepileupto(ltop, p2);
}

/* x\in\N: Gamma(-x)=(-1)^(1+x+x\p)*Gamma(1+x) */
static GEN
Qp_gamma_neg_Morita(long n, GEN p, long e)
{
  GEN g = ginv(Qp_gamma_Morita(n+1, p, e));
  return ((n^sdivsi(n,p)) & 1)? g: gneg(g);
}

/* p-adic Gamma function for x a p-adic integer */
/* If n < p*e : use Morita's definition.
 * Else : use Dwork's expansion.
 * If both n and p are big : itos(p) will fail.
 * TODO: handle p=2 better (Qp_gamma_Dwork is slow for p=2). */
GEN
Qp_gamma(GEN x)
{
  GEN n, m, N, p = gel(x,2);
  long s, e = precp(x);
  if (equaliu(p, 2) && e == 2) e = 1;
  if (valp(x) < 0) pari_err_DOMAIN("gamma","v_p(x)", "<", gen_0, x);
  n = gtrunc(x);
  m = gtrunc(gneg(x));
  N = cmpii(n,m)<=0?n:m;
  s = itos_or_0(N);
  if (s && cmpsi(s, muliu(p,e)) < 0) /* s < p*e */
    return (N == n) ? Qp_gamma_Morita(s,p,e): Qp_gamma_neg_Morita(s,p,e);
  return Qp_gamma_Dwork(x, itos(p));
}

GEN
ggamma(GEN x, long prec)
{
  pari_sp av;
  GEN y, z;

  switch(typ(x))
  {
    case t_INT:
      if (signe(x) <= 0)
        pari_err_DOMAIN("gamma","argument", "=",
                         strtoGENstr("non-positive integer"), x);
      if (cmpiu(x,481177) > 0) pari_err_OVERFLOW("gamma");
      return mpfactr(itos(x) - 1, prec);

    case t_REAL: case t_COMPLEX:
      return cxgamma(x, 0, prec);

    case t_FRAC:
    {
      GEN a = gel(x,1), b = gel(x,2), c;
      long m;
      if (equaliu(b,2))
      {
        if (is_bigint(a) || labs(m = itos(a)) > 962354)
        {
          pari_err_OVERFLOW("gamma");
          return NULL; /* not reached */
        }
        return gammahs(m-1, prec);
      }
      av = avma; c = subii(a,b);
      if (expi(c) - expi(b) < -10)
      {
        x = mkfrac(c,b);
        if (lgefint(b) >= prec) x = fractor(x,prec);
        y = mpexp(lngamma1(x, prec));
      }
      else
      {
        x = fractor(x, prec);
        y = cxgamma(x, 0, prec);
      }
      return gerepileupto(av, y);
    }

    case t_PADIC: return Qp_gamma(x);
    default:
      av = avma; if (!(y = toser_i(x))) break;
      /* exp(lngamma) */
      if (valp(y)>0 || lg(y) == 2)
        z = gdiv(gexp(glngamma(gaddgs(y,1),prec),prec),y);
      else
      { /* use fun eq. to avoid log singularity of lngamma at negative ints */
        GEN Y = y, y0 = gel(y,2), t = ground(y0), pi = NULL;
        if (gequal(y0, t) && typ(t) == t_INT && signe(t) < 0)
        {
          pi = mppi(prec);
          Y = gsubsg(1, y);
          y0= subsi(1, y0);
        }
        z = glngamma(Y,prec);
        if (!valp(z))
        {
          z = serchop0(z);
          z = gmul(ggamma(y0,prec), gexp(z,prec));
        }
        else
          z = gexp(z,prec);
        if (pi)
          z = gdiv(mpodd(t)? negr(pi): pi,
                   gmul(z, gsin(gmul(pi,serchop0(y)), prec)));
      }
      return gerepileupto(av, z);
  }
  return trans_eval("gamma",ggamma,x,prec);
}

GEN
mpfactr(long n, long prec)
{
  GEN f = cgetr(prec);
  pari_sp av = avma;

  if (n+1 > 350 + 70*(prec-2)) /* heuristic */
    affrr(cxgamma(stor(n+1, prec), 0, prec), f);
  else
    affir(mpfact(n), f);
  avma = av; return f;
}

GEN
glngamma(GEN x, long prec)
{
  pari_sp av = avma;
  GEN y, p1;

  switch(typ(x))
  {
    case t_INT:
      if (signe(x) <= 0)
        pari_err_DOMAIN("lngamma","argument", "=",
                         strtoGENstr("non-positive integer"), x);
      if (cmpiu(x,200 + 50*(prec-2)) > 0) /* heuristic */
        return cxgamma(x, 1, prec);
      return gerepileuptoleaf(av, logr_abs( itor(mpfact(itos(x) - 1), prec) ));
    case t_FRAC:
    {
      GEN a = gel(x,1), b = gel(x,2), c = subii(a,b);
      long e = expi(b) - expi(c);
      if (e > 10)
      {
        x = mkfrac(c,b);
        if (lgefint(b) >= prec) x = fractor(x,prec + nbits2nlong(e));
        y = lngamma1(x, prec);
      }
      else
      {
        x = fractor(x, e > 1? prec+EXTRAPRECWORD: prec);
        y = cxgamma(x, 1, prec);
      }
      return gerepileupto(av, y);
    }

    case t_REAL: case t_COMPLEX:
      return cxgamma(x, 1, prec);

    default:
      if (!(y = toser_i(x))) break;
      if (valp(y)) pari_err_DOMAIN("lngamma","valuation", "!=", gen_0, x);
      /* (lngamma y)' = y' psi(y) */
      p1 = integser(gmul(derivser(y), gpsi(y, prec)));
      if (!gequal1(gel(y,2))) p1 = gadd(p1, glngamma(gel(y,2),prec));
      return gerepileupto(av, p1);

    case t_PADIC: return gerepileupto(av, Qp_log(Qp_gamma(x)));
  }
  return trans_eval("lngamma",glngamma,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                  PSI(x) = GAMMA'(x)/GAMMA(x)                   **/
/**                                                                **/
/********************************************************************/

GEN
cxpsi(GEN s0, long prec)
{
  pari_sp av, av2;
  GEN sum,z,a,res,tes,in2,sig,tau,s,unr;
  long lim,nn,k;
  const long la = 3;
  int funeq = 0;
  pari_timer T;

  if (DEBUGLEVEL>2) timer_start(&T);
  s = trans_fix_arg(&prec,&s0,&sig,&tau,&av,&res);
  if (signe(sig) <= 0) { funeq = 1; s = gsub(gen_1, s); sig = real_i(s); }
  if (typ(s0) == t_INT && signe(s0) <= 0)
    pari_err_DOMAIN("psi","argument", "=",
                    strtoGENstr("non-positive integer"), s0);

  if (expo(sig) > 300 || (typ(s) == t_COMPLEX && gexpo(gel(s,2)) > 300))
  { /* |s| is HUGE. Play safe */
    GEN L, S = gprec_w(s,LOWDEFAULTPREC), rS = real_i(S), iS = imag_i(S);
    double l;

    l = rtodbl( gnorm(glog(S, 3)) );
    l = log(l) / 2.;
    lim = 2 + (long)ceil((prec2nbits_mul(prec, LOG2) - l) / (2*(1+log((double)la))));
    if (lim < 2) lim = 2;

    l = (2*lim-1)*la / (2.*M_PI);
    L = gsub(dbltor(l*l), gsqr(iS));
    if (signe(L) < 0) L = gen_0;

    L = gsub(gsqrt(L, 3), rS);
    if (signe(L) > 0) nn = (long)ceil(rtodbl(L)); else nn = 1;
    if (DEBUGLEVEL>2) err_printf("lim, nn: [%ld, %ld]\n",lim,nn);
  }
  else
  {
    double ssig = rtodbl(sig);
    double st = typ(s) == t_REAL? 0.0: rtodbl(imag_i(s));
    double l;
    {
      double rlog, ilog; /* log (s - Euler) */
      dcxlog(ssig - 0.57721566, st, &rlog,&ilog);
      l = dnorm(rlog,ilog);
    }
    if (l < 0.000001) l = 0.000001;
    l = log(l) / 2.;
    lim = 2 + (long)ceil((prec2nbits_mul(prec, LOG2) - l) / (2*(1+log((double)la))));
    if (lim < 2) lim = 2;

    l = (2*lim-1)*la / (2.*M_PI);
    l = l*l - st*st;
    if (l < 0.) l = 0.;
    nn = (long)ceil( sqrt(l) - ssig );
    if (nn < 1) nn = 1;
    if (DEBUGLEVEL>2) err_printf("lim, nn: [%ld, %ld]\n",lim,nn);
  }
  incrprec(prec); unr = real_1(prec); /* one extra word of precision */

  a = gdiv(unr, gaddgs(s, nn)); /* 1 / (s+n) */
  av2 = avma; sum = gmul2n(a,-1);
  for (k = 0; k < nn; k++)
  {
    sum = gadd(sum, gdiv(unr, gaddgs(s, k)));
    if ((k & 127) == 0) sum = gerepileupto(av2, sum);
  }
  z = gsub(glog(gaddgs(s, nn), prec), sum);
  if (DEBUGLEVEL>2) timer_printf(&T,"sum from 0 to N-1");

  in2 = gsqr(a);
  mpbern(lim,prec);
  av2 = avma; tes = divru(bernreal(2*lim, prec), 2*lim);
  for (k=2*lim-2; k>=2; k-=2)
  {
    tes = gadd(gmul(in2,tes), divru(bernreal(k, prec), k));
    if ((k & 255) == 0) tes = gerepileupto(av2, tes);
  }
  if (DEBUGLEVEL>2) timer_printf(&T,"Bernoulli sum");
  z = gsub(z, gmul(in2,tes));
  if (funeq)
  {
    GEN pi = mppi(prec);
    z = gadd(z, gmul(pi, gcotan(gmul(pi,s), prec)));
  }
  avma = av; return affc_fixlg(z, res);
}

/* psi(1+x) + O(x^n), x = pol_x(v) */
static GEN
serpsi1(long n, long v, long prec)
{
  long i, l = n+3;
  GEN z, g, s = cgetg(l, t_SER);
  s[1] = evalsigne(1)|evalvalp(0)|evalvarn(v);
  g = mpeuler(prec); setsigne(g, -1);
  z = veczeta(gen_1, gen_2, n, prec); /* zeta(2..n) */
  gel(s,2) = g;
  for (i = 2; i < l-1; i++)
  {
    GEN c = gel(z,i-1); /* zeta(i) */
    if (odd(i)) setsigne(c, -1);
    gel(s,i+1) = c;
  }
  return s;
}
/* T an RgX, return T(X + z0) + O(X^L) */
static GEN
tr(GEN T, GEN z0, long L)
{
  GEN s = RgX_to_ser(RgX_translate(T, z0), L+3);
  setvarn(s, 0); return s;
}
/* psi(z0+x) + O(x^n) */
static GEN
serpsiz0(GEN z0, long L, long v, long prec)
{
  pari_sp av;
  GEN A,A1,A2, B,B1,B2, Q;
  long n;

  if (equali1(z0)) return serpsi1(L, v, prec);
  /* otherwise use Luke's rational approximations for psi(x) */
  n = gprecision(z0); if (n) prec = n;
  z0 = gtofp(z0, prec + EXTRAPRECWORD);
  /* Start from n = 3; in Luke's notation, A2 := A_{n-2}, A1 := A_{n-1},
   * A := A_n. Same for B */
  av = avma;
  A2= gdivgs(mkpoln(2, gen_1, utoipos(6)), 2);
  B2 = scalarpol_shallow(utoipos(4), 0);
  A1= gdivgs(mkpoln(3, gen_1, utoipos(82), utoipos(96)), 6);
  B1 = mkpoln(2, utoipos(8), utoipos(28));
  A = gdivgs(mkpoln(4, gen_1, utoipos(387), utoipos(2906), utoipos(1920)), 12);
  B = mkpoln(3, utoipos(14), utoipos(204), utoipos(310));
  A2= tr(A2,z0, L);
  B2= tr(B2,z0, L);
  A1= tr(A1,z0, L);
  B1= tr(B1,z0, L);
  A = tr(A, z0, L);
  B = tr(B, z0, L); Q = gdiv(A, B);
  /* work with z0+x as a variable */
  for (n = 4;; n++)
  {
    GEN Q0 = Q, a, b, r, c3,c2,c1,c0 = muluu(2*n-3, n+1);
    GEN u = subiu(muluu(n, 7*n-9), 6);
    GEN t = addiu(muluu(n, 7*n-19), 4);
    /* c1=(2*n-1)*(3*(n-1)*z+7*n^2-9*n-6);
     * c2=(2*n-3)*(z-n-1)*(-3*(n-1)*z+7*n^2-19*n+4);
     * c3=(2*n-1)*(n-3)*(z-n)*(z-(n+1))*(z+(n-4)); */
    c1 = deg1pol_shallow(muluu(3*(n-1),2*n-1), muliu(u,2*n-1), 0);
    c2 = ZX_mul(deg1pol_shallow(utoipos(2*n-3), negi(muluu(2*n-3,n+1)), 0),
                deg1pol_shallow(utoineg(3*(n-1)), t, 0));
    r = mkvec3(utoipos(n), utoipos(n+1), stoi(4-n));
    c3 = ZX_Z_mul(roots_to_pol(r,0), muluu(2*n-1,n-3));
    c1 = tr(c1, z0, L+3);
    c2 = tr(c2, z0, L+3);
    c3 = tr(c3, z0, L+3);

    /* A_{n+1}, B_{n+1} */
    a = gdiv(gadd(gadd(gmul(c1,A),gmul(c2,A1)),gmul(c3,A2)), c0);
    b = gdiv(gadd(gadd(gmul(c1,B),gmul(c2,B1)),gmul(c3,B2)), c0);
    Q = gdiv(a,b);
    if (gexpo(gsub(Q,Q0)) < -prec2nbits(prec)) break;
    A2 = A1; A1 = A; A = a;
    B2 = B1; B1 = B; B = b;
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"serpsiz0, n = %ld", n);
      gerepileall(av, 7, &A,&A1,&A2, &B,&B1,&B2, &Q);
    }
  }
  Q = gmul(Q, gmul2n(gsubsg(1, ginv(tr(pol_x(v),z0, L))), 1));
  setvarn(Q, v);
  return gadd(negr(mpeuler(prec)), Q);
}
static GEN
serpsi(GEN y, long prec)
{
  GEN Q, z0, Y;
  long L = lg(y)-2, v  = varn(y), vy = valp(y);
  int reflect;

  if (!L) pari_err_DOMAIN("psi", "argument", "=", gen_0,y);
  if (vy < 0) pari_err_DOMAIN("psi", "series valuation", "<", gen_0,y);
  if (vy)
    z0 = gen_0;
  else
  {
    GEN t;
    z0 = simplify_shallow(gel(y,2));
    t = ground(z0);
    if (gequal(t,z0)) z0 = t;
  }
  reflect = (gcmp(real_i(z0),ghalf) < 0); /* use reflection formula */
  if (reflect) { z0 = gsubsg(1,z0); Y = gsubsg(1,y); } else Y = y;
  Q = serpsiz0(z0, L, v, prec);
  Q = gsubst(Q, v, serchop0(Y)); /* psi(Y) */
  if (reflect)
  { /* psi(y) = psi(Y) + Pi cotan(Pi Y) = psi(Y) - Pi cotan(Pi y) */
    GEN pi = mppi(prec);
    if (equali1(z0))
      Q = gsub(Q, gmul(pi, gcotan(gmul(pi,y), prec)));
    else
      Q = gadd(Q, gmul(pi, gcotan(gmul(pi,Y), prec)));
  }
  return Q;
}

GEN
gpsi(GEN x, long prec)
{
  pari_sp av;
  GEN y;
  switch(typ(x))
  {
    case t_REAL: case t_COMPLEX: return cxpsi(x,prec);
    default:
      av = avma; if (!(y = toser_i(x))) break;
      return gerepileupto(av, serpsi(y,prec));
  }
  return trans_eval("psi",gpsi,x,prec);
}
