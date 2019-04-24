#ifdef LONG_IS_64BIT
#define __MULII_KARATSUBA_LIMIT         23
#define __SQRI_KARATSUBA_LIMIT          36
#define __MULII_FFT_LIMIT             1441
#define __SQRI_FFT_LIMIT              1651
#define __MULRR_MULII_LIMIT            276
#define __Fp_POW_REDC_LIMIT             99
#define __Fp_POW_BARRETT_LIMIT         101
#define __INVNEWTON_LIMIT              656
#define __DIVRR_GMP_LIMIT               -1
#define __EXPNEWTON_LIMIT               66
#define __LOGAGM_LIMIT                  16
#define __LOGAGMCX_LIMIT                13
#define __AGM_ATAN_LIMIT                56
#define __INVMOD_GMP_LIMIT              -1
#define __Flx_MUL_KARATSUBA_LIMIT      147
#define __Flx_SQR_KARATSUBA_LIMIT      330
#define __Flx_MUL_HALFMULII_LIMIT        5
#define __Flx_SQR_HALFSQRI_LIMIT         3
#define __Flx_MUL_MULII_LIMIT         1639
#define __Flx_SQR_SQRI_LIMIT             5
#define __Flx_MUL_MULII2_LIMIT           5
#define __Flx_SQR_SQRI2_LIMIT            8
#define __Flx_INVBARRETT_LIMIT        3577
#define __Flx_DIVREM_BARRETT_LIMIT    2804
#define __Flx_REM_BARRETT_LIMIT       3577
#define __Flx_BARRETT_LIMIT           1623
#define __Flx_HALFGCD_LIMIT             80
#define __Flx_GCD_LIMIT               1890
#define __Flx_EXTGCD_LIMIT             284
#define __FpX_INVBARRETT_LIMIT         254
#define __FpX_DIVREM_BARRETT_LIMIT     292
#define __FpX_REM_BARRETT_LIMIT        306
#define __FpX_BARRETT_LIMIT             85
#define __FpX_HALFGCD_LIMIT             75
#define __FpX_GCD_LIMIT                731
#define __FpX_EXTGCD_LIMIT             117
#define __RgX_MUL_LIMIT                  9
#define __RgX_SQR_LIMIT                 35
#else
#define __MULII_KARATSUBA_LIMIT         18
#define __SQRI_KARATSUBA_LIMIT          27
#define __MULII_FFT_LIMIT             1386
#define __SQRI_FFT_LIMIT              1469
#define __MULRR_MULII_LIMIT            102
#define __Fp_POW_REDC_LIMIT             99
#define __Fp_POW_BARRETT_LIMIT          97
#define __INVNEWTON_LIMIT              380
#define __DIVRR_GMP_LIMIT               -1
#define __EXPNEWTON_LIMIT               66
#define __LOGAGM_LIMIT                  55
#define __LOGAGMCX_LIMIT                58
#define __AGM_ATAN_LIMIT               159
#define __INVMOD_GMP_LIMIT              -1
#define __Flx_MUL_KARATSUBA_LIMIT       85
#define __Flx_SQR_KARATSUBA_LIMIT      159
#define __Flx_MUL_HALFMULII_LIMIT        8
#define __Flx_SQR_HALFSQRI_LIMIT         6
#define __Flx_MUL_MULII_LIMIT          698
#define __Flx_SQR_SQRI_LIMIT          1276
#define __Flx_MUL_MULII2_LIMIT        3755
#define __Flx_SQR_SQRI2_LIMIT         4139
#define __Flx_INVBARRETT_LIMIT        4345
#define __Flx_DIVREM_BARRETT_LIMIT    3942
#define __Flx_REM_BARRETT_LIMIT       3942
#define __Flx_BARRETT_LIMIT            915
#define __Flx_HALFGCD_LIMIT            232
#define __Flx_GCD_LIMIT               7165
#define __Flx_EXTGCD_LIMIT             850
#define __FpX_INVBARRETT_LIMIT         337
#define __FpX_DIVREM_BARRETT_LIMIT     306
#define __FpX_REM_BARRETT_LIMIT        306
#define __FpX_BARRETT_LIMIT            144
#define __FpX_HALFGCD_LIMIT            145
#define __FpX_GCD_LIMIT               1292
#define __FpX_EXTGCD_LIMIT             238
#define __RgX_MUL_LIMIT                  5
#define __RgX_SQR_LIMIT                 26
#endif
#line 2 "../src/kernel/none/int.h"
/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#define int_MSW(x) ((x)+2)
/*x being a t_INT, return a pointer to the most significant word of x.*/

#define int_LSW(x) ((x)+lgefint((x))-1)
/*x being a t_INT, return a pointer to the least significant word of x.*/

#define int_precW(x) ((x)+1)
/*x pointing to a mantissa word, return the previous (less significant)
 * mantissa word.*/

#define int_nextW(x) ((x)-1)
/*x pointing to a mantissa word, return the next (more significant) mantissa
 * word.*/

#define int_W(x,l) ((x)+lgefint((x))-1-(l))
/*x being a t_INT, return a pointer to the l-th least significant word of x.*/

#define int_W_lg(x,l,lx) ((x)+lx-1-(l))
/*x being a t_INT, return a pointer to the l-th least significant word of x,
 * assuming lgefint(x) = lx.*/

#define PARI_KERNEL_NONE
/*This macro should not be used in libpari itself.*/
#line 2 "../src/kernel/none/level1.h"
/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* This file defines "level 1" kernel functions.
 * These functions can be inline; they are also defined externally in
 * mpinl.c, which includes this file and never needs to be changed */

INLINE pari_long
evallg(pari_long x)
{
  if (x & ~LGBITS) pari_err_OVERFLOW("lg()");
  return _evallg(x);
}
INLINE pari_long
evalvalp(pari_long x)
{
  pari_long v = _evalvalp(x);
  if (v & ~VALPBITS) pari_err_OVERFLOW("valp()");
  return v;
}
INLINE pari_long
evalexpo(pari_long x)
{
  pari_long v = _evalexpo(x);
  if (v & ~EXPOBITS) pari_err_OVERFLOW("expo()");
  return v;
}
INLINE pari_long
evalprecp(pari_long x)
{
  pari_long v = _evalprecp(x);
  if (x & ~((1ULL<<(BITS_IN_LONG-VALPnumBITS))-1)) pari_err_OVERFLOW("precp()");
  return v;
}

/* Inhibit some area gerepile-wise: declare it to be a non recursive
 * type, of length l. Thus gerepile won't inspect the zone, just copy it.
 * For the following situation:
 *   z = cgetg(t,a); av = avma; garbage(); ltop = avma;
 *   for (i=1; i<HUGE; i++) gel(z,i) = blah();
 *   stackdummy(av,ltop);
 * loses (av-ltop) words but save a costly gerepile. */
INLINE void
stackdummy(pari_sp av, pari_sp ltop) {
  pari_long l = ((GEN)av) - ((GEN)ltop);
  if (l > 0) {
    GEN z = (GEN)ltop;
    z[0] = evaltyp(t_VECSMALL) | evallg(l);
#ifdef DEBUG
    { pari_long i; for (i = 1; i < l; i++) z[i] = 0; }
#endif
  }
}
INLINE void
fixlg(GEN x, pari_long ly) {
  pari_long lx = lg(x), l = lx - ly;
  if (l > 0)
  { /* stackdummy(x+lx, x+ly) */
    GEN z = x + ly;
    z[0] = evaltyp(t_VECSMALL) | evallg(l);
    setlg(x, ly);
#ifdef DEBUG
    { pari_long i; for (i = 1; i < l; i++) z[i] = 0; }
#endif
  }
}
/* update lg(z) before affrr(y, z)  [ to cater for precision loss ]*/
INLINE void
affrr_fixlg(GEN y, GEN z) { fixlg(z, lg(y)); affrr(y, z); }

/*******************************************************************/
/*                                                                 */
/*                       ALLOCATE ON STACK                         */
/*                                                                 */
/*******************************************************************/
INLINE GEN
new_chunk(size_t x) /* x is a number of pari_longs */
{
  GEN z = ((GEN) avma) - x;
  if (x > (avma-bot) / sizeof(pari_long)) pari_err(e_STACK);
  CHECK_CTRLC
  avma = (pari_sp)z;

#ifdef MEMSTEP
  if (DEBUGMEM && memused != DISABLE_MEMUSED) {
    pari_long d = (pari_long)memused - (pari_long)z;
    if (d > 4*MEMSTEP || d < -4*MEMSTEP)
    {
      memused = (pari_sp)z;
      err_printf("...%4.0lf Mbytes used\n",(top-memused)/1048576.);
    }
  }
#endif
  return z;
}

INLINE char *
stack_malloc(size_t N)
{
  pari_long n = nchar2nlong(N);
  return (char*)new_chunk(n);
}

INLINE char *
stack_calloc(size_t N)
{
  char *p = stack_malloc(N);
  memset(p, 0, N); return p;
}

/* cgetg(lg(x), typ(x)), set *lx. Implicit unsetisclone() */
INLINE GEN
cgetg_copy(GEN x, pari_long *plx) {
  GEN y;
  *plx = lg(x); y = new_chunk((size_t)*plx);
  y[0] = x[0] & (TYPBITS|LGBITS); return y;
}
INLINE GEN
cgetg_block(pari_long x, pari_long y)
{
  GEN z = newblock((size_t)x);
  z[0] = evaltyp(y) | evallg(x);
  return z;
}
INLINE GEN
cgetg(pari_long x, pari_long y)
{
  GEN z = new_chunk((size_t)x);
  z[0] = evaltyp(y) | evallg(x);
  return z;
}
INLINE GEN
cgeti(pari_long x)
{
  GEN z = new_chunk((size_t)x);
  z[0] = evaltyp(t_INT) | evallg(x);
  return z;
}
INLINE GEN
cgetipos(pari_long x)
{
  GEN z = cgeti(x);
  z[1] = evalsigne(1) | evallgefint(x);
  return z;
}
INLINE GEN
cgetineg(pari_long x)
{
  GEN z = cgeti(x);
  z[1] = evalsigne(-1) | evallgefint(x);
  return z;
}
INLINE GEN
cgetr_block(pari_long x)
{
  GEN z = newblock((size_t)x);
  z[0] = evaltyp(t_REAL) | evallg(x);
  return z;
}
INLINE GEN
cgetr(pari_long x)
{
  GEN z = new_chunk((size_t)x);
  z[0] = evaltyp(t_REAL) | evallg(x);
  return z;
}

/*******************************************************************/
/*                                                                 */
/*                     COPY, NEGATION, ABSOLUTE VALUE              */
/*                                                                 */
/*******************************************************************/
/* cannot do memcpy because sometimes x and y overlap */
INLINE GEN
leafcopy(GEN x)
{
  register pari_long lx = lg(x);
  GEN y = new_chunk(lx); /* can't use cgetg_copy, in case x,y overlap */
  while (--lx > 0) y[lx] = x[lx];
  y[0] = x[0] & (TYPBITS|LGBITS); return y;
}
INLINE GEN
icopy(GEN x)
{
  pari_long i = lgefint(x), lx = i;
  GEN y = new_chunk(lx); /* can't use cgeti, in case x,y overlap */
  while (--i > 0) y[i] = x[i];
  y[0] = evaltyp(t_INT) | evallg(lx);
  return y;
}
INLINE GEN
icopyspec(GEN x, pari_long nx)
{
  pari_long i = nx+2, lx = i;
  GEN y = new_chunk(lx); /* can't use cgeti, in case x,y overlap */
  x -= 2; while (--i >= 2) y[i] = x[i];
  y[1] = evalsigne(1) | evallgefint(lx);
  y[0] = evaltyp(t_INT) | evallg(lx);
  return y;
}
INLINE GEN rcopy(GEN x) { return leafcopy(x); }
INLINE GEN mpcopy(GEN x) { return leafcopy(x); }

INLINE GEN
mpabs(GEN x) { GEN y = leafcopy(x); setabssign(y); return y; }
INLINE GEN
mpabs_shallow(GEN x) { return signe(x) < 0? mpabs(x): x; }
INLINE GEN absi(GEN x) { return mpabs(x); }
INLINE GEN absi_shallow(GEN x) { return signe(x) < 0? negi(x): x; }
INLINE GEN absr(GEN x) { return mpabs(x); }

INLINE GEN
mpneg(GEN x) { GEN y = leafcopy(x); togglesign(y); return y; }
INLINE GEN negi(GEN x) { return mpneg(x); }
INLINE GEN negr(GEN x) { return mpneg(x); }

/* negate in place */
INLINE void
togglesign(GEN x) { if (x[1] & SIGNBITS) { x[1] ^= HIGHBIT; } }
INLINE void
setabssign(GEN x) { x[1] &= ~HIGHBIT; }
/* negate in place, except universal constants */
INLINE void
togglesign_safe(GEN *px)
{
  switch(*px - gen_1) /* gen_1, gen_2, gen_m1, gen_m2 */
  {
    case 0: *px = gen_m1; break;
    case 3: *px = gen_m2;  break;
    case 6: *px = gen_1; break;
    case 9: *px = gen_2;  break;
    default: togglesign(*px);
  }
}
/* setsigne(y, signe(x)) */
INLINE void
affectsign(GEN x, GEN y)
{
  y[1] = (x[1] & SIGNBITS) | (y[1] & ~SIGNBITS);
}
/* copies sign in place, except for universal constants */
INLINE void
affectsign_safe(GEN x, GEN *py)
{
  if (((*py)[1] ^ x[1]) & HIGHBIT) togglesign_safe(py);
}
/*******************************************************************/
/*                                                                 */
/*                     GEN -> LONG, LONG -> GEN                    */
/*                                                                 */
/*******************************************************************/
/* assume x != 0, return -x as a t_INT */
INLINE GEN
utoineg(ulong x) { GEN y = cgetineg(3); y[2] = x; return y; }
/* assume x != 0, return utoi(x) */
INLINE GEN
utoipos(ulong x) { GEN y = cgetipos(3); y[2] = x; return y; }
INLINE GEN
utoi(ulong x) { return x? utoipos(x): gen_0; }
INLINE GEN
stoi(pari_long x)
{
  if (!x) return gen_0;
  return x > 0? utoipos((ulong)x): utoineg((ulong)-x);
}

/* x 2^BIL + y */
INLINE GEN
uutoi(ulong x, ulong y)
{
  GEN z;
  if (!x) return utoi(y);
  z = cgetipos(4);
  *int_W_lg(z, 1, 4) = x;
  *int_W_lg(z, 0, 4) = y; return z;
}
/* - (x 2^BIL + y) */
INLINE GEN
uutoineg(ulong x, ulong y)
{
  GEN z;
  if (!x) return y? utoineg(y): gen_0;
  z = cgetineg(4);
  *int_W_lg(z, 1, 4) = x;
  *int_W_lg(z, 0, 4) = y; return z;
}

INLINE pari_long
itos(GEN x)
{
  pari_long s = signe(x);
  pari_long u;

  if (!s) return 0;
  u = x[2];
  if (lgefint(x) > 3 || u < 0)
    pari_err_OVERFLOW("t_INT-->long assignment");
  return (s>0) ? u : -u;
}
/* as itos, but return 0 if too large. Cf is_bigint */
INLINE pari_long
itos_or_0(GEN x) {
  pari_long n;
  if (lgefint(x) != 3 || (n = x[2]) & HIGHBIT) return 0;
  return signe(x) > 0? n: -n;
}
INLINE ulong
itou(GEN x)
{
  switch(lgefint(x)) {
    case 2: return 0;
    case 3: return x[2];
    default:
      pari_err_OVERFLOW("t_INT-->ulong assignment");
      return 0; /* not reached */
  }
}

/* as itou, but return 0 if too large. Cf is_bigint */
INLINE ulong
itou_or_0(GEN x) {
  if (lgefint(x) != 3) return 0;
  return (ulong)x[2];
}

INLINE GEN
real_0_bit(pari_long bitprec) { GEN x=cgetr(2); x[1]=evalexpo(bitprec); return x; }
INLINE GEN
real_0(pari_long prec) { return real_0_bit(-prec2nbits(prec)); }
INLINE GEN
real_1(pari_long prec) {
  GEN x = cgetr(prec);
  pari_long i;
  x[1] = evalsigne(1) | _evalexpo(0);
  x[2] = (pari_long)HIGHBIT; for (i=3; i<prec; i++) x[i] = 0;
  return x;
}
INLINE GEN
real_m1(pari_long prec) {
  GEN x = cgetr(prec);
  pari_long i;
  x[1] = evalsigne(-1) | _evalexpo(0);
  x[2] = (pari_long)HIGHBIT; for (i=3; i<prec; i++) x[i] = 0;
  return x;
}

/* 2.^n */
INLINE GEN
real2n(pari_long n, pari_long prec) { GEN z = real_1(prec); setexpo(z, n); return z; }
INLINE GEN
real_m2n(pari_long n, pari_long prec) { GEN z = real_m1(prec); setexpo(z, n); return z; }
INLINE GEN
stor(pari_long s, pari_long prec) { GEN z = cgetr(prec); affsr(s,z); return z; }
INLINE GEN
utor(ulong s, pari_long prec){ GEN z = cgetr(prec); affur(s,z); return z; }
INLINE GEN
itor(GEN x, pari_long prec) { GEN z = cgetr(prec); affir(x,z); return z; }
INLINE GEN
rtor(GEN x, pari_long prec) { GEN z = cgetr(prec); affrr(x,z); return z; }

INLINE ulong int_bit(GEN x, pari_long n)
{
  pari_long r, q = dvmdsBIL(n, &r);
  return q < lgefint(x)-2?((ulong)*int_W(x,q) >> r) & 1ULL:0;
}

/*******************************************************************/
/*                                                                 */
/*                           COMPARISON                            */
/*                                                                 */
/*******************************************************************/
INLINE int
cmpir(GEN x, GEN y)
{
  pari_sp av;
  GEN z;

  if (!signe(x)) return -signe(y);
  if (!signe(y)) return  signe(x);
  av=avma; z = itor(x, realprec(y)); avma=av;
  return cmprr(z,y); /* cmprr does no memory adjustment */
}
INLINE int
cmpri(GEN x, GEN y) { return -cmpir(y,x); }
INLINE int
cmpsr(pari_long x, GEN y)
{
  pari_sp av;
  GEN z;

  if (!x) return -signe(y);
  av=avma; z = stor(x, LOWDEFAULTPREC); avma=av;
  return cmprr(z,y);
}
INLINE int
cmprs(GEN x, pari_long y) { return -cmpsr(y,x); }
/* compare x and |y| */
INLINE int
cmpui(ulong x, GEN y)
{
  pari_long l = lgefint(y);
  ulong p;

  if (!x) return (l > 2)? -1: 0;
  if (l == 2) return 1;
  if (l > 3) return -1;
  p = y[2]; if (p == x) return 0;
  return p < x ? 1 : -1;
}
INLINE int
cmpiu(GEN x, ulong y) { return -cmpui(y,x); }
INLINE int
cmpsi(pari_long x, GEN y)
{
  ulong p;

  if (!x) return -signe(y);

  if (x > 0)
  {
    if (signe(y)<=0) return 1;
    if (lgefint(y)>3) return -1;
    p = y[2]; if (p == (ulong)x) return 0;
    return p < (ulong)x ? 1 : -1;
  }

  if (signe(y)>=0) return -1;
  if (lgefint(y)>3) return 1;
  p = y[2]; if (p == (ulong)-x) return 0;
  return p < (ulong)(-x) ? -1 : 1;
}
INLINE int
cmpis(GEN x, pari_long y) { return -cmpsi(y,x); }
INLINE int
mpcmp(GEN x, GEN y)
{
  if (typ(x)==t_INT)
    return (typ(y)==t_INT) ? cmpii(x,y) : cmpir(x,y);
  return (typ(y)==t_INT) ? -cmpir(y,x) : cmprr(x,y);
}

/* x == y ? */
INLINE int
equalsi(pari_long x, GEN y)
{
  if (!x) return !signe(y);
  if (x > 0)
  {
    if (signe(y) <= 0 || lgefint(y) != 3) return 0;
    return ((ulong)y[2] == (ulong)x);
  }
  if (signe(y) >= 0 || lgefint(y) != 3) return 0;
  return ((ulong)y[2] == (ulong)-x);
}
/* x == |y| ? */
INLINE int
equalui(ulong x, GEN y)
{
  if (!x) return !signe(y);
  return (lgefint(y) == 3 && (ulong)y[2] == x);
}
INLINE int
equaliu(GEN x, ulong y) { return equalui(y,x); }
INLINE int
equalis(GEN x, pari_long y) { return equalsi(y,x); }

/* assume x != 0, is |x| == 2^n ? */
INLINE int
absrnz_equal2n(GEN x) {
  if ((ulong)x[2]==HIGHBIT)
  {
    pari_long i, lx = lg(x);
    for (i = 3; i < lx; i++)
      if (x[i]) return 0;
    return 1;
  }
  return 0;
}
/* assume x != 0, is |x| == 1 ? */
INLINE int
absrnz_equal1(GEN x) { return !expo(x) && absrnz_equal2n(x); }

INLINE pari_long
maxss(pari_long x, pari_long y) { return x>y?x:y; }
INLINE pari_long
minss(pari_long x, pari_long y) { return x<y?x:y; }
INLINE pari_long
minuu(ulong x, ulong y) { return x<y?x:y; }
INLINE pari_long
maxuu(ulong x, ulong y) { return x>y?x:y; }
INLINE double
maxdd(double x, double y) { return x>y?x:y; }
INLINE double
mindd(double x, double y) { return x<y?x:y; }

/*******************************************************************/
/*                                                                 */
/*                             ADD / SUB                           */
/*                                                                 */
/*******************************************************************/
INLINE GEN
subuu(ulong x, ulong y)
{
  ulong z;
  LOCAL_OVERFLOW;
  z = subll(x, y);
  return overflow? utoineg(-z): utoi(z);
}
INLINE GEN
adduu(ulong x, ulong y) { ulong t = x+y; return uutoi((t < x), t); }

INLINE GEN
addss(pari_long x, pari_long y)
{
  if (!x) return stoi(y);
  if (!y) return stoi(x);
  if (x > 0) return y > 0? adduu(x,y): subuu(x, -y);

  if (y > 0) return subuu(y, -x);
  else { /* - adduu(-x, -y) */
    ulong t = (-x)+(-y); return uutoineg((t < (ulong)(-x)), t);
  }
}
INLINE GEN subss(pari_long x, pari_long y) { return addss(-y,x); }

INLINE GEN
subii(GEN x, GEN y)
{
  if (x==y) return gen_0; /* frequent with x = y = gen_0 */
  return addii_sign(x, signe(x), y, -signe(y));
}
INLINE GEN
addii(GEN x, GEN y) { return addii_sign(x, signe(x), y, signe(y)); }
INLINE GEN
addrr(GEN x, GEN y) { return addrr_sign(x, signe(x), y, signe(y)); }
INLINE GEN
subrr(GEN x, GEN y) { return addrr_sign(x, signe(x), y, -signe(y)); }
INLINE GEN
addir(GEN x, GEN y) { return addir_sign(x, signe(x), y, signe(y)); }
INLINE GEN
subir(GEN x, GEN y) { return addir_sign(x, signe(x), y, -signe(y)); }
INLINE GEN
subri(GEN x, GEN y) { return addir_sign(y, -signe(y), x, signe(x)); }
INLINE GEN
addsi(pari_long x, GEN y) { return addsi_sign(x, y, signe(y)); }
INLINE GEN
addui(ulong x, GEN y) { return addui_sign(x, y, signe(y)); }
INLINE GEN
subsi(pari_long x, GEN y) { return addsi_sign(x, y, -signe(y)); }
INLINE GEN
subui(ulong x, GEN y) { return addui_sign(x, y, -signe(y)); }

/*******************************************************************/
/*                                                                 */
/*                           MOD, REM, DIV                         */
/*                                                                 */
/*******************************************************************/
INLINE ulong mod2BIL(GEN x) { return *int_LSW(x); }
INLINE pari_long mod64(GEN x) { return mod2BIL(x) & 63; }
INLINE pari_long mod32(GEN x) { return mod2BIL(x) & 31; }
INLINE pari_long mod16(GEN x) { return mod2BIL(x) & 15; }
INLINE pari_long mod8(GEN x)  { return mod2BIL(x) & 7; }
INLINE pari_long mod4(GEN x)  { return mod2BIL(x) & 3; }
INLINE pari_long mod2(GEN x)  { return mod2BIL(x) & 1; }
INLINE int
mpodd(GEN x) { return signe(x) && mod2(x); }

INLINE GEN
truedivii(GEN a,GEN b) { return truedvmdii(a,b,NULL); }
INLINE GEN
truedivis(GEN a, pari_long b) { return truedvmdis(a,b,NULL); }
INLINE GEN
truedivsi(pari_long a, GEN b) { return truedvmdsi(a,b,NULL); }

INLINE GEN
divii(GEN a, GEN b) { return dvmdii(a,b,NULL); }
INLINE GEN
remii(GEN a, GEN b) { return dvmdii(a,b,ONLY_REM); }

INLINE GEN
divss(pari_long x, pari_long y) { return stoi(x / y); }
INLINE GEN
modss(pari_long x, pari_long y) { return stoi(smodss(x, y)); }
INLINE GEN
remss(pari_long x, pari_long y) { return stoi(x % y); }
INLINE pari_long
smodss(pari_long x, pari_long y)
{
  pari_long r = x%y;
  return (r >= 0)? r: llabs(y) + r;
}

INLINE pari_long
sdivss_rem(pari_long x, pari_long y, pari_long *r)
{
  pari_long q;
  LOCAL_HIREMAINDER;
  if (!y) pari_err_INV("sdivss_rem",gen_0);
  hiremainder = 0; q = divll((ulong)llabs(x),(ulong)llabs(y));
  if (x < 0) { hiremainder = -((pari_long)hiremainder); q = -q; }
  if (y < 0) q = -q;
  *r = hiremainder; return q;
}
INLINE GEN
divss_rem(pari_long x, pari_long y, pari_long *r) { return stoi(sdivss_rem(x,y,r)); }
INLINE ulong
udivuu_rem(ulong x, ulong y, ulong *r)
{
  if (!y) pari_err_INV("udivuu_rem",gen_0);
  *r = x % y; return x / y;
}

INLINE ulong
udivui_rem(ulong x, GEN y, ulong *r)
{
  pari_long q, s = signe(y);
  LOCAL_HIREMAINDER;

  if (!s) pari_err_INV("udivui_rem",gen_0);
  if (!x || lgefint(y)>3) { *r = x; return 0; }
  hiremainder=0; q = (pari_long)divll(x, (ulong)y[2]);
  if (s < 0) q = -q;
  *r = hiremainder; return q;
}

/* assume d != 0 and |n| / d can be represented as an ulong.
 * Return |n|/d, set *r = |n| % d */
INLINE ulong
udiviu_rem(GEN n, ulong d, ulong *r)
{
  switch(lgefint(n))
  {
    case 2: *r = 0; return 0;
    case 3:
    {
      ulong nn = n[2];
      *r = nn % d; return nn / d;
    }
    default: /* 4 */
    {
      ulong n1, n0, q;
      LOCAL_HIREMAINDER;
      n0 = *int_W(n,0);
      n1 = *int_W(n,1);
      hiremainder = n1;
      q = divll(n0, d);
      *r = hiremainder; return q;
    }
  }
}

INLINE pari_long
sdivsi_rem(pari_long x, GEN y, pari_long *r)
{
  pari_long q, s = signe(y);
  LOCAL_HIREMAINDER;

  if (!s) pari_err_INV("sdivsi_rem",gen_0);
  if (!x || lgefint(y)>3 || ((pari_long)y[2]) < 0) { *r = x; return 0; }
  hiremainder=0; q = (pari_long)divll(llabs(x), (ulong)y[2]);
  if (x < 0) { hiremainder = -((pari_long)hiremainder); q = -q; }
  if (s < 0) q = -q;
  *r = hiremainder; return q;
}
INLINE GEN
divsi_rem(pari_long s, GEN y, pari_long *r) { return stoi(sdivsi_rem(s,y,r)); }

INLINE pari_long
sdivsi(pari_long x, GEN y)
{
  pari_long q, s = signe(y);

  if (!s) pari_err_INV("sdivsi",gen_0);
  if (!x || lgefint(y)>3 || ((pari_long)y[2]) < 0) return 0;
  q = llabs(x) / y[2];
  if (x < 0) q = -q;
  if (s < 0) q = -q;
  return q;
}

INLINE GEN
dvmdss(pari_long x, pari_long y, GEN *z)
{
  pari_long r;
  GEN q = divss_rem(x,y, &r);
  *z = stoi(r); return q;
}
INLINE pari_long
dvmdsBIL(pari_long n, pari_long *r) { *r = remsBIL(n); return divsBIL(n); }
INLINE ulong
dvmduBIL(ulong n, ulong *r) { *r = remsBIL(n); return divsBIL(n); }
INLINE GEN
dvmdsi(pari_long x, GEN y, GEN *z)
{
  pari_long r;
  GEN q = divsi_rem(x,y, &r);
  *z = stoi(r); return q;
}
INLINE GEN
dvmdis(GEN x, pari_long y, GEN *z)
{
  pari_long r;
  GEN q = divis_rem(x,y, &r);
  *z = stoi(r); return q;
}

INLINE pari_long
smodis(GEN x, pari_long y)
{
  pari_sp av = avma;
  pari_long r;
  (void)divis_rem(x,y, &r); avma = av; return (r >= 0) ? r: llabs(y) + r;
}
INLINE GEN
modis(GEN x, pari_long y) { return stoi(smodis(x,y)); }
INLINE GEN
modsi(pari_long x, GEN y) {
  pari_long r;
  (void)sdivsi_rem(x, y, &r);
  return (r >= 0)? stoi(r): addsi_sign(r, y, 1);
}

INLINE ulong
umodui(ulong x, GEN y)
{
  if (!signe(y)) pari_err_INV("umodui",gen_0);
  if (!x || lgefint(y) > 3) return x;
  return x % (ulong)y[2];
}

INLINE GEN
remsi(pari_long x, GEN y)
{ pari_long r; (void)sdivsi_rem(x,y, &r); return stoi(r); }
INLINE GEN
remis(GEN x, pari_long y)
{
  pari_sp av = avma;
  pari_long r;
  (void)divis_rem(x,y, &r); avma = av; return stoi(r);
}

INLINE GEN
rdivis(GEN x, pari_long y, pari_long prec)
{
  GEN z = cgetr(prec);
  pari_sp av = avma;
  affrr(divrs(itor(x,prec), y),z);
  avma = av; return z;
}
INLINE GEN
rdivsi(pari_long x, GEN y, pari_long prec)
{
  GEN z = cgetr(prec);
  pari_sp av = avma;
  affrr(divsr(x, itor(y,prec)), z);
  avma = av; return z;
}
INLINE GEN
rdivss(pari_long x, pari_long y, pari_long prec)
{
  GEN z = cgetr(prec);
  pari_sp av = avma;
  affrr(divrs(stor(x, prec), y), z);
  avma = av; return z;
}

INLINE void
rdiviiz(GEN x, GEN y, GEN z)
{
  pari_sp av = avma;
  pari_long prec = realprec(z);
  affir(x, z);
  if (!is_bigint(y)) {
    affrr(divrs(z, y[2]), z);
    if (signe(y) < 0) togglesign(z);
  }
  else
    affrr(divrr(z, itor(y,prec)), z);
  avma = av;
}
INLINE GEN
rdivii(GEN x, GEN y, pari_long prec)
{
  GEN z = cgetr(prec);
  pari_sp av = avma;
  affir(x, z);
  if (lg(y) == 3) {
    affrr(divru(z, y[2]), z);
    if (signe(y) < 0) togglesign(z);
  }
  else
    affrr(divrr(z, itor(y,prec)), z);
  avma = av; return z;
}
INLINE GEN
fractor(GEN x, pari_long prec) { return rdivii(gel(x,1), gel(x,2), prec); }

INLINE int
dvdii(GEN x, GEN y)
{
  pari_sp av=avma;
  GEN r = remii(x,y);
  avma = av; return r == gen_0;
}
INLINE int
dvdsi(pari_long x, GEN y)
{
  if (!signe(y)) return x == 0;
  if (lgefint(y) != 3) return 0;
  return x % y[2] == 0;
}
INLINE int
dvdui(ulong x, GEN y)
{
  if (!signe(y)) return x == 0;
  if (lgefint(y) != 3) return 0;
  return x % y[2] == 0;
}
INLINE int
dvdis(GEN x, pari_long y)
{ return y? smodis(x, y) == 0: signe(x) == 0; }
INLINE int
dvdiu(GEN x, ulong y)
{ return y? umodiu(x, y) == 0: signe(x) == 0; }

INLINE int
dvdisz(GEN x, pari_long y, GEN z)
{
  const pari_sp av = avma;
  pari_long r;
  GEN p1 = divis_rem(x,y, &r);
  avma = av; if (r) return 0;
  affii(p1,z); return 1;
}
INLINE int
dvdiuz(GEN x, ulong y, GEN z)
{
  const pari_sp av = avma;
  ulong r;
  GEN p1 = diviu_rem(x,y, &r);
  avma = av; if (r) return 0;
  affii(p1,z); return 1;
}
INLINE int
dvdiiz(GEN x, GEN y, GEN z)
{
  const pari_sp av=avma;
  GEN p2;
  const GEN p1=dvmdii(x,y,&p2);

  if (signe(p2)) { avma=av; return 0; }
  affii(p1,z); avma=av; return 1;
}

/*******************************************************************/
/*                                                                 */
/*                        MP (INT OR REAL)                         */
/*                                                                 */
/*******************************************************************/
INLINE GEN
mptrunc(GEN x) { return typ(x)==t_INT? icopy(x): truncr(x); }
INLINE GEN
mpfloor(GEN x) { return typ(x)==t_INT? icopy(x): floorr(x); }
INLINE GEN
mpceil(GEN x) { return typ(x)==t_INT? icopy(x): ceilr(x); }
INLINE GEN
mpround(GEN x) { return typ(x) == t_INT? icopy(x): roundr(x); }

INLINE pari_long
mpexpo(GEN x) { return typ(x) == t_INT? expi(x): expo(x); }

INLINE GEN
mpadd(GEN x, GEN y)
{
  if (typ(x)==t_INT)
    return (typ(y)==t_INT) ? addii(x,y) : addir(x,y);
  return (typ(y)==t_INT) ? addir(y,x) : addrr(x,y);
}
INLINE GEN
mpsub(GEN x, GEN y)
{
  if (typ(x)==t_INT)
    return (typ(y)==t_INT) ? subii(x,y) : subir(x,y);
  return (typ(y)==t_INT) ? subri(x,y) : subrr(x,y);
}
INLINE GEN
mpmul(GEN x, GEN y)
{
  if (typ(x)==t_INT)
    return (typ(y)==t_INT) ? mulii(x,y) : mulir(x,y);
  return (typ(y)==t_INT) ? mulir(y,x) : mulrr(x,y);
}
INLINE GEN
mpsqr(GEN x) { return (typ(x)==t_INT) ? sqri(x) : sqrr(x); }
INLINE GEN
mpdiv(GEN x, GEN y)
{
  if (typ(x)==t_INT)
    return (typ(y)==t_INT) ? divii(x,y) : divir(x,y);
  return (typ(y)==t_INT) ? divri(x,y) : divrr(x,y);
}

/*******************************************************************/
/*                                                                 */
/*                          Z/nZ, n ULONG                          */
/*                                                                 */
/*******************************************************************/
INLINE ulong
Fl_double(ulong a, ulong p)
{
  ulong res = a << 1;
  return (res >= p || res < a) ? res - p : res;
}
INLINE ulong
Fl_triple(ulong a, ulong p)
{
  ulong res = a << 1;
  if (res >= p || res < a) res -= p;
  res += a;
  return (res >= p || res < a)? res - p: res;
}
INLINE ulong
Fl_add(ulong a, ulong b, ulong p)
{
  ulong res = a + b;
  return (res >= p || res < a) ? res - p : res;
}
INLINE ulong
Fl_neg(ulong x, ulong p) { return x ? p - x: 0; }

INLINE ulong
Fl_sub(ulong a, ulong b, ulong p)
{
  ulong res = a - b;
  return (res > a) ? res + p: res;
}

/* centerlift(u mod p) */
INLINE pari_long
Fl_center(ulong u, ulong p, ulong ps2) { return (pari_long) (u > ps2)? u - p: u; }

INLINE ulong
Fl_mul(ulong a, ulong b, ulong p)
{
  register ulong x;
  LOCAL_HIREMAINDER;
  x = mulll(a,b);
  if (!hiremainder) return x % p;
  (void)divll(x,p); return hiremainder;
}
INLINE ulong
Fl_sqr(ulong a, ulong p)
{
  register ulong x;
  LOCAL_HIREMAINDER;
  x = mulll(a,a);
  if (!hiremainder) return x % p;
  (void)divll(x,p); return hiremainder;
}
INLINE ulong
Fl_div(ulong a, ulong b, ulong p) { return Fl_mul(a, Fl_inv(b, p), p); }

/*******************************************************************/
/*                                                                 */
/*        DEFINED FROM EXISTING ONE EXPLOITING COMMUTATIVITY       */
/*                                                                 */
/*******************************************************************/
INLINE GEN
addri(GEN x, GEN y) { return addir(y,x); }
INLINE GEN
addis(GEN x, pari_long s) { return addsi(s,x); }
INLINE GEN
addiu(GEN x, ulong s) { return addui(s,x); }
INLINE GEN
addrs(GEN x, pari_long s) { return addsr(s,x); }

INLINE GEN
subiu(GEN x, pari_long y) { GEN z = subui(y, x); togglesign(z); return z; }
INLINE GEN
subis(GEN x, pari_long y) { return addsi(-y,x); }
INLINE GEN
subrs(GEN x, pari_long y) { return addsr(-y,x); }

INLINE GEN
mulis(GEN x, pari_long s) { return mulsi(s,x); }
INLINE GEN
muliu(GEN x, ulong s) { return mului(s,x); }
INLINE GEN
mulru(GEN x, ulong s) { return mulur(s,x); }
INLINE GEN
mulri(GEN x, GEN s) { return mulir(s,x); }
INLINE GEN
mulrs(GEN x, pari_long s) { return mulsr(s,x); }

/*******************************************************************/
/*                                                                 */
/*                  VALUATION, EXPONENT, SHIFTS                    */
/*                                                                 */
/*******************************************************************/
INLINE pari_long
vali(GEN x)
{
  pari_long i;
  GEN xp;

  if (!signe(x)) return -1;
  xp=int_LSW(x);
  for (i=0; !*xp; i++) xp=int_nextW(xp);
  return vals(*xp) + i * BITS_IN_LONG;
}


/* assume x > 0 */
INLINE pari_long
expu(ulong x) { return (BITS_IN_LONG-1) - (pari_long)bfffo(x); }

INLINE pari_long
expi(GEN x)
{
  const pari_long lx=lgefint(x);
  return lx==2? -(pari_long)HIGHEXPOBIT: bit_accuracy(lx)-(pari_long)bfffo(*int_MSW(x))-1;
}

INLINE GEN
shiftr(GEN x, pari_long n)
{
  const pari_long e = evalexpo(expo(x)+n);
  const GEN y = rcopy(x);

  if (e & ~EXPOBITS) pari_err_OVERFLOW("expo()");
  y[1] = (y[1]&~EXPOBITS) | e; return y;
}
INLINE GEN
mpshift(GEN x, pari_long s) { return (typ(x)==t_INT)?shifti(x,s):shiftr(x,s); }

/* FIXME: adapt/use mpn_[lr]shift instead */
/* z2[imin..imax] := z1[imin..imax].f shifted left sh bits
 * (feeding f from the right). Assume sh > 0 */
INLINE void
shift_left(GEN z2, GEN z1, pari_long imin, pari_long imax, ulong f,  ulong sh)
{
  GEN sb = z1 + imin, se = z1 + imax, te = z2 + imax;
  ulong l, m = BITS_IN_LONG - sh, k = f >> m;
  while (se > sb) {
    l     = *se--;
    *te-- = (l << sh) | k;
    k     = l >> m;
  }
  *te = (*se << sh) | k;
}
/* z2[imin..imax] := f.z1[imin..imax-1] shifted right sh bits
 * (feeding f from the left). Assume sh > 0 */
INLINE void
shift_right(GEN z2, GEN z1, pari_long imin, pari_long imax, ulong f, ulong sh)
{
  GEN sb = z1 + imin, se = z1 + imax, tb = z2 + imin;
  ulong k, l = *sb++, m = BITS_IN_LONG - sh;
  *tb++ = (l >> sh) | (f << m);
  while (sb < se) {
    k     = l << m;
    l     = *sb++;
    *tb++ = (l >> sh) | k;
  }
}

/* Backward compatibility. Inefficient && unused */
extern ulong hiremainder;
INLINE ulong
shiftl(ulong x, ulong y)
{ hiremainder = x>>(BITS_IN_LONG-y); return (x<<y); }

INLINE ulong
shiftlr(ulong x, ulong y)
{ hiremainder = x<<(BITS_IN_LONG-y); return (x>>y); }

INLINE void
shiftr_inplace(GEN z, pari_long d)
{
  setexpo(z, expo(z)+d);
}

/*******************************************************************/
/*                                                                 */
/*                           ASSIGNMENT                            */
/*                                                                 */
/*******************************************************************/
INLINE void
affii(GEN x, GEN y)
{
  pari_long lx = lgefint(x);
  if (lg(y)<lx) pari_err_OVERFLOW("t_INT-->t_INT assignment");
  while (--lx) y[lx] = x[lx];
}
INLINE void
affsi(pari_long s, GEN x)
{
  if (!s) x[1] = evalsigne(0) | evallgefint(2);
  else
  {
    if (s > 0) { x[1] = evalsigne( 1) | evallgefint(3); x[2] =  s; }
    else       { x[1] = evalsigne(-1) | evallgefint(3); x[2] = -s; }
  }
}
INLINE void
affui(ulong u, GEN x)
{
  if (!u) x[1] = evalsigne(0) | evallgefint(2);
  else  { x[1] = evalsigne(1) | evallgefint(3); x[2] = u; }
}

INLINE void
affsr(pari_long x, GEN y)
{
  pari_long sh, i, ly = lg(y);

  if (!x)
  {
    y[1] = evalexpo(-prec2nbits(ly));
    return;
  }
  if (x < 0) {
    x = -x; sh = bfffo(x);
    y[1] = evalsigne(-1) | _evalexpo((BITS_IN_LONG-1)-sh);
  }
  else
  {
    sh = bfffo(x);
    y[1] = evalsigne(1) | _evalexpo((BITS_IN_LONG-1)-sh);
  }
  y[2] = x<<sh; for (i=3; i<ly; i++) y[i]=0;
}

INLINE void
affur(ulong x, GEN y)
{
  pari_long sh, i, ly = lg(y);

  if (!x)
  {
    y[1] = evalexpo(-prec2nbits(ly));
    return;
  }
  sh = bfffo(x);
  y[1] = evalsigne(1) | _evalexpo((BITS_IN_LONG-1)-sh);
  y[2] = x<<sh; for (i=3; i<ly; i++) y[i] = 0;
}

INLINE void
affiz(GEN x, GEN y) { if (typ(y)==t_INT) affii(x,y); else affir(x,y); }
INLINE void
affsz(pari_long x, GEN y) { if (typ(y)==t_INT) affsi(x,y); else affsr(x,y); }
INLINE void
mpaff(GEN x, GEN y) { if (typ(x)==t_INT) affiz(x, y); else affrr(x,y); }

/*******************************************************************/
/*                                                                 */
/*                    OPERATION + ASSIGNMENT                       */
/*                                                                 */
/*******************************************************************/

INLINE void addiiz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; affii(addii(x,y),z); avma = av; }
INLINE void addirz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; affrr(addir(x,y),z); avma = av; }
INLINE void addriz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; affrr(addri(x,y),z); avma = av; }
INLINE void addrrz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; affrr(addrr(x,y),z); avma = av; }
INLINE void addsiz(pari_long s, GEN y, GEN z)
{ pari_sp av = avma; affii(addsi(s,y),z); avma = av; }
INLINE void addsrz(pari_long s, GEN y, GEN z)
{ pari_sp av = avma; affrr(addsr(s,y),z); avma = av; }
INLINE void addssz(pari_long s, pari_long y, GEN z)
{ pari_sp av = avma; affii(addss(s,y),z); avma = av; }

INLINE void diviiz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; affii(divii(x,y),z); avma = av; }
INLINE void divirz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; mpaff(divir(x,y),z); avma = av; }
INLINE void divisz(GEN x, pari_long y, GEN z)
{ pari_sp av = avma; affii(divis(x,y),z); avma = av; }
INLINE void divriz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; affrr(divri(x,y),z); avma = av; }
INLINE void divrrz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; affrr(divrr(x,y),z); avma = av; }
INLINE void divrsz(GEN y, pari_long s, GEN z)
{ pari_sp av = avma; affrr(divrs(y,s),z); avma = av; }
INLINE void divsiz(pari_long x, GEN y, GEN z)
{ pari_long junk; affsi(sdivsi_rem(x,y,&junk), z); }
INLINE void divsrz(pari_long s, GEN y, GEN z)
{ pari_sp av = avma; mpaff(divsr(s,y),z); avma = av; }
INLINE void divssz(pari_long x, pari_long y, GEN z)
{ affsi(x/y, z); }

INLINE void modisz(GEN y, pari_long s, GEN z)
{ pari_sp av = avma; affii(modis(y,s),z); avma = av; }
INLINE void modsiz(pari_long s, GEN y, GEN z)
{ pari_sp av = avma; affii(modsi(s,y),z); avma = av; }
INLINE void modssz(pari_long s, pari_long y, GEN z)
{ pari_sp av = avma; affii(modss(s,y),z); avma = av; }

INLINE void mpaddz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; mpaff(mpadd(x,y),z); avma = av; }
INLINE void mpsubz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; mpaff(mpsub(x,y),z); avma = av; }
INLINE void mpmulz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; mpaff(mpmul(x,y),z); avma = av; }

INLINE void muliiz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; affii(mulii(x,y),z); avma = av; }
INLINE void mulirz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; mpaff(mulir(x,y),z); avma = av; }
INLINE void mulriz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; mpaff(mulri(x,y),z); avma = av; }
INLINE void mulrrz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; affrr(mulrr(x,y),z); avma = av; }
INLINE void mulsiz(pari_long s, GEN y, GEN z)
{ pari_sp av = avma; affii(mulsi(s,y),z); avma = av; }
INLINE void mulsrz(pari_long s, GEN y, GEN z)
{ pari_sp av = avma; mpaff(mulsr(s,y),z); avma = av; }
INLINE void mulssz(pari_long s, pari_long y, GEN z)
{ pari_sp av = avma; affii(mulss(s,y),z); avma = av; }

INLINE void remiiz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; affii(remii(x,y),z); avma = av; }
INLINE void remisz(GEN y, pari_long s, GEN z)
{ pari_sp av = avma; affii(remis(y,s),z); avma = av; }
INLINE void remsiz(pari_long s, GEN y, GEN z)
{ pari_sp av = avma; affii(remsi(s,y),z); avma = av; }
INLINE void remssz(pari_long s, pari_long y, GEN z)
{ pari_sp av = avma; affii(remss(s,y),z); avma = av; }

INLINE void subiiz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; affii(subii(x,y),z); avma = av; }
INLINE void subirz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; affrr(subir(x,y),z); avma = av; }
INLINE void subisz(GEN y, pari_long s, GEN z)
{ pari_sp av = avma; affii(addsi(-s,y),z); avma = av; }
INLINE void subriz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; affrr(subri(x,y),z); avma = av; }
INLINE void subrrz(GEN x, GEN y, GEN z)
{ pari_sp av = avma; affrr(subrr(x,y),z); avma = av; }
INLINE void subrsz(GEN y, pari_long s, GEN z)
{ pari_sp av = avma; affrr(addsr(-s,y),z); avma = av; }
INLINE void subsiz(pari_long s, GEN y, GEN z)
{ pari_sp av = avma; affii(subsi(s,y),z); avma = av; }
INLINE void subsrz(pari_long s, GEN y, GEN z)
{ pari_sp av = avma; affrr(subsr(s,y),z); avma = av; }
INLINE void subssz(pari_long x, pari_long y, GEN z) { addssz(x,-y,z); }

INLINE void
dvmdssz(pari_long x, pari_long y, GEN z, GEN t) {
  pari_sp av = avma;
  pari_long r;
  affii(divss_rem(x,y, &r), z); avma = av; affsi(r,t);
}
INLINE void
dvmdsiz(pari_long x, GEN y, GEN z, GEN t) {
  pari_sp av = avma;
  pari_long r;
  affii(divsi_rem(x,y, &r), z); avma = av; affsi(r,t);
}
INLINE void
dvmdisz(GEN x, pari_long y, GEN z, GEN t) {
  pari_sp av = avma;
  pari_long r;
  affii(divis_rem(x,y, &r),z); avma = av; affsi(r,t);
}
INLINE void
dvmdiiz(GEN x, GEN y, GEN z, GEN t) {
  pari_sp av = avma;
  GEN r;
  affii(dvmdii(x,y,&r),z); affii(r,t); avma=av;
}
