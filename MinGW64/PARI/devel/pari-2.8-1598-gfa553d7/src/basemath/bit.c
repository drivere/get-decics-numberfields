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
/*********************************************************************/
/**                                                                 **/
/**                       BINARY DECOMPOSITION                      **/
/**                                                                 **/
/*********************************************************************/

INLINE GEN
inegate(GEN z) { return subsi(-1,z); }

GEN
binary_zv(GEN x)
{
  GEN xp, z;
  long i, k, lx;
  if (!signe(x)) return cgetg(1,t_VECSMALL);
  xp = int_LSW(x);
  lx = lgefint(x);
  k = expi(x)+2;
  z = cgetg(k, t_VECSMALL);
  k--;
  for(i = 2; i < lx; i++)
  {
    ulong u = *xp;
    long j;
    for (j=0; j<BITS_IN_LONG && k; j++) z[k--] = (u>>j)&1UL;
    if (!k) break;
    xp = int_nextW(xp);
  }
  return z;
}
static GEN
F2v_to_ZV_inplace(GEN v)
{
  long i, l = lg(v);
  v[0] = evaltyp(t_VEC) | _evallg(l);
  for (i = 1; i < l; i++) gel(v,i) = v[i]? gen_1: gen_0;
  return v;
}
/* "vector" of l bits (possibly no code word) to non-negative t_INT */
GEN
bits_to_int(GEN x, long l)
{
  long i, j, lz;
  GEN z, zp;

  if (!l) return gen_0;
  lz = nbits2lg(l);
  z = cgetg(lz, t_INT);
  z[1] = evalsigne(1) | evallgefint(lz);
  zp = int_LSW(z); *zp = 0;
  for(i=l,j=0; i; i--,j++)
  {
    if (j==BITS_IN_LONG) { j=0; zp = int_nextW(zp); *zp = 0; }
    if (x[i]) *zp |= 1UL<<j;
  }
  return int_normalize(z, 0);
}
/* "vector" of l < BITS_IN_LONG bits (possibly no code word) to non-negative
 * ulong */
ulong
bits_to_u(GEN v, long l)
{
  ulong u = 0;
  long i;
  for (i = 1; i <= l; i++) u = (u <<1) | v[i];
  return u;
}

GEN
binaire(GEN x)
{
  ulong m,u;
  long i,lx,ex,ly,tx=typ(x);
  GEN y,p1,p2;

  switch(tx)
  {
    case t_INT:
      return F2v_to_ZV_inplace( binary_zv(x) );
    case t_REAL:
      ex = expo(x);
      if (!signe(x)) return const_vec(maxss(-ex,0), gen_0);

      lx=lg(x); y=cgetg(3,t_VEC);
      if (ex > bit_prec(x)) pari_err_PREC("binary");
      p1 = cgetg(maxss(ex,0)+2,t_VEC);
      p2 = cgetg(bit_prec(x)-ex,t_VEC);
      gel(y,1) = p1;
      gel(y,2) = p2;
      ly = -ex; ex++; m = HIGHBIT;
      if (ex<=0)
      {
        gel(p1,1) = gen_0; for (i=1; i <= -ex; i++) gel(p2,i) = gen_0;
        i=2;
      }
      else
      {
        ly=1;
        for (i=2; i<lx && ly<=ex; i++)
        {
          m=HIGHBIT; u=x[i];
          do
            { gel(p1,ly) = (m & u) ? gen_1 : gen_0; ly++; }
          while ((m>>=1) && ly<=ex);
        }
        ly=1;
        if (m) i--; else m=HIGHBIT;
      }
      for (; i<lx; i++)
      {
        u=x[i];
        do { gel(p2,ly) = m & u ? gen_1 : gen_0; ly++; } while (m>>=1);
        m=HIGHBIT;
      }
      break;

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = binaire(gel(x,i));
      break;
    default: pari_err_TYPE("binary",x);
      return NULL; /* not reached */
  }
  return y;
}

/* assume k < BITS_IN_LONG */
GEN
binary_2k_zv(GEN x, long k)
{
  long iv, j, n, nmodk, nk;
  GEN v, vk;
  if (k == 1) return binary_zv(x);
  if (!signe(x)) return cgetg(1,t_VECSMALL);
  v = binary_zv(x);
  n = lg(v)-1;
  nk = n / k; nmodk = n % k;
  if (nmodk) nk++;
  vk = cgetg(nk+1, t_VECSMALL);
  iv = n - k;
  if (!nmodk) nmodk = k;
  for (j = nk; j >= 2; j--,iv-=k) vk[j] = bits_to_u(v+iv, k);
  vk[1] = bits_to_u(v,nmodk);
  return vk;
}
GEN
binary_2k(GEN x, long k)
{
  long iv, j, n, nmodk, nk;
  GEN v, vk;
  if (!signe(x)) return cgetg(1,t_VEC);
  v = binary_zv(x);
  n = lg(v)-1;
  nk = n / k; nmodk = n % k;
  if (nmodk) nk++;
  vk = cgetg(nk+1, t_VEC);
  iv = n - k;
  if (!nmodk) nmodk = k;
  for (j = nk; j >= 2; j--,iv-=k) gel(vk,j) = bits_to_int(v+iv, k);
  gel(vk,1) = bits_to_int(v, nmodk);
  return vk;
}

/* return 1 if bit n of x is set, 0 otherwise */
long
bittest(GEN x, long n)
{
  if (typ(x) != t_INT) pari_err_TYPE("bittest",x);
  if (!signe(x) || n < 0) return 0;
  if (signe(x) < 0)
  {
    pari_sp ltop=avma;
    long b = !int_bit(inegate(x),n);
    avma=ltop;
    return b;
  }
  return int_bit(x, n);
}

GEN
gbittest(GEN x, long n) { return map_proto_lGL(bittest,x,n); }

/***********************************************************************/
/**                                                                   **/
/**                          BITMAP OPS                               **/
/** x & y (and), x | y (or), x ^ y (xor), ~x (neg), x & ~y (negimply) **/
/**                                                                   **/
/***********************************************************************/
/* Truncate a non-negative integer to a number of bits.  */
static GEN
ibittrunc(GEN x, long bits)
{
  long lowbits, known_zero_words, xl = lgefint(x) - 2;
  long len_out = nbits2nlong(bits);

  if (xl < len_out)
    return x;
      /* Check whether mask is trivial */
  lowbits = bits & (BITS_IN_LONG-1);
  if (!lowbits) {
    if (xl == len_out)
      return x;
  } else if (len_out <= xl) {
    GEN xi = int_W(x, len_out-1);
    /* Non-trival mask is given by a formula, if x is not
       normalized, this works even in the exceptional case */
    *xi &= (1L << lowbits) - 1;
    if (*xi && xl == len_out) return x;
  }
  /* Normalize */
  known_zero_words = xl - len_out;
  if (known_zero_words < 0) known_zero_words = 0;
  return int_normalize(x, known_zero_words);
}

GEN
gbitneg(GEN x, long bits)
{
  const ulong uzero = 0;
  long lowbits, xl, len_out, i;

  if (typ(x) != t_INT) pari_err_TYPE("bitwise negation",x);
  if (bits < -1)
    pari_err_DOMAIN("bitwise negation","exponent","<",gen_m1,stoi(bits));
  if (bits == -1) return inegate(x);
  if (bits == 0) return gen_0;
  if (signe(x) < 0) { /* Consider as if mod big power of 2 */
    pari_sp ltop = avma;
    return gerepileuptoint(ltop, ibittrunc(inegate(x), bits));
  }
  xl = lgefint(x);
  len_out = nbits2lg(bits);
  lowbits = bits & (BITS_IN_LONG-1);
  if (len_out > xl) /* Need to grow */
  {
    GEN out, outp, xp = int_MSW(x);
    out = cgetipos(len_out);
    outp = int_MSW(out);
    if (!lowbits)
      *outp = ~uzero;
    else
      *outp = (1L << lowbits) - 1;
    for (i = 3; i < len_out - xl + 2; i++)
    {
      outp = int_precW(outp); *outp = ~uzero;
    }
    for (     ; i < len_out; i++)
    {
      outp = int_precW(outp); *outp = ~*xp;
      xp   = int_precW(xp);
    }
    return out;
  }
  x = icopy(x);
  for (i = 2; i < xl; i++) x[i] = ~x[i];
  return ibittrunc(int_normalize(x,0), bits);
}

/* bitwise 'and' of two positive integers (any integers, but we ignore sign).
 * Inputs are not necessary normalized. */
GEN
ibitand(GEN x, GEN y)
{
  long lx, ly, lout;
  long *xp, *yp, *outp;
  GEN out;
  long i;

  if (!signe(x) || !signe(y)) return gen_0;
  lx=lgefint(x); ly=lgefint(y);
  lout = minss(lx,ly); /* > 2 */
  xp = int_LSW(x);
  yp = int_LSW(y);
  out = cgetipos(lout);
  outp = int_LSW(out);
  for (i=2; i<lout; i++)
  {
    *outp = (*xp) & (*yp);
    outp  = int_nextW(outp);
    xp    = int_nextW(xp);
    yp    = int_nextW(yp);
  }
  if ( !*int_MSW(out) ) out = int_normalize(out, 1);
  return out;
}

/* bitwise 'or' of absolute values of two integers */
GEN
ibitor(GEN x, GEN y)
{
  long lx, ly;
  long *xp, *yp, *outp;
  GEN  out;
  long i;
  if (!signe(x)) return absi(y);
  if (!signe(y)) return absi(x);

  lx = lgefint(x); xp = int_LSW(x);
  ly = lgefint(y); yp = int_LSW(y);
  if (lx < ly) swapspec(xp,yp,lx,ly);
  /* lx > 2 */
  out = cgetipos(lx);
  outp = int_LSW(out);
  for (i=2;i<ly;i++)
  {
    *outp = (*xp) | (*yp);
    outp  = int_nextW(outp);
    xp    = int_nextW(xp);
    yp    = int_nextW(yp);
  }
  for (   ;i<lx;i++)
  {
    *outp = *xp;
    outp  = int_nextW(outp);
    xp    = int_nextW(xp);
  }
  /* If input is normalized, this is not needed */
  if ( !*int_MSW(out) ) out = int_normalize(out, 1);
  return out;
}

/* bitwise 'xor' of absolute values of two integers */
GEN
ibitxor(GEN x, GEN y)
{
  long lx, ly;
  long *xp, *yp, *outp;
  GEN  out;
  long i;
  if (!signe(x)) return absi(y);
  if (!signe(y)) return absi(x);

  lx = lgefint(x); xp = int_LSW(x);
  ly = lgefint(y); yp = int_LSW(y);
  if (lx < ly) swapspec(xp,yp,lx,ly);
  /* lx > 2 */
  out = cgetipos(lx);
  outp = int_LSW(out);
  for (i=2;i<ly;i++)
  {
    *outp = (*xp) ^ (*yp);
    outp  = int_nextW(outp);
    xp    = int_nextW(xp);
    yp    = int_nextW(yp);
  }
  for (   ;i<lx;i++)
  {
    *outp = *xp;
    outp  = int_nextW(outp);
    xp    = int_nextW(xp);
  }
  if ( !*int_MSW(out) ) out = int_normalize(out, 1);
  return out;
}

/* bitwise 'negimply' of absolute values of two integers */
/* "negimply(x,y)" is ~(x => y) == ~(~x | y) == x & ~y   */
GEN
ibitnegimply(GEN x, GEN y)
{
  long lx, ly, lin;
  long *xp, *yp, *outp;
  GEN out;
  long i;
  if (!signe(x)) return gen_0;
  if (!signe(y)) return absi(x);

  lx = lgefint(x); xp = int_LSW(x);
  ly = lgefint(y); yp = int_LSW(y);
  lin = minss(lx,ly);
  out = cgetipos(lx);
  outp = int_LSW(out);
  for (i=2; i<lin; i++)
  {
    *outp = (*xp) & ~(*yp);
    outp  = int_nextW(outp);
    xp    = int_nextW(xp);
    yp    = int_nextW(yp);
  }
  for (   ;i<lx;i++)
  {
    *outp = *xp;
    outp  = int_nextW(outp);
    xp    = int_nextW(xp);
  }
  if ( !*int_MSW(out) ) out = int_normalize(out, 1);
  return out;
}

static int
signs(GEN x, GEN y) { return (((signe(x) >= 0) << 1) | (signe(y) >= 0)); }
static void
checkint2(const char *f,GEN x, GEN y)
{ if (typ(x)!=t_INT || typ(y)!=t_INT) pari_err_TYPE2(f,x,y); }

GEN
gbitor(GEN x, GEN y)
{
  pari_sp ltop = avma;
  GEN z;

  checkint2("bitwise or",x,y);
  switch (signs(x, y))
  {
    case 3: /*1,1*/
      return ibitor(x,y);
    case 2: /*1,-1*/
      z = ibitnegimply(inegate(y),x);
      break;
    case 1: /*-1,1*/
      z = ibitnegimply(inegate(x),y);
      break;
    default: /*-1,-1*/
      z = ibitand(inegate(x),inegate(y));
      break;
  }
  return gerepileuptoint(ltop, inegate(z));
}

GEN
gbitand(GEN x, GEN y)
{
  pari_sp ltop = avma;
  GEN z;

  checkint2("bitwise and",x,y);
  switch (signs(x, y))
  {
    case 3: /*1,1*/
      return ibitand(x,y);
    case 2: /*1,-1*/
      z = ibitnegimply(x,inegate(y));
      break;
    case 1: /*-1,1*/
      z = ibitnegimply(y,inegate(x));
      break;
    default: /*-1,-1*/
      z = inegate(ibitor(inegate(x),inegate(y)));
      break;
  }
  return gerepileuptoint(ltop, z);
}

GEN
gbitxor(GEN x, GEN y)
{
  pari_sp ltop = avma;
  GEN z;

  checkint2("bitwise xor",x,y);
  switch (signs(x, y))
  {
    case 3: /*1,1*/
      return ibitxor(x,y);
    case 2: /*1,-1*/
      z = inegate(ibitxor(x,inegate(y)));
      break;
    case 1: /*-1,1*/
      z = inegate(ibitxor(inegate(x),y));
      break;
    default: /*-1,-1*/
      z = ibitxor(inegate(x),inegate(y));
      break;
  }
  return gerepileuptoint(ltop,z);
}

/* x & ~y */
GEN
gbitnegimply(GEN x, GEN y)
{
  pari_sp ltop = avma;
  GEN z;

  checkint2("bitwise negated imply",x,y);
  switch (signs(x, y))
  {
    case 3: /*1,1*/
      return ibitnegimply(x,y);
    case 2: /*1,-1*/
      z = ibitand(x,inegate(y));
      break;
    case 1: /*-1,1*/
      z = inegate(ibitor(y,inegate(x)));
      break;
    default: /*-1,-1*/
      z = ibitnegimply(inegate(y),inegate(x));
      break;
  }
  return gerepileuptoint(ltop,z);
}

INLINE long
hamming_word(ulong w)
{
#if 0
  return __builtin_popcountl(w);
#endif
  static long byte_weight[] = {
    0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,
    1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
    1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
    2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
    1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
    2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
    2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
    3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,4,5,5,6,5,6,6,7,5,6,6,7,6,7,7,8
  };
  long sum = 0;
  while (w) { sum += byte_weight[w & 255]; w >>= 8; }
  return sum;
}

/* number of non-zero entries among x[a], ..., x[b] */
static long
hamming_slice(GEN x, long a, long b)
{
  long i, nb = 0;
  for (i = a; i <= b; i++)
    if (!gequal0(gel(x,i))) nb++;
  return nb;
}
static long
hamming_mat(GEN x)
{
  long i, lx = lg(x), nb = 0;
  for (i = 1; i < lx; i++) nb += hammingweight(gel(x,i));
  return nb;
}
static long
hamming_vecsmall(GEN x)
{
  long i, lx = lg(x), nb = 0;
  for (i = 1; i < lx; i++)
    if (x[i]) nb++;
  return nb;
}
static long
hamming_int(GEN n)
{
  long lx = lgefint(n), i, sum;
  if (lx == 2) return 0;
  sum = hamming_word(n[2]);
  for (i = 3; i < lx; i++) sum += hamming_word(n[i]);
  return sum;
}

long
hammingweight(GEN n)
{
  switch(typ(n))
  {
    case t_INT: return hamming_int(n);
    case t_VEC:
    case t_COL: return hamming_slice(n, 1, lg(n)-1);
    case t_POL: return hamming_slice(n, 2, lg(n)-1);
    case t_VECSMALL: return hamming_vecsmall(n);
    case t_MAT: return hamming_mat(n);
  }
  pari_err_TYPE("hammingweight", n);
  return 0;/*notreached*/
}
