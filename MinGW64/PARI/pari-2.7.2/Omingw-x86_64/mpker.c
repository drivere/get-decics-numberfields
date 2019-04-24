#line 2 "../src/kernel/none/mp.c"
/* Copyright (C) 2000-2003 The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/***********************************************************************/
/**                                                                   **/
/**                       MULTIPRECISION KERNEL                       **/
/**                                                                   **/
/***********************************************************************/
#include "pari.h"
#include "paripriv.h"
#include "../src/kernel/none/tune-gen.h"

void pari_kernel_init(void) { }
void pari_kernel_close(void) { }

/* NOTE: arguments of "spec" routines (muliispec, addiispec, etc.) aren't
 * GENs but pairs (pari_long *a, pari_long na) representing a list of digits (in basis
 * BITS_IN_LONG) : a[0], ..., a[na-1]. [ In ordre to facilitate splitting: no
 * need to reintroduce codewords ] */

#define LIMBS(x)  ((x)+2)
#define NLIMBS(x) (lgefint(x)-2)

/* Normalize a non-negative integer */
GEN
int_normalize(GEN x, pari_long known_zero_words)
{
  pari_long i, lx = lgefint(x);
  GEN x0;
  if (lx == 2) { x[1] = evalsigne(0) | evallgefint(2); return x; }
  if (!known_zero_words && x[2]) return x;
  for (i = 2+known_zero_words; i < lx; i++)
    if (x[i]) break;
  x0 = x; i -= 2; x += i;
  if (x0 == (GEN)avma) avma = (pari_sp)x;
  else stackdummy((pari_sp)(x0+i), (pari_sp)x0);
  lx -= i;
  x[0] = evaltyp(t_INT) | evallg(lx);
  if (lx == 2) x[1] = evalsigne(0) | evallgefint(lx);
  else         x[1] = evalsigne(1) | evallgefint(lx);
  return x;
}

/***********************************************************************/
/**                                                                   **/
/**                      ADDITION / SUBTRACTION                       **/
/**                                                                   **/
/***********************************************************************/

GEN
setloop(GEN a)
{
  pari_sp av = avma;
  (void)cgetg(lgefint(a) + 3, t_VECSMALL);
  return icopy_avma(a, av); /* two cells of extra space before a */
}

/* we had a = setloop(?), then some incloops. Reset a to b */
GEN
resetloop(GEN a, GEN b) {
  pari_long lb = lgefint(b);
  a += lgefint(a) - lb;
  a[0] = evaltyp(t_INT) | evallg(lb);
  affii(b, a); return a;
}

/* assume a > 0, initialized by setloop. Do a++ */
static GEN
incpos(GEN a)
{
  pari_long i, l = lgefint(a);
  for (i=l-1; i>1; i--)
    if (++a[i]) return a;
  l++; a--; /* use extra cell */
  a[0]=evaltyp(t_INT) | _evallg(l);
  a[1]=evalsigne(1) | evallgefint(l);
  a[2]=1; return a;
}

/* assume a < 0, initialized by setloop. Do a++ */
static GEN
incneg(GEN a)
{
  pari_long i, l = lgefint(a)-1;
  if (a[l]--)
  {
    if (l == 2 && !a[2])
    {
      a++; /* save one cell */
      a[0] = evaltyp(t_INT) | _evallg(2);
      a[1] = evalsigne(0) | evallgefint(2);
    }
    return a;
  }
  for (i = l-1;; i--) /* finishes since a[2] != 0 */
    if (a[i]--) break;
  if (!a[2])
  {
    a++; /* save one cell */
    a[0] = evaltyp(t_INT) | _evallg(l);
    a[1] = evalsigne(-1) | evallgefint(l);
  }
  return a;
}

/* assume a initialized by setloop. Do a++ */
GEN
incloop(GEN a)
{
  switch(signe(a))
  {
    case 0: a--; /* use extra cell */
      a[0]=evaltyp(t_INT) | _evallg(3);
      a[1]=evalsigne(1) | evallgefint(3);
      a[2]=1; return a;
    case -1: return incneg(a);
    default: return incpos(a);
  }
}

INLINE GEN
adduispec(ulong s, GEN x, pari_long nx)
{
  GEN xd, zd = (GEN)avma;
  pari_long lz;

  if (nx == 1) return adduu(s, (ulong)x[0]);
  lz = nx+3; (void)new_chunk(lz);
  xd = x + nx;
  *--zd = (ulong)*--xd + s;
  if ((ulong)*zd < s)
    for(;;)
    {
      if (xd == x) { *--zd = 1; break; } /* enlarge z */
      *--zd = ((ulong)*--xd) + 1;
      if (*zd) { lz--; break; }
    }
  else lz--;
  while (xd > x) *--zd = *--xd;
  *--zd = evalsigne(1) | evallgefint(lz);
  *--zd = evaltyp(t_INT) | evallg(lz);
  avma=(pari_sp)zd; return zd;
}

GEN
adduispec_offset(ulong s, GEN x, pari_long offset, pari_long nx)
{
  GEN xd = x+lgefint(x)-nx-offset;
  while (nx && *xd==0) {xd++; nx--;}
  if (!nx) return utoi(s);
  return adduispec(s,xd,nx);
}

static GEN
addiispec(GEN x, GEN y, pari_long nx, pari_long ny)
{
  GEN xd, yd, zd;
  pari_long lz, i = -2;
  LOCAL_OVERFLOW;

  if (nx < ny) swapspec(x,y, nx,ny);
  if (ny == 1) return adduispec(*y,x,nx);
  zd = (GEN)avma;
  lz = nx+3; (void)new_chunk(lz);
  xd = x + nx;
  yd = y + ny;
  zd[-1] = addll(xd[-1], yd[-1]);
#ifdef addllx8
  for (  ; i-8 > -ny; i-=8)
    addllx8(xd+i, yd+i, zd+i, overflow);
#endif
  for (  ; i >= -ny; i--) zd[i] = addllx(xd[i], yd[i]);
  if (overflow)
    for(;;)
    {
      if (i < -nx) { zd[i] = 1; i--; break; } /* enlarge z */
      zd[i] = (ulong)xd[i] + 1;
      if (zd[i]) { i--; lz--; break; }
      i--;
    }
  else lz--;
  for (; i >= -nx; i--) zd[i] = xd[i];
  zd += i+1;
  *--zd = evalsigne(1) | evallgefint(lz);
  *--zd = evaltyp(t_INT) | evallg(lz);
  avma=(pari_sp)zd; return zd;
}

/* assume x >= s */
INLINE GEN
subiuspec(GEN x, ulong s, pari_long nx)
{
  GEN xd, zd = (GEN)avma;
  pari_long lz;
  LOCAL_OVERFLOW;

  if (nx == 1) return utoi(x[0] - s);

  lz = nx+2; (void)new_chunk(lz);
  xd = x + nx;
  *--zd = subll(*--xd, s);
  if (overflow)
    for(;;)
    {
      *--zd = ((ulong)*--xd) - 1;
      if (*xd) break;
    }
  if (xd == x)
    while (*zd == 0) { zd++; lz--; } /* shorten z */
  else
    do  *--zd = *--xd; while (xd > x);
  *--zd = evalsigne(1) | evallgefint(lz);
  *--zd = evaltyp(t_INT) | evallg(lz);
  avma=(pari_sp)zd; return zd;
}

/* assume x > y */
static GEN
subiispec(GEN x, GEN y, pari_long nx, pari_long ny)
{
  GEN xd,yd,zd;
  pari_long lz, i = -2;
  LOCAL_OVERFLOW;

  if (ny==1) return subiuspec(x,*y,nx);
  zd = (GEN)avma;
  lz = nx+2; (void)new_chunk(lz);
  xd = x + nx;
  yd = y + ny;
  zd[-1] = subll(xd[-1], yd[-1]);
#ifdef subllx8
  for (  ; i-8 > -ny; i-=8)
    subllx8(xd+i, yd+i, zd+i, overflow);
#endif
  for (  ; i >= -ny; i--) zd[i] = subllx(xd[i], yd[i]);
  if (overflow)
    for(;;)
    {
      zd[i] = ((ulong)xd[i]) - 1;
      if (xd[i--]) break;
    }
  if (i>=-nx)
    for (; i >= -nx; i--) zd[i] = xd[i];
  else
    while (zd[i+1] == 0) { i++; lz--; } /* shorten z */
  zd += i+1;
  *--zd = evalsigne(1) | evallgefint(lz);
  *--zd = evaltyp(t_INT) | evallg(lz);
  avma=(pari_sp)zd; return zd;
}

static void
roundr_up_ip(GEN x, pari_long l)
{
  pari_long i = l;
  for(;;)
  {
    if (++((ulong*)x)[--i]) break;
    if (i == 2) { x[2] = (pari_long)HIGHBIT; shiftr_inplace(x, 1); break; }
  }
}

void
affir(GEN x, GEN y)
{
  const pari_long s = signe(x), ly = lg(y);
  pari_long lx, sh, i;

  if (!s)
  {
    y[1] = evalexpo(-bit_accuracy(ly));
    return;
  }

  lx = lgefint(x); sh = bfffo(x[2]);
  y[1] = evalsigne(s) | evalexpo(bit_accuracy(lx)-sh-1);
  if (sh) {
    if (lx <= ly)
    {
      for (i=lx; i<ly; i++) y[i]=0;
      shift_left(y,x,2,lx-1, 0,sh);
      return;
    }
    shift_left(y,x,2,ly-1, x[ly],sh);
    /* lx > ly: round properly */
    if ((x[ly]<<sh) & HIGHBIT) roundr_up_ip(y, ly);
  }
  else {
    if (lx <= ly)
    {
      for (i=2; i<lx; i++) y[i]=x[i];
      for (   ; i<ly; i++) y[i]=0;
      return;
    }
    for (i=2; i<ly; i++) y[i]=x[i];
    /* lx > ly: round properly */
    if (x[ly] & HIGHBIT) roundr_up_ip(y, ly);
  }
}

INLINE GEN
shiftispec(GEN x, pari_long nx, pari_long n)
{
  pari_long ny, i, m;
  GEN y, yd;
  if (!n)  return icopyspec(x, nx);

  if (n > 0)
  {
    GEN z = (GEN)avma;
    pari_long d = dvmdsBIL(n, &m);

    ny = nx+d; y = new_chunk(ny + 2); yd = y + 2;
    for ( ; d; d--) *--z = 0;
    if (!m) for (i=0; i<nx; i++) yd[i]=x[i];
    else
    {
      register const ulong sh = BITS_IN_LONG - m;
      shift_left(yd,x, 0,nx-1, 0,m);
      i = ((ulong)x[0]) >> sh;
      /* Extend y on the left? */
      if (i) { ny++; y = new_chunk(1); y[2] = i; }
    }
  }
  else
  {
    ny = nx - dvmdsBIL(-n, &m);
    if (ny<1) return gen_0;
    y = new_chunk(ny + 2); yd = y + 2;
    if (m) {
      shift_right(yd,x, 0,ny, 0,m);
      if (yd[0] == 0)
      {
        if (ny==1) { avma = (pari_sp)(y+3); return gen_0; }
        ny--; avma = (pari_sp)(++y);
      }
    } else {
      for (i=0; i<ny; i++) yd[i]=x[i];
    }
  }
  y[1] = evalsigne(1)|evallgefint(ny + 2);
  y[0] = evaltyp(t_INT)|evallg(ny + 2); return y;
}

GEN
mantissa2nr(GEN x, pari_long n)
{ /*This is a kludge since x is not an integer*/
  pari_long s = signe(x);
  GEN y;

  if(s == 0) return gen_0;
  y = shiftispec(x + 2, lg(x) - 2, n);
  if (signe(y)) setsigne(y, s);
  return y;
}

GEN
truncr(GEN x)
{
  pari_long d,e,i,s,m;
  GEN y;

  if ((s=signe(x)) == 0 || (e=expo(x)) < 0) return gen_0;
  d = nbits2prec(e+1); m = remsBIL(e);
  if (d > lg(x)) pari_err_PREC( "truncr (precision loss in truncation)");

  y=cgeti(d); y[1] = evalsigne(s) | evallgefint(d);
  if (++m == BITS_IN_LONG)
    for (i=2; i<d; i++) y[i]=x[i];
  else
    shift_right(y,x, 2,d,0, BITS_IN_LONG - m);
  return y;
}

/* integral part */
GEN
floorr(GEN x)
{
  pari_long d,e,i,lx,m;
  GEN y;

  if (signe(x) >= 0) return truncr(x);
  if ((e=expo(x)) < 0) return gen_m1;
  d = nbits2prec(e+1); m = remsBIL(e);
  lx=lg(x); if (d>lx) pari_err_PREC( "floorr (precision loss in truncation)");
  y = new_chunk(d);
  if (++m == BITS_IN_LONG)
  {
    for (i=2; i<d; i++) y[i]=x[i];
    i=d; while (i<lx && !x[i]) i++;
    if (i==lx) goto END;
  }
  else
  {
    shift_right(y,x, 2,d,0, BITS_IN_LONG - m);
    if (x[d-1]<<m == 0)
    {
      i=d; while (i<lx && !x[i]) i++;
      if (i==lx) goto END;
    }
  }
  /* set y:=y+1 */
  for (i=d-1; i>=2; i--) { y[i]++; if (y[i]) goto END; }
  y=new_chunk(1); y[2]=1; d++;
END:
  y[1] = evalsigne(-1) | evallgefint(d);
  y[0] = evaltyp(t_INT) | evallg(d); return y;
}

INLINE int
cmpiispec(GEN x, GEN y, pari_long lx, pari_long ly)
{
  pari_long i;
  if (lx < ly) return -1;
  if (lx > ly) return  1;
  i = 0; while (i<lx && x[i]==y[i]) i++;
  if (i==lx) return 0;
  return ((ulong)x[i] > (ulong)y[i])? 1: -1;
}

INLINE int
equaliispec(GEN x, GEN y, pari_long lx, pari_long ly)
{
  pari_long i;
  if (lx != ly) return 0;
  i = ly-1; while (i>=0 && x[i]==y[i]) i--;
  return i < 0;
}

/***********************************************************************/
/**                                                                   **/
/**                          MULTIPLICATION                           **/
/**                                                                   **/
/***********************************************************************/
/* assume ny > 0 */
INLINE GEN
muluispec(ulong x, GEN y, pari_long ny)
{
  GEN yd, z = (GEN)avma;
  pari_long lz = ny+3;
  LOCAL_HIREMAINDER;

  (void)new_chunk(lz);
  yd = y + ny; *--z = mulll(x, *--yd);
  while (yd > y) *--z = addmul(x,*--yd);
  if (hiremainder) *--z = hiremainder; else lz--;
  *--z = evalsigne(1) | evallgefint(lz);
  *--z = evaltyp(t_INT) | evallg(lz);
  avma=(pari_sp)z; return z;
}

/* a + b*|Y| */
GEN
addumului(ulong a, ulong b, GEN Y)
{
  GEN yd,y,z;
  pari_long ny,lz;
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;

  if (!signe(Y)) return utoi(a);

  y = LIMBS(Y); z = (GEN)avma;
  ny = NLIMBS(Y);
  lz = ny+3;

  (void)new_chunk(lz);
  yd = y + ny; *--z = addll(a, mulll(b, *--yd));
  if (overflow) hiremainder++; /* can't overflow */
  while (yd > y) *--z = addmul(b,*--yd);
  if (hiremainder) *--z = hiremainder; else lz--;
  *--z = evalsigne(1) | evallgefint(lz);
  *--z = evaltyp(t_INT) | evallg(lz);
  avma=(pari_sp)z; return z;
}

/***********************************************************************/
/**                                                                   **/
/**                          DIVISION                                 **/
/**                                                                   **/
/***********************************************************************/

ulong
umodiu(GEN y, ulong x)
{
  pari_long sy=signe(y),ly,i;
  LOCAL_HIREMAINDER;

  if (!x) pari_err_INV("umodiu",gen_0);
  if (!sy) return 0;
  ly = lgefint(y);
  if (x <= (ulong)y[2]) hiremainder=0;
  else
  {
    if (ly==3) return (sy > 0)? (ulong)y[2]: x - (ulong)y[2];
    hiremainder=y[2]; ly--; y++;
  }
  for (i=2; i<ly; i++) (void)divll(y[i],x);
  if (!hiremainder) return 0;
  return (sy > 0)? hiremainder: x - hiremainder;
}

/* return |y| \/ x */
GEN
diviu_rem(GEN y, ulong x, ulong *rem)
{
  pari_long ly,i;
  GEN z;
  LOCAL_HIREMAINDER;

  if (!x) pari_err_INV("diviu_rem",gen_0);
  if (!signe(y)) { *rem = 0; return gen_0; }

  ly = lgefint(y);
  if (x <= (ulong)y[2]) hiremainder=0;
  else
  {
    if (ly==3) { *rem = (ulong)y[2]; return gen_0; }
    hiremainder=y[2]; ly--; y++;
  }
  z = cgetipos(ly);
  for (i=2; i<ly; i++) z[i]=divll(y[i],x);
  *rem = hiremainder; return z;
}

GEN
divis_rem(GEN y, pari_long x, pari_long *rem)
{
  pari_long sy=signe(y),ly,s,i;
  GEN z;
  LOCAL_HIREMAINDER;

  if (!x) pari_err_INV("divis_rem",gen_0);
  if (!sy) { *rem=0; return gen_0; }
  if (x<0) { s = -sy; x = -x; } else s = sy;

  ly = lgefint(y);
  if ((ulong)x <= (ulong)y[2]) hiremainder=0;
  else
  {
    if (ly==3) { *rem = itos(y); return gen_0; }
    hiremainder=y[2]; ly--; y++;
  }
  z = cgeti(ly); z[1] = evallgefint(ly) | evalsigne(s);
  for (i=2; i<ly; i++) z[i]=divll(y[i],x);
  if (sy<0) hiremainder = - ((pari_long)hiremainder);
  *rem = (pari_long)hiremainder; return z;
}

GEN
divis(GEN y, pari_long x)
{
  pari_long sy=signe(y),ly,s,i;
  GEN z;
  LOCAL_HIREMAINDER;

  if (!x) pari_err_INV("divis",gen_0);
  if (!sy) return gen_0;
  if (x<0) { s = -sy; x = -x; } else s = sy;

  ly = lgefint(y);
  if ((ulong)x <= (ulong)y[2]) hiremainder=0;
  else
  {
    if (ly==3) return gen_0;
    hiremainder=y[2]; ly--; y++;
  }
  z = cgeti(ly); z[1] = evallgefint(ly) | evalsigne(s);
  for (i=2; i<ly; i++) z[i]=divll(y[i],x);
  return z;
}

GEN
divrr(GEN x, GEN y)
{
  pari_long sx=signe(x), sy=signe(y), lx,ly,lr,e,i,j;
  ulong y0,y1;
  GEN r, r1;

  if (!x) pari_err_INV("divrr",y);
  e = expo(x) - expo(y);
  if (!sx) return real_0_bit(e);
  if (sy<0) sx = -sx;

  lx=lg(x); ly=lg(y);
  if (ly==3)
  {
    ulong k = x[2], l = (lx>3)? x[3]: 0;
    LOCAL_HIREMAINDER;
    if (k < (ulong)y[2]) e--;
    else
    {
      l >>= 1; if (k&1) l |= HIGHBIT;
      k >>= 1;
    }
    hiremainder = k; k = divll(l,y[2]);
    if (hiremainder & HIGHBIT)
    {
      k++;
      if (!k) { k = HIGHBIT; e++; }
    }
    r = cgetr(3);
    r[1] = evalsigne(sx) | evalexpo(e);
    r[2] = k; return r;
  }

  lr = minss(lx,ly); r = new_chunk(lr);
  r1 = r-1;
  r1[1] = 0; for (i=2; i<lr; i++) r1[i]=x[i];
  r1[lr] = (lx>ly)? x[lr]: 0;
  y0 = y[2]; y1 = y[3];
  for (i=0; i<lr-1; i++)
  { /* r1 = r + (i-1), OK up to r1[2] (accesses at most r[lr]) */
    ulong k, qp;
    LOCAL_HIREMAINDER;
    LOCAL_OVERFLOW;

    if ((ulong)r1[1] == y0)
    {
      qp = ULONG_MAX; k = addll(y0,r1[2]);
    }
    else
    {
      if ((ulong)r1[1] > y0) /* can't happen if i=0 */
      {
        GEN y1 = y+1;
        j = lr-i; r1[j] = subll(r1[j],y1[j]);
        for (j--; j>0; j--) r1[j] = subllx(r1[j],y1[j]);
        j=i; do ((ulong*)r)[--j]++; while (j && !r[j]);
      }
      hiremainder = r1[1]; overflow = 0;
      qp = divll(r1[2],y0); k = hiremainder;
    }
    j = lr-i+1;
    if (!overflow)
    {
      pari_long k3, k4;
      k3 = mulll(qp,y1);
      if (j == 3) /* i = lr - 2 maximal, r1[3] undefined -> 0 */
        k4 = subll(hiremainder,k);
      else
      {
        k3 = subll(k3, r1[3]);
        k4 = subllx(hiremainder,k);
      }
      while (!overflow && k4) { qp--; k3 = subll(k3,y1); k4 = subllx(k4,y0); }
    }
    if (j<ly) (void)mulll(qp,y[j]); else { hiremainder = 0 ; j = ly; }
    for (j--; j>1; j--)
    {
      r1[j] = subll(r1[j], addmul(qp,y[j]));
      hiremainder += overflow;
    }
    if ((ulong)r1[1] != hiremainder)
    {
      if ((ulong)r1[1] < hiremainder)
      {
        qp--;
        j = lr-i-(lr-i>=ly); r1[j] = addll(r1[j], y[j]);
        for (j--; j>1; j--) r1[j] = addllx(r1[j], y[j]);
      }
      else
      {
        r1[1] -= hiremainder;
        while (r1[1])
        {
          qp++; if (!qp) { j=i; do ((ulong*)r)[--j]++; while (j && !r[j]); }
          j = lr-i-(lr-i>=ly); r1[j] = subll(r1[j],y[j]);
          for (j--; j>1; j--) r1[j] = subllx(r1[j],y[j]);
          r1[1] -= overflow;
        }
      }
    }
    *++r1 = qp;
  }
  /* i = lr-1 */
  /* round correctly */
  if ((ulong)r1[1] > (y0>>1))
  {
    j=i; do ((ulong*)r)[--j]++; while (j && !r[j]);
  }
  r1 = r-1; for (j=i; j>=2; j--) r[j]=r1[j];
  if (r[0] == 0) e--;
  else if (r[0] == 1) { shift_right(r,r, 2,lr, 1,1); }
  else { /* possible only when rounding up to 0x2 0x0 ... */
    r[2] = (pari_long)HIGHBIT; e++;
  }
  r[0] = evaltyp(t_REAL)|evallg(lr);
  r[1] = evalsigne(sx) | evalexpo(e);
  return r;
}

GEN
divri(GEN x, GEN y)
{
  pari_long lx, s = signe(y);
  pari_sp av;
  GEN z;

  if (!s) pari_err_INV("divri",y);
  if (!signe(x)) return real_0_bit(expo(x) - expi(y));
  if (!is_bigint(y)) {
    GEN z = divru(x, y[2]);
    if (s < 0) togglesign(z);
    return z;
  }
  lx = lg(x); z = cgetr(lx); av = avma;
  affrr(divrr(x, itor(y, lx+1)), z);
  avma = av; return z;
}

/* Integer division x / y: such that sign(r) = sign(x)
 *   if z = ONLY_REM return remainder, otherwise return quotient
 *   if z != NULL set *z to remainder
 *   *z is the last object on stack (and thus can be disposed of with cgiv
 *   instead of gerepile)
 * If *z is zero, we put gen_0 here and no copy.
 * space needed: lx + ly */
GEN
dvmdii(GEN x, GEN y, GEN *z)
{
  pari_long sx=signe(x),sy=signe(y);
  pari_long lx, ly, lz, i, j, sh, lq, lr;
  pari_sp av;
  ulong y0,y1, *xd,*rd,*qd;
  GEN q, r, r1;

  if (!sy)
  {
    if (z == ONLY_REM && !sx) return gen_0;
    if (!sy) pari_err_INV("dvmdii",gen_0);
  }
  if (!sx)
  {
    if (!z || z == ONLY_REM) return gen_0;
    *z=gen_0; return gen_0;
  }
  lx=lgefint(x);
  ly=lgefint(y); lz=lx-ly;
  if (lz <= 0)
  {
    if (lz == 0)
    {
      for (i=2; i<lx; i++)
        if (x[i] != y[i])
        {
          if ((ulong)x[i] > (ulong)y[i]) goto DIVIDE;
          goto TRIVIAL;
        }
      if (z == ONLY_REM) return gen_0;
      if (z) *z = gen_0;
      if (sx < 0) sy = -sy;
      return stoi(sy);
    }
TRIVIAL:
    if (z == ONLY_REM) return icopy(x);
    if (z) *z = icopy(x);
    return gen_0;
  }
DIVIDE: /* quotient is non-zero */
  av=avma; if (sx<0) sy = -sy;
  if (ly==3)
  {
    LOCAL_HIREMAINDER;
    y0 = y[2];
    if (y0 <= (ulong)x[2]) hiremainder=0;
    else
    {
      hiremainder = x[2]; lx--; x++;
    }
    q = new_chunk(lx); for (i=2; i<lx; i++) q[i]=divll(x[i],y0);
    if (z == ONLY_REM)
    {
      avma=av; if (!hiremainder) return gen_0;
      r=cgeti(3);
      r[1] = evalsigne(sx) | evallgefint(3);
      r[2]=hiremainder; return r;
    }
    q[1] = evalsigne(sy) | evallgefint(lx);
    q[0] = evaltyp(t_INT) | evallg(lx);
    if (!z) return q;
    if (!hiremainder) { *z=gen_0; return q; }
    r=cgeti(3);
    r[1] = evalsigne(sx) | evallgefint(3);
    r[2] = hiremainder; *z=r; return q;
  }

  r1 = new_chunk(lx); sh = bfffo(y[2]);
  if (sh)
  { /* normalize so that highbit(y) = 1 (shift left x and y by sh bits)*/
    register const ulong m = BITS_IN_LONG - sh;
    r = new_chunk(ly);
    shift_left(r, y,2,ly-1, 0,sh); y = r;
    shift_left(r1,x,2,lx-1, 0,sh);
    r1[1] = ((ulong)x[2]) >> m;
  }
  else
  {
    r1[1] = 0; for (j=2; j<lx; j++) r1[j] = x[j];
  }
  x = r1;
  y0 = y[2]; y1 = y[3];
  for (i=0; i<=lz; i++)
  { /* r1 = x + i */
    ulong k, qp;
    LOCAL_HIREMAINDER;
    LOCAL_OVERFLOW;

    if ((ulong)r1[1] == y0)
    {
      qp = ULONG_MAX; k = addll(y0,r1[2]);
    }
    else
    {
      hiremainder = r1[1]; overflow = 0;
      qp = divll(r1[2],y0); k = hiremainder;
    }
    if (!overflow)
    {
      pari_long k3 = subll(mulll(qp,y1), r1[3]);
      pari_long k4 = subllx(hiremainder,k);
      while (!overflow && k4) { qp--; k3 = subll(k3,y1); k4 = subllx(k4,y0); }
    }
    hiremainder = 0; j = ly;
    for (j--; j>1; j--)
    {
      r1[j] = subll(r1[j], addmul(qp,y[j]));
      hiremainder += overflow;
    }
    if ((ulong)r1[1] < hiremainder)
    {
      qp--;
      j = ly-1; r1[j] = addll(r1[j],y[j]);
      for (j--; j>1; j--) r1[j] = addllx(r1[j],y[j]);
    }
    *++r1 = qp;
  }

  lq = lz+2;
  if (!z)
  {
    qd = (ulong*)av;
    xd = (ulong*)(x + lq);
    if (x[1]) { lz++; lq++; }
    while (lz--) *--qd = *--xd;
    *--qd = evalsigne(sy) | evallgefint(lq);
    *--qd = evaltyp(t_INT) | evallg(lq);
    avma = (pari_sp)qd; return (GEN)qd;
  }

  j=lq; while (j<lx && !x[j]) j++;
  lz = lx-j;
  if (z == ONLY_REM)
  {
    if (lz==0) { avma = av; return gen_0; }
    rd = (ulong*)av; lr = lz+2;
    xd = (ulong*)(x + lx);
    if (!sh) while (lz--) *--rd = *--xd;
    else
    { /* shift remainder right by sh bits */
      const ulong shl = BITS_IN_LONG - sh;
      ulong l;
      xd--;
      while (--lz) /* fill r[3..] */
      {
        l = *xd >> sh;
        *--rd = l | (*--xd << shl);
      }
      l = *xd >> sh;
      if (l) *--rd = l; else lr--;
    }
    *--rd = evalsigne(sx) | evallgefint(lr);
    *--rd = evaltyp(t_INT) | evallg(lr);
    avma = (pari_sp)rd; return (GEN)rd;
  }

  lr = lz+2;
  rd = NULL; /* gcc -Wall */
  if (lz)
  { /* non zero remainder: initialize rd */
    xd = (ulong*)(x + lx);
    if (!sh)
    {
      rd = (ulong*)avma; (void)new_chunk(lr);
      while (lz--) *--rd = *--xd;
    }
    else
    { /* shift remainder right by sh bits */
      const ulong shl = BITS_IN_LONG - sh;
      ulong l;
      rd = (ulong*)x; /* overwrite shifted y */
      xd--;
      while (--lz)
      {
        l = *xd >> sh;
        *--rd = l | (*--xd << shl);
      }
      l = *xd >> sh;
      if (l) *--rd = l; else lr--;
    }
    *--rd = evalsigne(sx) | evallgefint(lr);
    *--rd = evaltyp(t_INT) | evallg(lr);
    rd += lr;
  }
  qd = (ulong*)av;
  xd = (ulong*)(x + lq);
  if (x[1]) lq++;
  j = lq-2; while (j--) *--qd = *--xd;
  *--qd = evalsigne(sy) | evallgefint(lq);
  *--qd = evaltyp(t_INT) | evallg(lq);
  q = (GEN)qd;
  if (lr==2) *z = gen_0;
  else
  { /* rd has been properly initialized: we had lz > 0 */
    while (lr--) *--qd = *--rd;
    *z = (GEN)qd;
  }
  avma = (pari_sp)qd; return q;
}

/* Montgomery reduction.
 * N has k words, assume T >= 0 has less than 2k.
 * Return res := T / B^k mod N, where B = 2^BIL
 * such that 0 <= res < T/B^k + N  and  res has less than k words */
GEN
red_montgomery(GEN T, GEN N, ulong inv)
{
  pari_sp av;
  GEN Te, Td, Ne, Nd, scratch;
  ulong i, j, m, t, d, k = NLIMBS(N);
  int carry;
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;

  if (k == 0) return gen_0;
  d = NLIMBS(T); /* <= 2*k */
  if (d == 0) return gen_0;
#ifdef DEBUG
  if (d > 2*k) pari_err_BUG("red_montgomery");
#endif
  if (k == 1)
  { /* as below, special cased for efficiency */
    ulong n = (ulong)N[2];
    if (d == 1) {
      hiremainder = (ulong)T[2];
      m = hiremainder * inv;
      (void)addmul(m, n); /* t + m*n = 0 */
      return utoi(hiremainder);
    } else { /* d = 2 */
      hiremainder = (ulong)T[3];
      m = hiremainder * inv;
      (void)addmul(m, n); /* t + m*n = 0 */
      t = addll(hiremainder, (ulong)T[2]);
      if (overflow) t -= n; /* t > n doesn't fit in 1 word */
      return utoi(t);
    }
  }
  /* assume k >= 2 */
  av = avma; scratch = new_chunk(k<<1); /* >= k + 2: result fits */

  /* copy T to scratch space (pad with zeroes to 2k words) */
  Td = (GEN)av;
  Te = T + (d+2);
  for (i=0; i < d     ; i++) *--Td = *--Te;
  for (   ; i < (k<<1); i++) *--Td = 0;

  Te = (GEN)av; /* 1 beyond end of current T mantissa (in scratch) */
  Ne = N + k+2; /* 1 beyond end of N mantissa */

  carry = 0;
  for (i=0; i<k; i++) /* set T := T/B nod N, k times */
  {
    Td = Te; /* one beyond end of (new) T mantissa */
    Nd = Ne;
    hiremainder = *--Td;
    m = hiremainder * inv; /* solve T + m N = O(B) */

    /* set T := (T + mN) / B */
    Te = Td;
    (void)addmul(m, *--Nd); /* = 0 */
    for (j=1; j<k; j++)
    {
      t = addll(addmul(m, *--Nd), *--Td);
      *Td = t;
      hiremainder += overflow;
    }
    t = addll(hiremainder, *--Td); *Td = t + carry;
    carry = (overflow || (carry && *Td == 0));
  }
  if (carry)
  { /* Td > N overflows (k+1 words), set Td := Td - N */
    Td = Te;
    Nd = Ne;
    t = subll(*--Td, *--Nd); *Td = t;
    while (Td > scratch) { t = subllx(*--Td, *--Nd); *Td = t; }
  }

  /* copy result */
  Td = (GEN)av;
  while (*scratch == 0 && Te > scratch) scratch++; /* strip leading 0s */
  while (Te > scratch) *--Td = *--Te;
  k = (GEN)av - Td; if (!k) { avma = av; return gen_0; }
  k += 2;
  *--Td = evalsigne(1) | evallgefint(k);
  *--Td = evaltyp(t_INT) | evallg(k);
#ifdef DEBUG
{
  pari_long l = NLIMBS(N), s = BITS_IN_LONG*l;
  GEN R = int2n(s);
  GEN res = remii(mulii(T, Fp_inv(R, N)), N);
  if (k > lgefint(N)
    || !equalii(remii(Td,N),res)
    || cmpii(Td, addii(shifti(T, -s), N)) >= 0) pari_err_BUG("red_montgomery");
}
#endif
  avma = (pari_sp)Td; return Td;
}

/* EXACT INTEGER DIVISION */

/* assume xy>0, the division is exact and y is odd. Destroy x */
static GEN
diviuexact_i(GEN x, ulong y)
{
  pari_long i, lz, lx;
  ulong q, yinv;
  GEN z, z0, x0, x0min;

  if (y == 1) return icopy(x);
  lx = lgefint(x);
  if (lx == 3) return utoipos((ulong)x[2] / y);
  yinv = invmod2BIL(y);
  lz = (y <= (ulong)x[2]) ? lx : lx-1;
  z = new_chunk(lz);
  z0 = z + lz;
  x0 = x + lx; x0min = x + lx-lz+2;

  while (x0 > x0min)
  {
    *--z0 = q = yinv*((ulong)*--x0); /* i-th quotient */
    if (!q) continue;
    /* x := x - q * y */
    { /* update neither lowest word (could set it to 0) nor highest ones */
      register GEN x1 = x0 - 1;
      LOCAL_HIREMAINDER;
      (void)mulll(q,y);
      if (hiremainder)
      {
        if ((ulong)*x1 < hiremainder)
        {
          *x1 -= hiremainder;
          do (*--x1)--; while ((ulong)*x1 == ULONG_MAX);
        }
        else
          *x1 -= hiremainder;
      }
    }
  }
  i=2; while(!z[i]) i++;
  z += i-2; lz -= i-2;
  z[0] = evaltyp(t_INT)|evallg(lz);
  z[1] = evalsigne(1)|evallg(lz);
  avma = (pari_sp)z; return z;
}

/* assume y != 0 and the division is exact */
GEN
diviuexact(GEN x, ulong y)
{
  pari_sp av;
  pari_long lx, vy, s = signe(x);
  GEN z;

  if (!s) return gen_0;
  if (y == 1) return icopy(x);
  lx = lgefint(x);
  if (lx == 3) {
    ulong q = (ulong)x[2] / y;
    return (s > 0)? utoipos(q): utoineg(q);
  }
  av = avma; (void)new_chunk(lx); vy = vals(y);
  if (vy) {
    y >>= vy;
    if (y == 1) { avma = av; return shifti(x, -vy); }
    x = shifti(x, -vy);
    if (lx == 3) {
      ulong q = (ulong)x[2] / y;
      avma = av;
      return (s > 0)? utoipos(q): utoineg(q);
    }
  } else x = icopy(x);
  avma = av;
  z = diviuexact_i(x, y);
  setsigne(z, s); return z;
}

/* Find z such that x=y*z, knowing that y | x (unchecked)
 * Method: y0 z0 = x0 mod B = 2^BITS_IN_LONG ==> z0 = 1/y0 mod B.
 *    Set x := (x - z0 y) / B, updating only relevant words, and repeat */
GEN
diviiexact(GEN x, GEN y)
{
  pari_long lx, ly, lz, vy, i, ii, sx = signe(x), sy = signe(y);
  pari_sp av;
  ulong y0inv,q;
  GEN z;

  if (!sy) pari_err_INV("diviiexact",gen_0);
  if (!sx) return gen_0;
  lx = lgefint(x);
  if (lx == 3) {
    q = (ulong)x[2] / (ulong)y[2];
    return (sx+sy) ? utoipos(q): utoineg(q);
  }
  vy = vali(y); av = avma;
  (void)new_chunk(lx); /* enough room for z */
  if (vy)
  { /* make y odd */
    y = shifti(y,-vy);
    x = shifti(x,-vy); lx = lgefint(x);
  }
  else x = icopy(x); /* necessary because we destroy x */
  avma = av; /* will erase our x,y when exiting */
  /* now y is odd */
  ly = lgefint(y);
  if (ly == 3)
  {
    x = diviuexact_i(x,(ulong)y[2]); /* x != 0 */
    setsigne(x, (sx+sy)? 1: -1); return x;
  }
  y0inv = invmod2BIL(y[ly-1]);
  i=2; while (i<ly && y[i]==x[i]) i++;
  lz = (i==ly || (ulong)y[i] < (ulong)x[i]) ? lx-ly+3 : lx-ly+2;
  z = new_chunk(lz);

  y += ly - 1; /* now y[-i] = i-th word of y */
  for (ii=lx-1,i=lz-1; i>=2; i--,ii--)
  {
    pari_long limj;
    LOCAL_HIREMAINDER;
    LOCAL_OVERFLOW;

    z[i] = q = y0inv*((ulong)x[ii]); /* i-th quotient */
    if (!q) continue;

    /* x := x - q * y */
    (void)mulll(q,y[0]); limj = maxss(lx - lz, ii+3-ly);
    { /* update neither lowest word (could set it to 0) nor highest ones */
      register GEN x0 = x + (ii - 1), y0 = y - 1, xlim = x + limj;
      for (; x0 >= xlim; x0--, y0--)
      {
        *x0 = subll(*x0, addmul(q,*y0));
        hiremainder += overflow;
      }
      if (hiremainder && limj != lx - lz)
      {
        if ((ulong)*x0 < hiremainder)
        {
          *x0 -= hiremainder;
          do (*--x0)--; while ((ulong)*x0 == ULONG_MAX);
        }
        else
          *x0 -= hiremainder;
      }
    }
  }
  i=2; while(!z[i]) i++;
  z += i-2; lz -= (i-2);
  z[0] = evaltyp(t_INT)|evallg(lz);
  z[1] = evalsigne((sx+sy)? 1: -1) | evallg(lz);
  avma = (pari_sp)z; return z;
}

/* assume yz != and yz | x */
GEN
diviuuexact(GEN x, ulong y, ulong z)
{
  pari_long tmp[4];
  ulong t;
  LOCAL_HIREMAINDER;
  t = mulll(y, z);
  if (!hiremainder) return diviuexact(x, t);
  tmp[0] = evaltyp(t_INT)|_evallg(4);
  tmp[1] = evalsigne(1)|evallgefint(4);
  tmp[2] = hiremainder;
  tmp[3] = t;
  return diviiexact(x, tmp);
}

/********************************************************************/
/**                                                                **/
/**               INTEGER MULTIPLICATION (BASECASE)                **/
/**                                                                **/
/********************************************************************/
/* nx >= ny = num. of digits of x, y (not GEN, see mulii) */
INLINE GEN
muliispec_basecase(GEN x, GEN y, pari_long nx, pari_long ny)
{
  GEN z2e,z2d,yd,xd,ye,zd;
  pari_long p1,lz;
  LOCAL_HIREMAINDER;

  if (ny == 1) return muluispec((ulong)*y, x, nx);
  if (ny == 0) return gen_0;
  zd = (GEN)avma; lz = nx+ny+2;
  (void)new_chunk(lz);
  xd = x + nx;
  yd = y + ny;
  ye = yd; p1 = *--xd;

  *--zd = mulll(p1, *--yd); z2e = zd;
  while (yd > y) *--zd = addmul(p1, *--yd);
  *--zd = hiremainder;

  while (xd > x)
  {
    LOCAL_OVERFLOW;
    yd = ye; p1 = *--xd;

    z2d = --z2e;
    *z2d = addll(mulll(p1, *--yd), *z2d); z2d--;
    while (yd > y)
    {
      hiremainder += overflow;
      *z2d = addll(addmul(p1, *--yd), *z2d); z2d--;
    }
    *--zd = hiremainder + overflow;
  }
  if (*zd == 0) { zd++; lz--; } /* normalize */
  *--zd = evalsigne(1) | evallgefint(lz);
  *--zd = evaltyp(t_INT) | evallg(lz);
  avma=(pari_sp)zd; return zd;
}

INLINE GEN
sqrispec_basecase(GEN x, pari_long nx)
{
  GEN z2e,z2d,yd,xd,zd,x0,z0;
  pari_long p1,lz;
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;

  if (nx == 1) return sqru((ulong)*x);
  if (nx == 0) return gen_0;
  zd = (GEN)avma; lz = (nx+1) << 1;
  z0 = new_chunk(lz);
  if (nx == 1)
  {
    *--zd = mulll(*x, *x);
    *--zd = hiremainder; goto END;
  }
  xd = x + nx;

  /* compute double products --> zd */
  p1 = *--xd; yd = xd; --zd;
  *--zd = mulll(p1, *--yd); z2e = zd;
  while (yd > x) *--zd = addmul(p1, *--yd);
  *--zd = hiremainder;

  x0 = x+1;
  while (xd > x0)
  {
    LOCAL_OVERFLOW;
    p1 = *--xd; yd = xd;

    z2e -= 2; z2d = z2e;
    *z2d = addll(mulll(p1, *--yd), *z2d); z2d--;
    while (yd > x)
    {
      hiremainder += overflow;
      *z2d = addll(addmul(p1, *--yd), *z2d); z2d--;
    }
    *--zd = hiremainder + overflow;
  }
  /* multiply zd by 2 (put result in zd - 1) */
  zd[-1] = ((*zd & HIGHBIT) != 0);
  shift_left(zd, zd, 0, (nx<<1)-3, 0, 1);

  /* add the squares */
  xd = x + nx; zd = z0 + lz;
  p1 = *--xd;
  zd--; *zd = mulll(p1,p1);
  zd--; *zd = addll(hiremainder, *zd);
  while (xd > x)
  {
    p1 = *--xd;
    zd--; *zd = addll(mulll(p1,p1)+ overflow, *zd);
    zd--; *zd = addll(hiremainder + overflow, *zd);
  }

END:
  if (*zd == 0) { zd++; lz--; } /* normalize */
  *--zd = evalsigne(1) | evallgefint(lz);
  *--zd = evaltyp(t_INT) | evallg(lz);
  avma=(pari_sp)zd; return zd;
}

/********************************************************************/
/**                                                                **/
/**               INTEGER MULTIPLICATION (FFT)                     **/
/**                                                                **/
/********************************************************************/

/*
 Compute parameters for FFT:
   len: result length
   k: FFT depth.
   n: number of blocks (2^k)
   bs: block size
   mod: Modulus is M=2^(BIL*mod)+1
   ord: order of 2 in Z/MZ.
 We must have:
   bs*n >= l
   2^(BIL*mod) > nb*2^(2*BIL*bs)
   2^k | 2*BIL*mod
*/
static void
mulliifft_params(pari_long len, pari_long *k, pari_long *mod, pari_long *bs, pari_long *n, ulong *ord)
{
  pari_long r;
  *k = expu((3*len)>>2)-3;
  do {
    (*k)--;
    r  = *k-(TWOPOTBITS_IN_LONG+2);
    *n = 1LL<<*k;
    *bs = (len+*n-1)>>*k;
    *mod= 2**bs+1;
    if (r>0)
      *mod=((*mod+(1LL<<r)-1)>>r)<<r;
  } while(*mod>=3**bs);
  *ord= 4**mod*BITS_IN_LONG;
}

/* Zf_: arithmetic in ring Z/MZ where M= 2^(BITS_IN_LONG*mod)+1
 * for some mod.
 * Do not garbage collect.
 */

static GEN
Zf_add(GEN a, GEN b, GEN M)
{
  GEN y, z = addii(a,b);
  pari_long mod = lgefint(M)-3;
  pari_long l = NLIMBS(z);
  if (l<=mod) return z;
  y = subis(z, 1);
  if (NLIMBS(y)<=mod) return z;
  return int_normalize(y,1);
}

static GEN
Zf_sub(GEN a, GEN b, GEN M)
{
  GEN z = subii(a,b);
  return signe(z)>=0? z: addii(M,z);
}

/* destroy z */
static GEN
Zf_red_destroy(GEN z, GEN M)
{
  pari_long mod = lgefint(M)-3;
  pari_long l = NLIMBS(z);
  GEN y;
  if (l<=mod) return z;
  y = shifti(z, -mod*BITS_IN_LONG);
  z = int_normalize(z, NLIMBS(y));
  y = Zf_red_destroy(y, M);
  z = subii(z, y);
  if (signe(z)<0) z = addii(z, M);
  return z;
}

INLINE GEN
Zf_shift(GEN a, ulong s, GEN M) { return Zf_red_destroy(shifti(a, s), M); }

/*
 Multiply by sqrt(2)^s
 We use the formula sqrt(2)=z_8*(1-z_4)) && z_8=2^(ord/16) [2^(ord/4)+1]
*/

static GEN
Zf_mulsqrt2(GEN a, ulong s, ulong ord, GEN M)
{
  ulong hord = ord>>1;
  if (!signe(a)) return gen_0;
  if (odd(s)) /* Multiply by 2^(s/2) */
  {
    GEN az8  = Zf_shift(a,   ord>>4, M);
    GEN az83 = Zf_shift(az8, ord>>3, M);
    a = Zf_sub(az8, az83, M);
    s--;
  }
  if (s < hord)
    return Zf_shift(a, s>>1, M);
  else
    return subii(M,Zf_shift(a, (s-hord)>>1, M));
}

INLINE GEN
Zf_sqr(GEN a, GEN M) { return Zf_red_destroy(sqri(a), M); }

INLINE GEN
Zf_mul(GEN a, GEN b, GEN M) { return Zf_red_destroy(mulii(a,b), M); }

/* In place, bit reversing FFT */
static void
muliifft_dit(ulong o, ulong ord, GEN M, GEN FFT, pari_long d, pari_long step)
{
  pari_sp av = avma;
  pari_long i;
  ulong j, no = (o<<1)%ord;
  pari_long hstep=step>>1;
  for (i = d+1, j = 0; i <= d+hstep; ++i, j =(j+o)%ord)
  {
    GEN a = Zf_add(gel(FFT,i), gel(FFT,i+hstep), M);
    GEN b = Zf_mulsqrt2(Zf_sub(gel(FFT,i), gel(FFT,i+hstep), M), j, ord, M);
    affii(a,gel(FFT,i));
    affii(b,gel(FFT,i+hstep));
    avma = av;
  }
  if (hstep>1)
  {
    muliifft_dit(no, ord, M, FFT, d, hstep);
    muliifft_dit(no, ord, M, FFT, d+hstep, hstep);
  }
}

/* In place, bit reversed FFT, inverse of muliifft_dit */
static void
muliifft_dis(ulong o, ulong ord, GEN M, GEN FFT, pari_long d, pari_long step)
{
  pari_sp av = avma;
  pari_long i;
  ulong j, no = (o<<1)%ord;
  pari_long hstep=step>>1;
  if (hstep>1)
  {
    muliifft_dis(no, ord, M, FFT, d, hstep);
    muliifft_dis(no, ord, M, FFT, d+hstep, hstep);
  }
  for (i = d+1, j = 0; i <= d+hstep; ++i, j =(j+o)%ord)
  {
    GEN z = Zf_mulsqrt2(gel(FFT,i+hstep), j, ord, M);
    GEN a = Zf_add(gel(FFT,i), z, M);
    GEN b = Zf_sub(gel(FFT,i), z, M);
    affii(a,gel(FFT,i));
    affii(b,gel(FFT,i+hstep));
    avma = av;
  }
}

static GEN
muliifft_spliti(GEN a, pari_long na, pari_long bs, pari_long n, pari_long mod)
{
  GEN ap = a+na-1;
  GEN c  = cgetg(n+1, t_VEC);
  pari_long i,j;
  for(i=1;i<=n;i++)
  {
    GEN z = cgeti(mod+3);
    if (na)
    {
      pari_long m = minss(bs, na), v=0;
      GEN zp, aa=ap-m+1;
      while (!*aa && v<m) {aa++; v++;}
      zp = z+m-v+1;
      for (j=v; j < m; j++)
        *zp-- = *ap--;
      ap -= v; na -= m;
      z[1] = evalsigne(m!=v) | evallgefint(m-v+2);
    } else
      z[1] = evalsigne(0) | evallgefint(2);
    gel(c, i) = z;
  }
  return c;
}

static GEN
muliifft_unspliti(GEN V, pari_long bs, pari_long len)
{
  pari_long s, i, j, l = lg(V);
  GEN a = cgeti(len);
  a[1] = evalsigne(1)|evallgefint(len);
  for(i=2;i<len;i++)
    a[i] = 0;
  for(i=1, s=0; i<l; i++, s+=bs)
  {
    GEN  u = gel(V,i);
    if (signe(u))
    {
      GEN ap = int_W(a,s);
      GEN up = int_LSW(u);
      pari_long lu = NLIMBS(u);
      LOCAL_OVERFLOW;
      *ap = addll(*ap, *up--); ap--;
      for (j=1; j<lu; j++)
       { *ap = addllx(*ap, *up--); ap--; }
      while (overflow)
       { *ap = addll(*ap, 1); ap--; }
    }
  }
  return int_normalize(a,0);
}

static GEN
sqrispec_fft(GEN a, pari_long na)
{
  pari_sp av, ltop = avma;
  pari_long len = 2*na;
  pari_long k, mod, bs, n;
  GEN  FFT, M;
  pari_long i;
  ulong o, ord;

  mulliifft_params(len,&k,&mod,&bs,&n,&ord);
  o = ord>>k;
  M = int2n(mod*BITS_IN_LONG);
  M[2+mod] = 1;
  FFT = muliifft_spliti(a, na, bs, n, mod);
  muliifft_dit(o, ord, M, FFT, 0, n);
  av = avma;
  for(i=1; i<=n; i++)
  {
    affii(Zf_sqr(gel(FFT,i), M), gel(FFT,i));
    avma=av;
  }
  muliifft_dis(ord-o, ord, M, FFT, 0, n);
  for(i=1; i<=n; i++)
  {
    affii(Zf_shift(gel(FFT,i), (ord>>1)-k, M), gel(FFT,i));
    avma=av;
  }
  return gerepileuptoint(ltop, muliifft_unspliti(FFT,bs,2+len));
}

static GEN
muliispec_fft(GEN a, GEN b, pari_long na, pari_long nb)
{
  pari_sp av, av2, ltop = avma;
  pari_long len = na+nb;
  pari_long k, mod, bs, n;
  GEN FFT, FFTb, M;
  pari_long i;
  ulong o, ord;

  mulliifft_params(len,&k,&mod,&bs,&n,&ord);
  o = ord>>k;
  M = int2n(mod*BITS_IN_LONG);
  M[2+mod] = 1;
  FFT = muliifft_spliti(a, na, bs, n, mod);
  av=avma;
  muliifft_dit(o, ord, M, FFT, 0, n);
  FFTb = muliifft_spliti(b, nb, bs, n, mod);
  av2 = avma;
  muliifft_dit(o, ord, M, FFTb, 0, n);
  for(i=1; i<=n; i++)
  {
    affii(Zf_mul(gel(FFT,i), gel(FFTb,i), M), gel(FFT,i));
    avma=av2;
  }
  avma=av;
  muliifft_dis(ord-o, ord, M, FFT, 0, n);
  for(i=1; i<=n; i++)
  {
    affii(Zf_shift(gel(FFT,i),(ord>>1)-k,M), gel(FFT,i));
    avma=av;
  }
  return gerepileuptoint(ltop, muliifft_unspliti(FFT,bs,2+len));
}

/********************************************************************/
/**                                                                **/
/**               INTEGER MULTIPLICATION (KARATSUBA)               **/
/**                                                                **/
/********************************************************************/

/* return (x shifted left d words) + y. Assume d > 0, x > 0 and y >= 0 */
static GEN
addshiftw(GEN x, GEN y, pari_long d)
{
  GEN z,z0,y0,yd, zd = (GEN)avma;
  pari_long a,lz,ly = lgefint(y);

  z0 = new_chunk(d);
  a = ly-2; yd = y+ly;
  if (a >= d)
  {
    y0 = yd-d; while (yd > y0) *--zd = *--yd; /* copy last d words of y */
    a -= d;
    if (a)
      z = addiispec(LIMBS(x), LIMBS(y), NLIMBS(x), a);
    else
      z = icopy(x);
  }
  else
  {
    y0 = yd-a; while (yd > y0) *--zd = *--yd; /* copy last a words of y */
    while (zd > z0) *--zd = 0;    /* complete with 0s */
    z = icopy(x);
  }
  lz = lgefint(z)+d;
  z[1] = evalsigne(1) | evallgefint(lz);
  z[0] = evaltyp(t_INT) | evallg(lz); return z;
}

/* Fast product (Karatsuba) of integers. a and b are "special" GENs
 * c,c0,c1,c2 are genuine GENs.
 */
GEN
muliispec(GEN a, GEN b, pari_long na, pari_long nb)
{
  GEN a0,c,c0;
  pari_long n0, n0a, i;
  pari_sp av;

  if (na < nb) swapspec(a,b, na,nb);
  if (nb < MULII_KARATSUBA_LIMIT) return muliispec_basecase(a,b,na,nb);
  if (nb >= MULII_FFT_LIMIT)      return muliispec_fft(a,b,na,nb);
  i=(na>>1); n0=na-i; na=i;
  av=avma; a0=a+na; n0a=n0;
  while (n0a && !*a0) { a0++; n0a--; }

  if (n0a && nb > n0)
  { /* nb <= na <= n0 */
    GEN b0,c1,c2;
    pari_long n0b;

    nb -= n0;
    c = muliispec(a,b,na,nb);
    b0 = b+nb; n0b = n0;
    while (n0b && !*b0) { b0++; n0b--; }
    if (n0b)
    {
      c0 = muliispec(a0,b0, n0a,n0b);

      c2 = addiispec(a0,a, n0a,na);
      c1 = addiispec(b0,b, n0b,nb);
      c1 = muliispec(LIMBS(c1),LIMBS(c2), NLIMBS(c1),NLIMBS(c2));
      c2 = addiispec(LIMBS(c0),LIMBS(c),  NLIMBS(c0),NLIMBS(c));

      c1 = subiispec(LIMBS(c1),LIMBS(c2), NLIMBS(c1),NLIMBS(c2));
    }
    else
    {
      c0 = gen_0;
      c1 = muliispec(a0,b, n0a,nb);
    }
    c = addshiftw(c,c1, n0);
  }
  else
  {
    c = muliispec(a,b,na,nb);
    c0 = muliispec(a0,b,n0a,nb);
  }
  return gerepileuptoint(av, addshiftw(c,c0, n0));
}
GEN
muluui(ulong x, ulong y, GEN z)
{
  pari_long t, s = signe(z);
  GEN r;
  LOCAL_HIREMAINDER;

  if (!x || !y || !signe(z)) return gen_0;
  t = mulll(x,y);
  if (!hiremainder)
    r = muluispec(t, z+2, lgefint(z)-2);
  else
  {
    pari_long tmp[2];
    tmp[0] = hiremainder;
    tmp[1] = t;
    r = muliispec(z+2,tmp,lgefint(z)-2,2);
  }
  setsigne(r,s); return r;
}

#define sqrispec_mirror sqrispec
#define muliispec_mirror muliispec

/* x % (2^n), assuming n >= 0 */
GEN
remi2n(GEN x, pari_long n)
{
  pari_long hi,l,k,lx,ly, sx = signe(x);
  GEN z, xd, zd;

  if (!sx || !n) return gen_0;

  k = dvmdsBIL(n, &l);
  lx = lgefint(x);
  if (lx < k+3) return icopy(x);

  xd = x + (lx-k-1);
  /* x = |_|...|#|1|...|k| : copy the last l bits of # and the last k words
   *            ^--- initial xd  */
  hi = ((ulong)*xd) & ((1ULL<<l)-1); /* last l bits of # = top bits of result */
  if (!hi)
  { /* strip leading zeroes from result */
    xd++; while (k && !*xd) { k--; xd++; }
    if (!k) return gen_0;
    ly = k+2; xd--;
  }
  else
    ly = k+3;

  zd = z = cgeti(ly);
  *++zd = evalsigne(sx) | evallgefint(ly);
  if (hi) *++zd = hi;
  for ( ;k; k--) *++zd = *++xd;
  return z;
}

GEN
sqrispec(GEN a, pari_long na)
{
  GEN a0,c;
  pari_long n0, n0a, i;
  pari_sp av;

  if (na < SQRI_KARATSUBA_LIMIT) return sqrispec_basecase(a,na);
  if (na >= SQRI_FFT_LIMIT) return sqrispec_fft(a,na);
  i=(na>>1); n0=na-i; na=i;
  av=avma; a0=a+na; n0a=n0;
  while (n0a && !*a0) { a0++; n0a--; }
  c = sqrispec(a,na);
  if (n0a)
  {
    GEN t, c1, c0 = sqrispec(a0,n0a);
#if 0
    c1 = shifti(muliispec(a0,a, n0a,na),1);
#else /* faster */
    t = addiispec(a0,a,n0a,na);
    t = sqrispec(LIMBS(t),NLIMBS(t));
    c1= addiispec(LIMBS(c0),LIMBS(c), NLIMBS(c0), NLIMBS(c));
    c1= subiispec(LIMBS(t),LIMBS(c1), NLIMBS(t), NLIMBS(c1));
#endif
    c = addshiftw(c,c1, n0);
    c = addshiftw(c,c0, n0);
  }
  else
    c = addshiftw(c,gen_0,n0<<1);
  return gerepileuptoint(av, c);
}

/********************************************************************/
/**                                                                **/
/**                    KARATSUBA SQUARE ROOT                       **/
/**      adapted from Paul Zimmermann's implementation of          **/
/**      his algorithm in GMP (mpn_sqrtrem)                        **/
/**                                                                **/
/********************************************************************/

/* Square roots table */
static const unsigned char approx_tab[192] = {
  128,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,
  143,144,144,145,146,147,148,149,150,150,151,152,153,154,155,155,
  156,157,158,159,160,160,161,162,163,163,164,165,166,167,167,168,
  169,170,170,171,172,173,173,174,175,176,176,177,178,178,179,180,
  181,181,182,183,183,184,185,185,186,187,187,188,189,189,190,191,
  192,192,193,193,194,195,195,196,197,197,198,199,199,200,201,201,
  202,203,203,204,204,205,206,206,207,208,208,209,209,210,211,211,
  212,212,213,214,214,215,215,216,217,217,218,218,219,219,220,221,
  221,222,222,223,224,224,225,225,226,226,227,227,228,229,229,230,
  230,231,231,232,232,233,234,234,235,235,236,236,237,237,238,238,
  239,240,240,241,241,242,242,243,243,244,244,245,245,246,246,247,
  247,248,248,249,249,250,250,251,251,252,252,253,253,254,254,255
};

/* N[0], assume N[0] >= 2^(BIL-2).
 * Return r,s such that s^2 + r = N, 0 <= r <= 2s */
static void
p_sqrtu1(ulong *N, ulong *ps, ulong *pr)
{
  ulong prec, r, s, q, u, n0 = N[0];

  q = n0 >> (BITS_IN_LONG - 8);
  /* 2^6 = 64 <= q < 256 = 2^8 */
  s = approx_tab[q - 64];                                /* 128 <= s < 255 */
  r = (n0 >> (BITS_IN_LONG - 16)) - s * s;                /* r <= 2*s */
  if (r > (s << 1)) { r -= (s << 1) | 1; s++; }

  /* 8-bit approximation from the high 8-bits of N[0] */
  prec = 8;
  n0 <<= 2 * prec;
  while (2 * prec < BITS_IN_LONG)
  { /* invariant: s has prec bits, and r <= 2*s */
    r = (r << prec) + (n0 >> (BITS_IN_LONG - prec));
    n0 <<= prec;
    u = 2 * s;
    q = r / u; u = r - q * u;
    s = (s << prec) + q;
    u = (u << prec) + (n0 >> (BITS_IN_LONG - prec));
    q = q * q;
    r = u - q;
    if (u < q) { s--; r += (s << 1) | 1; }
    n0 <<= prec;
    prec = 2 * prec;
  }
  *ps = s;
  *pr = r;
}

/* N[0..1], assume N[0] >= 2^(BIL-2).
 * Return 1 if remainder overflows, 0 otherwise */
static int
p_sqrtu2(ulong *N, ulong *ps, ulong *pr)
{
  ulong cc, qhl, r, s, q, u, n1 = N[1];
  LOCAL_OVERFLOW;

  p_sqrtu1(N, &s, &r); /* r <= 2s */
  qhl = 0; while (r >= s) { qhl++; r -= s; }
  /* now r < s < 2^(BIL/2) */
  r = (r << BITS_IN_HALFULONG) | (n1 >> BITS_IN_HALFULONG);
  u = s << 1;
  q = r / u; u = r - q * u;
  q += (qhl & 1) << (BITS_IN_HALFULONG - 1);
  qhl >>= 1;
  /* (initial r)<<(BIL/2) + n1>>(BIL/2) = (qhl<<(BIL/2) + q) * 2s + u */
  s = ((s + qhl) << BITS_IN_HALFULONG) + q;
  cc = u >> BITS_IN_HALFULONG;
  r = (u << BITS_IN_HALFULONG) | (n1 & LOWMASK);
  r = subll(r, q * q);
  cc -= overflow + qhl;
  /* now subtract 2*q*2^(BIL/2) + 2^BIL if qhl is set */
  if ((pari_long)cc < 0)
  {
    if (s) {
      r = addll(r, s);
      cc += overflow;
      s--;
    } else {
      cc++;
      s = ~0ULL;
    }
    r = addll(r, s);
    cc += overflow;
  }
  *ps = s;
  *pr = r; return (int)cc;
}

static void
xmpn_zero(GEN x, pari_long n)
{
  while (--n >= 0) x[n]=0;
}
static void
xmpn_copy(GEN z, GEN x, pari_long n)
{
  pari_long k = n;
  while (--k >= 0) z[k] = x[k];
}
/* a[0..la-1] * 2^(lb BIL) | b[0..lb-1] */
static GEN
catii(GEN a, pari_long la, GEN b, pari_long lb)
{
  pari_long l = la + lb + 2;
  GEN z = cgetipos(l);
  xmpn_copy(LIMBS(z), a, la);
  xmpn_copy(LIMBS(z) + la, b, lb);
  return int_normalize(z, 0);
}

/* sqrt n[0..1], assume n normalized */
static GEN
sqrtispec2(GEN n, GEN *pr)
{
  ulong s, r;
  int hi = p_sqrtu2((ulong*)n, &s, &r);
  GEN S = utoi(s);
  *pr = hi? uutoi(1,r): utoi(r);
  return S;
}

/* sqrt n[0], _dont_ assume n normalized */
static GEN
sqrtispec1_sh(GEN n, GEN *pr)
{
  GEN S;
  ulong r, s, u0 = (ulong)n[0];
  int sh = (int)(bfffo(u0) & ~1ULL);
  if (sh) u0 <<= sh;
  p_sqrtu1(&u0, &s, &r);
  /* s^2 + r = u0, s < 2^(BIL/2). Rescale back:
   * 2^(2k) n = S^2 + R
   * so 2^(2k) n = (S - s0)^2 + (2*S*s0 - s0^2 + R), s0 = S mod 2^k. */
  if (sh) {
    int k = sh >> 1;
    ulong s0 = s & ((1LL<<k) - 1);
    r += s * (s0<<1);
    s >>= k;
    r >>= sh;
  }
  S = utoi(s);
  if (pr) *pr = utoi(r);
  return S;
}

/* sqrt n[0..1], _dont_ assume n normalized */
static GEN
sqrtispec2_sh(GEN n, GEN *pr)
{
  GEN S;
  ulong U[2], r, s, u0 = (ulong)n[0], u1 = (ulong)n[1];
  int hi, sh = (int)(bfffo(u0) & ~1ULL);
  if (sh) {
    u0 = (u0 << sh) | (u1 >> (BITS_IN_LONG-sh));
    u1 <<= sh;
  }
  U[0] = u0;
  U[1] = u1; hi = p_sqrtu2(U, &s, &r);
  /* s^2 + R = u0|u1. Rescale back:
   * 2^(2k) n = S^2 + R
   * so 2^(2k) n = (S - s0)^2 + (2*S*s0 - s0^2 + R), s0 = S mod 2^k. */
  if (sh) {
    int k = sh >> 1;
    ulong s0 = s & ((1LL<<k) - 1);
    LOCAL_HIREMAINDER;
    LOCAL_OVERFLOW;
    r = addll(r, mulll(s, (s0<<1)));
    if (overflow) hiremainder++;
    hiremainder += hi; /* + 0 or 1 */
    s >>= k;
    r = (r>>sh) | (hiremainder << (BITS_IN_LONG-sh));
    hi = (int)(hiremainder & (1LL<<sh));
  }
  S = utoi(s);
  if (pr) *pr = hi? uutoi(1,r): utoi(r);
  return S;
}

/* Let N = N[0..2n-1]. Return S (and set R) s.t S^2 + R = N, 0 <= R <= 2S
 * Assume N normalized */
static GEN
sqrtispec(GEN N, pari_long n, GEN *r)
{
  GEN S, R, q, z, u;
  pari_long l, h;

  if (n == 1) return sqrtispec2(N, r);
  l = n >> 1;
  h = n - l; /* N = a3(h) | a2(h) | a1(l) | a0(l words) */
  S = sqrtispec(N, h, &R); /* S^2 + R = a3|a2 */

  z = catii(LIMBS(R), NLIMBS(R), N + 2*h, l); /* = R | a1(l) */
  q = dvmdii(z, shifti(S,1), &u);
  z = catii(LIMBS(u), NLIMBS(u), N + n + h, l); /* = u | a0(l) */

  S = addshiftw(S, q, l);
  R = subii(z, sqri(q));
  if (signe(R) < 0)
  {
    GEN S2 = shifti(S,1);
    R = addis(subiispec(LIMBS(S2),LIMBS(R), NLIMBS(S2),NLIMBS(R)), -1);
    S = addis(S, -1);
  }
  *r = R; return S;
}

/* Return S (and set R) s.t S^2 + R = N, 0 <= R <= 2S.
 * As for dvmdii, R is last on stack and guaranteed to be gen_0 in case the
 * remainder is 0. R = NULL is allowed. */
GEN
sqrtremi(GEN N, GEN *r)
{
  pari_sp av;
  GEN S, R, n = N+2;
  pari_long k, l2, ln = NLIMBS(N);
  int sh;

  if (ln <= 2)
  {
    if (ln == 2) return sqrtispec2_sh(n, r);
    if (ln == 1) return sqrtispec1_sh(n, r);
    if (r) *r = gen_0;
    return gen_0;
  }
  av = avma;
  sh = (int)(bfffo(n[0]) >> 1);
  l2 = (ln + 1) >> 1;
  if (sh || (ln & 1)) { /* normalize n, so that n[0] >= 2^BIL / 4 */
    GEN s0, t = new_chunk(ln + 1);
    t[ln] = 0;
    if (sh)
      shift_left(t, n, 0,ln-1, 0, sh << 1);
    else
      xmpn_copy(t, n, ln);
    S = sqrtispec(t, l2, &R); /* t normalized, 2 * l2 words */
    /* Rescale back:
     * 2^(2k) n = S^2 + R, k = sh + (ln & 1)*BIL/2
     * so 2^(2k) n = (S - s0)^2 + (2*S*s0 - s0^2 + R), s0 = S mod 2^k. */
    k = sh + (ln & 1) * (BITS_IN_LONG/2);
    s0 = remi2n(S, k);
    R = addii(shifti(R,-1), mulii(s0, S));
    R = shifti(R, 1 - (k<<1));
    S = shifti(S, -k);
  }
  else
    S = sqrtispec(n, l2, &R);

  if (!r) { avma = (pari_sp)S; return gerepileuptoint(av, S); }
  gerepileall(av, 2, &S, &R); *r = R; return S;
}

/* compute sqrt(|a|), assuming a != 0 */

#if 1
GEN
sqrtr_abs(GEN x)
{
  pari_long l = lg(x) - 2, e = expo(x), er = e>>1;
  GEN b, c, res = cgetr(2 + l);
  res[1] = evalsigne(1) | evalexpo(er);
  if (e&1) {
    b = new_chunk(l << 1);
    xmpn_copy(b, x+2, l);
    xmpn_zero(b + l,l);
    b = sqrtispec(b, l, &c);
    xmpn_copy(res+2, b+2, l);
    if (cmpii(c, b) > 0) roundr_up_ip(res, l+2);
  } else {
    ulong u;
    b = new_chunk(2 + (l << 1));
    shift_left(b+1, x+2, 0,l-1, 0, BITS_IN_LONG-1);
    b[0] = ((ulong)x[2])>>1;
    xmpn_zero(b + l+1,l+1);
    b = sqrtispec(b, l+1, &c);
    xmpn_copy(res+2, b+2, l);
    u = (ulong)b[l+2];
    if ( u&HIGHBIT || (u == ~HIGHBIT && cmpii(c,b) > 0))
      roundr_up_ip(res, l+2);
  }
  avma = (pari_sp)res; return res;
}

#else /* use t_REAL: currently much slower (quadratic division) */

#ifdef LONG_IS_64BIT
/* 64 bits of b = sqrt(a[0] * 2^64 + a[1])  [ up to 1ulp ] */
static ulong
sqrtu2(ulong *a)
{
  ulong c, b = dblmantissa( sqrt((double)a[0]) );
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;

  /* > 32 correct bits, 1 Newton iteration to reach 64 */
  if (b <= a[0]) return HIGHBIT | (a[0] >> 1);
  hiremainder = a[0]; c = divll(a[1], b);
  return (addll(c, b) >> 1) | HIGHBIT;
}
/* 64 bits of sqrt(a[0] * 2^63) */
static ulong
sqrtu2_1(ulong *a)
{
  ulong t[2];
  t[0] = (a[0] >> 1);
  t[1] = (a[0] << (BITS_IN_LONG-1)) | (a[1] >> 1);
  return sqrtu2(t);
}
#else
/* 32 bits of sqrt(a[0] * 2^32) */
static ulong
sqrtu2(ulong *a)   { return dblmantissa( sqrt((double)a[0]) ); }
/* 32 bits of sqrt(a[0] * 2^31) */
static ulong
sqrtu2_1(ulong *a) { return dblmantissa( sqrt(2. * a[0]) ); }
#endif

GEN
sqrtr_abs(GEN x)
{
  pari_long l1, i, l = lg(x), ex = expo(x);
  GEN a, t, y = cgetr(l);
  pari_sp av, av0 = avma;

  a = rtor(x, l+1);
  t = cgetr(l+1);
  if (ex & 1) { /* odd exponent */
    a[1] = evalsigne(1) | _evalexpo(1);
    t[2] = (pari_long)sqrtu2((ulong*)a + 2);
  } else { /* even exponent */
    a[1] = evalsigne(1) | _evalexpo(0);
    t[2] = (pari_long)sqrtu2_1((ulong*)a + 2);
  }
  t[1] = evalsigne(1) | _evalexpo(0);
  for (i = 3; i <= l; i++) t[i] = 0;

  /* |x| = 2^(ex/2) a, t ~ sqrt(a) */
  l--; l1 = 1; av = avma;
  while (l1 < l) { /* let t := (t + a/t)/2 */
    l1 <<= 1; if (l1 > l) l1 = l;
    setlg(a, l1 + 2);
    setlg(t, l1 + 2);
    affrr(addrr(t, divrr(a,t)), t); shiftr_inplace(t, -1);
    avma = av;
  }
  affrr(t,y); shiftr_inplace(y, (ex>>1));
  avma = av0; return y;
}

#endif

/*******************************************************************
 *                                                                 *
 *                           Base Conversion                       *
 *                                                                 *
 *******************************************************************/

static void
convi_dac(GEN x, ulong l, ulong *res)
{
  pari_sp ltop=avma;
  ulong m;
  GEN x1,x2;
  if (l==1) { *res=itou(x); return; }
  m=l>>1;
  x1=dvmdii(x,powuu(1000000000ULL,m),&x2);
  convi_dac(x1,l-m,res+m);
  convi_dac(x2,m,res);
  avma=ltop;
}

/* convert integer --> base 10^9 [not memory clean] */
ulong *
convi(GEN x, pari_long *l)
{
  pari_long lz, lx = lgefint(x);
  ulong *z;
  if (lx == 3 && (ulong)x[2] < 1000000000ULL) {
    z = (ulong*)new_chunk(1);
    *z = x[2];
    *l = 1; return z+1;
  }
  lz = 1 + (pari_long)bit_accuracy_mul(lx, LOG10_2/9);
  z = (ulong*)new_chunk(lz);
  convi_dac(x,(ulong)lz,z);
  while (z[lz-1]==0) lz--;
  *l=lz; return z+lz;
}

#line 2 "../src/kernel/none/cmp.c"
/* Copyright (C) 2002-2003  The PARI group.

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
/**                      Comparison routines                       **/
/**                                                                **/
/********************************************************************/

/*They depend on cmpiispec and equaliispec in mp.c*/

int
equalii(GEN x, GEN y)
{
  if ((x[1] & (LGBITS|SIGNBITS)) != (y[1] & (LGBITS|SIGNBITS))) return 0;
  return equaliispec(x+2, y+2, lgefint(x)-2, lgefint(y)-2);
}

int
cmpii(GEN x, GEN y)
{
  const pari_long sx = signe(x), sy = signe(y);
  if (sx<sy) return -1;
  if (sx>sy) return 1;
  if (!sx) return 0;
  if (sx>0)
    return cmpiispec(x+2, y+2, lgefint(x)-2, lgefint(y)-2);
  else
    return -cmpiispec(x+2, y+2, lgefint(x)-2, lgefint(y)-2);
}

int
equalrr(GEN x, GEN y)
{
  pari_long lx, ly, i;

  if (!signe(x)) return signe(y) == 0; /* all zeroes are equal */
  if (x[1] != y[1]) return 0; /* includes signe(y) = 0 */

  lx = lg(x);
  ly = lg(y);
  if (lx < ly)
  {
    i=2; while (i<lx && x[i]==y[i]) i++;
    if (i<lx) return 0;
    for (; i < ly; i++) if (y[i]) return 0;
  }
  else
  {
    i=2; while (i<ly && x[i]==y[i]) i++;
    if (i<ly) return 0;
    for (; i < lx; i++) if (x[i]) return 0;
  }
  return 1;
}

int
cmprr(GEN x, GEN y)
{
  const int sx = signe(x), sy = signe(y);
  pari_long ex,ey,lx,ly,lz,i;

  if (sx<sy) return -1;
  if (sx>sy) return 1;
  if (!sx) return 0;

  ex=expo(x); ey=expo(y);
  if (ex>ey) return sx;
  if (ex<ey) return -sx;

  lx=lg(x); ly=lg(y); lz = (lx<ly)?lx:ly;
  i=2; while (i<lz && x[i]==y[i]) i++;
  if (i<lz) return ((ulong)x[i] > (ulong)y[i]) ? sx : -sx;
  if (lx>=ly)
  {
    while (i<lx && !x[i]) i++;
    return (i==lx) ? 0 : sx;
  }
  while (i<ly && !y[i]) i++;
  return (i==ly) ? 0 : -sx;
}

/* x and y are integers. Return 1 if |x| == |y|, 0 otherwise */
int
absi_equal(GEN x, GEN y)
{
  if (!signe(x)) return !signe(y);
  if (!signe(y)) return 0;
  return equaliispec(x+2, y+2, lgefint(x)-2, lgefint(y)-2);
}

/* x and y are integers. Return sign(|x| - |y|) */
int
absi_cmp(GEN x, GEN y)
{
  if (!signe(x)) return signe(y)? -1: 0;
  if (!signe(y)) return 1;
  return cmpiispec(x+2, y+2, lgefint(x)-2, lgefint(y)-2);
}

/* x and y are reals. Return sign(|x| - |y|) */
int
absr_cmp(GEN x, GEN y)
{
  pari_long ex,ey,lx,ly,lz,i;

  if (!signe(x)) return signe(y)? -1: 0;
  if (!signe(y)) return 1;

  ex=expo(x); ey=expo(y);
  if (ex>ey) return  1;
  if (ex<ey) return -1;

  lx=lg(x); ly=lg(y); lz = (lx<ly)?lx:ly;
  i=2; while (i<lz && x[i]==y[i]) i++;
  if (i<lz) return ((ulong)x[i] > (ulong)y[i])? 1: -1;
  if (lx>=ly)
  {
    while (i<lx && !x[i]) i++;
    return (i==lx)? 0: 1;
  }
  while (i<ly && !y[i]) i++;
  return (i==ly)? 0: -1;
}

#line 2 "../src/kernel/none/gcdll.c"
/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/***********************************************************************/
/**                                                                   **/
/**                          GCD                                      **/
/**                                                                   **/
/***********************************************************************/
/* Fast ulong gcd.  Called with y odd; x can be arbitrary (but will most of
 * the time be smaller than y). */

/* Gotos are Harmful, and Programming is a Science.  E.W.Dijkstra. */
ulong
gcduodd(ulong x, ulong y)         /* assume y&1==1, y > 1 */
{
  if (!x) return y;
  /* fix up x */
  while (!(x&1)) x>>=1;
  if (x==1) return 1;
  if (x==y) return y;
  else if (x>y) goto xislarger;/* will be rare, given how we'll use this */
  /* loop invariants: x,y odd and distinct. */
 yislarger:
  if ((x^y)&2)                 /* ...01, ...11 or vice versa */
    y=(x>>2)+(y>>2)+1;         /* ==(x+y)>>2 except it can't overflow */
  else                         /* ...01,...01 or ...11,...11 */
    y=(y-x)>>2;                /* now y!=0 in either case */
  while (!(y&1)) y>>=1;        /* kill any windfall-gained powers of 2 */
  if (y==1) return 1;          /* comparand == return value... */
  if (x==y) return y;          /* this and the next is just one comparison */
  else if (x<y) goto yislarger;/* else fall through to xislarger */

 xislarger:                    /* same as above, seen through a mirror */
  if ((x^y)&2)
    x=(x>>2)+(y>>2)+1;
  else
    x=(x-y)>>2;                /* x!=0 */
  while (!(x&1)) x>>=1;
  if (x==1) return 1;
  if (x==y) return y;
  else if (x>y) goto xislarger;

  goto yislarger;
}
/* Gotos are useful, and Programming is an Art.  D.E.Knuth. */
/* PS: Of course written with Dijkstra's lessons firmly in mind... --GN */

/* at least one of a or b is odd, return gcd(a,b) */
INLINE ulong
mygcduodd(ulong a, ulong b)
{
  ulong c;
  if (b&1)
  {
    if (a==1 || b==1)
      c = 1;
    else
     c = gcduodd(a, b);
  }
  else
  {
    if (a==1)
      c = 1;
    else
      c = gcduodd(b, a);
  }
  return c;
}

/* modified right shift binary algorithm with at most one division */
pari_long
cgcd(pari_long a, pari_long b)
{
  pari_long v;
#ifdef MINGW64
  a=llabs(a); if (!b) return a;
  b=llabs(b); if (!a) return b;
#else
  a=labs(a); if (!b) return a;
  b=labs(b); if (!a) return b;
#endif

  if (a>b) { a %= b; if (!a) return b; }
  else     { b %= a; if (!b) return a; }
  v = vals(a|b);
  return (pari_long)(mygcduodd((ulong)(a>>v), (ulong)(b>>v)) << v);
}
ulong
ugcd(ulong a,ulong b)
{
  pari_long v;
  if (!b) return a;
  if (!a) return b;
  if (a>b) { a %= b; if (!a) return b; }
  else     { b %= a; if (!b) return a; }
  v = vals(a|b);
  return mygcduodd(a>>v, b>>v) << v;
}

/* For gcdii(): assume a>b>0, return gcd(a,b) as a GEN */
static GEN
igcduu(ulong a, ulong b)
{
  pari_long v;
  a %= b; if (!a) return utoipos(b);
  v = vals(a|b);
  return utoipos( mygcduodd(a>>v, b>>v) << v );
}

/*Warning: overflows silently if lcm does not fit*/
pari_long
clcm(pari_long a, pari_long b)
{
  pari_long d = cgcd(a,b);
  if (!d) return 0;
  return d == 1? a*b: a*(b/d);
}

/********************************************************************/
/**                                                                **/
/**               INTEGER EXTENDED GCD  (AND INVMOD)               **/
/**                                                                **/
/********************************************************************/

/* GN 1998Oct25, originally developed in January 1998 under 2.0.4.alpha,
 * in the context of trying to improve elliptic curve cryptosystem attacking
 * algorithms.  2001Jan02 -- added bezout() functionality.
 *
 * Two basic ideas - (1) avoid many integer divisions, especially when the
 * quotient is 1 (which happens more than 40% of the time).  (2) Use Lehmer's
 * trick as modified by Jebelean of extracting a couple of words' worth of
 * leading bits from both operands, and compute partial quotients from them
 * as long as we can be sure of their values.  The Jebelean modifications
 * consist in reliable inequalities from which we can decide fast whether
 * to carry on or to return to the outer loop, and in re-shifting after the
 * first word's worth of bits has been used up.  All of this is described
 * in R. Lercier's these [pp148-153 & 163f.], except his outer loop isn't
 * quite right  (the catch-up divisions needed when one partial quotient is
 * larger than a word are missing).
 *
 * The API consists of invmod() and bezout() below;  the single-word routines
 * xgcduu and xxgcduu may be called directly if desired;  lgcdii() probably
 * doesn't make much sense out of context.
 *
 * The whole lot is a factor 6 .. 8 faster on word-sized operands, and asym-
 * ptotically about a factor 2.5 .. 3, depending on processor architecture,
 * than the naive continued-division code.  Unfortunately, thanks to the
 * unrolled loops and all, the code is a bit lengthy.
 */

/*==================================
 * xgcduu(d,d1,f,v,v1,s)
 * xxgcduu(d,d1,f,u,u1,v,v1,s)
 * rgcduu(d,d1,vmax,u,u1,v,v1,s)
 *==================================*/
/*
 * Fast `final' extended gcd algorithm, acting on two ulongs.  Ideally this
 * should be replaced with assembler versions wherever possible.  The present
 * code essentially does `subtract, compare, and possibly divide' at each step,
 * which is reasonable when hardware division (a) exists, (b) is a bit slowish
 * and (c) does not depend a lot on the operand values (as on i486).  When
 * wordsize division is in fact an assembler routine based on subtraction,
 * this strategy may not be the most efficient one.
 *
 * xxgcduu() should be called with  d > d1 > 0, returns gcd(d,d1), and assigns
 * the usual signless cont.frac. recurrence matrix to [u, u1; v, v1]  (i.e.,
 * the product of all the [0, 1; 1 q_j] where the leftmost factor arises from
 * the quotient of the first division step),  and the information about the
 * implied signs to s  (-1 when an odd number of divisions has been done,
 * 1 otherwise).  xgcduu() is exactly the same except that u,u1 are not com-
 * puted (and not returned, of course).
 *
 * The input flag f should be set to 1 if we know in advance that gcd(d,d1)==1
 * (so we can stop the chain division one step early:  as soon as the remainder
 * equals 1).  Use this when you intend to use only what would be v, or only
 * what would be u and v, after that final division step, but not u1 and v1.
 * With the flag in force and thus without that final step, the interesting
 * quantity/ies will still sit in [u1 and] v1, of course.
 *
 * For computing the inverse of a single-word INTMOD known to exist, pass f=1
 * to xgcduu(), and obtain the result from s and v1.  (The routine does the
 * right thing when d1==1 already.)  For finishing a multiword modinv known
 * to exist, pass f=1 to xxgcduu(), and multiply the returned matrix  (with
 * properly adjusted signs)  onto the values v' and v1' previously obtained
 * from the multiword division steps.  Actually, just take the scalar product
 * of [v',v1'] with [u1,-v1], and change the sign if s==-1.  (If the final
 * step had been carried out, it would be [-u,v], and s would also change.)
 * For reducing a rational number to lowest terms, pass f=0 to xgcduu().
 * Finally, f=0 with xxgcduu() is useful for Bezout computations.
 * [Harrumph.  In the above prescription, the sign turns out to be precisely
 * wrong.]
 * (It is safe for invmod() to call xgcduu() with f=1, because f&1 doesn't
 * make a difference when gcd(d,d1)>1.  The speedup is negligible.)
 *
 * In principle, when gcd(d,d1) is known to be 1, it is straightforward to
 * recover the final u,u1 given only v,v1 and s.  However, it probably isn't
 * worthwhile, as it trades a few multiplications for a division.
 *
 * Note that these routines do not know and do not need to know about the
 * PARI stack.
 *
 * Added 2001Jan15:
 * rgcduu() is a variant of xxgcduu() which does not have f  (the effect is
 * that of f=0),  but instead has a ulong vmax parameter, for use in rational
 * reconstruction below.  It returns when v1 exceeds vmax;  v will never
 * exceed vmax.  (vmax=0 is taken as a synonym of ULONG_MAX i.e. unlimited,
 * in which case rgcduu behaves exactly like xxgcduu with f=0.)  The return
 * value of rgcduu() is typically meaningless;  the interesting part is the
 * matrix.
 */

ulong
xgcduu(ulong d, ulong d1, int f, ulong* v, ulong* v1, pari_long *s)
{
  ulong xv,xv1, xs, q,res;
  LOCAL_HIREMAINDER;

  /* The above blurb contained a lie.  The main loop always stops when d1
   * has become equal to 1.  If (d1 == 1 && !(f&1)) after the loop, we do
   * the final `division' of d by 1 `by hand' as it were.
   *
   * The loop has already been unrolled once.  Aggressive optimization could
   * well lead to a totally unrolled assembler version...
   *
   * On modern x86 architectures, this loop is a pig anyway.  The division
   * instruction always puts its result into the same pair of registers, and
   * we always want to use one of them straight away, so pipeline performance
   * will suck big time.  An assembler version should probably do a first loop
   * computing and storing all the quotients -- their number is bounded in
   * advance -- and then assembling the matrix in a second pass.  On other
   * architectures where we can cycle through four or so groups of registers
   * and exploit a fast ALU result-to-operand feedback path, this is much less
   * of an issue.  (Intel sucks.  See http://www.x86.org/ ...)
   */
  xs = res = 0;
  xv = 0ULL; xv1 = 1ULL;
  while (d1 > 1ULL)
  {
    d -= d1;                        /* no need to use subll */
    if (d >= d1)
    {
      hiremainder = 0; q = 1 + divll(d,d1); d = hiremainder;
      xv += q * xv1;
    }
    else
      xv += xv1;
                                /* possible loop exit */
    if (d <= 1ULL) { xs=1; break; }
                                /* repeat with inverted roles */
    d1 -= d;
    if (d1 >= d)
    {
      hiremainder = 0; q = 1 + divll(d1,d); d1 = hiremainder;
      xv1 += q * xv;
    }
    else
      xv1 += xv;
  } /* while */

  if (!(f&1))                        /* division by 1 postprocessing if needed */
  {
    if (xs && d==1)
    { xv1 += d1 * xv; xs = 0; res = 1ULL; }
    else if (!xs && d1==1)
    { xv += d * xv1; xs = 1; res = 1ULL; }
  }

  if (xs)
  {
    *s = -1; *v = xv1; *v1 = xv;
    return (res ? res : (d==1 ? 1ULL : d1));
  }
  else
  {
    *s = 1; *v = xv; *v1 = xv1;
    return (res ? res : (d1==1 ? 1ULL : d));
  }
}


ulong
xxgcduu(ulong d, ulong d1, int f,
        ulong* u, ulong* u1, ulong* v, ulong* v1, pari_long *s)
{
  ulong xu,xu1, xv,xv1, xs, q,res;
  LOCAL_HIREMAINDER;

  xs = res = 0;
  xu = xv1 = 1ULL;
  xu1 = xv = 0ULL;
  while (d1 > 1ULL)
  {
    d -= d1;                        /* no need to use subll */
    if (d >= d1)
    {
      hiremainder = 0; q = 1 + divll(d,d1); d = hiremainder;
      xv += q * xv1;
      xu += q * xu1;
    }
    else
    { xv += xv1; xu += xu1; }
                                /* possible loop exit */
    if (d <= 1ULL) { xs=1; break; }
                                /* repeat with inverted roles */
    d1 -= d;
    if (d1 >= d)
    {
      hiremainder = 0; q = 1 + divll(d1,d); d1 = hiremainder;
      xv1 += q * xv;
      xu1 += q * xu;
    }
    else
    { xv1 += xv; xu1 += xu; }
  } /* while */

  if (!(f&1))                        /* division by 1 postprocessing if needed */
  {
    if (xs && d==1)
    {
      xv1 += d1 * xv;
      xu1 += d1 * xu;
      xs = 0; res = 1ULL;
    }
    else if (!xs && d1==1)
    {
      xv += d * xv1;
      xu += d * xu1;
      xs = 1; res = 1ULL;
    }
  }

  if (xs)
  {
    *s = -1; *u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
    return (res ? res : (d==1 ? 1ULL : d1));
  }
  else
  {
    *s = 1; *u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
    return (res ? res : (d1==1 ? 1ULL : d));
  }
}

ulong
rgcduu(ulong d, ulong d1, ulong vmax,
       ulong* u, ulong* u1, ulong* v, ulong* v1, pari_long *s)
{
  ulong xu,xu1, xv,xv1, xs, q, res=0;
  int f = 0;
  LOCAL_HIREMAINDER;

  if (vmax == 0) vmax = ULONG_MAX;
  xs = res = 0;
  xu = xv1 = 1ULL;
  xu1 = xv = 0ULL;
  while (d1 > 1ULL)
  {
    d -= d1;                        /* no need to use subll */
    if (d >= d1)
    {
      hiremainder = 0; q = 1 + divll(d,d1); d = hiremainder;
      xv += q * xv1;
      xu += q * xu1;
    }
    else
    { xv += xv1; xu += xu1; }
                                /* possible loop exit */
    if (xv > vmax) { f=xs=1; break; }
    if (d <= 1ULL) { xs=1; break; }
                                /* repeat with inverted roles */
    d1 -= d;
    if (d1 >= d)
    {
      hiremainder = 0; q = 1 + divll(d1,d); d1 = hiremainder;
      xv1 += q * xv;
      xu1 += q * xu;
    }
    else
    { xv1 += xv; xu1 += xu; }
                                /* possible loop exit */
    if (xv1 > vmax) { f=1; break; }
  } /* while */


  if (!(f&1))                        /* division by 1 postprocessing if needed */
  {
    if (xs && d==1)
    {
      xv1 += d1 * xv;
      xu1 += d1 * xu;
      xs = 0; res = 1ULL;
    }
    else if (!xs && d1==1)
    {
      xv += d * xv1;
      xu += d * xu1;
      xs = 1; res = 1ULL;
    }
  }

  if (xs)
  {
    *s = -1; *u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
    return (res ? res : (d==1 ? 1ULL : d1));
  }
  else
  {
    *s = 1; *u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
    return (res ? res : (d1==1 ? 1ULL : d));
  }
}

/*==================================
 * cbezout(a,b,uu,vv)
 *==================================
 * Same as bezout() but for C pari_longs.
 *    Return g = gcd(a,b) >= 0, and assign pari_longs u,v through pointers uu,vv
 *    such that g = u*a + v*b.
 * Special cases:
 *    a == b == 0 ==> pick u=1, v=0 (and return 1, surprisingly)
 *    a != 0 == b ==> keep v=0
 *    a == 0 != b ==> keep u=0
 *    |a| == |b| != 0 ==> keep u=0, set v=+-1
 * Assignments through uu,vv happen unconditionally;  non-NULL pointers
 * _must_ be used.
 */
pari_long
cbezout(pari_long a, pari_long b, pari_long *uu, pari_long *vv)
{
  pari_long s,*t;
#ifdef MINGW64
  ulong d = llabs(a), d1 = llabs(b);
#else
  ulong d = labs(a), d1 = labs(b);
#endif
  ulong r,u,u1,v,v1;

#ifdef DEBUG_CBEZOUT
  err_printf("> cbezout(%ld,%ld,%p,%p)\n", a, b, (void *)uu, (void *)vv);
#endif
  if (!b)
  {
    *vv=0LL;
    if (!a)
    {
      *uu=1LL;
#ifdef DEBUG_CBEZOUT
      err_printf("< %ld (%ld, %ld)\n", 1LL, *uu, *vv);
#endif
      return 0LL;
    }
    *uu = a < 0 ? -1LL : 1LL;
#ifdef DEBUG_CBEZOUT
    err_printf("< %ld (%ld, %ld)\n", (pari_long)d, *uu, *vv);
#endif
    return (pari_long)d;
  }
  else if (!a || (d == d1))
  {
    *uu = 0LL; *vv = b < 0 ? -1LL : 1LL;
#ifdef DEBUG_CBEZOUT
    err_printf("< %ld (%ld, %ld)\n", (pari_long)d1, *uu, *vv);
#endif
    return (pari_long)d1;
  }
  else if (d == 1)                /* frequently used by nfinit */
  {
    *uu = a; *vv = 0LL;
#ifdef DEBUG_CBEZOUT
    err_printf("< %ld (%ld, %ld)\n", 1LL, *uu, *vv);
#endif
    return 1LL;
  }
  else if (d < d1)
  {
/* bug in gcc-2.95.3:
 * s = a; a = b; b = s; produces wrong result a = b. This is OK:  */
    { pari_long _x = a; a = b; b = _x; }        /* in order to keep the right signs */
    r = d; d = d1; d1 = r;
    t = uu; uu = vv; vv = t;
#ifdef DEBUG_CBEZOUT
    err_printf("  swapping\n");
#endif
  }
  /* d > d1 > 0 */
  r = xxgcduu(d, d1, 0, &u, &u1, &v, &v1, &s);
  if (s < 0)
  {
    *uu = a < 0 ? (pari_long)u : -(pari_long)u;
    *vv = b < 0 ? -(pari_long)v : (pari_long)v;
  }
  else
  {
    *uu = a < 0 ? -(pari_long)u : (pari_long)u;
    *vv = b < 0 ? (pari_long)v : -(pari_long)v;
  }
#ifdef DEBUG_CBEZOUT
  err_printf("< %ld (%ld, %ld)\n", (pari_long)r, *uu, *vv);
#endif
  return (pari_long)r;
}

/*==================================
 * lgcdii(d,d1,u,u1,v,v1,vmax)
 *==================================*/
/* Lehmer's partial extended gcd algorithm, acting on two t_INT GENs.
 *
 * Tries to determine, using the leading 2*BITS_IN_LONG significant bits of d
 * and a quantity of bits from d1 obtained by a shift of the same displacement,
 * as many partial quotients of d/d1 as possible, and assigns to [u,u1;v,v1]
 * the product of all the [0, 1; 1, q_j] thus obtained, where the leftmost
 * factor arises from the quotient of the first division step.
 *
 * For use in rational reconstruction, input param vmax can be given a
 * nonzero value.  In this case, we will return early as soon as v1 > vmax
 * (i.e. it is guaranteed that v <= vmax). --2001Jan15
 *
 * MUST be called with  d > d1 > 0, and with  d  occupying more than one
 * significant word  (if it doesn't, the caller has no business with us;
 * he/she/it should use xgcduu() instead).  Returns the number of reduction/
 * swap steps carried out, possibly zero, or under certain conditions minus
 * that number.  When the return value is nonzero, the caller should use the
 * returned recurrence matrix to update its own copies of d,d1.  When the
 * return value is non-positive, and the latest remainder after updating
 * turns out to be nonzero, the caller should at once attempt a full division,
 * rather than first trying lgcdii() again -- this typically happens when we
 * are about to encounter a quotient larger than half a word.  (This is not
 * detected infallibly -- after a positive return value, it is perfectly
 * possible that the next stage will end up needing a full division.  After
 * a negative return value, however, this is certain, and should be acted
 * upon.)
 *
 * (The sign information, for which xgcduu() has its return argument s, is now
 * implicit in the LSB of our return value, and the caller may take advantage
 * of the fact that a return value of +-1 implies u==0,u1==v==1  [only v1 pro-
 * vides interesting information in this case].  One might also use the fact
 * that if the return value is +-2, then u==1, but this is rather marginal.)
 *
 * If it was not possible to determine even the first quotient, either because
 * we're too close to an integer quotient or because the quotient would be
 * larger than one word  (if the `leading digit' of d1 after shifting is all
 * zeros),  we return 0 and do not bother to assign anything to the last four
 * args.
 *
 * The division chain might (sometimes) even run to completion.  It will be
 * up to the caller to detect this case.
 *
 * This routine does _not_ change d or d1;  this will also be up to the caller.
 *
 * Note that this routine does not know and does not need to know about the
 * PARI stack.
 */
/*#define DEBUG_LEHMER 1 */
int
lgcdii(ulong* d, ulong* d1,
       ulong* u, ulong* u1, ulong* v, ulong* v1,
       ulong vmax)
{
  /* Strategy:  (1) Extract/shift most significant bits.  We assume that d
   * has at least two significant words, but we can cope with a one-word d1.
   * Let dd,dd1 be the most significant dividend word and matching part of the
   * divisor.
   * (2) Check for overflow on the first division.  For our purposes, this
   * happens when the upper half of dd1 is zero.  (Actually this is detected
   * during extraction.)
   * (3) Get a fix on the first quotient.  We compute q = floor(dd/dd1), which
   * is an upper bound for floor(d/d1), and which gives the true value of the
   * latter if (and-almost-only-if) the remainder dd' = dd-q*dd1 is >= q.
   * (If it isn't, we give up.  This is annoying because the subsequent full
   * division will repeat some work already done, but it happens very infre-
   * quently.  Doing the extra-bit-fetch in this case would be awkward.)
   * (4) Finish initializations.
   *
   * The remainder of the action is comparatively boring... The main loop has
   * been unrolled once  (so we don't swap things and we can apply Jebelean's
   * termination conditions which alternatingly take two different forms during
   * successive iterations).  When we first run out of sufficient bits to form
   * a quotient, and have an extra word of each operand, we pull out two whole
   * word's worth of dividend bits, and divisor bits of matching significance;
   * to these we apply our partial matrix (disregarding overflow because the
   * result mod 2^(2*BITS_IN_LONG) will in fact give the correct values), and
   * re-extract one word's worth of the current dividend and a matching amount
   * of divisor bits.  The affair will normally terminate with matrix entries
   * just short of a whole word.  (We terminate the inner loop before these can
   * possibly overflow.)
   */
  ulong dd,dd1,ddlo,dd1lo, sh,shc;        /* `digits', shift count */
  ulong xu,xu1, xv,xv1, q,res;        /* recurrences, partial quotient, count */
  ulong tmp0,tmp1,tmp2,tmpd,tmpu,tmpv; /* temps */
  ulong dm1,dm2,d1m1,d1m2;
  pari_long ld, ld1, lz;                /* t_INT effective lengths */
  int skip = 0;                        /* a boolean flag */
  LOCAL_OVERFLOW;
  LOCAL_HIREMAINDER;

#ifdef DEBUG_LEHMER
  voir(d, -1); voir(d1, -1);
#endif
  /* following is just for convenience: vmax==0 means no bound */
  if (vmax == 0) vmax = ULONG_MAX;
  ld = lgefint(d); ld1 = lgefint(d1); lz = ld - ld1; /* >= 0 */
  if (lz > 1) return 0;                /* rare, quick and desperate exit */

  d = int_MSW(d); d1 = int_MSW(d1);                /* point at the leading `digits' */
  dm1 = *int_precW(d); d1m1 = *int_precW(d1);
  dm2 = *int_precW(int_precW(d)); d1m2 = *int_precW(int_precW(d1));
  dd1lo = 0;                        /* unless we find something better */
  sh = bfffo(*d);                /* obtain dividend left shift count */

  if (sh)
  {                                /* do the shifting */
    shc = BITS_IN_LONG - sh;
    if (lz)
    {                                /* dividend longer than divisor */
      dd1 = (*d1 >> shc);
      if (!(HIGHMASK & dd1)) return 0;  /* overflow detected */
      if (ld1 > 3)
        dd1lo = (*d1 << sh) + (d1m1 >> shc);
      else
        dd1lo = (*d1 << sh);
    }
    else
    {                                /* dividend and divisor have the same length */
      dd1 = (*d1 << sh);
      if (!(HIGHMASK & dd1)) return 0;
      if (ld1 > 3)
      {
        dd1 += (d1m1 >> shc);
        if (ld1 > 4)
          dd1lo = (d1m1 << sh) + (d1m2 >> shc);
        else
          dd1lo = (d1m1 << sh);
      }
    }
    /* following lines assume d to have 2 or more significant words */
    dd = (*d << sh) + (dm1 >> shc);
    if (ld > 4)
      ddlo = (dm1 << sh) + (dm2 >> shc);
    else
      ddlo = (dm1 << sh);
  }
  else
  {                                /* no shift needed */
    if (lz) return 0;                /* div'd longer than div'r: o'flow automatic */
    dd1 = *d1;
    if (!(HIGHMASK & dd1)) return 0;
    if(ld1 > 3) dd1lo = d1m1;
    /* assume again that d has another significant word */
    dd = *d; ddlo = dm1;
  }
#ifdef DEBUG_LEHMER
  err_printf("  %lx:%lx, %lx:%lx\n", dd, ddlo, dd1, dd1lo);
#endif

  /* First subtraction/division stage.  (If a subtraction initially suffices,
   * we don't divide at all.)  If a Jebelean condition is violated, and we
   * can't fix it even by looking at the low-order bits in ddlo,dd1lo, we
   * give up and ask for a full division.  Otherwise we commit the result,
   * possibly deciding to re-shift immediately afterwards.
   */
  dd -= dd1;
  if (dd < dd1)
  {                                /* first quotient known to be == 1 */
    xv1 = 1ULL;
    if (!dd)                        /* !(Jebelean condition), extraspecial case */
    {                                /* note this can actually happen...  Now
                                     * q==1 is known, but we underflow already.
                                 * OTOH we've just shortened d by a whole word.
                                 * Thus we feel pleased with ourselves and
                                 * return.  (The re-shift code below would
                                 * do so anyway.) */
      *u = 0; *v = *u1 = *v1 = 1ULL;
      return -1;                /* Next step will be a full division. */
    } /* if !(Jebelean) then */
  }
  else
  {                                /* division indicated */
    hiremainder = 0;
    xv1 = 1 + divll(dd, dd1);        /* xv1: alternative spelling of `q', here ;) */
    dd = hiremainder;
    if (dd < xv1)                /* !(Jebelean cond'), non-extra special case */
    {                                /* Attempt to complete the division using the
                                 * less significant bits, before skipping right
                                 * past the 1st loop to the reshift stage. */
      ddlo = subll(ddlo, mulll(xv1, dd1lo));
      dd = subllx(dd, hiremainder);

      /* If we now have an overflow, q was _certainly_ too large.  Thanks to
       * our decision not to get here unless the original dd1 had bits set in
       * the upper half of the word, however, we now do know that the correct
       * quotient is in fact q-1.  Adjust our data accordingly. */
      if (overflow)
      {
        xv1--;
        ddlo = addll(ddlo,dd1lo);
        dd = addllx(dd,dd1);        /* overflows again which cancels the borrow */
        /* ...and fall through to skip=1 below */
      }
      else
      /* Test Jebelean condition anew, at this point using _all_ the extracted
       * bits we have.  This is clutching at straws; we have a more or less
       * even chance of succeeding this time.  Note that if we fail, we really
       * do not know whether the correct quotient would have been q or some
       * smaller value. */
        if (!dd && ddlo < xv1) return 0;

      /* Otherwise, we now know that q is correct, but we cannot go into the
       * 1st loop.  Raise a flag so we'll remember to skip past the loop.
       * Get here also after the q-1 adjustment case. */
      skip = 1;
    } /* if !(Jebelean) then */
  }
  res = 1;
#ifdef DEBUG_LEHMER
  err_printf("  q = %ld, %lx, %lx\n", xv1, dd1, dd);
#endif
  if (xv1 > vmax)
  {                                /* gone past the bound already */
    *u = 0ULL; *u1 = 1ULL; *v = 1ULL; *v1 = xv1;
    return (int)res;
  }
  xu = 0ULL; xv = xu1 = 1ULL;

  /* Some invariants from here across the first loop:
   *
   * At this point, and again after we are finished with the first loop and
   * subsequent conditional, a division and the associated update of the
   * recurrence matrix have just been carried out completely.  The matrix
   * xu,xu1;xv,xv1 has been initialized (or updated, possibly with permuted
   * columns), and the current remainder == next divisor (dd at the moment)
   * is nonzero (it might be zero here, but then skip will have been set).
   *
   * After the first loop, or when skip is set already, it will also be the
   * case that there aren't sufficiently many bits to continue without re-
   * shifting.  If the divisor after reshifting is zero, or indeed if it
   * doesn't have more than half a word's worth of bits, we will have to
   * return at that point.  Otherwise, we proceed into the second loop.
   *
   * Furthermore, when we reach the re-shift stage, dd:ddlo and dd1:dd1lo will
   * already reflect the result of applying the current matrix to the old
   * ddorig:ddlo and dd1orig:dd1lo.  (For the first iteration above, this
   * was easy to achieve, and we didn't even need to peek into the (now
   * no longer existent!) saved words.  After the loop, we'll stop for a
   * moment to merge in the ddlo,dd1lo contributions.)
   *
   * Note that after the first division, even an a priori quotient of 1 cannot
   * be trusted until we've checked Jebelean's condition -- it cannot be too
   * large, of course, but it might be too small.
   */

  if (!skip)
  {
    for(;;)
    {
      /* First half of loop divides dd into dd1, and leaves the recurrence
       * matrix xu,...,xv1 groomed the wrong way round (xu,xv will be the newer
       * entries) when successful. */
      tmpd = dd1 - dd;
      if (tmpd < dd)
      {                                /* quotient suspected to be 1 */
#ifdef DEBUG_LEHMER
        q = 1;
#endif
        tmpu = xu + xu1;        /* cannot overflow -- everything bounded by
                                 * the original dd during first loop */
        tmpv = xv + xv1;
      }
      else
      {                                /* division indicated */
        hiremainder = 0;
        q = 1 + divll(tmpd, dd);
        tmpd = hiremainder;
        tmpu = xu + q*xu1;        /* can't overflow, but may need to be undone */
        tmpv = xv + q*xv1;
      }

      tmp0 = addll(tmpv, xv1);
      if ((tmpd < tmpu) || overflow ||
          (dd - tmpd < tmp0))        /* !(Jebelean cond.) */
        break;                        /* skip ahead to reshift stage */
      else
      {                                /* commit dd1, xu, xv */
        res++;
        dd1 = tmpd; xu = tmpu; xv = tmpv;
#ifdef DEBUG_LEHMER
        err_printf("  q = %ld, %lx, %lx [%lu,%lu;%lu,%lu]\n",
                   q, dd, dd1, xu1, xu, xv1, xv);
#endif
        if (xv > vmax)
        {                        /* time to return */
          *u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
          return (int)res;
        }
      }

      /* Second half of loop divides dd1 into dd, and the matrix returns to its
       * normal arrangement. */
      tmpd = dd - dd1;
      if (tmpd < dd1)
      {                                /* quotient suspected to be 1 */
#ifdef DEBUG_LEHMER
        q = 1;
#endif
        tmpu = xu1 + xu;        /* cannot overflow */
        tmpv = xv1 + xv;
      }
      else
      {                                /* division indicated */
        hiremainder = 0;
        q = 1 + divll(tmpd, dd1);
        tmpd = hiremainder;
        tmpu = xu1 + q*xu;
        tmpv = xv1 + q*xv;
      }

      tmp0 = addll(tmpu, xu);
      if ((tmpd < tmpv) || overflow ||
          (dd1 - tmpd < tmp0))        /* !(Jebelean cond.) */
        break;                        /* skip ahead to reshift stage */
      else
      {                                /* commit dd, xu1, xv1 */
        res++;
        dd = tmpd; xu1 = tmpu; xv1 = tmpv;
#ifdef DEBUG_LEHMER
        err_printf("  q = %ld, %lx, %lx [%lu,%lu;%lu,%lu]\n",
                q, dd1, dd, xu, xu1, xv, xv1);
#endif
        if (xv1 > vmax)
        {                        /* time to return */
          *u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
          return (int)res;
        }
      }

    } /* end of first loop */

    /* Intermezzo: update dd:ddlo, dd1:dd1lo.  (But not if skip is set.) */

    if (res&1)
    {
      /* after failed division in 1st half of loop:
       * [dd1:dd1lo,dd:ddlo] = [ddorig:ddlo,dd1orig:dd1lo]
       *                       * [ -xu, xu1 ; xv, -xv1 ]
       * (Actually, we only multiply [ddlo,dd1lo] onto the matrix and
       * add the high-order remainders + overflows onto [dd1,dd].)
       */
      tmp1 = mulll(ddlo, xu); tmp0 = hiremainder;
      tmp1 = subll(mulll(dd1lo,xv), tmp1);
      dd1 += subllx(hiremainder, tmp0);
      tmp2 = mulll(ddlo, xu1); tmp0 = hiremainder;
      ddlo = subll(tmp2, mulll(dd1lo,xv1));
      dd += subllx(tmp0, hiremainder);
      dd1lo = tmp1;
    }
    else
    {
      /* after failed division in 2nd half of loop:
       * [dd:ddlo,dd1:dd1lo] = [ddorig:ddlo,dd1orig:dd1lo]
       *                       * [ xu1, -xu ; -xv1, xv ]
       * (Actually, we only multiply [ddlo,dd1lo] onto the matrix and
       * add the high-order remainders + overflows onto [dd,dd1].)
       */
      tmp1 = mulll(ddlo, xu1); tmp0 = hiremainder;
      tmp1 = subll(tmp1, mulll(dd1lo,xv1));
      dd += subllx(tmp0, hiremainder);
      tmp2 = mulll(ddlo, xu); tmp0 = hiremainder;
      dd1lo = subll(mulll(dd1lo,xv), tmp2);
      dd1 += subllx(hiremainder, tmp0);
      ddlo = tmp1;
    }
#ifdef DEBUG_LEHMER
    err_printf("  %lx:%lx, %lx:%lx\n", dd, ddlo, dd1, dd1lo);
#endif
  } /* end of skip-pable section:  get here also, with res==1, when there
     * was a problem immediately after the very first division. */

  /* Re-shift.  Note:  the shift count _can_ be zero, viz. under the following
   * precise conditions:  The original dd1 had its topmost bit set, so the 1st
   * q was 1, and after subtraction, dd had its topmost bit unset.  If now
   * dd==0, we'd have taken the return exit already, so we couldn't have got
   * here.  If not, then it must have been the second division which has gone
   * amiss  (because dd1 was very close to an exact multiple of the remainder
   * dd value, so this will be very rare).  At this point, we'd have a fairly
   * slim chance of fixing things by re-examining dd1:dd1lo vs. dd:ddlo, but
   * this is not guaranteed to work.  Instead of trying, we return at once.
   * The caller will see to it that the initial subtraction is re-done using
   * _all_ the bits of both operands, which already helps, and the next round
   * will either be a full division  (if dd occupied a halfword or less),  or
   * another llgcdii() first step.  In the latter case, since we try a little
   * harder during our first step, we may actually be able to fix the problem,
   * and get here again with improved low-order bits and with another step
   * under our belt.  Otherwise we'll have given up above and forced a full-
   * blown division.
   *
   * If res is even, the shift count _cannot_ be zero.  (The first step forces
   * a zero into the remainder's MSB, and all subsequent remainders will have
   * inherited it.)
   *
   * The re-shift stage exits if the next divisor has at most half a word's
   * worth of bits.
   *
   * For didactic reasons, the second loop will be arranged in the same way
   * as the first -- beginning with the division of dd into dd1, as if res
   * was odd.  To cater for this, if res is actually even, we swap things
   * around during reshifting.  (During the second loop, the parity of res
   * does not matter;  we know in which half of the loop we are when we decide
   * to return.)
   */
#ifdef DEBUG_LEHMER
  err_printf("(sh)");
#endif

  if (res&1)
  {                                /* after odd number of division(s) */
    if (dd1 && (sh = bfffo(dd1)))
    {
      shc = BITS_IN_LONG - sh;
      dd = (ddlo >> shc) + (dd << sh);
      if (!(HIGHMASK & dd))
      {
        *u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
        return (int)-res;                /* full division asked for */
      }
      dd1 = (dd1lo >> shc) + (dd1 << sh);
    }
    else
    {                                /* time to return: <= 1 word left, or sh==0 */
      *u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
      return (int)res;
    }
  }
  else
  {                                /* after even number of divisions */
    if (dd)
    {
      sh = bfffo(dd);                /* Known to be positive. */
      shc = BITS_IN_LONG - sh;
                                /* dd:ddlo will become the new dd1, and v.v. */
      tmpd = (ddlo >> shc) + (dd << sh);
      dd = (dd1lo >> shc) + (dd1 << sh);
      dd1 = tmpd;
      /* This has completed the swap;  now dd is again the current divisor.
       * The following test originally inspected dd1 -- a most subtle and
       * most annoying bug. The Management. */
      if (HIGHMASK & dd)
      {
        /* recurrence matrix is the wrong way round;  swap it. */
        tmp0 = xu; xu = xu1; xu1 = tmp0;
        tmp0 = xv; xv = xv1; xv1 = tmp0;
      }
      else
      {
        /* recurrence matrix is the wrong way round;  fix this. */
        *u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
        return (int)-res;                /* full division asked for */
      }
    }
    else
    {                                /* time to return: <= 1 word left */
      *u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
      return (int)res;
    }
  } /* end reshift */

#ifdef DEBUG_LEHMER
  err_printf("  %lx:%lx, %lx:%lx\n", dd, ddlo, dd1, dd1lo);
#endif

  /* The Second Loop.  Rip-off of the first, but we now check for overflow
   * in the recurrences.  Returns instead of breaking when we cannot fix the
   * quotient any longer.
   */

  for(;;)
  {
    /* First half of loop divides dd into dd1, and leaves the recurrence
     * matrix xu,...,xv1 groomed the wrong way round (xu,xv will be the newer
     * entries) when successful. */
    tmpd = dd1 - dd;
    if (tmpd < dd)
    {                                /* quotient suspected to be 1 */
#ifdef DEBUG_LEHMER
      q = 1;
#endif
      tmpu = xu + xu1;
      tmpv = addll(xv, xv1);        /* xv,xv1 will overflow first */
      tmp1 = overflow;
    }
    else
    {                                /* division indicated */
      hiremainder = 0;
      q = 1 + divll(tmpd, dd);
      tmpd = hiremainder;
      tmpu = xu + q*xu1;
      tmpv = addll(xv, mulll(q,xv1));
      tmp1 = overflow | hiremainder;
    }

    tmp0 = addll(tmpv, xv1);
    if ((tmpd < tmpu) || overflow || tmp1 ||
        (dd - tmpd < tmp0))        /* !(Jebelean cond.) */
    {
      /* The recurrence matrix has not yet been warped... */
      *u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
      break;
    }
    /* commit dd1, xu, xv */
    res++;
    dd1 = tmpd; xu = tmpu; xv = tmpv;
#ifdef DEBUG_LEHMER
    err_printf("  q = %ld, %lx, %lx\n", q, dd, dd1);
#endif
    if (xv > vmax)
    {                                /* time to return */
      *u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
      return (int)res;
    }

    /* Second half of loop divides dd1 into dd, and the matrix returns to its
     * normal arrangement. */
    tmpd = dd - dd1;
    if (tmpd < dd1)
    {                                /* quotient suspected to be 1 */
#ifdef DEBUG_LEHMER
      q = 1;
#endif
      tmpu = xu1 + xu;
      tmpv = addll(xv1, xv);
      tmp1 = overflow;
    }
    else
    {                                /* division indicated */
      hiremainder = 0;
      q = 1 + divll(tmpd, dd1);
      tmpd = hiremainder;
      tmpu = xu1 + q*xu;
      tmpv = addll(xv1, mulll(q, xv));
      tmp1 = overflow | hiremainder;
    }

    tmp0 = addll(tmpu, xu);
    if ((tmpd < tmpv) || overflow || tmp1 ||
        (dd1 - tmpd < tmp0))        /* !(Jebelean cond.) */
    {
      /* The recurrence matrix has not yet been unwarped, so it is
       * the wrong way round;  fix this. */
      *u = xu1; *u1 = xu; *v = xv1; *v1 = xv;
      break;
    }

    res++; /* commit dd, xu1, xv1 */
    dd = tmpd; xu1 = tmpu; xv1 = tmpv;
#ifdef DEBUG_LEHMER
    err_printf("  q = %ld, %lx, %lx\n", q, dd1, dd);
#endif
    if (xv1 > vmax)
    {                                /* time to return */
      *u = xu; *u1 = xu1; *v = xv; *v1 = xv1;
      return (int)res;
    }
  } /* end of second loop */

  return (int)res;
}

/* 1 / Mod(x,p). Assume x < p */
ulong
Fl_invsafe(ulong x, ulong p)
{
  pari_long s;
  ulong xv, xv1, g = xgcduu(p, x, 1, &xv, &xv1, &s);
  if (g != 1ULL) return 0ULL;
  xv = xv1 % p; if (s < 0) xv = p - xv;
  return xv;
}

/* 1 / Mod(x,p). Assume x < p */
ulong
Fl_inv(ulong x, ulong p)
{
  ulong xv  = Fl_invsafe(x, p);
  if (!xv && p!=1ULL) pari_err_INV("Fl_inv", mkintmod(utoi(x), utoi(p)));
  return xv;
}
#line 2 "../src/kernel/none/ratlift.c"
/* Copyright (C) 2003  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*==========================================================
 * Fp_ratlift(GEN x, GEN m, GEN *a, GEN *b, GEN amax, GEN bmax)
 *==========================================================
 * Reconstruct rational number from its residue x mod m
 *    Given t_INT x, m, amax>=0, bmax>0 such that
 *         0 <= x < m;  2*amax*bmax < m
 *    attempts to find t_INT a, b such that
 *         (1) a = b*x (mod m)
 *         (2) |a| <= amax, 0 < b <= bmax
 *         (3) gcd(m, b) = gcd(a, b)
 *    If unsuccessful, it will return 0 and leave a,b unchanged  (and
 *    caller may deduce no such a,b exist).  If successful, sets a,b
 *    and returns 1.  If there exist a,b satisfying (1), (2), and
 *         (3') gcd(m, b) = 1
 *    then they are uniquely determined subject to (1),(2) and
 *         (3'') gcd(a, b) = 1,
 *    and will be returned by the routine.  (The caller may wish to
 *    check gcd(a,b)==1, either directly or based on known prime
 *    divisors of m, depending on the application.)
 * Reference:
 @article {MR97c:11116,
     AUTHOR = {Collins, George E. and Encarnaci{\'o}n, Mark J.},
      TITLE = {Efficient rational number reconstruction},
    JOURNAL = {J. Symbolic Comput.},
     VOLUME = {20},
       YEAR = {1995},
     NUMBER = {3},
      PAGES = {287--297},
 }
 * Preprint available from:
 * ftp://ftp.risc.uni-linz.ac.at/pub/techreports/1994/94-64.ps.gz */

/* #define DEBUG_RATLIFT */
static ulong
get_vmax(GEN r, pari_long lb, pari_long lbb)
{
  pari_long lr = lb - lgefint(r);
  ulong vmax;
  if (lr > 1)        /* still more than a word's worth to go */
    vmax = ULONG_MAX;        /* (cannot in fact happen) */
  else
  { /* take difference of bit lengths */
    pari_long lbr = bfffo(*int_MSW(r));
    lr = lr*BITS_IN_LONG - lbb + lbr;
    if ((ulong)lr > BITS_IN_LONG)
      vmax = ULONG_MAX;
    else if (lr == 0)
      vmax = 1ULL;
    else
      vmax = 1ULL << (lr-1); /* pessimistic but faster than a division */
  }
#ifdef DEBUG_RATLIFT
  err_printf("rl-fs: vmax=%lu\n", vmax);
#endif
  return vmax;
}

/* Assume x,m,amax >= 0,bmax > 0 are t_INTs, 0 <= x < m, 2 amax * bmax < m */
int
Fp_ratlift(GEN x, GEN m, GEN amax, GEN bmax, GEN *a, GEN *b)
{
  GEN d, d1, v, v1, q, r;
  pari_sp av = avma, av1, lim;
  pari_long lb, lbb, s, s0;
  ulong vmax;
  ulong xu, xu1, xv, xv1; /* Lehmer stage recurrence matrix */
  int lhmres;             /* Lehmer stage return value */

  /* special cases x=0 and/or amax=0 */
  if (!signe(x)) { *a = gen_0; *b = gen_1; return 1; }
  if (!signe(amax)) return 0;
  /* assert: m > x > 0, amax > 0 */

  /* check whether a=x, b=1 is a solution */
  if (cmpii(x,amax) <= 0) { *a = icopy(x); *b = gen_1; return 1; }

  /* There is no special case for single-word numbers since this is
   * mainly meant to be used with large moduli. */
  (void)new_chunk(lgefint(bmax) + lgefint(amax)); /* room for a,b */
  d = m; d1 = x;
  v = gen_0; v1 = gen_1;
  /* assert d1 > amax, v1 <= bmax here */
  lb = lgefint(bmax);
  lbb = bfffo(*int_MSW(bmax));
  s = 1;
  av1 = avma; lim = stack_lim(av, 1);


  /* General case: Euclidean division chain starting with m div x, and
   * with bounds on the sequence of convergents' denoms v_j.
   * Just to be different from what invmod and bezout are doing, we work
   * here with the all-nonnegative matrices [u,u1;v,v1]=prod_j([0,1;1,q_j]).
   * Loop invariants:
   * (a) (sign)*[-v,v1]*x = [d,d1] (mod m)  (componentwise)
   * (sign initially +1, changes with each Euclidean step)
   * so [a,b] will be obtained in the form [-+d,v] or [+-d1,v1];
   * this congruence is a consequence of
   *
   * (b) [x,m]~ = [u,u1;v,v1]*[d1,d]~,
   * where u,u1 is the usual numerator sequence starting with 1,0
   * instead of 0,1  (just multiply the eqn on the left by the inverse
   * matrix, which is det*[v1,-u1;-v,u], where "det" is the same as the
   * "(sign)" in (a)).  From m = v*d1 + v1*d and
   *
   * (c) d > d1 >= 0, 0 <= v < v1,
   * we have d >= m/(2*v1), so while v1 remains smaller than m/(2*amax),
   * the pair [-(sign)*d,v] satisfies (1) but violates (2) (d > amax).
   * Conversely, v1 > bmax indicates that no further solutions will be
   * forthcoming;  [-(sign)*d,v] will be the last, and first, candidate.
   * Thus there's at most one point in the chain division where a solution
   * can live:  v < bmax, v1 >= m/(2*amax) > bmax,  and this is acceptable
   * iff in fact d <= amax  (e.g. m=221, x=34 or 35, amax=bmax=10 fail on
   * this count while x=32,33,36,37 succeed).  However, a division may leave
   * a zero residue before we ever reach this point  (consider m=210, x=35,
   * amax=bmax=10),  and our caller may find that gcd(d,v) > 1  (Examples:
   * keep m=210 and consider any of x=29,31,32,33,34,36,37,38,39,40,41).
   * Furthermore, at the start of the loop body we have in fact
   *
   * (c') 0 <= v < v1 <= bmax, d > d1 > amax >= 0,
   * (and are never done already).
   *
   * Main loop is similar to those of invmod() and bezout(), except for
   * having to determine appropriate vmax bounds, and checking termination
   * conditions.  The signe(d1) condition is only for paranoia */

  while (lgefint(d) > 3 && signe(d1))
  {
    /* determine vmax for lgcdii so as to ensure v won't overshoot.
     * If v+v1 > bmax, the next step would take v1 beyond the limit, so
     * since [+-d1,v1] is not a solution, we give up.  Otherwise if v+v1
     * is way shorter than bmax, use vmax=MAXULUNG.  Otherwise, set vmax
     * to a crude lower approximation of bmax/(v+v1), or to 1, which will
     * allow the inner loop to do one step */
    r = addii(v,v1);
    if (cmpii(r,bmax) > 0) { avma = av; return 0; } /* done, not found */
    vmax = get_vmax(r, lb, lbb);
    /* do a Lehmer-Jebelean round */
    lhmres = lgcdii((ulong *)d, (ulong *)d1, &xu, &xu1, &xv, &xv1, vmax);

    if (lhmres) /* check progress */
    { /* apply matrix */
      if (lhmres == 1 || lhmres == -1)
      {
        s = -s;
        if (xv1 == 1)
        { /* re-use v+v1 computed above */
          v = v1; v1 = r;
          r = subii(d,d1); d = d1; d1 = r;
        }
        else
        {
          r = subii(d, mului(xv1,d1)); d = d1; d1 = r;
          r = addii(v, mului(xv1,v1)); v = v1; v1 = r;
        }
      }
      else
      {
        r  = subii(muliu(d,xu),  muliu(d1,xv));
        d1 = subii(muliu(d,xu1), muliu(d1,xv1)); d = r;
        r  = addii(muliu(v,xu),  muliu(v1,xv));
        v1 = addii(muliu(v,xu1), muliu(v1,xv1)); v = r;
        if (lhmres&1) { togglesign(d); s = -s; } else togglesign(d1);
      }
      /* check whether we're done.  Assert v <= bmax here.  Examine v1:
       * if v1 > bmax, check d and return 0 or 1 depending on the outcome;
       * if v1 <= bmax, check d1 and return 1 if d1 <= amax, otherwise proceed*/
      if (cmpii(v1,bmax) > 0)
      {
        avma = av;
        if (cmpii(d,amax) > 0) return 0; /* done, not found */
        /* done, found */
        *a = icopy(d); setsigne(*a,-s);
        *b = icopy(v); return 1;
      }
      if (cmpii(d1,amax) <= 0)
      { /* done, found */
        avma = av;
        if (signe(d1)) { *a = icopy(d1); setsigne(*a,s); } else *a = gen_0;
        *b = icopy(v1); return 1;
      }
    } /* lhmres != 0 */

    if (lhmres <= 0 && signe(d1))
    {
      q = dvmdii(d,d1,&r);
#ifdef DEBUG_LEHMER
      err_printf("Full division:\n  q = %Ps\n", q);
#endif
      d = d1; d1 = r;
      r = addii(v, mulii(q,v1));
      v = v1; v1 = r;
      s = -s;
      /* check whether we are done now.  Since we weren't before the div, it
       * suffices to examine v1 and d1 -- the new d (former d1) cannot cut it */
      if (cmpii(v1,bmax) > 0) { avma = av; return 0; } /* done, not found */
      if (cmpii(d1,amax) <= 0) /* done, found */
      {
        avma = av;
        if (signe(d1)) { *a = icopy(d1); setsigne(*a,s); } else *a = gen_0;
        *b = icopy(v1); return 1;
      }
    }

    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ratlift");
      gerepileall(av1, 4, &d, &d1, &v, &v1);
    }
  } /* end while */

  /* Postprocessing - final sprint.  Since we usually underestimate vmax,
   * this function needs a loop here instead of a simple conditional.
   * Note we can only get here when amax fits into one word  (which will
   * typically not be the case!).  The condition is bogus -- d1 is never
   * zero at the start of the loop.  There will be at most a few iterations,
   * so we don't bother collecting garbage */

  while (signe(d1))
  {
    /* Assertions: lgefint(d)==lgefint(d1)==3.
     * Moreover, we aren't done already, or we would have returned by now.
     * Recompute vmax */
#ifdef DEBUG_RATLIFT
    err_printf("rl-fs: d,d1=%Ps,%Ps\n", d, d1);
    err_printf("rl-fs: v,v1=%Ps,%Ps\n", v, v1);
#endif
    r = addii(v,v1);
    if (cmpii(r,bmax) > 0) { avma = av; return 0; } /* done, not found */
    vmax = get_vmax(r, lb, lbb);
    /* single-word "Lehmer", discarding the gcd or whatever it returns */
    (void)rgcduu((ulong)*int_MSW(d), (ulong)*int_MSW(d1), vmax, &xu, &xu1, &xv, &xv1, &s0);
#ifdef DEBUG_RATLIFT
    err_printf("rl-fs: [%lu,%lu; %lu,%lu] %s\n",
               xu, xu1, xv, xv1, s0 < 0 ? "-" : "+");
#endif

    if (xv1 == 1) /* avoid multiplications */
    { /* re-use r = v+v1 computed above */
      v = v1; v1 = r;
      r = subii(d,d1); d = d1; d1 = r;
      s = -s;
    }
    else if (xu == 0) /* and xv==1, xu1==1, xv1 > 1 */
    {
      r = subii(d, mului(xv1,d1)); d = d1; d1 = r;
      r = addii(v, mului(xv1,v1)); v = v1; v1 = r;
      s = -s;
    }
    else
    {
      r  = subii(muliu(d,xu),  muliu(d1,xv));
      d1 = subii(muliu(d,xu1), muliu(d1,xv1)); d = r;
      r  = addii(muliu(v,xu),  muliu(v1,xv));
      v1 = addii(muliu(v,xu1), muliu(v1,xv1)); v = r;
      if (s0 < 0) { togglesign(d); s = -s; } else togglesign(d1);
    }
    /* check whether we're done, as above.  Assert v <= bmax.
     * if v1 > bmax, check d and return 0 or 1 depending on the outcome;
     * if v1 <= bmax, check d1 and return 1 if d1 <= amax, otherwise proceed.
     */
    if (cmpii(v1,bmax) > 0)
    {
      avma = av;
      if (cmpii(d,amax) > 0) return 0; /* done, not found */
      /* done, found */
      *a = icopy(d); setsigne(*a,-s);
      *b = icopy(v); return 1;
    }
    if (cmpii(d1,amax) <= 0)
    { /* done, found */
      avma = av;
      if (signe(d1)) { *a = icopy(d1); setsigne(*a,s); } else *a = gen_0;
      *b = icopy(v1); return 1;
    }
  } /* while */

  /* We have run into d1 == 0 before returning. This cannot happen */
  pari_err_BUG("ratlift failed to catch d1 == 0");
  return 0; /* NOTREACHED */
}
#line 2 "../src/kernel/none/invmod.c"
/* Copyright (C) 2003  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*==================================
 * invmod(a,b,res)
 *==================================
 *    If a is invertible, return 1, and set res  = a^{ -1 }
 *    Otherwise, return 0, and set res = gcd(a,b)
 *
 * This is sufficiently different from bezout() to be implemented separately
 * instead of having a bunch of extra conditionals in a single function body
 * to meet both purposes.
 */

#ifdef INVMOD_PARI
INLINE int
invmod_pari(GEN a, GEN b, GEN *res)
#else
int
invmod(GEN a, GEN b, GEN *res)
#endif
{
  GEN v,v1,d,d1,q,r;
  pari_sp av, av1, lim;
  pari_long s;
  ulong g;
  ulong xu,xu1,xv,xv1; /* Lehmer stage recurrence matrix */
  int lhmres; /* Lehmer stage return value */

  if (!signe(b)) { *res=absi(a); return 0; }
  av = avma;
  if (lgefint(b) == 3) /* single-word affair */
  {
    ulong d1 = umodiu(a, (ulong)(b[2]));
    if (d1 == 0)
    {
      if (b[2] == 1LL)
        { *res = gen_0; return 1; }
      else
        { *res = absi(b); return 0; }
    }
    g = xgcduu((ulong)(b[2]), d1, 1, &xv, &xv1, &s);
#ifdef DEBUG_LEHMER
    err_printf(" <- %lu,%lu\n", (ulong)(b[2]), (ulong)(d1[2]));
    err_printf(" -> %lu,%ld,%lu; %lx\n", g,s,xv1,avma);
#endif
    avma = av;
    if (g != 1ULL) { *res = utoipos(g); return 0; }
    xv = xv1 % (ulong)(b[2]); if (s < 0) xv = ((ulong)(b[2])) - xv;
    *res = utoipos(xv); return 1;
  }

  (void)new_chunk(lgefint(b));
  d = absi(b); d1 = modii(a,d);

  v=gen_0; v1=gen_1;        /* general case */
#ifdef DEBUG_LEHMER
  err_printf("INVERT: -------------------------\n");
  output(d1);
#endif
  av1 = avma; lim = stack_lim(av,1);

  while (lgefint(d) > 3 && signe(d1))
  {
#ifdef DEBUG_LEHMER
    err_printf("Calling Lehmer:\n");
#endif
    lhmres = lgcdii((ulong*)d, (ulong*)d1, &xu, &xu1, &xv, &xv1, ULONG_MAX);
    if (lhmres != 0)                /* check progress */
    {                                /* apply matrix */
#ifdef DEBUG_LEHMER
      err_printf("Lehmer returned %d [%lu,%lu;%lu,%lu].\n",
              lhmres, xu, xu1, xv, xv1);
#endif
      if ((lhmres == 1) || (lhmres == -1))
      {
        if (xv1 == 1)
        {
          r = subii(d,d1); d=d1; d1=r;
          a = subii(v,v1); v=v1; v1=a;
        }
        else
        {
          r = subii(d, mului(xv1,d1)); d=d1; d1=r;
          a = subii(v, mului(xv1,v1)); v=v1; v1=a;
        }
      }
      else
      {
        r  = subii(muliu(d,xu),  muliu(d1,xv));
        a  = subii(muliu(v,xu),  muliu(v1,xv));
        d1 = subii(muliu(d,xu1), muliu(d1,xv1)); d = r;
        v1 = subii(muliu(v,xu1), muliu(v1,xv1)); v = a;
        if (lhmres&1) { togglesign(d);  togglesign(v); }
        else          { togglesign(d1); togglesign(v1); }
      }
    }
#ifdef DEBUG_LEHMER
    else
      err_printf("Lehmer returned 0.\n");
    output(d); output(d1); output(v); output(v1);
    sleep(1);
#endif

    if (lhmres <= 0 && signe(d1))
    {
      q = dvmdii(d,d1,&r);
#ifdef DEBUG_LEHMER
      err_printf("Full division:\n");
      printf("  q = "); output(q); sleep (1);
#endif
      a = subii(v,mulii(q,v1));
      v=v1; v1=a;
      d=d1; d1=r;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"invmod");
      gerepileall(av1, 4, &d,&d1,&v,&v1);
    }
  } /* end while */

  /* Postprocessing - final sprint */
  if (signe(d1))
  {
    /* Assertions: lgefint(d)==lgefint(d1)==3, and
     * gcd(d,d1) is nonzero and fits into one word
     */
    g = xxgcduu((ulong)d[2], (ulong)d1[2], 1, &xu, &xu1, &xv, &xv1, &s);
#ifdef DEBUG_LEHMER
    output(d);output(d1);output(v);output(v1);
    err_printf(" <- %lu,%lu\n", (ulong)d[2], (ulong)d1[2]);
    err_printf(" -> %lu,%ld,%lu; %lx\n", g,s,xv1,avma);
#endif
    if (g != 1ULL) { avma = av; *res = utoipos(g); return 0; }
    /* (From the xgcduu() blurb:)
     * For finishing the multiword modinv, we now have to multiply the
     * returned matrix  (with properly adjusted signs)  onto the values
     * v' and v1' previously obtained from the multiword division steps.
     * Actually, it is sufficient to take the scalar product of [v',v1']
     * with [u1,-v1], and change the sign if s==1.
     */
    v = subii(muliu(v,xu1),muliu(v1,xv1));
    if (s > 0) setsigne(v,-signe(v));
    avma = av; *res = modii(v,b);
#ifdef DEBUG_LEHMER
    output(*res); fprintfderr("============================Done.\n");
    sleep(1);
#endif
    return 1;
  }
  /* get here when the final sprint was skipped (d1 was zero already) */
  avma = av;
  if (!equalii(d,gen_1)) { *res = icopy(d); return 0; }
  *res = modii(v,b);
#ifdef DEBUG_LEHMER
  output(*res); err_printf("============================Done.\n");
  sleep(1);
#endif
  return 1;
}

#line 2 "../src/kernel/none/gcd.c"
/* Copyright (C) 2003  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* assume y > x > 0. return y mod x */
static ulong
resiu(GEN y, ulong x)
{
  pari_long i, ly = lgefint(y);
  LOCAL_HIREMAINDER;

  hiremainder = 0;
  for (i=2; i<ly; i++) (void)divll(y[i],x);
  return hiremainder;
}

/* Assume x>y>0, both of them odd. return x-y if x=y mod 4, x+y otherwise */
static void
gcd_plus_minus(GEN x, GEN y, GEN res)
{
  pari_sp av = avma;
  pari_long lx = lgefint(x)-1;
  pari_long ly = lgefint(y)-1, lt,m,i;
  GEN t;

  if ((x[lx]^y[ly]) & 3) /* x != y mod 4*/
    t = addiispec(x+2,y+2,lx-1,ly-1);
  else
    t = subiispec(x+2,y+2,lx-1,ly-1);

  lt = lgefint(t)-1; while (!t[lt]) lt--;
  m = vals(t[lt]); lt++;
  if (m == 0) /* 2^32 | t */
  {
    for (i = 2; i < lt; i++) res[i] = t[i];
  }
  else if (t[2] >> m)
  {
    shift_right(res,t, 2,lt, 0,m);
  }
  else
  {
    lt--; t++;
    shift_right(res,t, 2,lt, t[1],m);
  }
  res[1] = evalsigne(1)|evallgefint(lt);
  avma = av;
}

/* uses modified right-shift binary algorithm now --GN 1998Jul23 */
GEN
gcdii(GEN a, GEN b)
{
  pari_long v, w;
  pari_sp av;
  GEN t, p1;

  switch (absi_cmp(a,b))
  {
    case 0: return absi(a);
    case -1: t=b; b=a; a=t;
  }
  if (!signe(b)) return absi(a);
  /* here |a|>|b|>0. Try single precision first */
  if (lgefint(a)==3)
    return igcduu((ulong)a[2], (ulong)b[2]);
  if (lgefint(b)==3)
  {
    ulong u = resiu(a,(ulong)b[2]);
    if (!u) return absi(b);
    return igcduu((ulong)b[2], u);
  }

  /* larger than gcd: "avma=av" gerepile (erasing t) is valid */
  av = avma; (void)new_chunk(lgefint(b)); /* HACK */
  t = remii(a,b);
  if (!signe(t)) { avma=av; return absi(b); }

  a = b; b = t;
  v = vali(a); a = shifti(a,-v); setabssign(a);
  w = vali(b); b = shifti(b,-w); setabssign(b);
  if (w < v) v = w;
  switch(absi_cmp(a,b))
  {
    case  0: avma=av; a=shifti(a,v); return a;
    case -1: p1=b; b=a; a=p1;
  }
  if (is_pm1(b)) { avma=av; return int2n(v); }

  /* we have three consecutive memory locations: a,b,t.
   * All computations are done in place */

  /* a and b are odd now, and a>b>1 */
  while (lgefint(a) > 3)
  {
    /* if a=b mod 4 set t=a-b, otherwise t=a+b, then strip powers of 2 */
    /* so that t <= (a+b)/4 < a/2 */
    gcd_plus_minus(a,b, t);
    if (is_pm1(t)) { avma=av; return int2n(v); }
    switch(absi_cmp(t,b))
    {
      case -1: p1 = a; a = b; b = t; t = p1; break;
      case  1: p1 = a; a = t; t = p1; break;
      case  0: avma = av; b=shifti(b,v); return b;
    }
  }
  {
    pari_long r[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 0};
    r[2] = (pari_long) gcduodd((ulong)b[2], (ulong)a[2]);
    avma = av; return shifti(r,v);
  }
}
#line 2 "../src/kernel/none/gcdext.c"
/* Copyright (C) 2003  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*==================================
 * bezout(a,b,pu,pv)
 *==================================
 *    Return g = gcd(a,b) >= 0, and assign GENs u,v through pointers pu,pv
 *    such that g = u*a + v*b.
 * Special cases:
 *    a == b == 0 ==> pick u=1, v=0
 *    a != 0 == b ==> keep v=0
 *    a == 0 != b ==> keep u=0
 *    |a| == |b| != 0 ==> keep u=0, set v=+-1
 * Assignments through pu,pv will be suppressed when the corresponding
 * pointer is NULL  (but the computations will happen nonetheless).
 */

GEN
bezout(GEN a, GEN b, GEN *pu, GEN *pv)
{
  GEN t,u,u1,v,v1,d,d1,q,r;
  GEN *pt;
  pari_sp av, av1, lim;
  pari_long s, sa, sb;
  ulong g;
  ulong xu,xu1,xv,xv1;                /* Lehmer stage recurrence matrix */
  int lhmres;                        /* Lehmer stage return value */

  s = absi_cmp(a,b);
  if (s < 0)
  {
    t=b; b=a; a=t;
    pt=pu; pu=pv; pv=pt;
  }
  /* now |a| >= |b| */

  sa = signe(a); sb = signe(b);
  if (!sb)
  {
    if (pv) *pv = gen_0;
    switch(sa)
    {
    case  0: if (pu) *pu = gen_0; return gen_0;
    case  1: if (pu) *pu = gen_1; return icopy(a);
    case -1: if (pu) *pu = gen_m1; return(negi(a));
    }
  }
  if (s == 0)                        /* |a| == |b| != 0 */
  {
    if (pu) *pu = gen_0;
    if (sb > 0)
    { if (pv) *pv = gen_1; return icopy(b); }
    else
    { if (pv) *pv = gen_m1; return(negi(b)); }
  }
  /* now |a| > |b| > 0 */

  if (lgefint(a) == 3)                /* single-word affair */
  {
    g = xxgcduu((ulong)a[2], (ulong)b[2], 0, &xu, &xu1, &xv, &xv1, &s);
    sa = s > 0 ? sa : -sa;
    sb = s > 0 ? -sb : sb;
    if (pu)
    {
      if (xu == 0) *pu = gen_0; /* can happen when b divides a */
      else if (xu == 1) *pu = sa < 0 ? gen_m1 : gen_1;
      else if (xu == 2) *pu = sa < 0 ? gen_m2 : gen_2;
      else
      {
        *pu = cgeti(3);
        (*pu)[1] = evalsigne(sa)|evallgefint(3);
        (*pu)[2] = xu;
      }
    }
    if (pv)
    {
      if (xv == 1) *pv = sb < 0 ? gen_m1 : gen_1;
      else if (xv == 2) *pv = sb < 0 ? gen_m2 : gen_2;
      else
      {
        *pv = cgeti(3);
        (*pv)[1] = evalsigne(sb)|evallgefint(3);
        (*pv)[2] = xv;
      }
    }
    if      (g == 1) return gen_1;
    else if (g == 2) return gen_2;
    else return utoipos(g);
  }

  /* general case */
  av = avma;
  (void)new_chunk(lgefint(b) + (lgefint(a)<<1)); /* room for u,v,gcd */
  /* if a is significantly larger than b, calling lgcdii() is not the best
   * way to start -- reduce a mod b first
   */
  if (lgefint(a) > lgefint(b))
  {
    d = absi(b), q = dvmdii(absi(a), d, &d1);
    if (!signe(d1))                /* a == qb */
    {
      avma = av;
      if (pu) *pu = gen_0;
      if (pv) *pv = sb < 0 ? gen_m1 : gen_1;
      return (icopy(d));
    }
    else
    {
      u = gen_0;
      u1 = v = gen_1;
      v1 = negi(q);
    }
    /* if this results in lgefint(d) == 3, will fall past main loop */
  }
  else
  {
    d = absi(a); d1 = absi(b);
    u = v1 = gen_1; u1 = v = gen_0;
  }
  av1 = avma; lim = stack_lim(av, 1);

  /* main loop is almost identical to that of invmod() */
  while (lgefint(d) > 3 && signe(d1))
  {
    lhmres = lgcdii((ulong *)d, (ulong *)d1, &xu, &xu1, &xv, &xv1, ULONG_MAX);
    if (lhmres != 0)                /* check progress */
    {                                /* apply matrix */
      if ((lhmres == 1) || (lhmres == -1))
      {
        if (xv1 == 1)
        {
          r = subii(d,d1); d=d1; d1=r;
          a = subii(u,u1); u=u1; u1=a;
          a = subii(v,v1); v=v1; v1=a;
        }
        else
        {
          r = subii(d, mului(xv1,d1)); d=d1; d1=r;
          a = subii(u, mului(xv1,u1)); u=u1; u1=a;
          a = subii(v, mului(xv1,v1)); v=v1; v1=a;
        }
      }
      else
      {
        r  = subii(muliu(d,xu),  muliu(d1,xv));
        d1 = subii(muliu(d,xu1), muliu(d1,xv1)); d = r;
        a  = subii(muliu(u,xu),  muliu(u1,xv));
        u1 = subii(muliu(u,xu1), muliu(u1,xv1)); u = a;
        a  = subii(muliu(v,xu),  muliu(v1,xv));
        v1 = subii(muliu(v,xu1), muliu(v1,xv1)); v = a;
        if (lhmres&1) { togglesign(d);  togglesign(u);  togglesign(v); }
        else          { togglesign(d1); togglesign(u1); togglesign(v1); }
      }
    }
    if (lhmres <= 0 && signe(d1))
    {
      q = dvmdii(d,d1,&r);
#ifdef DEBUG_LEHMER
      err_printf("Full division:\n");
      printf("  q = "); output(q); sleep (1);
#endif
      a = subii(u,mulii(q,u1));
      u=u1; u1=a;
      a = subii(v,mulii(q,v1));
      v=v1; v1=a;
      d=d1; d1=r;
    }
    if (low_stack(lim, stack_lim(av,1)))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"bezout");
      gerepileall(av1,6, &d,&d1,&u,&u1,&v,&v1);
    }
  } /* end while */

  /* Postprocessing - final sprint */
  if (signe(d1))
  {
    /* Assertions: lgefint(d)==lgefint(d1)==3, and
     * gcd(d,d1) is nonzero and fits into one word
     */
    g = xxgcduu((ulong)(d[2]), (ulong)(d1[2]), 0, &xu, &xu1, &xv, &xv1, &s);
    u = subii(muliu(u,xu), muliu(u1, xv));
    v = subii(muliu(v,xu), muliu(v1, xv));
    if (s < 0) { sa = -sa; sb = -sb; }
    avma = av;
    if (pu) *pu = sa < 0 ? negi(u) : icopy(u);
    if (pv) *pv = sb < 0 ? negi(v) : icopy(v);
    if (g == 1) return gen_1;
    else if (g == 2) return gen_2;
    else return utoipos(g);
  }
  /* get here when the final sprint was skipped (d1 was zero already).
   * Now the matrix is final, and d contains the gcd.
   */
  avma = av;
  if (pu) *pu = sa < 0 ? negi(u) : icopy(u);
  if (pv) *pv = sb < 0 ? negi(v) : icopy(v);
  return icopy(d);
}

#line 2 "../src/kernel/none/mp_indep.c"
/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* Find c such that 1=c*b mod 2^BITS_IN_LONG, assuming b odd (unchecked) */
ulong
invmod2BIL(ulong b)
{
  static int tab[] = { 0, 0, 0, 8, 0, 8, 0, 0 };
  ulong x = b + tab[b & 7]; /* b^(-1) mod 2^4 */

  /* Newton applied to 1/x - b = 0 */
#ifdef LONG_IS_64BIT
  x = x*(2-b*x); /* one more pass necessary */
#endif
  x = x*(2-b*x);
  x = x*(2-b*x); return x*(2-b*x);
}

void
affrr(GEN x, GEN y)
{
  pari_long lx,ly,i;

  y[1] = x[1]; if (!signe(x)) return;

  lx=lg(x); ly=lg(y);
  if (lx <= ly)
  {
    for (i=2; i<lx; i++) y[i]=x[i];
    for (   ; i<ly; i++) y[i]=0;
    return;
  }
  for (i=2; i<ly; i++) y[i]=x[i];
  /* lx > ly: round properly */
  if (x[ly] & HIGHBIT) roundr_up_ip(y, ly);
}

GEN
trunc2nr(GEN x, pari_long n)
{
  pari_long ex;
  if (!signe(x)) return gen_0;
  ex = expo(x) + n; if (ex < 0) return gen_0;
  return mantissa2nr(x, ex - bit_prec(x) + 1);
}

/* x a t_REAL, x = i/2^e, i a t_INT */
GEN
mantissa_real(GEN x, pari_long *e)
{
  *e = bit_prec(x)-1-expo(x);
  return mantissa2nr(x, 0);
}

GEN
mului(ulong x, GEN y)
{
  pari_long s = signe(y);
  GEN z;

  if (!s || !x) return gen_0;
  z = muluispec(x, y+2, lgefint(y)-2);
  setsigne(z,s); return z;
}

GEN
mulsi(pari_long x, GEN y)
{
  pari_long s = signe(y);
  GEN z;

  if (!s || !x) return gen_0;
  if (x<0) { s = -s; x = -x; }
  z = muluispec((ulong)x, y+2, lgefint(y)-2);
  setsigne(z,s); return z;
}

GEN
mulss(pari_long x, pari_long y)
{
  pari_long p1;
  LOCAL_HIREMAINDER;

  if (!x || !y) return gen_0;
  if (x<0) {
    x = -x;
    if (y<0) { y = -y; p1 = mulll(x,y); return uutoi(hiremainder, p1); }
    p1 = mulll(x,y); return uutoineg(hiremainder, p1);
  } else {
    if (y<0) { y = -y; p1 = mulll(x,y); return uutoineg(hiremainder, p1); }
    p1 = mulll(x,y); return uutoi(hiremainder, p1);
  }
}
GEN
sqrs(pari_long x)
{
  pari_long p1;
  LOCAL_HIREMAINDER;

  if (!x) return gen_0;
  if (x<0) x = -x;
  p1 = mulll(x,x); return uutoi(hiremainder, p1);
}
GEN
muluu(ulong x, ulong y)
{
  pari_long p1;
  LOCAL_HIREMAINDER;

  if (!x || !y) return gen_0;
  p1 = mulll(x,y); return uutoi(hiremainder, p1);
}
GEN
sqru(ulong x)
{
  pari_long p1;
  LOCAL_HIREMAINDER;

  if (!x) return gen_0;
  p1 = mulll(x,x); return uutoi(hiremainder, p1);
}

/* assume x > 1, y != 0. Return u * y with sign s */
static GEN
mulur_2(ulong x, GEN y, pari_long s)
{
  pari_long m, sh, i, lx = lg(y), e = expo(y);
  GEN z = cgetr(lx);
  ulong garde;
  LOCAL_HIREMAINDER;

  y--; garde = mulll(x,y[lx]);
  for (i=lx-1; i>=3; i--) z[i]=addmul(x,y[i]);
  z[2]=hiremainder; /* != 0 since y normalized and |x| > 1 */
  sh = bfffo(hiremainder); m = BITS_IN_LONG-sh;
  if (sh) shift_left(z,z, 2,lx-1, garde,sh);
  z[1] = evalsigne(s) | evalexpo(m+e);
  if ((garde << sh) & HIGHBIT) roundr_up_ip(z, lx);
  return z;
}

INLINE GEN
mul0r(GEN x)
{
  pari_long l = lg(x), e = expo(x);
  e = (l > 2)? -bit_accuracy(l) + e: (e < 0? (e<<1): 0);
  return real_0_bit(e);
}
/* lg(x) > 2 */
INLINE GEN
div0r(GEN x) {
  pari_long l = lg(x), e = expo(x);
  return real_0_bit(-bit_accuracy(l) - e);
}

GEN
mulsr(pari_long x, GEN y)
{
  pari_long s;

  if (!x) return mul0r(y);
  s = signe(y);
  if (!s)
  {
    if (x < 0) x = -x;
    return real_0_bit( expo(y) + expu(x) );
  }
  if (x==1)  return rcopy(y);
  if (x==-1) return negr(y);
  if (x < 0)
    return mulur_2((ulong)-x, y, -s);
  else
    return mulur_2((ulong)x, y, s);
}

GEN
mulur(ulong x, GEN y)
{
  pari_long s;

  if (!x) return mul0r(y);
  s = signe(y);
  if (!s) return real_0_bit( expo(y) + expu(x) );
  if (x==1) return rcopy(y);
  return mulur_2(x, y, s);
}

INLINE void
mulrrz_end(GEN z, GEN hi, pari_long lz, pari_long sz, pari_long ez, ulong garde)
{
  pari_long i;
  if (hi[2] < 0)
  {
    if (z != hi)
      for (i=2; i<lz ; i++) z[i] = hi[i];
    ez++;
  }
  else
  {
    shift_left(z,hi,2,lz-1, garde, 1);
    garde <<= 1;
  }
  if (garde & HIGHBIT)
  { /* round to nearest */
    i = lz; do ((ulong*)z)[--i]++; while (i>1 && z[i]==0);
    if (i == 1) { z[2] = (pari_long)HIGHBIT; ez++; }
  }
  z[1] = evalsigne(sz)|evalexpo(ez);
}
/* mulrrz_end for lz = 3, minor simplifications. z[2]=hiremainder from mulll */
INLINE void
mulrrz_3end(GEN z, pari_long sz, pari_long ez, ulong garde)
{
  if (z[2] < 0)
  { /* z2 < (2^BIL-1)^2 / 2^BIL, hence z2+1 != 0 */
    if (garde & HIGHBIT) z[2]++; /* round properly */
    ez++;
  }
  else
  {
    z[2] = (z[2]<<1) | (garde>>(BITS_IN_LONG-1));
    if (garde & (1ULL<<(BITS_IN_LONG-2)))
    {
      z[2]++; /* round properly, z2+1 can overflow */
      if (!z[2]) { z[2] = (pari_long)HIGHBIT; ez++; }
    }
  }
  z[1] = evalsigne(sz)|evalexpo(ez);
}

/* set z <-- x^2 != 0, floating point multiplication.
 * lz = lg(z) = lg(x) */
INLINE void
sqrz_i(GEN z, GEN x, pari_long lz)
{
  pari_long ez = expo(x) << 1;
  pari_long i, j, lzz, p1;
  ulong garde;
  GEN x1;
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;

  if (lz > MULRR_MULII_LIMIT)
  {
    pari_sp av = avma;
    GEN hi = sqrispec_mirror(x+2, lz-2);
    mulrrz_end(z, hi, lz, 1, ez, hi[lz]);
    avma = av; return;
  }
  if (lz == 3)
  {
    garde = mulll(x[2],x[2]);
    z[2] = hiremainder;
    mulrrz_3end(z, 1, ez, garde);
    return;
  }

  lzz = lz-1; p1 = x[lzz];
  if (p1)
  {
    (void)mulll(p1,x[3]);
    garde = addmul(p1,x[2]);
    z[lzz] = hiremainder;
  }
  else
  {
    garde = 0;
    z[lzz] = 0;
  }
  for (j=lz-2, x1=x-j; j>=3; j--)
  {
    p1 = x[j]; x1++;
    if (p1)
    {
      (void)mulll(p1,x1[lz+1]);
      garde = addll(addmul(p1,x1[lz]), garde);
      for (i=lzz; i>j; i--)
      {
        hiremainder += overflow;
        z[i] = addll(addmul(p1,x1[i]), z[i]);
      }
      z[j] = hiremainder+overflow;
    }
    else z[j]=0;
  }
  p1 = x[2]; x1++;
  garde = addll(mulll(p1,x1[lz]), garde);
  for (i=lzz; i>2; i--)
  {
    hiremainder += overflow;
    z[i] = addll(addmul(p1,x1[i]), z[i]);
  }
  z[2] = hiremainder+overflow;
  mulrrz_end(z, z, lz, 1, ez, garde);
}

/* lz "large" = lg(y) = lg(z), lg(x) > lz if flag = 1 and >= if flag = 0 */
INLINE void
mulrrz_int(GEN z, GEN x, GEN y, pari_long lz, pari_long flag, pari_long sz)
{
  pari_sp av = avma;
  GEN hi = muliispec_mirror(y+2, x+2, lz+flag-2, lz-2);
  mulrrz_end(z, hi, lz, sz, expo(x)+expo(y), hi[lz]);
  avma = av;
}

/* lz = 3 */
INLINE void
mulrrz_3(GEN z, GEN x, GEN y, pari_long flag, pari_long sz)
{
  ulong garde;
  LOCAL_HIREMAINDER;
  if (flag)
  {
    (void)mulll(x[2],y[3]);
    garde = addmul(x[2],y[2]);
  }
  else
    garde = mulll(x[2],y[2]);
  z[2] = hiremainder;
  mulrrz_3end(z, sz, expo(x)+expo(y), garde);
}

/* set z <-- x*y, floating point multiplication. Trailing 0s for x are
 * treated efficiently (important application: mulir).
 * lz = lg(z) = lg(x) <= ly <= lg(y), sz = signe(z). flag = lg(x) < lg(y) */
INLINE void
mulrrz_i(GEN z, GEN x, GEN y, pari_long lz, pari_long flag, pari_long sz)
{
  pari_long ez, i, j, lzz, p1;
  ulong garde;
  GEN y1;
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;

  if (x == y) { sqrz_i(z,x,lz); return; }
  if (lz > MULRR_MULII_LIMIT) { mulrrz_int(z,x,y,lz,flag,sz); return; }
  if (lz == 3) { mulrrz_3(z,x,y,flag,sz); return; }
  ez = expo(x) + expo(y);
  if (flag) { (void)mulll(x[2],y[lz]); garde = hiremainder; } else garde = 0;
  lzz=lz-1; p1=x[lzz];
  if (p1)
  {
    (void)mulll(p1,y[3]);
    garde = addll(addmul(p1,y[2]), garde);
    z[lzz] = overflow+hiremainder;
  }
  else z[lzz]=0;
  for (j=lz-2, y1=y-j; j>=3; j--)
  {
    p1 = x[j]; y1++;
    if (p1)
    {
      (void)mulll(p1,y1[lz+1]);
      garde = addll(addmul(p1,y1[lz]), garde);
      for (i=lzz; i>j; i--)
      {
        hiremainder += overflow;
        z[i] = addll(addmul(p1,y1[i]), z[i]);
      }
      z[j] = hiremainder+overflow;
    }
    else z[j]=0;
  }
  p1 = x[2]; y1++;
  garde = addll(mulll(p1,y1[lz]), garde);
  for (i=lzz; i>2; i--)
  {
    hiremainder += overflow;
    z[i] = addll(addmul(p1,y1[i]), z[i]);
  }
  z[2] = hiremainder+overflow;
  mulrrz_end(z, z, lz, sz, ez, garde);
}

GEN
mulrr(GEN x, GEN y)
{
  pari_long flag, ly, lz, sx, sy;
  GEN z;

  if (x == y) return sqrr(x);
  sx = signe(x); if (!sx) return real_0_bit(expo(x) + expo(y));
  sy = signe(y); if (!sy) return real_0_bit(expo(x) + expo(y));
  if (sy < 0) sx = -sx;
  lz = lg(x);
  ly = lg(y);
  if (lz > ly) { lz = ly; swap(x, y); flag = 1; } else flag = (lz != ly);
  z = cgetr(lz);
  mulrrz_i(z, x,y, lz,flag, sx);
  return z;
}

GEN
sqrr(GEN x)
{
  pari_long lz, sx = signe(x);
  GEN z;

  if (!sx) return real_0_bit(2*expo(x));
  lz = lg(x); z = cgetr(lz);
  sqrz_i(z, x, lz);
  return z;
}

GEN
mulir(GEN x, GEN y)
{
  pari_long sx = signe(x), sy;
  if (!sx) return mul0r(y);
  if (lgefint(x) == 3) {
    GEN z = mulur((ulong)x[2], y);
    if (sx < 0) togglesign(z);
    return z;
  }
  sy = signe(y);
  if (!sy) return real_0_bit(expi(x) + expo(y));
  if (sy < 0) sx = -sx;
  {
    pari_long lz = lg(y), lx = lgefint(x);
    GEN hi, z = cgetr(lz);
    pari_sp av = avma;
    if (lx < (lz>>1) || (lx < lz && lz > MULRR_MULII_LIMIT))
    { /* size mantissa of x < half size of mantissa z, or lx < lz so large
       * that mulrr will call mulii anyway: mulii */
      x = itor(x, lx);
      hi = muliispec_mirror(y+2, x+2, lz-2, lx-2);
      mulrrz_end(z, hi, lz, sx, expo(x)+expo(y), hi[lz]);
    }
    else /* dubious: complete x with 0s and call mulrr */
      mulrrz_i(z, itor(x,lz), y, lz, 0, sx);
    avma = av; return z;
  }
}

/* x + y*z, generic. If lgefint(z) <= 3, caller should use faster variants  */
static GEN
addmulii_gen(GEN x, GEN y, GEN z, pari_long lz)
{
  pari_long lx = lgefint(x), ly;
  pari_sp av;
  GEN t;
  if (lx == 2) return mulii(z,y);
  ly = lgefint(y);
  if (ly == 2) return icopy(x); /* y = 0, wasteful copy */
  av = avma; (void)new_chunk(lx+ly+lz); /*HACK*/
  t = mulii(z, y);
  avma = av; return addii(t,x);
}
/* x + y*z, lgefint(z) == 3 */
static GEN
addmulii_lg3(GEN x, GEN y, GEN z)
{
  pari_long s = signe(z), lx, ly;
  ulong w = z[2];
  pari_sp av;
  GEN t;
  if (w == 1) return (s > 0)? addii(x,y): subii(x,y); /* z = +- 1 */
  lx = lgefint(x);
  ly = lgefint(y);
  if (lx == 2)
  { /* x = 0 */
    if (ly == 2) return gen_0;
    t = muluispec(w, y+2, ly-2);
    if (signe(y) < 0) s = -s;
    setsigne(t, s); return t;
  }
  if (ly == 2) return icopy(x); /* y = 0, wasteful copy */
  av = avma; (void)new_chunk(1+lx+ly);/*HACK*/
  t = muluispec(w, y+2, ly-2);
  if (signe(y) < 0) s = -s;
  setsigne(t, s);
  avma = av; return addii(x,t);
}
/* x + y*z */
GEN
addmulii(GEN x, GEN y, GEN z)
{
  pari_long lz = lgefint(z);
  switch(lz)
  {
    case 2: return icopy(x); /* z = 0, wasteful copy */
    case 3: return addmulii_lg3(x, y, z);
    default:return addmulii_gen(x, y, z, lz);
  }
}
/* x + y*z, returns x itself and not a copy when y*z = 0 */
GEN
addmulii_inplace(GEN x, GEN y, GEN z)
{
  pari_long lz;
  if (lgefint(y) == 2) return x;
  lz = lgefint(z);
  switch(lz)
  {
    case 2: return x;
    case 3: return addmulii_lg3(x, y, z);
    default:return addmulii_gen(x, y, z, lz);
  }
}

/* written by Bruno Haible following an idea of Robert Harley */
pari_long
vals(ulong z)
{
  static char tab[64]={-1,0,1,12,2,6,-1,13,3,-1,7,-1,-1,-1,-1,14,10,4,-1,-1,8,-1,-1,25,-1,-1,-1,-1,-1,21,27,15,31,11,5,-1,-1,-1,-1,-1,9,-1,-1,24,-1,-1,20,26,30,-1,-1,-1,-1,23,-1,19,29,-1,22,18,28,17,16,-1};
#ifdef LONG_IS_64BIT
  pari_long s;
#endif

  if (!z) return -1;
#ifdef LONG_IS_64BIT
  if (! (z&0xffffffffLL)) { s = 32; z >>=32; } else s = 0;
#endif
  z |= ~z + 1;
  z += z << 4;
  z += z << 6;
  z ^= z << 16; /* or  z -= z<<16 */
#ifdef LONG_IS_64BIT
  return s + tab[(z&0xffffffffLL)>>26];
#else
  return tab[z>>26];
#endif
}

GEN
divsi(pari_long x, GEN y)
{
  pari_long p1, s = signe(y);
  LOCAL_HIREMAINDER;

  if (!s) pari_err_INV("divsi",gen_0);
  if (!x || lgefint(y)>3 || ((pari_long)y[2])<0) return gen_0;
#ifdef MINGW64
  hiremainder=0; p1=divll(llabs(x),y[2]);
#else
  hiremainder=0; p1=divll(labs(x),y[2]);
#endif
  if (x<0) { hiremainder = -((pari_long)hiremainder); p1 = -p1; }
  if (s<0) p1 = -p1;
  return stoi(p1);
}

GEN
divir(GEN x, GEN y)
{
  GEN z;
  pari_long ly = lg(y), lx = lgefint(x);
  pari_sp av;

  if (ly == 2) pari_err_INV("divir",y);
  if (lx == 2) return div0r(y);
  if (lx == 3) {
    z = divur(x[2], y);
    if (signe(x) < 0) togglesign(z);
    return z;
  }
  z = cgetr(ly); av = avma;
  affrr(divrr(itor(x, ly+1), y), z);
  avma = av; return z;
}

GEN
divur(ulong x, GEN y)
{
  pari_sp av;
  pari_long ly = lg(y);
  GEN z;

  if (ly == 2) pari_err_INV("divur",y);
  if (!x) return div0r(y);
  if (ly > INVNEWTON_LIMIT) {
    av = avma; z = invr(y);
    if (x == 1) return z;
    return gerepileuptoleaf(av, mulur(x, z));
  }
  z = cgetr(ly); av = avma;
  affrr(divrr(utor(x,ly+1), y), z);
  avma = av; return z;
}

GEN
divsr(pari_long x, GEN y)
{
  pari_sp av;
  pari_long ly = lg(y);
  GEN z;

  if (ly == 2) pari_err_INV("divsr",y);
  if (!x) return div0r(y);
  if (ly > INVNEWTON_LIMIT) {
    av = avma; z = invr(y);
    if (x == 1) return z;
    if (x ==-1) { togglesign(z); return z; }
    return gerepileuptoleaf(av, mulsr(x, z));
  }
  z = cgetr(ly); av = avma;
  affrr(divrr(stor(x,ly+1), y), z);
  avma = av; return z;
}

/* returns 1/y, assume y != 0 */
static GEN
invr_basecase(GEN y)
{
  pari_long ly = lg(y);
  GEN z = cgetr(ly);
  pari_sp av = avma;
  affrr(divrr(real_1(ly+1), y), z);
  avma = av; return z;
}
/* returns 1/b, Newton iteration */
GEN
invr(GEN b)
{
  const pari_long s = 6;
  pari_long i, p, l = lg(b);
  GEN x, a;
  ulong mask;

  if (l <= maxss(INVNEWTON_LIMIT, (1LL<<s) + 2)) {
    if (l == 2) pari_err_INV("invr",b);
    return invr_basecase(b);
  }
  mask = quadratic_prec_mask(l-2);
  for(i=0, p=1; i<s; i++) { p <<= 1; if (mask & 1) p--; mask >>= 1; }
  x = cgetr(l);
  a = rcopy(b); a[1] = _evalexpo(0) | evalsigne(1);
  affrr(invr_basecase(rtor(a, p+2)), x);
  while (mask > 1)
  {
    p <<= 1; if (mask & 1) p--;
    mask >>= 1;
    setlg(a, p + 2);
    setlg(x, p + 2);
    /* TODO: mulrr(a,x) should be a half product (the higher half is known).
     * mulrr(x, ) already is */
    affrr(addrr(x, mulrr(x, subsr(1, mulrr(a,x)))), x);
    avma = (pari_sp)a;
  }
  x[1] = (b[1] & SIGNBITS) | evalexpo(expo(x)-expo(b));
  avma = (pari_sp)x; return x;
}

GEN
modii(GEN x, GEN y)
{
  switch(signe(x))
  {
    case 0: return gen_0;
    case 1: return remii(x,y);
    default:
    {
      pari_sp av = avma;
      (void)new_chunk(lgefint(y));
      x = remii(x,y); avma=av;
      if (x==gen_0) return x;
      return subiispec(y+2,x+2,lgefint(y)-2,lgefint(x)-2);
    }
  }
}

void
modiiz(GEN x, GEN y, GEN z)
{
  const pari_sp av = avma;
  affii(modii(x,y),z); avma=av;
}

GEN
divrs(GEN x, pari_long y)
{
  pari_long i, lx, garde, sh, s = signe(x);
  GEN z;
  LOCAL_HIREMAINDER;

  if (!y) pari_err_INV("divrs",gen_0);
  if (y<0) { s = -s; y = -y; }
  if (!s) return real_0_bit(expo(x) - expu(y));
  if (y==1) { z = rcopy(x); setsigne(z,s); return z; }
  if (y==2) { z = shiftr(x, -1); setsigne(z,s); return z; }

  z=cgetr(lx=lg(x)); hiremainder=0;
  for (i=2; i<lx; i++) z[i] = divll(x[i],y);

  /* we may have hiremainder != 0 ==> garde */
  garde=divll(0,y); sh=bfffo(z[2]);
  if (sh) shift_left(z,z, 2,lx-1, garde,sh);
  z[1] = evalsigne(s) | evalexpo(expo(x)-sh);
  if ((garde << sh) & HIGHBIT) roundr_up_ip(z, lx);
  return z;
}

GEN
divru(GEN x, ulong y)
{
  pari_long i, lx, garde, sh, e, s = signe(x);
  GEN z;
  LOCAL_HIREMAINDER;

  if (!y) pari_err_INV("divru",gen_0);
  if (!s) return real_0_bit(expo(x) - expu(y));
  if (y==1) return rcopy(x);
  if (y==2) return shiftr(x, -1);

  e = expo(x);
  lx = lg(x);
  z = cgetr(lx);
  if (y <= (ulong)x[2])
  {
    hiremainder = 0;
    for (i=2; i<lx; i++) z[i] = divll(x[i],y);
    /* we may have hiremainder != 0 ==> garde */
    garde = divll(0,y);
  }
  else
  {
    pari_long l = lx-1;
    hiremainder = x[2];
    for (i=2; i<l; i++) z[i] = divll(x[i+1],y);
    z[i] = divll(0,y);
    garde = hiremainder;
    e -= BITS_IN_LONG;
  }
  sh=bfffo(z[2]); /* z[2] != 0 */
  if (sh) shift_left(z,z, 2,lx-1, garde,sh);
  z[1] = evalsigne(s) | evalexpo(e-sh);
  if ((garde << sh) & HIGHBIT) roundr_up_ip(z, lx);
  return z;
}

GEN
truedvmdii(GEN x, GEN y, GEN *z)
{
  pari_sp av;
  GEN r, q, *gptr[2];
  if (!is_bigint(y)) return truedvmdis(x, itos(y), z);
  if (z == ONLY_REM) return modii(x,y);

  av = avma;
  q = dvmdii(x,y,&r); /* assume that r is last on stack */
  switch(signe(r))
  {
    case 0:
      if (z) *z = gen_0;
      return q;
    case 1:
      if (z) *z = r; else cgiv(r);
      return q;
    case -1: break;
  }
  q = addis(q, -signe(y));
  if (!z) return gerepileuptoint(av, q);

  *z = subiispec(y+2,r+2, lgefint(y)-2,lgefint(r)-2);
  gptr[0]=&q; gptr[1]=z; gerepilemanysp(av,(pari_sp)r,gptr,2);
  return q;
}
GEN
truedvmdis(GEN x, pari_long y, GEN *z)
{
  pari_sp av = avma;
  pari_long r;
  GEN q;

  if (z == ONLY_REM) return modis(x, y);
  q = divis_rem(x,y,&r);

  if (r >= 0)
  {
    if (z) *z = utoi(r);
    return q;
  }
  q = gerepileuptoint(av, addis(q, (y < 0)? 1: -1));
#ifdef MINGW64
  if (z) *z = utoi(r + llabs(y));
#else
  if (z) *z = utoi(r + labs(y));
#endif
  return q;
}
GEN
truedvmdsi(pari_long x, GEN y, GEN *z)
{
  pari_long q, r;
  if (z == ONLY_REM) return modsi(x, y);
  q = sdivsi_rem(x,y,&r);
  if (r >= 0) {
    if (z) *z = utoi(r);
    return stoi(q);
  }
  q = q - signe(y);
  if (!z) return stoi(q);

  *z = subiuspec(y+2,(ulong)-r, lgefint(y)-2);
  return stoi(q);
}

/* 2^n = shifti(gen_1, n) */
GEN
int2n(pari_long n) {
  pari_long i, m, l;
  GEN z;
  if (n < 0) return gen_0;
  if (n == 0) return gen_1;

  l = dvmdsBIL(n, &m) + 3;
  z = cgetipos(l);
  for (i = 2; i < l; i++) z[i] = 0;
  *int_MSW(z) = 1LL << m; return z;
}
/* To avoid problems when 2^(BIL-1) < n. Overflow cleanly, where int2n
 * returns gen_0 */
GEN
int2u(ulong n) {
  ulong i, m, l;
  GEN z;
  if (n == 0) return gen_1;

  l = dvmduBIL(n, &m) + 3;
  z = cgetipos(l);
  for (i = 2; i < l; i++) z[i] = 0;
  *int_MSW(z) = 1LL << m; return z;
}

GEN
shifti(GEN x, pari_long n)
{
  pari_long s = signe(x);
  GEN y;

  if(s == 0) return gen_0;
  y = shiftispec(x + 2, lgefint(x) - 2, n);
  if (signe(y)) setsigne(y, s);
  return y;
}

/* actual operations will take place on a+2 and b+2: we strip the codewords */
GEN
mulii(GEN a,GEN b)
{
  pari_long sa,sb;
  GEN z;

  sa=signe(a); if (!sa) return gen_0;
  sb=signe(b); if (!sb) return gen_0;
  if (sb<0) sa = -sa;
  z = muliispec(a+2,b+2, lgefint(a)-2,lgefint(b)-2);
  setsigne(z,sa); return z;
}

GEN
sqri(GEN a) { return sqrispec(a+2, lgefint(a)-2); }

/* sqrt()'s result may be off by 1 when a is not representable exactly as a
 * double [64bit machine] */
ulong
usqrt(ulong a)
{
  ulong x = (ulong)sqrt((double)a);
#ifdef LONG_IS_64BIT
  if (x > LOWMASK || x*x > a) x--;
#endif
  return x;
}

/********************************************************************/
/**                                                                **/
/**              EXPONENT / CONVERSION t_REAL --> double           **/
/**                                                                **/
/********************************************************************/

#ifdef LONG_IS_64BIT
pari_long
dblexpo(double x)
{
  union { double f; ulong i; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */

  if (x==0.) return -exp_mid;
  fi.f = x;
  return ((fi.i & (HIGHBIT-1)) >> mant_len) - exp_mid;
}

ulong
dblmantissa(double x)
{
  union { double f; ulong i; } fi;
  const int expo_len = 11; /* number of bits of exponent */

  if (x==0.) return 0;
  fi.f = x;
  return (fi.i << expo_len) | HIGHBIT;
}

GEN
dbltor(double x)
{
  GEN z;
  pari_long e;
  union { double f; ulong i; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int expo_len = 11; /* number of bits of exponent */

  if (x==0.) return real_0_bit(-exp_mid);
  fi.f = x; z = cgetr(DEFAULTPREC);
  {
    const ulong a = fi.i;
    ulong A;
    e = ((a & (HIGHBIT-1)) >> mant_len) - exp_mid;
    if (e == exp_mid+1) pari_err_OVERFLOW("dbltor [NaN or Infinity]");
    A = a << expo_len;
    if (e == -exp_mid)
    { /* unnormalized values */
      int sh = (int)bfffo(A);
      e -= sh-1;
      z[2] = A << sh;
    }
    else
      z[2] = HIGHBIT | A;
    z[1] = _evalexpo(e) | evalsigne(x<0? -1: 1);
  }
  return z;
}

double
rtodbl(GEN x)
{
  pari_long ex,s=signe(x);
  ulong a;
  union { double f; ulong i; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int expo_len = 11; /* number of bits of exponent */

  if (!s || (ex=expo(x)) < - exp_mid) return 0.0;

  /* start by rounding to closest */
  a = (x[2] & (HIGHBIT-1)) + 0x400;
  if (a & HIGHBIT) { ex++; a=0; }
  if (ex >= exp_mid) pari_err_OVERFLOW("t_REAL->double conversion");
  fi.i = ((ex + exp_mid) << mant_len) | (a >> expo_len);
  if (s<0) fi.i |= HIGHBIT;
  return fi.f;
}

#else /* LONG_IS_64BIT */

#if   PARI_DOUBLE_FORMAT == 1
#  define INDEX0 1
#  define INDEX1 0
#elif PARI_DOUBLE_FORMAT == 0
#  define INDEX0 0
#  define INDEX1 1
#endif

pari_long
dblexpo(double x)
{
  union { double f; ulong i[2]; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int shift = mant_len-32;

  if (x==0.) return -exp_mid;
  fi.f = x;
  {
    const ulong a = fi.i[INDEX0];
    return ((a & (HIGHBIT-1)) >> shift) - exp_mid;
  }
}

ulong
dblmantissa(double x)
{
  union { double f; ulong i[2]; } fi;
  const int expo_len = 11; /* number of bits of exponent */

  if (x==0.) return 0;
  fi.f = x;
  {
    const ulong a = fi.i[INDEX0];
    const ulong b = fi.i[INDEX1];
    return HIGHBIT | b >> (BITS_IN_LONG-expo_len) | (a << expo_len);
  }
}

GEN
dbltor(double x)
{
  GEN z;
  pari_long e;
  union { double f; ulong i[2]; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int expo_len = 11; /* number of bits of exponent */
  const int shift = mant_len-32;

  if (x==0.) return real_0_bit(-exp_mid);
  fi.f = x; z = cgetr(DEFAULTPREC);
  {
    const ulong a = fi.i[INDEX0];
    const ulong b = fi.i[INDEX1];
    ulong A, B;
    e = ((a & (HIGHBIT-1)) >> shift) - exp_mid;
    if (e == exp_mid+1) pari_err_OVERFLOW("dbltor [NaN or Infinity]");
    A = b >> (BITS_IN_LONG-expo_len) | (a << expo_len);
    B = b << expo_len;
    if (e == -exp_mid)
    { /* unnormalized values */
      int sh;
      if (A)
      {
        sh = bfffo(A);
        e -= sh-1;
        z[2] = (A << sh) | (B >> (32-sh));
        z[3] = B << sh;
      }
      else
      {
        sh = bfffo(B); /* B != 0 */
        e -= sh-1 + 32;
        z[2] = B << sh;
        z[3] = 0;
      }
    }
    else
    {
      z[3] = B;
      z[2] = HIGHBIT | A;
    }
    z[1] = _evalexpo(e) | evalsigne(x<0? -1: 1);
  }
  return z;
}

double
rtodbl(GEN x)
{
  pari_long ex,s=signe(x),lx=lg(x);
  ulong a,b,k;
  union { double f; ulong i[2]; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int expo_len = 11; /* number of bits of exponent */
  const int shift = mant_len-32;

  if (!s || (ex=expo(x)) < - exp_mid) return 0.0;

  /* start by rounding to closest */
  a = x[2] & (HIGHBIT-1);
  if (lx > 3)
  {
    b = x[3] + 0x400ULL; if (b < 0x400ULL) a++;
    if (a & HIGHBIT) { ex++; a=0; }
  }
  else b = 0;
  if (ex >= exp_mid) pari_err_OVERFLOW("t_REAL->double conversion");
  ex += exp_mid;
  k = (a >> expo_len) | (ex << shift);
  if (s<0) k |= HIGHBIT;
  fi.i[INDEX0] = k;
  fi.i[INDEX1] = (a << (BITS_IN_LONG-expo_len)) | (b >> expo_len);
  return fi.f;
}
#endif /* LONG_IS_64BIT */

#line 2 "../src/kernel/none/add.c"
/* Copyright (C) 2002-2003  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

INLINE GEN
icopy_sign(GEN x, pari_long sx)
{
  GEN y=icopy(x);
  setsigne(y,sx);
  return y;
}

GEN
addsi_sign(pari_long x, GEN y, pari_long sy)
{
  pari_long sx,ly;
  GEN z;

  if (!x) return icopy_sign(y, sy);
  if (!sy) return stoi(x);
  if (x<0) { sx=-1; x=-x; } else sx=1;
  if (sx==sy)
  {
    z = adduispec(x,y+2, lgefint(y)-2);
    setsigne(z,sy); return z;
  }
  ly=lgefint(y);
  if (ly==3)
  {
    const pari_long d = y[2] - x;
    if (!d) return gen_0;
    z=cgeti(3);
    if (y[2] < 0 || d > 0) {
      z[1] = evalsigne(sy) | evallgefint(3);
      z[2] = d;
    }
    else {
      z[1] = evalsigne(-sy) | evallgefint(3);
      z[2] =-d;
    }
    return z;
  }
  z = subiuspec(y+2,x, ly-2);
  setsigne(z,sy); return z;
}
GEN
addui_sign(ulong x, GEN y, pari_long sy)
{
  pari_long ly;
  GEN z;

  if (!x) return icopy_sign(y, sy);
  if (!sy) return utoipos(x);
  if (sy == 1) return adduispec(x,y+2, lgefint(y)-2);
  ly=lgefint(y);
  if (ly==3)
  {
    const ulong t = y[2];
    if (x == t) return gen_0;
    z=cgeti(3);
    if (x < t) {
      z[1] = evalsigne(-1) | evallgefint(3);
      z[2] = t - x;
    }
    else {
      z[1] = evalsigne(1) | evallgefint(3);
      z[2] = x - t;
    }
    return z;
  }
  z = subiuspec(y+2,x, ly-2);
  setsigne(z,-1); return z;
}

/* return gen_0 when the sign is 0 */
GEN
addii_sign(GEN x, pari_long sx, GEN y, pari_long sy)
{
  pari_long lx,ly;
  GEN z;

  if (!sx) return sy? icopy_sign(y, sy): gen_0;
  if (!sy) return icopy_sign(x, sx);
  lx = lgefint(x);
  ly = lgefint(y);
  if (sx==sy)
    z = addiispec(x+2,y+2,lx-2,ly-2);
  else
  { /* sx != sy */
    pari_long i = cmpiispec(x+2,y+2,lx-2,ly-2);
    if (!i) return gen_0;
    /* we must ensure |x| > |y| for subiispec */
    if (i < 0) {
      sx = sy;
      z = subiispec(y+2,x+2,ly-2,lx-2);
    }
    else
      z = subiispec(x+2,y+2,lx-2,ly-2);
  }
  setsigne(z,sx); return z;
}

INLINE GEN
rcopy_sign(GEN x, pari_long sx) { GEN y = rcopy(x); setsigne(y,sx); return y; }

GEN
addir_sign(GEN x, pari_long sx, GEN y, pari_long sy)
{
  pari_long e, l, ly;
  GEN z;

  if (!sx) return rcopy_sign(y, sy);
  e = expo(y) - expi(x);
  if (!sy)
  {
    if (e >= 0) return rcopy_sign(y, sy);
    z = itor(x, nbits2prec(-e));
    setsigne(z, sx); return z;
  }

  ly = lg(y);
  if (e > 0)
  {
    l = ly - divsBIL(e);
    if (l < 3) return rcopy_sign(y, sy);
  }
  else l = ly + nbits2extraprec(-e);
  z = (GEN)avma;
  y = addrr_sign(itor(x,l), sx, y, sy);
  ly = lg(y); while (ly--) *--z = y[ly];
  avma = (pari_sp)z; return z;
}

static GEN
addsr_sign(pari_long x, GEN y, pari_long sy)
{
  pari_long e, l, ly, sx;
  GEN z;

  if (!x) return rcopy_sign(y, sy);
  if (x < 0) { sx = -1; x = -x; } else sx = 1;
  e = expo(y) - expu(x);
  if (!sy)
  {
    if (e >= 0) return rcopy_sign(y, sy);
    if (sx == -1) x = -x;
    return stor(x, nbits2prec(-e));
  }

  ly = lg(y);
  if (e > 0)
  {
    l = ly - divsBIL(e);
    if (l < 3) return rcopy_sign(y, sy);
  }
  else l = ly + nbits2extraprec(-e);
  z = (GEN)avma;
  y = addrr_sign(stor(x,l), sx, y, sy);
  ly = lg(y); while (ly--) *--z = y[ly];
  avma = (pari_sp)z; return z;
}

GEN
addsr(pari_long x, GEN y) { return addsr_sign(x, y, signe(y)); }

GEN
subsr(pari_long x, GEN y) { return addsr_sign(x, y, -signe(y)); }

/* return x + 1, assuming x > 0 is a normalized t_REAL of exponent 0 */
GEN
addrex01(GEN x)
{
  pari_long l = lg(x);
  GEN y = cgetr(l);
  y[1] = evalsigne(1) | _evalexpo(1);
  y[2] = HIGHBIT | (((ulong)x[2] & ~HIGHBIT) >> 1);
  shift_right(y, x, 3,l, x[2], 1);
  return y;
}
/* return subrs(x,1) to the min of (prec(x), prec(x-1) + 1),
 * assuming x > 1 is a normalized t_REAL of exponent 0
 * [ goal: avoid the loss of significant bits form subrs ]*/
GEN
subrex01(GEN x)
{
  pari_long i, sh, k, ly, lx = lg(x);
  ulong u;
  GEN y;
  k = 2;
  u = (ulong)x[2] & (~HIGHBIT);
  while (!u) u = x[++k]; /* terminates: x not a power of 2 */
  ly = (k == 2)? lx: lx - k+3; /* NB: +3, not +2: 1 extra word */
  y = cgetr(ly);
  sh = bfffo(u);
  if (sh)
    shift_left(y+2, x+k, 0, lx-k-1, 0, sh);
  else
  { for (i = 2; i < lx-k+2; i++) y[i] = x[k-2 + i]; }
  for (i = lx-k+2; i < ly; i++) y[i] = 0;
  y[1] = evalsigne(1) | evalexpo(- (bit_accuracy(k) + sh));
  return y;
}

GEN
addrr_sign(GEN x, pari_long sx, GEN y, pari_long sy)
{
  pari_long lx, ex = expo(x);
  pari_long ly, ey = expo(y), e = ey - ex;
  pari_long i, j, lz, ez, m;
  int extend, f2;
  GEN z;
  LOCAL_OVERFLOW;

  if (!sy)
  {
    if (!sx)
    {
      if (e > 0) ex = ey;
      return real_0_bit(ex);
    }
    if (e >= 0) return real_0_bit(ey);
    lz = nbits2prec(-e);
    lx = lg(x); if (lz > lx) lz = lx;
    z = cgetr(lz); while(--lz) z[lz] = x[lz];
    setsigne(z,sx); return z;
  }
  if (!sx)
  {
    if (e <= 0) return real_0_bit(ex);
    lz = nbits2prec(e);
    ly = lg(y); if (lz > ly) lz = ly;
    z = cgetr(lz); while (--lz) z[lz] = y[lz];
    setsigne(z,sy); return z;
  }

  if (e < 0) { swap(x,y); lswap(sx,sy); ey=ex; e=-e; }
  /* now ey >= ex */
  lx = lg(x);
  ly = lg(y);
  /* If exponents differ, need to shift one argument, here x. If
   * extend = 1: extension of x,z by m < BIL bits (round to 1 word) */
  /* in this case, lz = lx + d + 1, otherwise lx + d */
  extend = 0;
  if (e)
  {
    pari_long d = dvmdsBIL(e, &m), l = ly-d;
    if (l <= 2) return rcopy_sign(y, sy);
    if (l > lx) { lz = lx + d + 1; extend = 1; }
    else        { lz = ly; lx = l; }
    if (m)
    { /* shift x right m bits */
      const pari_sp av = avma;
      const ulong sh = BITS_IN_LONG-m;
      GEN p1 = x; x = new_chunk(lx + lz + 1);
      shift_right(x,p1,2,lx, 0,m);
      if (extend) x[lx] = p1[lx-1] << sh;
      avma = av; /* HACK: cgetr(lz) will not overwrite x */
    }
  }
  else
  { /* d = 0 */
    m = 0;
    if (lx > ly) lx = ly;
    lz = lx;
  }

  if (sx == sy)
  { /* addition */
    i = lz-1;
    j = lx-1;
    if (extend) {
      ulong garde = addll(x[lx], y[i]);
      if (m < 4) /* don't extend for few correct bits */
        z = cgetr(--lz);
      else
      {
        z = cgetr(lz);
        z[i] = garde;
      }
    }
    else
    {
      z = cgetr(lz);
      z[i] = addll(x[j], y[i]); j--;
    }
    i--;
    for (; j>=2; i--,j--) z[i] = addllx(x[j],y[i]);
    if (overflow)
    {
      z[1] = 1; /* stops since z[1] != 0 */
      for (;;) { z[i] = (ulong) y[i]+1; if (z[i--]) break; }
      if (i <= 0)
      {
        shift_right(z,z, 2,lz, 1,1);
        z[1] = evalsigne(sx) | evalexpo(ey+1); return z;
      }
    }
    for (; i>=2; i--) z[i] = y[i];
    z[1] = evalsigne(sx) | evalexpo(ey); return z;
  }

  /* subtraction */
  if (e) f2 = 1;
  else
  {
    i = 2; while (i < lx && x[i] == y[i]) i++;
    if (i==lx) return real_0_bit(ey+1 - bit_accuracy(lx));
    f2 = ((ulong)y[i] > (ulong)x[i]);
  }
  /* result is non-zero. f2 = (y > x) */
  i = lz-1; z = cgetr(lz);
  if (f2)
  {
    j = lx-1;
    if (extend) z[i] = subll(y[i], x[lx]);
    else        z[i] = subll(y[i], x[j--]);
    for (i--; j>=2; i--) z[i] = subllx(y[i], x[j--]);
    if (overflow) /* stops since y[1] != 0 */
      for (;;) { z[i] = (ulong) y[i]-1; if (y[i--]) break; }
    for (; i>=2; i--) z[i] = y[i];
    sx = sy;
  }
  else
  {
    if (extend) z[i] = subll(x[lx], y[i]);
    else        z[i] = subll(x[i],  y[i]);
    for (i--; i>=2; i--) z[i] = subllx(x[i], y[i]);
  }

  x = z+2; i = 0; while (!x[i]) i++;
  lz -= i; z += i;
  j = bfffo(z[2]); /* need to shift left by j bits to normalize mantissa */
  ez = ey - (j | (i * BITS_IN_LONG));
  if (extend)
  { /* z was extended by d+1 words [should be e bits = d words + m bits] */
    /* not worth keeping extra word if less than 5 significant bits in there */
    if (m - j < 5 && lz > 3)
    { /* shorten z */
      ulong last = (ulong)z[--lz]; /* cancelled word */

      /* if we need to shift anyway, shorten from left
       * If not, shorten from right, neutralizing last word of z */
      if (j == 0)
        /* stackdummy((pari_sp)(z + lz+1), (pari_sp)(z + lz)); */
        z[lz] = evaltyp(t_VECSMALL) | _evallg(1);
      else
      {
        GEN t = z;
        z++; shift_left(z,t,2,lz-1, last,j);
      }
      if ((last<<j) & HIGHBIT)
      { /* round up */
        i = lz-1;
        while (++((ulong*)z)[i] == 0 && i > 1) i--;
        if (i == 1) { ez++; z[2] = (pari_long)HIGHBIT; }
      }
    }
    else if (j) shift_left(z,z,2,lz-1, 0,j);
  }
  else if (j) shift_left(z,z,2,lz-1, 0,j);
  z[1] = evalsigne(sx) | evalexpo(ez);
  z[0] = evaltyp(t_REAL) | evallg(lz);
  avma = (pari_sp)z; return z;
}
