/* Copyright (C) 2012  The PARI group.

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

/* Not so fast arithmetic with polynomials over FpX */

/*******************************************************************/
/*                                                                 */
/*                             FpXX                                */
/*                                                                 */
/*******************************************************************/
/*Polynomials whose coefficients are either polynomials or integers*/

static ulong
to_FlxqX(GEN P, GEN Q, GEN T, GEN p, GEN *pt_P, GEN *pt_Q, GEN *pt_T)
{
  ulong pp = uel(p,2);
  long v = get_FpX_var(T);
  *pt_P = ZXX_to_FlxX(P, pp, v);
  if (pt_Q) *pt_Q = ZXX_to_FlxX(Q, pp, v);
  *pt_T = ZXT_to_FlxT(T, pp);
  return pp;
}

static GEN
ZXX_copy(GEN a) { return gcopy(a); }

GEN
FpXX_red(GEN z, GEN p)
{
  GEN res;
  long i, l = lg(z);
  res = cgetg(l,t_POL); res[1] = z[1];
  for (i=2; i<l; i++)
  {
    GEN zi = gel(z,i), c;
    if (typ(zi)==t_INT)
      c = modii(zi,p);
    else
    {
      pari_sp av = avma;
      c = FpX_red(zi,p);
      switch(lg(c)) {
        case 2: avma = av; c = gen_0; break;
        case 3: c = gerepilecopy(av, gel(c,2)); break;
      }
    }
    gel(res,i) = c;
  }
  return FpXX_renormalize(res,lg(res));
}
GEN
FpXX_add(GEN x, GEN y, GEN p)
{
  long i,lz;
  GEN z;
  long lx=lg(x);
  long ly=lg(y);
  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx; z = cgetg(lz, t_POL); z[1]=x[1];
  for (i=2; i<ly; i++) gel(z,i) = Fq_add(gel(x,i), gel(y,i), NULL, p);
  for (   ; i<lx; i++) gel(z,i) = gcopy(gel(x,i));
  return FpXX_renormalize(z, lz);
}
GEN
FpXX_sub(GEN x, GEN y, GEN p)
{
  long i,lz;
  GEN z;
  long lx=lg(x);
  long ly=lg(y);
  if (ly <= lx)
  {
    lz = lx; z = cgetg(lz, t_POL); z[1]=x[1];
    for (i=2; i<ly; i++) gel(z,i) = Fq_sub(gel(x,i), gel(y,i), NULL, p);
    for (   ; i<lx; i++) gel(z,i) = gcopy(gel(x,i));
  }
  else
  {
    lz = ly; z = cgetg(lz, t_POL); z[1]=x[1];
    for (i=2; i<lx; i++) gel(z,i) = Fq_sub(gel(x,i), gel(y,i), NULL, p);
    for (   ; i<ly; i++) gel(z,i) = Fq_neg(gel(y,i), NULL, p);
  }
  return FpXX_renormalize(z, lz);
}

static GEN
FpXX_subspec(GEN x, GEN y, GEN p, long nx, long ny)
{
  long i,lz;
  GEN z;
  if (ny <= nx)
  {
    lz = nx+2; z = cgetg(lz, t_POL)+2;
    for (i=0; i<ny; i++) gel(z,i) = Fq_sub(gel(x,i), gel(y,i), NULL, p);
    for (   ; i<nx; i++) gel(z,i) = gcopy(gel(x,i));
  }
  else
  {
    lz = ny+2; z = cgetg(lz, t_POL)+2;
    for (i=0; i<nx; i++) gel(z,i) = Fq_sub(gel(x,i), gel(y,i), NULL, p);
    for (   ; i<ny; i++) gel(z,i) = Fq_neg(gel(y,i), NULL, p);
  }
  return FpXX_renormalize(z-2, lz);
}

GEN
FpXX_neg(GEN x, GEN p)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx,t_POL);
  y[1] = x[1];
  for(i=2; i<lx; i++) gel(y,i) = Fq_neg(gel(x,i), NULL, p);
  return FpXX_renormalize(y, lx);
}

GEN
FpXX_Fp_mul(GEN P, GEN u, GEN p)
{
  long i, lP;
  GEN res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP; i++)
  {
    GEN x = gel(P,i);
    gel(res,i) = typ(x)==t_INT? Fp_mul(x,u,p): FpX_Fp_mul(x,u,p);
  }
  return FpXX_renormalize(res,lP);
}

GEN
FpXX_mulu(GEN P, ulong u, GEN p)
{
  long i, lP;
  GEN res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP; i++)
  {
    GEN x = gel(P,i);
    gel(res,i) = typ(x)==t_INT? Fp_mulu(x,u,p): FpX_mulu(x,u,p);
  }
  return FpXX_renormalize(res,lP);
}

/*******************************************************************/
/*                                                                 */
/*                             (Fp[X]/(Q))[Y]                      */
/*                                                                 */
/*******************************************************************/
/*Not stack clean*/
GEN
Kronecker_to_FpXQX(GEN Z, GEN T, GEN p)
{
  long i,j,lx,l, N = (get_FpX_degree(T)<<1) + 1;
  GEN x, t = cgetg(N,t_POL), z = FpX_red(Z, p);
  t[1] = evalvarn(get_FpX_var(T));
  l = lg(z); lx = (l-2) / (N-2);
  x = cgetg(lx+3,t_POL);
  x[1] = z[1];
  for (i=2; i<lx+2; i++)
  {
    for (j=2; j<N; j++) gel(t,j) = gel(z,j);
    z += (N-2);
    gel(x,i) = FpX_rem(FpX_renormalize(t,N), T,p);
  }
  N = (l-2) % (N-2) + 2;
  for (j=2; j<N; j++) gel(t,j) = gel(z,j);
  gel(x,i) = FpX_rem(FpX_renormalize(t,N), T,p);
  return FpXQX_renormalize(x, i+1);
}

/* shallow, n = deg(T) */
GEN
Kronecker_to_ZXX(GEN z, long n, long v)
{
  long i,j,lx,l, N = (n<<1)+1;
  GEN x, t;
  l = lg(z); lx = (l-2) / (N-2);
  x = cgetg(lx+3,t_POL);
  x[1] = z[1];
  for (i=2; i<lx+2; i++)
  {
    t = cgetg(N,t_POL); t[1] = evalvarn(v);
    for (j=2; j<N; j++) gel(t,j) = gel(z,j);
    z += (N-2);
    gel(x,i) = ZX_renormalize(t,N);
  }
  N = (l-2) % (N-2) + 2;
  t = cgetg(N,t_POL); t[1] = evalvarn(v);
  for (j=2; j<N; j++) gel(t,j) = gel(z,j);
  gel(x,i) = ZX_renormalize(t,N);
  return ZXX_renormalize(x, i+1);
}
/* shallow */
GEN
ZXX_mul_Kronecker(GEN x, GEN y, long n)
{ return ZX_mul(ZXX_to_Kronecker(x,n), ZXX_to_Kronecker(y,n)); }

GEN
ZXX_sqr_Kronecker(GEN x, long n)
{ return ZX_sqr(ZXX_to_Kronecker(x,n)); }

GEN
FpXQX_red(GEN z, GEN T, GEN p)
{
  long i, l = lg(z);
  GEN res = cgetg(l,t_POL); res[1] = z[1];
  for(i=2;i<l;i++)
    if (typ(gel(z,i)) == t_INT)
      gel(res,i) = modii(gel(z,i),p);
    else
      gel(res,i) = FpXQ_red(gel(z,i),T,p);
  return FpXQX_renormalize(res,l);
}

static int
ZXX_is_ZX_spec(GEN a,long na)
{
  long i;
  for(i=0;i<na;i++)
    if(typ(gel(a,i))!=t_INT) return 0;
  return 1;
}

static int
ZXX_is_ZX(GEN a) { return ZXX_is_ZX_spec(a+2,lgpol(a)); }

static GEN
FpXX_FpX_mulspec(GEN P, GEN U, GEN p, long v, long lU)
{
  long i, lP =lg(P);
  GEN res;
  res = cgetg(lP, t_POL); res[1] = P[1];
  for(i=2; i<lP; i++)
  {
    GEN Pi = gel(P,i);
    gel(res,i) = typ(Pi)==t_INT? FpX_Fp_mulspec(U, Pi, p, lU):
                                 FpX_mulspec(U, Pi+2, p, lU, lgpol(Pi));
    setvarn(gel(res,i),v);
  }
  return FpXQX_renormalize(res,lP);
}

GEN
FpXX_FpX_mul(GEN P, GEN U, GEN p)
{ return FpXX_FpX_mulspec(P,U+2,p,varn(U),lgpol(U)); }

static GEN
FpXY_FpY_mulspec(GEN x, GEN y, GEN T, GEN p, long lx, long ly)
{
  pari_sp av = avma;
  long v = fetch_var();
  GEN z = RgXY_swapspec(x,get_FpX_degree(T)-1,v,lx);
  z = FpXX_FpX_mulspec(z,y,p,v,ly);
  z = RgXY_swapspec(z+2,lx+ly+3,get_FpX_var(T),lgpol(z));
  (void)delete_var(); return gerepilecopy(av,z);
}

static GEN
FpXQX_mulspec(GEN x, GEN y, GEN T, GEN p, long lx, long ly)
{
  pari_sp av = avma;
  GEN z, kx, ky;
  long n;
  if (ZXX_is_ZX_spec(y,ly))
  {
    if (ZXX_is_ZX_spec(x,lx))
      return FpX_mulspec(x,y,p,lx,ly);
    else
      return FpXY_FpY_mulspec(x,y,T,p,lx,ly);
  } else if (ZXX_is_ZX_spec(x,lx))
      return FpXY_FpY_mulspec(y,x,T,p,ly,lx);
  n = get_FpX_degree(T);
  kx = ZXX_to_Kronecker_spec(x, lx, n);
  ky = ZXX_to_Kronecker_spec(y, ly, n);
  z = Kronecker_to_FpXQX(ZX_mul(ky,kx), T, p);
  return gerepileupto(av, z);
}

GEN
FpXQX_mul(GEN x, GEN y, GEN T, GEN p)
{
  GEN z = FpXQX_mulspec(x+2,y+2,T,p,lgpol(x),lgpol(y));
  setvarn(z,varn(x)); return z;
}

GEN
FpXQX_sqr(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z, kx;
  if (ZXX_is_ZX(x)) return ZX_sqr(x);
  kx= ZXX_to_Kronecker(x, get_FpX_degree(T));
  z = Kronecker_to_FpXQX(ZX_sqr(kx), T, p);
  return gerepileupto(av, z);
}

GEN
FpXQX_FpXQ_mul(GEN P, GEN U, GEN T, GEN p)
{
  long i, lP;
  GEN res;
  res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP; i++)
    gel(res,i) = typ(gel(P,i))==t_INT? FpX_Fp_mul(U, gel(P,i), p):
                                       FpXQ_mul(U, gel(P,i), T,p);
  return FpXQX_renormalize(res,lP);
}

/* x and y in Z[Y][X]. Assume T irreducible mod p */
static GEN
FpXQX_divrem_basecase(GEN x, GEN y, GEN T, GEN p, GEN *pr)
{
  long vx, dx, dy, dz, i, j, sx, lr;
  pari_sp av0, av, tetpil;
  GEN z,p1,rem,lead;

  if (!T) return FpX_divrem(x,y,p,pr);
  if (!signe(y)) pari_err_INV("FpX_divrem",y);
  vx=varn(x); dy=degpol(y); dx=degpol(x);
  if (dx < dy)
  {
    if (pr)
    {
      av0 = avma; x = FpXQX_red(x, T, p);
      if (pr == ONLY_DIVIDES) { avma=av0; return signe(x)? NULL: pol_0(vx); }
      if (pr == ONLY_REM) return x;
      *pr = x;
    }
    return pol_0(vx);
  }
  lead = leading_term(y);
  if (!dy) /* y is constant */
  {
    if (pr && pr != ONLY_DIVIDES)
    {
      if (pr == ONLY_REM) return pol_0(vx);
      *pr = pol_0(vx);
    }
    if (gequal1(lead)) return FpXQX_red(x,T,p);
    av0 = avma; x = FqX_Fq_mul(x, Fq_inv(lead, T,p), T,p);
    return gerepileupto(av0,x);
  }
  av0 = avma; dz = dx-dy;
  if (lgefint(p) == 3)
  { /* assume ab != 0 mod p */
    {
      GEN *gptr[2];
      GEN a, b, t;
      ulong pp = to_FlxqX(x, y, T, p, &a, &b, &t);
      z = FlxqX_divrem(a,b,t,pp,pr);
      tetpil=avma;
      z = FlxX_to_ZXX(z);
      if (pr && pr != ONLY_DIVIDES && pr != ONLY_REM)
        *pr = FlxX_to_ZXX(*pr);
      else return gerepile(av0,tetpil,z);
      gptr[0]=pr; gptr[1]=&z;
      gerepilemanysp(av0,tetpil,gptr,2);
      return z;
    }
  }
  lead = gequal1(lead)? NULL: gclone(Fq_inv(lead,T,p));
  avma = av0;
  z = cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2; y += 2; z += 2;

  p1 = gel(x,dx); av = avma;
  gel(z,dz) = lead? gerepileupto(av, Fq_mul(p1,lead, T, p)): gcopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=gel(x,i);
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = Fq_sub(p1, Fq_mul(gel(z,j),gel(y,i-j),NULL,p),NULL,p);
    if (lead) p1 = Fq_mul(p1, lead, NULL,p);
    tetpil=avma; gel(z,i-dy) = gerepile(av,tetpil,Fq_red(p1,T,p));
  }
  if (!pr) { if (lead) gunclone(lead); return z-2; }

  rem = (GEN)avma; av = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = Fq_sub(p1, Fq_mul(gel(z,j),gel(y,i-j),NULL,p),NULL,p);
    tetpil=avma; p1 = Fq_red(p1, T, p); if (signe(p1)) { sx = 1; break; }
    if (!i) break;
    avma=av;
  }
  if (pr == ONLY_DIVIDES)
  {
    if (lead) gunclone(lead);
    if (sx) { avma=av0; return NULL; }
    avma = (pari_sp)rem; return z-2;
  }
  lr=i+3; rem -= lr;
  rem[0] = evaltyp(t_POL) | evallg(lr);
  rem[1] = z[-1];
  p1 = gerepile((pari_sp)rem,tetpil,p1);
  rem += 2; gel(rem,i) = p1;
  for (i--; i>=0; i--)
  {
    av=avma; p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = Fq_sub(p1, Fq_mul(gel(z,j),gel(y,i-j), NULL,p), NULL,p);
    tetpil=avma; gel(rem,i) = gerepile(av,tetpil, Fq_red(p1, T, p));
  }
  rem -= 2;
  if (lead) gunclone(lead);
  if (!sx) (void)FpXQX_renormalize(rem, lr);
  if (pr == ONLY_REM) return gerepileupto(av0,rem);
  *pr = rem; return z-2;
}

GEN
FpXQX_gcd(GEN P, GEN Q, GEN T, GEN p)
{
  pari_sp av=avma, av0;
  GEN R;
  if (lgefint(p) == 3)
  {
    GEN Pl, Ql, Tl, U;
    ulong pp = to_FlxqX(P, Q, T, p, &Pl, &Ql, &Tl);
    U  = FlxqX_gcd(Pl, Ql, Tl, pp);
    return gerepileupto(av, FlxX_to_ZXX(U));
  }
  P = FpXX_red(P, p); av0 = avma;
  Q = FpXX_red(Q, p);
  while (signe(Q))
  {
    av0 = avma; R = FpXQX_rem(P,Q,T,p); P=Q; Q=R;
  }
  avma = av0; return gerepileupto(av, P);
}

/* x and y in Z[Y][X], return lift(gcd(x mod T,p, y mod T,p)). Set u and v st
 * ux + vy = gcd (mod T,p) */
GEN
FpXQX_extgcd(GEN x, GEN y, GEN T, GEN p, GEN *ptu, GEN *ptv)
{
  GEN a, b, q, r, u, v, d, d1, v1;
  long vx = varn(x);
  pari_sp ltop=avma;
  if (lgefint(p) == 3)
  {
    GEN Pl, Ql, Tl, Dl;
    ulong pp = to_FlxqX(x, y, T, p, &Pl, &Ql, &Tl);
    Dl = FlxqX_extgcd(Pl, Ql, Tl, pp, ptu, ptv);
    if (ptu) *ptu = FlxX_to_ZXX(*ptu);
    *ptv = FlxX_to_ZXX(*ptv);
    d = FlxX_to_ZXX(Dl);
  }
  else
  {
    a = FpXQX_red(x, T, p);
    b = FpXQX_red(y, T, p);
    d = a; d1 = b; v = pol_0(vx); v1 = pol_1(vx);
    while (signe(d1))
    {
      q = FpXQX_divrem(d,d1,T,p, &r);
      v = FpXX_sub(v, FpXQX_mul(q,v1, T,p), p);
      u=v; v=v1; v1=u;
      u=r; d=d1; d1=u;
    }
    if (ptu) *ptu = FpXQX_div(FpXX_sub(d, FpXQX_mul(b,v, T,p), p),a, T,p);
    *ptv = v;
  }
  gerepileall(ltop,ptu?3:2,&d,ptv,ptu);
  return d;
}

/***********************************************************************/
/**                                                                   **/
/**                       Barrett reduction                           **/
/**                                                                   **/
/***********************************************************************/

/* Return new lgpol */
static long
ZXX_lgrenormalizespec(GEN x, long lx)
{
  long i;
  for (i = lx-1; i>=0; i--)
    if (signe(gel(x,i))) break;
  return i+1;
}

static GEN
FpXQX_invBarrett_basecase(GEN S, GEN T, GEN p)
{
  long i, l=lg(S)-1, lr = l-1, k;
  GEN r=cgetg(lr, t_POL); r[1]=S[1];
  gel(r,2) = gen_1;
  for (i=3; i<lr; i++)
  {
    pari_sp av = avma;
    GEN u = gel(S,l-i+2);
    for (k=3; k<i; k++)
      u = Fq_add(u, Fq_mul(gel(S,l-i+k), gel(r,k), NULL, p), NULL, p);
    gel(r,i) = gerepileupto(av, Fq_red(Fq_neg(u, NULL, p), T, p));
  }
  return FpXQX_renormalize(r,lr);
}

INLINE GEN
FpXQX_recipspec(GEN x, long l, long n)
{
  return RgX_recipspec_shallow(x, l, n);
}

static GEN
FpXQX_invBarrett_Newton(GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  long nold, lx, lz, lq, l = degpol(S), i, lQ;
  GEN q, y, z, x = cgetg(l+2, t_POL) + 2;
  ulong mask = quadratic_prec_mask(l-2); /* assume l > 2 */
  for (i=0;i<l;i++) gel(x,i) = gen_0;
  q = RgX_recipspec_shallow(S+2,l+1,l+1); lQ = lgpol(q); q+=2;
  /* We work on _spec_ FpX's, all the l[xzq] below are lgpol's */

  /* initialize */
  gel(x,0) = Fq_inv(gel(q,0), T, p);
  if (lQ>1) gel(q,1) = Fq_red(gel(q,1), T, p);
  if (lQ>1 && signe(gel(q,1)))
  {
    GEN u = gel(q, 1);
    if (!gequal1(gel(x,0))) u = Fq_mul(u, Fq_sqr(gel(x,0), T, p), T, p);
    gel(x,1) = Fq_neg(u, T, p); lx = 2;
  }
  else
    lx = 1;
  nold = 1;
  for (; mask > 1; )
  { /* set x -= x(x*q - 1) + O(t^(nnew + 1)), knowing x*q = 1 + O(t^(nold+1)) */
    long i, lnew, nnew = nold << 1;

    if (mask & 1) nnew--;
    mask >>= 1;

    lnew = nnew + 1;
    lq = ZXX_lgrenormalizespec(q, minss(lQ,lnew));
    z = FpXQX_mulspec(x, q, T, p, lx, lq); /* FIXME: high product */
    lz = lgpol(z); if (lz > lnew) lz = lnew;
    z += 2;
    /* subtract 1 [=>first nold words are 0]: renormalize so that z(0) != 0 */
    for (i = nold; i < lz; i++) if (signe(gel(z,i))) break;
    nold = nnew;
    if (i >= lz) continue; /* z-1 = 0(t^(nnew + 1)) */

    /* z + i represents (x*q - 1) / t^i */
    lz = ZXX_lgrenormalizespec (z+i, lz-i);
    z = FpXQX_mulspec(x, z+i, T, p, lx, lz); /* FIXME: low product */
    lz = lgpol(z); z += 2;
    if (lz > lnew-i) lz = ZXX_lgrenormalizespec(z, lnew-i);

    lx = lz+ i;
    y  = x + i; /* x -= z * t^i, in place */
    for (i = 0; i < lz; i++) gel(y,i) = Fq_neg(gel(z,i), T, p);
  }
  x -= 2; setlg(x, lx + 2); x[1] = S[1];
  return gerepilecopy(av, x);
}

const long FpXQX_INVBARRETT_LIMIT = 50;
const long FpXQX_DIVREM_BARRETT_LIMIT = 50;
const long FpXQX_REM_BARRETT_LIMIT = 50;

/* 1/polrecip(S)+O(x^(deg(S)-1)) */
GEN
FpXQX_invBarrett(GEN S, GEN T, GEN p)
{
  pari_sp ltop = avma;
  long l = lg(S);
  GEN r;
  if (l<5) return pol_0(varn(S));
  if (l<=FpXQX_INVBARRETT_LIMIT)
  {
    GEN c = gel(S,l-1), ci=gen_1;
    if (!gequal1(c))
    {
      ci = Fq_inv(c, T, p);
      S = FqX_Fq_mul(S, ci, T, p);
      r = FpXQX_invBarrett_basecase(S, T, p);
      r = FqX_Fq_mul(r, ci, T, p);
    } else
      r = FpXQX_invBarrett_basecase(S, T, p);
  }
  else
    r = FpXQX_invBarrett_Newton(S, T, p);
  return gerepileupto(ltop, r);
}

/* Compute x mod S where 2 <= degpol(S) <= l+1 <= 2*(degpol(S)-1)
 * and mg is the Barrett inverse of S. */
static GEN
FpXQX_divrem_Barrettspec(GEN x, long l, GEN mg, GEN S, GEN T, GEN p, GEN *pr)
{
  GEN q, r;
  long lt = degpol(S); /*We discard the leading term*/
  long ld, lm, lT, lmg;
  ld = l-lt;
  lm = minss(ld, lgpol(mg));
  lT  = ZXX_lgrenormalizespec(S+2,lt);
  lmg = ZXX_lgrenormalizespec(mg+2,lm);
  q = FpXQX_recipspec(x+lt,ld,ld);                 /* q = rec(x)     lq<=ld*/
  q = FpXQX_mulspec(q+2,mg+2,T,p,lgpol(q),lmg);    /* q = rec(x) * mg lq<=ld+lm*/
  q = FpXQX_recipspec(q+2,minss(ld,lgpol(q)),ld);  /* q = rec (rec(x) * mg) lq<=ld*/
  if (!pr) return q;
  r = FpXQX_mulspec(q+2,S+2,T,p,lgpol(q),lT);      /* r = q*pol        lr<=ld+lt*/
  r = FpXX_subspec(x,r+2,p,lt,minss(lt,lgpol(r))); /* r = x - r   lr<=lt */
  if (pr == ONLY_REM) return r;
  *pr = r; return q;
}

static GEN
FpXQX_divrem_Barrett_noGC(GEN x, GEN mg, GEN S, GEN T, GEN p, GEN *pr)
{
  long l = lgpol(x), lt = degpol(S), lm = 2*lt-1;
  GEN q = NULL, r;
  long i;
  if (l <= lt)
  {
    if (pr == ONLY_REM) return ZXX_copy(x);
    if (pr == ONLY_DIVIDES) return signe(x)? NULL: pol_0(varn(x));
    if (pr) *pr =  ZXX_copy(x);
    return pol_0(varn(x));
  }
  if (lt <= 1)
    return FpXQX_divrem_basecase(x,S,T,p,pr);
  if (pr != ONLY_REM && l>lm)
  {
    q = cgetg(l-lt+2, t_POL);
    for (i=0;i<l-lt;i++) gel(q+2,i) = gen_0;
  }
  r = l>lm ? shallowcopy(x): x;
  while (l>lm)
  {
    GEN zr, zq = FpXQX_divrem_Barrettspec(r+2+l-lm,lm,mg,S,T,p,&zr);
    long lz = lgpol(zr);
    if (pr != ONLY_REM)
    {
      long lq = lgpol(zq);
      for(i=0; i<lq; i++) gel(q+2+l-lm,i) = gel(zq,2+i);
    }
    for(i=0; i<lz; i++) gel(r+2+l-lm,i) = gel(zr,2+i);
    l = l-lm+lz;
  }
  if (pr != ONLY_REM)
  {
    if (l > lt)
    {
      GEN zq = FpXQX_divrem_Barrettspec(r+2,l,mg,S,T,p,&r);
      if (!q) q = zq;
      else
      {
        long lq = lgpol(zq);
        for(i=0; i<lq; i++) gel(q+2,i) = gel(zq,2+i);
      }
    }
    else
    { setlg(r, l+2); r = ZXX_copy(r); }
  }
  else
  {
    if (l > lt)
      (void) FpXQX_divrem_Barrettspec(r+2,l,mg,S,T,p,&r);
    else
    { setlg(r, l+2); r = ZXX_copy(r); }
    r[1] = x[1]; return FpXQX_renormalize(r, lg(r));
  }
  if (pr) { r[1] = x[1]; r = FpXQX_renormalize(r, lg(r)); }
  q[1] = x[1]; q = FpXQX_renormalize(q, lg(q));
  if (pr == ONLY_DIVIDES) return signe(r)? NULL: q;
  if (pr) *pr = r;
  return q;
}

GEN
FpXQX_divrem_Barrett(GEN x, GEN B, GEN S, GEN T, GEN p, GEN *pr)
{
  pari_sp av = avma;
  GEN q = FpXQX_divrem_Barrett_noGC(x,B,S,T,p,pr);
  if (!q) {avma=av; return NULL;}
  if (!pr || pr==ONLY_REM || pr==ONLY_DIVIDES) return gerepilecopy(av, q);
  gerepileall(av,2,&q,pr);
  return q;
}

GEN
FpXQX_divrem(GEN x, GEN y, GEN T, GEN p, GEN *pr)
{
  long dy = degpol(y), dx = degpol(x), d = dx-dy;
  if (pr==ONLY_REM) return FpXQX_rem(x, y, T, p);
  if (d+3 < FpXQX_DIVREM_BARRETT_LIMIT)
    return FpXQX_divrem_basecase(x,y,T,p,pr);
  else
  {
    pari_sp av=avma;
    GEN mg = FpXQX_invBarrett(y, T, p);
    GEN q = FpXQX_divrem_Barrett_noGC(x,mg,y,T,p,pr);
    if (!q) {avma=av; return NULL;}
    if (!pr || pr==ONLY_DIVIDES) return gerepilecopy(av, q);
    gerepileall(av,2,&q,pr);
    return q;
  }
}

GEN
FpXQX_rem_Barrett(GEN x, GEN mg, GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  return gerepileupto(av, FpXQX_divrem_Barrett_noGC(x,mg,S, T, p, ONLY_REM));
}

GEN
FpXQX_rem(GEN x, GEN y, GEN T, GEN p)
{
  long dy = degpol(y), dx = degpol(x), d = dx-dy;
  if (d < 0) return FpXQX_red(x, T, p);
  if (d+3 < FpXQX_REM_BARRETT_LIMIT)
    return FpXQX_divrem_basecase(x,y, T, p, ONLY_REM);
  else
  {
    pari_sp av=avma;
    GEN mg = FpXQX_invBarrett(y, T, p);
    GEN r = FpXQX_divrem_Barrett_noGC(x, mg, y, T, p, ONLY_REM);
    return gerepileupto(av, r);
  }
}

/* x + y*z mod p */
INLINE GEN
Fq_addmul(GEN x, GEN y, GEN z, GEN T, GEN p)
{
  pari_sp av;
  if (!signe(y) || !signe(z)) return Fq_red(x, T, p);
  if (!signe(x)) return Fq_mul(z,y, T, p);
  av = avma;
  return gerepileupto(av, Fq_add(x, Fq_mul(y, z, T, p), T, p));
}

GEN
FpXQX_div_by_X_x(GEN a, GEN x, GEN T, GEN p, GEN *r)
{
  long l = lg(a)-1, i;
  GEN z = cgetg(l, t_POL);
  z[1] = evalsigne(1) | evalvarn(0);
  gel(z, l-1) = gel(a,l);
  for (i=l-2; i>1; i--) /* z[i] = a[i+1] + x*z[i+1] */
    gel(z, i) = Fq_addmul(gel(a,i+1), x, gel(z,i+1), T, p);
  if (r) *r = Fq_addmul(gel(a,2), x, gel(z,2), T, p);
  return z;
}

struct _FpXQX { GEN T,p; };

static GEN _FpXQX_mul(void *data, GEN a,GEN b)
{
  struct _FpXQX *d=(struct _FpXQX*)data;
  return FpXQX_mul(a,b,d->T,d->p);
}

static GEN _FpXQX_sqr(void *data, GEN a)
{
  struct _FpXQX *d=(struct _FpXQX*)data;
  return FpXQX_sqr(a, d->T, d->p);
}

GEN
FpXQX_powu(GEN x, ulong n, GEN T, GEN p)
{
  struct _FpXQX D;
  if (n==0) return pol_1(varn(x));
  D.T = T; D.p = p;
  return gen_powu(x, n, (void *)&D, _FpXQX_sqr, _FpXQX_mul);
}

GEN
FpXQXV_prod(GEN V, GEN T, GEN p)
{
  if (lgefint(p) == 3)
  {
    pari_sp av = avma;
    ulong pp = p[2];
    GEN Tl = ZXT_to_FlxT(T, pp);
    GEN Vl = ZXXV_to_FlxXV(V, pp, get_FpX_var(T));
    Tl = FlxqXV_prod(Vl, Tl, pp);
    return gerepileupto(av, FlxX_to_ZXX(Tl));
  }
  else
  {
    struct _FpXQX d;
    d.p=p;
    d.T=T;
    return gen_product(V, (void*)&d, &_FpXQX_mul);
  }
}

static GEN
_FpXQX_divrem(void * E, GEN x, GEN y, GEN *r)
{
  struct _FpXQX *d = (struct _FpXQX *) E;
  return FpXQX_divrem(x, y, d->T, d->p, r);
}

static GEN
_FpXQX_add(void * E, GEN x, GEN y)
{
  struct _FpXQX *d = (struct _FpXQX *) E;
  return FpXX_add(x, y, d->p);
}

static struct bb_ring FpXQX_ring = { _FpXQX_add, _FpXQX_mul, _FpXQX_sqr };

GEN
FpXQX_digits(GEN x, GEN B, GEN T, GEN p)
{
  pari_sp av = avma;
  long d = degpol(B), n = (lgpol(x)+d-1)/d;
  GEN z;
  struct _FpXQX D;
  D.T = T; D.p = p;
  z = gen_digits(x, B, n, (void *)&D, &FpXQX_ring, _FpXQX_divrem);
  return gerepileupto(av, z);
}

GEN
FpXQX_fromdigits(GEN x, GEN B, GEN T, GEN p)
{
  pari_sp av = avma;
  struct _FpXQX D;
  GEN z;
  D.T = T; D.p = p;
  z = gen_fromdigits(x,B,(void *)&D, &FpXQX_ring);
  return gerepileupto(av, z);
}

/* Q an FpXY (t_POL with FpX coeffs), evaluate at X = x */
GEN
FpXY_evalx(GEN Q, GEN x, GEN p)
{
  long i, lb = lg(Q);
  GEN z;
  z = cgetg(lb, t_POL); z[1] = Q[1];
  for (i=2; i<lb; i++)
  {
    GEN q = gel(Q,i);
    gel(z,i) = typ(q) == t_INT? modii(q,p): FpX_eval(q, x, p);
  }
  return FpX_renormalize(z, lb);
}
/* Q an FpXY, evaluate at Y = y */
GEN
FpXY_evaly(GEN Q, GEN y, GEN p, long vx)
{
  pari_sp av = avma;
  long i, lb = lg(Q);
  GEN z;
  if (!signe(Q)) return pol_0(vx);
  if (lb == 3 || !signe(y)) {
    z = gel(Q, 2);
    return typ(z)==t_INT? scalar_ZX(z, vx): ZX_copy(z);
  }
  z = gel(Q, lb-1);
  if (typ(z) == t_INT) z = scalar_ZX_shallow(z, vx);
  for (i=lb-2; i>=2; i--) z = Fq_add(gel(Q,i), FpX_Fp_mul(z, y, p), NULL, p);
  return gerepileupto(av, z);
}
/* Q an FpXY, evaluate at (X,Y) = (x,y) */
GEN
FpXY_eval(GEN Q, GEN y, GEN x, GEN p)
{
  pari_sp av = avma;
  return gerepileuptoint(av, FpX_eval(FpXY_evalx(Q, x, p), y, p));
}

GEN
FpXY_FpXQV_evalx(GEN P, GEN x, GEN T, GEN p)
{
  long i, lP = lg(P);
  GEN res = cgetg(lP,t_POL);
  res[1] = P[1];
  for(i=2; i<lP; i++)
    gel(res,i) = typ(gel(P,i))==t_INT? icopy(gel(P,i)):
                                       FpX_FpXQV_eval(gel(P,i), x, T, p);
  return FlxX_renormalize(res, lP);
}

GEN
FpXY_FpXQ_evalx(GEN P, GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  long n = brent_kung_optpow(get_FpX_degree(T)-1,lgpol(P),1);
  GEN xp = FpXQ_powers(x, n, T, p);
  return gerepileupto(av, FpXY_FpXQV_evalx(P, xp, T, p));
}

/*******************************************************************/
/*                                                                 */
/*                       (Fp[X]/T(X))[Y] / S(Y)                    */
/*                                                                 */
/*******************************************************************/

/*Preliminary implementation to speed up FpX_ffisom*/
typedef struct {
  GEN S, T, p;
} FpXYQQ_muldata;

/* reduce x in Fp[X, Y] in the algebra Fp[X,Y]/ (S(X),T(Y)) */
static GEN
FpXYQQ_redswap(GEN x, GEN S, GEN T, GEN p)
{
  pari_sp ltop=avma;
  long n = get_FpX_degree(S);
  long m = get_FpX_degree(T);
  long v = get_FpX_var(T);
  GEN V = RgXY_swap(x,m,v);
  V = FpXQX_red(V,S,p);
  V = RgXY_swap(V,n,v);
  return gerepilecopy(ltop,V);
}
static GEN
FpXYQQ_sqr(void *data, GEN x)
{
  FpXYQQ_muldata *D = (FpXYQQ_muldata*)data;
  return FpXYQQ_redswap(FpXQX_sqr(x, D->T, D->p),D->S,D->T,D->p);

}
static GEN
FpXYQQ_mul(void *data, GEN x, GEN y)
{
  FpXYQQ_muldata *D = (FpXYQQ_muldata*)data;
  return FpXYQQ_redswap(FpXQX_mul(x,y, D->T, D->p),D->S,D->T,D->p);
}

/* x in Z[X,Y], S in Z[X] over Fq = Z[Y]/(p,T); compute lift(x^n mod (S,T,p)) */
GEN
FpXYQQ_pow(GEN x, GEN n, GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  FpXYQQ_muldata D;
  GEN y;
  if (lgefint(p) == 3)
  {
    ulong pp = to_FlxqX(x, NULL, T, p, &x, NULL, &T);
    S = ZX_to_Flx(S, pp);
    y = FlxX_to_ZXX( FlxYqq_pow(x, n, S, T, pp) );
  }
  else
  {
    D.S = S;
    D.T = T;
    D.p = p;
    y = gen_pow(x, n, (void*)&D, &FpXYQQ_sqr, &FpXYQQ_mul);
  }
  return gerepileupto(av, y);
}

GEN
FpXQXQ_mul(GEN x, GEN y, GEN S, GEN T, GEN p) {
  return FpXQX_rem(FpXQX_mul(x, y, T, p), S, T, p);
}

GEN
FpXQXQ_sqr(GEN x, GEN S, GEN T, GEN p) {
  return FpXQX_rem(FpXQX_sqr(x, T, p), S, T, p);
}

/* Inverse of x in Z/pZ[X]/(pol) or NULL if inverse doesn't exist
 * return lift(1 / (x mod (p,pol))) */
GEN
FpXQXQ_invsafe(GEN x, GEN S, GEN T, GEN p)
{
  GEN V, z = FpXQX_extgcd(S, x, T, p, NULL, &V);
  if (degpol(z)) return NULL;
  z = gel(z,2);
  z = typ(z)==t_INT ? Fp_invsafe(z,p) : FpXQ_invsafe(z,T,p);
  if (!z) return NULL;
  return typ(z)==t_INT ? FpXX_Fp_mul(V, z, p): FpXQX_FpXQ_mul(V, z, T, p);
}

GEN
FpXQXQ_inv(GEN x, GEN S, GEN T,GEN p)
{
  pari_sp av = avma;
  GEN U = FpXQXQ_invsafe(x, S, T, p);
  if (!U) pari_err_INV("FpXQXQ_inv",x);
  return gerepileupto(av, U);
}

GEN
FpXQXQ_div(GEN x,GEN y,GEN S, GEN T,GEN p)
{
  pari_sp av = avma;
  return gerepileupto(av, FpXQXQ_mul(x, FpXQXQ_inv(y,S,T,p),S,T,p));
}

typedef struct {
  GEN T, S;
  GEN p;
} FpXQXQ_muldata;
static GEN
_FpXQXQ_add(void *data, GEN x, GEN y) {
  FpXQXQ_muldata *d = (FpXQXQ_muldata*) data;
  return FpXX_add(x,y, d->p);
}
static GEN
_FpXQXQ_cmul(void *data, GEN P, long a, GEN x) {
  FpXQXQ_muldata *d = (FpXQXQ_muldata*) data;
  GEN y = gel(P,a+2);
  return typ(y)==t_INT ? FpXX_Fp_mul(x,y, d->p):
                         FpXX_FpX_mul(x,y,d->p);
}
static GEN
_FpXQXQ_red(void *data, GEN x) {
  FpXQXQ_muldata *d = (FpXQXQ_muldata*) data;
  return FpXQX_red(x, d->T, d->p);
}
static GEN
_FpXQXQ_mul(void *data, GEN x, GEN y) {
  FpXQXQ_muldata *d = (FpXQXQ_muldata*) data;
  return FpXQXQ_mul(x,y, d->S,d->T, d->p);
}
static GEN
_FpXQXQ_sqr(void *data, GEN x) {
  FpXQXQ_muldata *d = (FpXQXQ_muldata*) data;
  return FpXQXQ_sqr(x, d->S,d->T, d->p);
}

static GEN
_FpXQXQ_one(void *data) {
  FpXQXQ_muldata *d = (FpXQXQ_muldata*) data;
  return pol_1(varn(d->S));
}

static GEN
_FpXQXQ_zero(void *data) {
  FpXQXQ_muldata *d = (FpXQXQ_muldata*) data;
  return pol_0(varn(d->S));
}

static struct bb_algebra FpXQXQ_algebra = { _FpXQXQ_red,_FpXQXQ_add,_FpXQXQ_mul,_FpXQXQ_sqr,_FpXQXQ_one,_FpXQXQ_zero };

/* x over Fq, return lift(x^n) mod S */
GEN
FpXQXQ_pow(GEN x, GEN n, GEN S, GEN T, GEN p)
{
  pari_sp ltop = avma;
  GEN y;
  FpXQXQ_muldata D;
  long s = signe(n);
  if (!s) return pol_1(varn(x));
  if (is_pm1(n)) /* +/- 1 */
    return (s < 0)? FpXQXQ_inv(x,S,T,p): ZXX_copy(x);
  if (lgefint(p) == 3)
  {
    ulong pp = to_FlxqX(x, S, T, p, &x, &S, &T);
    GEN z = FlxqXQ_pow(x, n, S, T, pp);
    y = FlxX_to_ZXX(z);
  }
  else
  {
    D.S = S; D.T = T; D.p = p;
    if (s < 0) x = FpXQXQ_inv(x,S,T,p);
    y = gen_pow(x, n, (void*)&D,&_FpXQXQ_sqr,&_FpXQXQ_mul);
  }
  return gerepileupto(ltop, y);
}

/* generates the list of powers of x of degree 0,1,2,...,l*/
GEN
FpXQXQ_powers(GEN x, long l, GEN S, GEN T, GEN p)
{
  FpXQXQ_muldata D;
  int use_sqr = (degpol(x)<<1) >= degpol(S);
  D.S = S; D.T = T; D.p = p;
  return gen_powers(x, l, use_sqr, (void*)&D, &_FpXQXQ_sqr, &_FpXQXQ_mul,&_FpXQXQ_one);
}

GEN
FpXQXQ_matrix_pow(GEN y, long n, long m, GEN S, GEN T, GEN p)
{
  return RgXV_to_RgM(FpXQXQ_powers(y,m-1,S,T,p),n);
}

GEN
FpXQX_FpXQXQV_eval(GEN P, GEN V, GEN S, GEN T, GEN p)
{
  FpXQXQ_muldata D;
  D.S=S; D.T=T; D.p=p;
  return gen_bkeval_powers(P, degpol(P), V, (void*)&D, &FpXQXQ_algebra,
                                                   _FpXQXQ_cmul);
}

GEN
FpXQX_FpXQXQ_eval(GEN Q, GEN x, GEN S, GEN T, GEN p)
{
  FpXQXQ_muldata D;
  int use_sqr = (degpol(x)<<1) >= degpol(S);
  D.S=S; D.T=T; D.p=p;
  return gen_bkeval(Q, degpol(Q), x, use_sqr, (void*)&D, &FpXQXQ_algebra,
                                                    _FpXQXQ_cmul);
}

static GEN
FpXQXQ_autpow_sqr(void * E, GEN x)
{
  FpXQXQ_muldata *D = (FpXQXQ_muldata *)E;
  GEN T = D->T, p = D->p;
  GEN phi = gel(x,1), S = gel(x,2);
  long n = brent_kung_optpow(get_FpX_degree(T)-1,lgpol(S)+1,1);
  GEN V = FpXQ_powers(phi, n, T, p);
  GEN phi2 = FpX_FpXQV_eval(phi, V, T, p);
  GEN Sphi = FpXY_FpXQV_evalx(S, V, T, p);
  GEN S2 = FpXQX_FpXQXQ_eval(Sphi, S, D->S, T, p);
  return mkvec2(phi2, S2);
}

static GEN
FpXQXQ_autpow_mul(void * E, GEN x, GEN y)
{
  FpXQXQ_muldata *D = (FpXQXQ_muldata *)E;
  GEN T = D->T, p = D->p;
  GEN phi1 = gel(x,1), S1 = gel(x,2);
  GEN phi2 = gel(y,1), S2 = gel(y,2);
  long n = brent_kung_optpow(get_FpX_degree(T)-1, lgpol(S1)+1, 1);
  GEN V = FpXQ_powers(phi2, n, T, p);
  GEN phi3 = FpX_FpXQV_eval(phi1, V, T, p);
  GEN Sphi = FpXY_FpXQV_evalx(S1, V, T, p);
  GEN S3 = FpXQX_FpXQXQ_eval(Sphi, S2, D->S, T, p);
  return mkvec2(phi3, S3);
}

GEN
FpXQXQV_autpow(GEN aut, long n, GEN S, GEN T, GEN p)
{
  FpXQXQ_muldata D;
  D.S=S; D.T=T; D.p=p;
  return gen_powu(aut,n,&D,FpXQXQ_autpow_sqr,FpXQXQ_autpow_mul);
}

static GEN
FpXQXQ_autsum_mul(void *E, GEN x, GEN y)
{
  FpXQXQ_muldata *D = (FpXQXQ_muldata *) E;
  GEN T = D->T, p = D->p;
  GEN phi1 = gel(x,1), S1 = gel(x,2), a1 = gel(x,3);
  GEN phi2 = gel(y,1), S2 = gel(y,2), a2 = gel(y,3);
  long n2 = brent_kung_optpow(get_FpX_degree(T)-1, lgpol(S1)+lgpol(a1)+1, 1);
  GEN V2 = FpXQ_powers(phi2, n2, T, p);
  GEN phi3 = FpX_FpXQV_eval(phi1, V2, T, p);
  GEN Sphi = FpXY_FpXQV_evalx(S1, V2, T, p);
  GEN aphi = FpXY_FpXQV_evalx(a1, V2, T, p);
  long n = brent_kung_optpow(degpol(D->S)-1,2,1);
  GEN V = FpXQXQ_powers(S2, n, D->S, T, p);
  GEN S3 = FpXQX_FpXQXQV_eval(Sphi, V, D->S, T, p);
  GEN aS = FpXQX_FpXQXQV_eval(aphi, V, D->S, T, p);
  GEN a3 = FpXQXQ_mul(aS,a2,D->S, T, p);
  return mkvec3(phi3, S3, a3);
}

static GEN
FpXQXQ_autsum_sqr(void * T, GEN x)
{ return FpXQXQ_autsum_mul(T,x,x); }

GEN
FpXQXQV_autsum(GEN aut, long n, GEN S, GEN T, GEN p)
{
  FpXQXQ_muldata D;
  D.S=S; D.T=T; D.p=p;
  return gen_powu(aut,n,&D,FpXQXQ_autsum_sqr,FpXQXQ_autsum_mul);
}
