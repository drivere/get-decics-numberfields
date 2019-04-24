/* Copyright (C) 2007  The PARI group.

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

/* Not so fast arithmetic with polynomials over Fp */

static GEN
get_FpX_red(GEN T, GEN *B)
{
  if (typ(T)!=t_VEC) { *B=NULL; return T; }
  *B = gel(T,1); return gel(T,2);
}

GEN
get_FpX_mod(GEN T) { return typ(T)==t_VEC? gel(T,2): T; }

long
get_FpX_var(GEN T) { return typ(T)==t_VEC? varn(gel(T,2)): varn(T); }

long
get_FpX_degree(GEN T) { return typ(T)==t_VEC? degpol(gel(T,2)): degpol(T); }

/***********************************************************************/
/**                                                                   **/
/**                              FpX                                  **/
/**                                                                   **/
/***********************************************************************/

/* FpX are polynomials over Z/pZ represented as t_POL with
 * t_INT coefficients.
 * 1) Coefficients should belong to {0,...,p-1}, though non-reduced
 * coefficients should work but be slower.
 *
 * 2) p is not assumed to be prime, but it is assumed that impossible divisions
 *    will not happen.
 * 3) Theses functions let some garbage on the stack, but are gerepileupto
 * compatible.
 */

static ulong
to_Flx(GEN *P, GEN *Q, GEN p)
{
  ulong pp = uel(p,2);
  *P = ZX_to_Flx(*P, pp);
  *Q = ZX_to_Flx(*Q, pp); return pp;
}

static ulong
to_Flxq(GEN *P, GEN *T, GEN p)
{
  ulong pp = uel(p,2);
  if (P) *P = ZX_to_Flx(*P, pp);
  *T = ZXT_to_FlxT(*T, pp); return pp;
}

GEN
Z_to_FpX(GEN a, GEN p, long v)
{
  pari_sp av = avma;
  GEN z = cgetg(3, t_POL);
  GEN x = modii(a, p);
  if (!signe(x)) { avma =av; return pol_0(v); }
  z[1] = evalsigne(1) | evalvarn(v);
  gel(z,2) = x; return z;
}

/* z in Z[X], return lift(z * Mod(1,p)), normalized*/
GEN
FpX_red(GEN z, GEN p)
{
  long i, l = lg(z);
  GEN x = cgetg(l, t_POL);
  for (i=2; i<l; i++) gel(x,i) = modii(gel(z,i),p);
  x[1] = z[1]; return FpX_renormalize(x,l);
}
GEN
FpXV_red(GEN z, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_VEC);
  for (i=1; i<l; i++) gel(x,i) = FpX_red(gel(z,i), p);
  return x;
}

GEN
FpXT_red(GEN z, GEN p)
{
  if (typ(z) == t_POL)
    return FpX_red(z, p);
  else
  {
    long i,l = lg(z);
    GEN x = cgetg(l, t_VEC);
    for (i=1; i<l; i++) gel(x,i) = FpXT_red(gel(z,i), p);
    return x;
  }
}

GEN
FpX_normalize(GEN z, GEN p)
{
  GEN p1 = leading_term(z);
  if (lg(z) == 2 || equali1(p1)) return z;
  return FpX_Fp_mul_to_monic(z, Fp_inv(p1,p), p);
}

GEN
FpX_center(GEN T, GEN p, GEN pov2)
{
  long i, l = lg(T);
  GEN P = cgetg(l,t_POL);
  for(i=2; i<l; i++) gel(P,i) = Fp_center(gel(T,i), p, pov2);
  P[1] = T[1]; return P;
}

GEN
FpX_add(GEN x,GEN y,GEN p)
{
  long lx = lg(x), ly = lg(y), i;
  GEN z;
  if (lx < ly) swapspec(x,y, lx,ly);
  z = cgetg(lx,t_POL); z[1] = x[1];
  for (i=2; i<ly; i++) gel(z,i) = Fp_add(gel(x,i),gel(y,i), p);
  for (   ; i<lx; i++) gel(z,i) = modii(gel(x,i), p);
  z = ZX_renormalize(z, lx);
  if (!lgpol(z)) { avma = (pari_sp)(z + lx); return pol_0(varn(x)); }
  return z;
}

static GEN
Fp_red_FpX(GEN x, GEN p, long v)
{
  GEN z;
  if (!signe(x)) return pol_0(v);
  z = cgetg(3, t_POL);
  gel(z,2) = Fp_red(x,p);
  z[1] = evalvarn(v);
  return FpX_renormalize(z, 3);
}

static GEN
Fp_neg_FpX(GEN x, GEN p, long v)
{
  GEN z;
  if (!signe(x)) return pol_0(v);
  z = cgetg(3, t_POL);
  gel(z,2) = Fp_neg(x,p);
  z[1] = evalvarn(v);
  return FpX_renormalize(z, 3);
}

GEN
FpX_Fp_add(GEN y,GEN x,GEN p)
{
  long i, lz = lg(y);
  GEN z;
  if (lz == 2) return Fp_red_FpX(x,p,varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = Fp_add(gel(y,2),x, p);
  if (lz == 3) z = FpX_renormalize(z,lz);
  else
    for(i=3;i<lz;i++) gel(z,i) = icopy(gel(y,i));
  return z;
}
GEN
FpX_Fp_add_shallow(GEN y,GEN x,GEN p)
{
  long i, lz = lg(y);
  GEN z;
  if (lz == 2) return scalar_ZX_shallow(x,varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = Fp_add(gel(y,2),x, p);
  if (lz == 3) z = FpX_renormalize(z,lz);
  else
    for(i=3;i<lz;i++) gel(z,i) = gel(y,i);
  return z;
}
GEN
FpX_Fp_sub(GEN y,GEN x,GEN p)
{
  long i, lz = lg(y);
  GEN z;
  if (lz == 2) return Fp_neg_FpX(x,p,varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = Fp_sub(gel(y,2),x, p);
  if (lz == 3) z = FpX_renormalize(z,lz);
  else
    for(i=3;i<lz;i++) gel(z,i) = icopy(gel(y,i));
  return z;
}
GEN
FpX_Fp_sub_shallow(GEN y,GEN x,GEN p)
{
  long i, lz = lg(y);
  GEN z;
  if (lz == 2) return Fp_neg_FpX(x,p,varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = Fp_sub(gel(y,2),x, p);
  if (lz == 3) z = FpX_renormalize(z,lz);
  else
    for(i=3;i<lz;i++) gel(z,i) = gel(y,i);
  return z;
}

GEN
FpX_neg(GEN x,GEN p)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx,t_POL);
  y[1] = x[1];
  for(i=2; i<lx; i++) gel(y,i) = Fp_neg(gel(x,i), p);
  return ZX_renormalize(y, lx);
}

static GEN
FpX_subspec(GEN x,GEN y,GEN p, long nx, long ny)
{
  long i, lz;
  GEN z;
  if (nx >= ny)
  {
    lz = nx+2;
    z = cgetg(lz,t_POL); z[1] = 0; z += 2;
    for (i=0; i<ny; i++) gel(z,i) = Fp_sub(gel(x,i),gel(y,i), p);
    for (   ; i<nx; i++) gel(z,i) = modii(gel(x,i), p);
  }
  else
  {
    lz = ny+2;
    z = cgetg(lz,t_POL); z[1] = 0; z += 2;
    for (i=0; i<nx; i++) gel(z,i) = Fp_sub(gel(x,i),gel(y,i), p);
    for (   ; i<ny; i++) gel(z,i) = Fp_neg(gel(y,i), p);
  }
  z = FpX_renormalize(z-2, lz);
  if (!lgpol(z)) { avma = (pari_sp)(z + lz); return pol_0(0); }
  return z;
}

GEN
FpX_sub(GEN x,GEN y,GEN p)
{
  GEN z = FpX_subspec(x+2,y+2,p,lgpol(x),lgpol(y));
  setvarn(z, varn(x));
  return z;
}

GEN
Fp_FpX_sub(GEN x, GEN y, GEN p)
{
  long ly = lg(y), i;
  GEN z;
  if (ly <= 3) {
    z = cgetg(3, t_POL);
    x = (ly == 3)? Fp_sub(x, gel(y,2), p): modii(x, p);
    if (!signe(x)) { avma = (pari_sp)(z + 3); return pol_0(varn(y)); }
    z[1] = evalsigne(1)|y[1]; gel(z,2) = x; return z;
  }
  z = cgetg(ly,t_POL);
  gel(z,2) = Fp_sub(x, gel(y,2), p);
  for (i = 3; i < ly; i++) gel(z,i) = Fp_neg(gel(y,i), p);
  z = ZX_renormalize(z, ly);
  if (!lgpol(z)) { avma = (pari_sp)(z + ly); return pol_0(varn(x)); }
  z[1] = y[1]; return z;
}

GEN
FpX_mul(GEN x,GEN y,GEN p) { return FpX_red(ZX_mul(x, y), p); }

GEN
FpX_mulspec(GEN a, GEN b, GEN p, long na, long nb)
{ return FpX_red(ZX_mulspec(a, b, na, nb), p); }

GEN
FpX_sqr(GEN x,GEN p) { return FpX_red(ZX_sqr(x), p); }

GEN
FpX_mulu(GEN y, ulong x,GEN p)
{
  GEN z;
  long i, l;
  if (!x) return zeropol(varn(y));
  z = cgetg_copy(y, &l); z[1] = y[1];
  for(i=2; i<l; i++) gel(z,i) = Fp_mulu(gel(y,i), x, p);
  return z;
}

GEN
FpX_Fp_mulspec(GEN y,GEN x,GEN p,long ly)
{
  GEN z;
  long i;
  if (!signe(x)) return pol_0(0);
  z = cgetg(ly+2,t_POL); z[1] = evalsigne(1);
  for(i=0; i<ly; i++) gel(z,i+2) = Fp_mul(gel(y,i), x, p);
  return ZX_renormalize(z, ly+2);
}

GEN
FpX_Fp_mul(GEN y,GEN x,GEN p)
{
  GEN z = FpX_Fp_mulspec(y+2,x,p,lgpol(y));
  setvarn(z, varn(y)); return z;
}

GEN
FpX_Fp_mul_to_monic(GEN y,GEN x,GEN p)
{
  GEN z;
  long i, l;
  z = cgetg_copy(y, &l); z[1] = y[1];
  for(i=2; i<l-1; i++) gel(z,i) = Fp_mul(gel(y,i), x, p);
  gel(z,l-1) = gen_1; return z;
}

static GEN
_FpX_sqr(void * E, GEN x) { return FpX_sqr(x, (GEN) E); }

static GEN
_FpX_mul(void * E, GEN x, GEN y) { return FpX_mul(x, y, (GEN) E); }

GEN
FpX_powu(GEN x, ulong n, GEN p)
{
  if (n==0) return pol_1(varn(x));
  return gen_powu(x, n, (void *)p, _FpX_sqr, _FpX_mul);
}

GEN
FpX_halve(GEN y, GEN p)
{
  GEN z;
  long i, l;
  z = cgetg_copy(y, &l); z[1] = y[1];
  for(i=2; i<l; i++) gel(z,i) = Fp_halve(gel(y,i), p);
  return z;
}

static GEN
FpX_divrem_basecase(GEN x, GEN y, GEN p, GEN *pr)
{
  long vx, dx, dy, dz, i, j, sx, lr;
  pari_sp av0, av;
  GEN z,p1,rem,lead;

  if (!signe(y)) pari_err_INV("FpX_divrem",y);
  vx = varn(x);
  dy = degpol(y);
  dx = degpol(x);
  if (dx < dy)
  {
    if (pr)
    {
      av0 = avma; x = FpX_red(x, p);
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
    av0 = avma;
    if (equali1(lead)) return FpX_red(x, p);
    else return gerepileupto(av0, FpX_Fp_mul(x, Fp_inv(lead,p), p));
  }
  av0 = avma; dz = dx-dy;
  if (lgefint(p) == 3)
  { /* assume ab != 0 mod p */
    ulong pp = to_Flx(&x, &y, p);
    z = Flx_divrem(x, y, pp, pr);
    avma = av0; /* HACK: assume pr last on stack, then z */
    if (!z) return NULL;
    z = leafcopy(z);
    if (pr && pr != ONLY_DIVIDES && pr != ONLY_REM)
    {
      *pr = leafcopy(*pr);
      *pr = Flx_to_ZX_inplace(*pr);
    }
    return Flx_to_ZX_inplace(z);
  }
  lead = equali1(lead)? NULL: gclone(Fp_inv(lead,p));
  avma = av0;
  z=cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2; y += 2; z += 2;

  p1 = gel(x,dx); av = avma;
  gel(z,dz) = lead? gerepileuptoint(av, Fp_mul(p1,lead, p)): icopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=gel(x,i);
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii(gel(z,j),gel(y,i-j)));
    if (lead) p1 = mulii(p1,lead);
    gel(z,i-dy) = gerepileuptoint(av,modii(p1, p));
  }
  if (!pr) { if (lead) gunclone(lead); return z-2; }

  rem = (GEN)avma; av = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii(gel(z,j),gel(y,i-j)));
    p1 = modii(p1,p); if (signe(p1)) { sx = 1; break; }
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
  p1 = gerepileuptoint((pari_sp)rem, p1);
  rem += 2; gel(rem,i) = p1;
  for (i--; i>=0; i--)
  {
    av=avma; p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii(gel(z,j),gel(y,i-j)));
    gel(rem,i) = gerepileuptoint(av, modii(p1,p));
  }
  rem -= 2;
  if (lead) gunclone(lead);
  if (!sx) (void)FpX_renormalize(rem, lr);
  if (pr == ONLY_REM) return gerepileupto(av0,rem);
  *pr = rem; return z-2;
}

GEN
FpX_div_by_X_x(GEN a, GEN x, GEN p, GEN *r)
{
  long l = lg(a)-1, i;
  GEN z = cgetg(l, t_POL);
  z[1] = evalsigne(1) | evalvarn(0);
  gel(z, l-1) = gel(a,l);
  for (i=l-2; i>1; i--) /* z[i] = a[i+1] + x*z[i+1] */
    gel(z, i) = Fp_addmul(gel(a,i+1), x, gel(z,i+1), p);
  if (r) *r = Fp_addmul(gel(a,2), x, gel(z,2), p);
  return z;
}

static GEN
_FpX_divrem(void * E, GEN x, GEN y, GEN *r) { return FpX_divrem(x, y, (GEN) E, r); }
static GEN
_FpX_add(void * E, GEN x, GEN y) { return FpX_add(x, y, (GEN) E); }

static struct bb_ring FpX_ring = { _FpX_add,_FpX_mul,_FpX_sqr };

GEN
FpX_digits(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  long d = degpol(T), n = (lgpol(x)+d-1)/d;
  GEN z = gen_digits(x,T,n,(void *)p, &FpX_ring, _FpX_divrem);
  return gerepileupto(av, z);
}

GEN
FpX_fromdigits(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z = gen_fromdigits(x,T,(void *)p, &FpX_ring);
  return gerepileupto(av, z);
}

long
FpX_valrem(GEN x, GEN t, GEN p, GEN *py)
{
  pari_sp av=avma;
  long k;
  GEN r, y;

  for (k=0; ; k++)
  {
    y = FpX_divrem(x, t, p, &r);
    if (signe(r)) break;
    x = y;
  }
  *py = gerepilecopy(av,x);
  return k;
}

static GEN
FpX_halfgcd_basecase(GEN a, GEN b, GEN p)
{
  pari_sp av=avma;
  GEN u,u1,v,v1;
  long vx = varn(a);
  long n = lgpol(a)>>1;
  u1 = v = pol_0(vx);
  u = v1 = pol_1(vx);
  while (lgpol(b)>n)
  {
    GEN r, q = FpX_divrem(a,b,p, &r);
    a = b; b = r; swap(u,u1); swap(v,v1);
    u1 = FpX_sub(u1, FpX_mul(u, q, p), p);
    v1 = FpX_sub(v1, FpX_mul(v, q ,p), p);
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpX_halfgcd (d = %ld)",degpol(b));
      gerepileall(av,6, &a,&b,&u1,&v1,&u,&v);
    }
  }
  return gerepilecopy(av, mkmat2(mkcol2(u,u1), mkcol2(v,v1)));
}
static GEN
FpX_addmulmul(GEN u, GEN v, GEN x, GEN y, GEN p)
{
  return FpX_add(FpX_mul(u, x, p),FpX_mul(v, y, p), p);
}

static GEN
FpXM_FpX_mul2(GEN M, GEN x, GEN y, GEN p)
{
  GEN res = cgetg(3, t_COL);
  gel(res, 1) = FpX_addmulmul(gcoeff(M,1,1), gcoeff(M,1,2), x, y, p);
  gel(res, 2) = FpX_addmulmul(gcoeff(M,2,1), gcoeff(M,2,2), x, y, p);
  return res;
}

/*TODO: implement Strassen 7 multiplications formula (p is large) */
static GEN
FpXM_mul2(GEN M, GEN N, GEN p)
{
  GEN res = cgetg(3, t_MAT);
  gel(res, 1) = FpXM_FpX_mul2(M,gcoeff(N,1,1),gcoeff(N,2,1),p);
  gel(res, 2) = FpXM_FpX_mul2(M,gcoeff(N,1,2),gcoeff(N,2,2),p);
  return res;
}

/* Return [0,1;1,-q]*M */
static GEN
FpX_FpXM_qmul(GEN q, GEN M, GEN p)
{
  GEN u, v, res = cgetg(3, t_MAT);
  u = FpX_sub(gcoeff(M,1,1), FpX_mul(gcoeff(M,2,1), q, p), p);
  gel(res,1) = mkcol2(gcoeff(M,2,1), u);
  v = FpX_sub(gcoeff(M,1,2), FpX_mul(gcoeff(M,2,2), q, p), p);
  gel(res,2) = mkcol2(gcoeff(M,2,2), v);
  return res;
}

static GEN
matid2_FpXM(long v)
{
  retmkmat2(mkcol2(pol_1(v),pol_0(v)),
            mkcol2(pol_0(v),pol_1(v)));
}

static GEN
FpX_halfgcd_split(GEN x, GEN y, GEN p)
{
  pari_sp av=avma;
  GEN R, S, V;
  GEN y1, r, q;
  long l = lgpol(x), n = l>>1, k;
  if (lgpol(y)<=n) return matid2_FpXM(varn(x));
  R = FpX_halfgcd(RgX_shift_shallow(x,-n),RgX_shift_shallow(y,-n),p);
  V = FpXM_FpX_mul2(R,x,y,p); y1 = gel(V,2);
  if (lgpol(y1)<=n) return gerepilecopy(av, R);
  q = FpX_divrem(gel(V,1), y1, p, &r);
  k = 2*n-degpol(y1);
  S = FpX_halfgcd(RgX_shift_shallow(y1,-k), RgX_shift_shallow(r,-k),p);
  return gerepileupto(av, FpXM_mul2(S,FpX_FpXM_qmul(q,R,p),p));
}

/* Return M in GL_2(Fp[X]) such that:
if [a',b']~=M*[a,b]~ then degpol(a')>= (lgpol(a)>>1) >degpol(b')
*/

static GEN
FpX_halfgcd_i(GEN x, GEN y, GEN p)
{
  if (lg(x)<=FpX_HALFGCD_LIMIT) return FpX_halfgcd_basecase(x,y,p);
  return FpX_halfgcd_split(x,y,p);
}

GEN
FpX_halfgcd(GEN x, GEN y, GEN p)
{
  pari_sp av = avma;
  GEN M,q,r;
  if (lgefint(p)==3)
  {
    ulong pp = to_Flx(&x, &y, p);
    M = FlxM_to_ZXM(Flx_halfgcd(x, y, pp));
  }
  else
  {
    if (!signe(x))
    {
      long v = varn(x);
      retmkmat2(mkcol2(pol_0(v),pol_1(v)),
                mkcol2(pol_1(v),pol_0(v)));
    }
    if (degpol(y)<degpol(x)) return FpX_halfgcd_i(x,y,p);
    q = FpX_divrem(y,x,p,&r);
    M = FpX_halfgcd_i(x,r,p);
    gcoeff(M,1,1) = FpX_sub(gcoeff(M,1,1), FpX_mul(q, gcoeff(M,1,2), p), p);
    gcoeff(M,2,1) = FpX_sub(gcoeff(M,2,1), FpX_mul(q, gcoeff(M,2,2), p), p);
  }
  return gerepilecopy(av, M);
}

static GEN
FpX_gcd_basecase(GEN a, GEN b, GEN p)
{
  pari_sp av = avma, av0=avma;
  while (signe(b))
  {
    GEN c;
    if (gc_needed(av0,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpX_gcd (d = %ld)",degpol(b));
      gerepileall(av0,2, &a,&b);
    }
    av = avma; c = FpX_rem(a,b,p); a=b; b=c;
  }
  avma = av; return a;
}

GEN
FpX_gcd(GEN x, GEN y, GEN p)
{
  pari_sp av = avma;
  if (lgefint(p)==3)
  {
    ulong pp;
    (void)new_chunk((lg(x) + lg(y)) << 2); /* scratch space */
    pp = to_Flx(&x, &y, p);
    x = Flx_gcd(x, y, pp);
    avma = av; return Flx_to_ZX(x);
  }
  x = FpX_red(x, p);
  y = FpX_red(y, p);
  if (!signe(x)) return gerepileupto(av, y);
  while (lg(y)>FpX_GCD_LIMIT)
  {
    GEN c;
    if (lgpol(y)<=(lgpol(x)>>1))
    {
      GEN r = FpX_rem(x, y, p);
      x = y; y = r;
    }
    c = FpXM_FpX_mul2(FpX_halfgcd(x,y, p), x, y, p);
    x = gel(c,1); y = gel(c,2);
    gerepileall(av,2,&x,&y);
  }
  return gerepileupto(av, FpX_gcd_basecase(x,y,p));
}

/*Return 1 if gcd can be computed
 * else return a factor of p*/

GEN
FpX_gcd_check(GEN x, GEN y, GEN p)
{
  GEN a,b,c;
  pari_sp av=avma;

  a = FpX_red(x, p);
  b = FpX_red(y, p);
  while (signe(b))
  {
    GEN lead = leading_term(b);
    GEN g = gcdii(lead,p);
    if (!equali1(g)) return gerepileuptoint(av,g);
    c = FpX_rem(a,b,p); a=b; b=c;
  }
  avma = av; return gen_1;
}

static GEN
FpX_extgcd_basecase(GEN a, GEN b, GEN p, GEN *ptu, GEN *ptv)
{
  pari_sp av=avma;
  GEN u,v,d,d1,v1;
  long vx = varn(a);
  d = a; d1 = b;
  v = pol_0(vx); v1 = pol_1(vx);
  while (signe(d1))
  {
    GEN r, q = FpX_divrem(d,d1,p, &r);
    v = FpX_sub(v,FpX_mul(q,v1,p),p);
    u=v; v=v1; v1=u;
    u=r; d=d1; d1=u;
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpX_extgcd (d = %ld)",degpol(d));
      gerepileall(av,5, &d,&d1,&u,&v,&v1);
    }
  }
  if (ptu) *ptu = FpX_div(FpX_sub(d,FpX_mul(b,v,p),p),a,p);
  *ptv = v; return d;
}

static GEN
FpX_extgcd_halfgcd(GEN x, GEN y, GEN p, GEN *ptu, GEN *ptv)
{
  pari_sp av=avma;
  GEN u,v,R = matid2_FpXM(varn(x));
  while (lg(y)>FpX_EXTGCD_LIMIT)
  {
    GEN M, c;
    if (lgpol(y)<=(lgpol(x)>>1))
    {
      GEN r, q = FpX_divrem(x, y, p, &r);
      x = y; y = r;
      R = FpX_FpXM_qmul(q, R, p);
    }
    M = FpX_halfgcd(x,y, p);
    c = FpXM_FpX_mul2(M, x,y, p);
    R = FpXM_mul2(M, R, p);
    x = gel(c,1); y = gel(c,2);
    gerepileall(av,3,&x,&y,&R);
  }
  y = FpX_extgcd_basecase(x,y,p,&u,&v);
  if (ptu) *ptu = FpX_addmulmul(u,v,gcoeff(R,1,1),gcoeff(R,2,1),p);
  *ptv = FpX_addmulmul(u,v,gcoeff(R,1,2),gcoeff(R,2,2),p);
  return y;
}

/* x and y in Z[X], return lift(gcd(x mod p, y mod p)). Set u and v st
 * ux + vy = gcd (mod p) */
GEN
FpX_extgcd(GEN x, GEN y, GEN p, GEN *ptu, GEN *ptv)
{
  GEN d;
  pari_sp ltop=avma;
  if (lgefint(p)==3)
  {
    ulong pp = to_Flx(&x, &y, p);
    d = Flx_extgcd(x,y, pp, ptu,ptv);
    d = Flx_to_ZX(d);
    if (ptu) *ptu=Flx_to_ZX(*ptu);
    *ptv=Flx_to_ZX(*ptv);
  }
  else
  {
    x = FpX_red(x, p);
    y = FpX_red(y, p);
    if (lg(y)>FpX_EXTGCD_LIMIT)
      d = FpX_extgcd_halfgcd(x, y, p, ptu, ptv);
    else
      d = FpX_extgcd_basecase(x, y, p, ptu, ptv);
  }
  gerepileall(ltop,ptu?3:2,&d,ptv,ptu);
  return d;
}

GEN
FpX_rescale(GEN P, GEN h, GEN p)
{
  long i, l = lg(P);
  GEN Q = cgetg(l,t_POL), hi = h;
  Q[l-1] = P[l-1];
  for (i=l-2; i>=2; i--)
  {
    gel(Q,i) = Fp_mul(gel(P,i), hi, p);
    if (i == 2) break;
    hi = Fp_mul(hi,h, p);
  }
  Q[1] = P[1]; return Q;
}

GEN
FpX_deriv(GEN x, GEN p) { return FpX_red(ZX_deriv(x), p); }

int
FpX_is_squarefree(GEN f, GEN p)
{
  pari_sp av = avma;
  GEN z = FpX_gcd(f,FpX_deriv(f,p),p);
  avma = av;
  return degpol(z)==0;
}

GEN
random_FpX(long d1, long v, GEN p)
{
  long i, d = d1+2;
  GEN y = cgetg(d,t_POL); y[1] = evalsigne(1) | evalvarn(v);
  for (i=2; i<d; i++) gel(y,i) = randomi(p);
  return FpX_renormalize(y,d);
}

/* Evaluation in Fp
 * x a ZX and y an Fp, return x(y) mod p
 *
 * If p is very large (several longs) and x has small coefficients(<<p),
 * then Brent & Kung algorithm is faster. */
GEN
FpX_eval(GEN x,GEN y,GEN p)
{
  pari_sp av;
  GEN p1,r,res;
  long j, i=lg(x)-1;
  if (i<=2)
    return (i==2)? modii(gel(x,2),p): gen_0;
  res=cgeti(lgefint(p));
  av=avma; p1=gel(x,i);
  /* specific attention to sparse polynomials (see poleval)*/
  /*You've guessed it! It's a copy-paste(tm)*/
  for (i--; i>=2; i=j-1)
  {
    for (j=i; !signe(gel(x,j)); j--)
      if (j==2)
      {
        if (i!=j) y = Fp_powu(y,i-j+1,p);
        p1=mulii(p1,y);
        goto fppoleval;/*sorry break(2) no implemented*/
      }
    r = (i==j)? y: Fp_powu(y,i-j+1,p);
    p1 = Fp_addmul(gel(x,j), p1, r, p);
    if ((i & 7) == 0) { affii(p1, res); p1 = res; avma = av; }
  }
 fppoleval:
  modiiz(p1,p,res);
  avma = av; return res;
}

/* Tz=Tx*Ty where Tx and Ty coprime
 * return lift(chinese(Mod(x*Mod(1,p),Tx*Mod(1,p)),Mod(y*Mod(1,p),Ty*Mod(1,p))))
 * if Tz is NULL it is computed
 * As we do not return it, and the caller will frequently need it,
 * it must compute it and pass it.
 */
GEN
FpX_chinese_coprime(GEN x,GEN y,GEN Tx,GEN Ty,GEN Tz,GEN p)
{
  pari_sp av = avma;
  GEN ax,p1;
  ax = FpX_mul(FpXQ_inv(Tx,Ty,p), Tx,p);
  p1 = FpX_mul(ax, FpX_sub(y,x,p),p);
  p1 = FpX_add(x,p1,p);
  if (!Tz) Tz=FpX_mul(Tx,Ty,p);
  p1 = FpX_rem(p1,Tz,p);
  return gerepileupto(av,p1);
}

/* Res(A,B) = Res(B,R) * lc(B)^(a-r) * (-1)^(ab), with R=A%B, a=deg(A) ...*/
GEN
FpX_resultant(GEN a, GEN b, GEN p)
{
  long da,db,dc;
  pari_sp av;
  GEN c,lb, res = gen_1;

  if (!signe(a) || !signe(b)) return gen_0;
  da = degpol(a);
  db = degpol(b);
  if (db > da)
  {
    swapspec(a,b, da,db);
    if (both_odd(da,db)) res = subii(p, res);
  }
  if (!da) return gen_1; /* = res * a[2] ^ db, since 0 <= db <= da = 0 */
  av = avma;
  while (db)
  {
    lb = gel(b,db+2);
    c = FpX_rem(a,b, p);
    a = b; b = c; dc = degpol(c);
    if (dc < 0) { avma = av; return NULL; }

    if (both_odd(da,db)) res = subii(p, res);
    if (!equali1(lb)) res = Fp_mul(res, Fp_powu(lb, da - dc, p), p);
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpX_resultant (da = %ld)",da);
      gerepileall(av,3, &a,&b,&res);
    }
    da = db; /* = degpol(a) */
    db = dc; /* = degpol(b) */
  }
  res = Fp_mul(res, Fp_powu(gel(b,2), da, p), p);
  return gerepileuptoint(av, res);
}

GEN
FpX_disc(GEN x, GEN p)
{
  pari_sp av = avma;
  GEN L, D = FpX_resultant(x, FpX_deriv(x,p), p);
  if (!D || !signe(D)) return gen_0;
  L = leading_term(x); if (!equali1(L)) D = Fp_div(D,L,p);
  if (degpol(x) & 2) D = Fp_neg(D,p);
  return gerepileuptoint(av, D);
}

GEN
FpXV_prod(GEN V, GEN p)
{
  return gen_product(V, (void *)p, &_FpX_mul);
}

GEN
FpV_roots_to_pol(GEN V, GEN p, long v)
{
  pari_sp ltop=avma;
  long i;
  GEN g=cgetg(lg(V),t_VEC);
  for(i=1;i<lg(V);i++)
    gel(g,i) = deg1pol_shallow(gen_1,modii(negi(gel(V,i)),p),v);
  return gerepileupto(ltop,FpXV_prod(g,p));
}

/* invert all elements of x mod p using Montgomery's multi-inverse trick.
 * Not stack-clean. */
GEN
FpV_inv(GEN x, GEN p)
{
  long i, lx = lg(x);
  GEN u, y = cgetg(lx, t_VEC);

  gel(y,1) = gel(x,1);
  for (i=2; i<lx; i++) gel(y,i) = Fp_mul(gel(y,i-1), gel(x,i), p);

  u = Fp_inv(gel(y,--i), p);
  for ( ; i > 1; i--)
  {
    gel(y,i) = Fp_mul(u, gel(y,i-1), p);
    u = Fp_mul(u, gel(x,i), p); /* u = 1 / (x[1] ... x[i-1]) */
  }
  gel(y,1) = u; return y;
}
GEN
FqV_inv(GEN x, GEN T, GEN p)
{
  long i, lx = lg(x);
  GEN u, y = cgetg(lx, t_VEC);

  gel(y,1) = gel(x,1);
  for (i=2; i<lx; i++) gel(y,i) = Fq_mul(gel(y,i-1), gel(x,i), T,p);

  u = Fq_inv(gel(y,--i), T,p);
  for ( ; i > 1; i--)
  {
    gel(y,i) = Fq_mul(u, gel(y,i-1), T,p);
    u = Fq_mul(u, gel(x,i), T,p); /* u = 1 / (x[1] ... x[i-1]) */
  }
  gel(y,1) = u; return y;
}

/***********************************************************************/
/**                                                                   **/
/**                      Barrett reduction                            **/
/**                                                                   **/
/***********************************************************************/

static GEN
FpX_invBarrett_basecase(GEN T, GEN p)
{
  long i, l=lg(T)-1, lr = l-1, k;
  GEN r=cgetg(lr, t_POL); r[1]=T[1];
  gel(r,2) = gen_1;
  for (i=3; i<lr; i++)
  {
    pari_sp av = avma;
    GEN u = gel(T,l-i+2);
    for (k=3; k<i; k++)
      u = addii(u, mulii(gel(T,l-i+k), gel(r,k)));
    gel(r,i) = gerepileupto(av, modii(negi(u), p));
  }
  return FpX_renormalize(r,lr);
}

/* Return new lgpol */
static long
ZX_lgrenormalizespec(GEN x, long lx)
{
  long i;
  for (i = lx-1; i>=0; i--)
    if (signe(gel(x,i))) break;
  return i+1;
}

INLINE GEN
FpX_recipspec(GEN x, long l, long n)
{
  return RgX_recipspec_shallow(x, l, n);
}

static GEN
FpX_invBarrett_Newton(GEN T, GEN p)
{
  pari_sp av = avma;
  long nold, lx, lz, lq, l = degpol(T), i, lQ;
  GEN q, y, z, x = cgetg(l+2, t_POL) + 2;
  ulong mask = quadratic_prec_mask(l-2); /* assume l > 2 */
  for (i=0;i<l;i++) gel(x,i) = gen_0;
  q = FpX_recipspec(T+2,l+1,l+1); lQ = lgpol(q); q+=2;
  /* We work on _spec_ FpX's, all the l[xzq] below are lgpol's */

  /* initialize */
  gel(x,0) = Fp_inv(gel(q,0), p);
  if (lQ>1) gel(q,1) = Fp_red(gel(q,1), p);
  if (lQ>1 && signe(gel(q,1)))
  {
    GEN u = gel(q, 1);
    if (!equali1(gel(x,0))) u = Fp_mul(u, Fp_sqr(gel(x,0), p), p);
    gel(x,1) = Fp_neg(u, p); lx = 2;
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
    lq = ZX_lgrenormalizespec(q, minss(lQ,lnew));
    z = FpX_mulspec(x, q, p, lx, lq); /* FIXME: high product */
    lz = lgpol(z); if (lz > lnew) lz = lnew;
    z += 2;
    /* subtract 1 [=>first nold words are 0]: renormalize so that z(0) != 0 */
    for (i = nold; i < lz; i++) if (signe(gel(z,i))) break;
    nold = nnew;
    if (i >= lz) continue; /* z-1 = 0(t^(nnew + 1)) */

    /* z + i represents (x*q - 1) / t^i */
    lz = ZX_lgrenormalizespec (z+i, lz-i);
    z = FpX_mulspec(x, z+i, p, lx, lz); /* FIXME: low product */
    lz = lgpol(z); z += 2;
    if (lz > lnew-i) lz = ZX_lgrenormalizespec(z, lnew-i);

    lx = lz+ i;
    y  = x + i; /* x -= z * t^i, in place */
    for (i = 0; i < lz; i++) gel(y,i) = Fp_neg(gel(z,i), p);
  }
  x -= 2; setlg(x, lx + 2); x[1] = T[1];
  return gerepilecopy(av, x);
}

/* 1/polrecip(T)+O(x^(deg(T)-1)) */
GEN
FpX_invBarrett(GEN T, GEN p)
{
  pari_sp ltop = avma;
  long l = lg(T);
  GEN r;
  if (l<5) return pol_0(varn(T));
  if (l<=FpX_INVBARRETT_LIMIT)
  {
    GEN c = gel(T,l-1), ci=gen_1;
    if (!equali1(c))
    {
      ci = Fp_inv(c, p);
      T = FpX_Fp_mul(T, ci, p);
      r = FpX_invBarrett_basecase(T, p);
      r = FpX_Fp_mul(r, ci, p);
    } else
      r = FpX_invBarrett_basecase(T, p);
  }
  else
    r = FpX_invBarrett_Newton(T, p);
  return gerepileupto(ltop, r);
}

GEN
FpX_get_red(GEN T, GEN p)
{
  if (typ(T)==t_POL && lg(T)>FpX_BARRETT_LIMIT)
    retmkvec2(FpX_invBarrett(T,p),T);
  return T;
}

/* Compute x mod T where 2 <= degpol(T) <= l+1 <= 2*(degpol(T)-1)
 * and mg is the Barrett inverse of T. */
static GEN
FpX_divrem_Barrettspec(GEN x, long l, GEN mg, GEN T, GEN p, GEN *pr)
{
  GEN q, r;
  long lt = degpol(T); /*We discard the leading term*/
  long ld, lm, lT, lmg;
  ld = l-lt;
  lm = minss(ld, lgpol(mg));
  lT  = ZX_lgrenormalizespec(T+2,lt);
  lmg = ZX_lgrenormalizespec(mg+2,lm);
  q = FpX_recipspec(x+lt,ld,ld);              /* q = rec(x)     lq<=ld*/
  q = FpX_mulspec(q+2,mg+2,p,lgpol(q),lmg);    /* q = rec(x) * mg lq<=ld+lm*/
  q = FpX_recipspec(q+2,minss(ld,lgpol(q)),ld);/* q = rec (rec(x) * mg) lq<=ld*/
  if (!pr) return q;
  r = FpX_mulspec(q+2,T+2,p,lgpol(q),lT);      /* r = q*pol        lr<=ld+lt*/
  r = FpX_subspec(x,r+2,p,lt,minss(lt,lgpol(r)));/* r = x - r   lr<=lt */
  if (pr == ONLY_REM) return r;
  *pr = r; return q;
}

static GEN
FpX_divrem_Barrett_noGC(GEN x, GEN mg, GEN T, GEN p, GEN *pr)
{
  GEN q = NULL, r = FpX_red(x, p);
  long l = lgpol(r), lt = degpol(T), lm = 2*lt-1;
  long i;
  if (l <= lt)
  {
    if (pr == ONLY_REM) return r;
    if (pr == ONLY_DIVIDES) return signe(x)? NULL: pol_0(varn(x));
    if (pr) *pr = r;
    return pol_0(varn(T));
  }
  if (lt <= 1)
    return FpX_divrem_basecase(r,T,p,pr);
  if (pr != ONLY_REM && l>lm)
  {
    q = cgetg(l-lt+2, t_POL);
    for (i=0;i<l-lt;i++) gel(q+2,i) = gen_0;
  }
  while (l>lm)
  {
    GEN zr, zq = FpX_divrem_Barrettspec(r+2+l-lm,lm,mg,T,p,&zr);
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
      GEN zq = FpX_divrem_Barrettspec(r+2,l,mg,T,p,&r);
      if (!q) q = zq;
      else
      {
        long lq = lgpol(zq);
        for(i=0; i<lq; i++) gel(q+2,i) = gel(zq,2+i);
      }
    }
    else
      r = FpX_renormalize(r, l+2);
  }
  else
  {
    if (l > lt)
      r = FpX_divrem_Barrettspec(r+2, l, mg, T, p, ONLY_REM);
    else
      r = FpX_renormalize(r, l+2);
    r[1] = x[1]; return FpX_renormalize(r, lg(r));
  }
  if (pr) { r[1] = x[1]; r = FpX_renormalize(r, lg(r)); }
  q[1] = x[1]; q = FpX_renormalize(q, lg(q));
  if (pr == ONLY_DIVIDES) return signe(r)? NULL: q;
  if (pr) *pr = r;
  return q;
}

GEN
FpX_divrem(GEN x, GEN T, GEN p, GEN *pr)
{
  GEN B, y = get_FpX_red(T, &B);
  long dy = degpol(y), dx = degpol(x), d = dx-dy;
  if (pr==ONLY_REM) return FpX_rem(x, y, p);
  if (!B && d+3 < FpX_DIVREM_BARRETT_LIMIT)
    return FpX_divrem_basecase(x,y,p,pr);
  else if (lgefint(p)==3)
  {
    pari_sp av = avma;
    ulong pp = to_Flxq(&x, &T, p);
    GEN z = Flx_divrem(x, T, pp, pr);
    if (!z) return NULL;
    if (!pr || pr == ONLY_DIVIDES)
      return Flx_to_ZX_inplace(gerepileuptoleaf(av, z));
    z = Flx_to_ZX(z);
    *pr = Flx_to_ZX(*pr);
    gerepileall(av, 2, &z, pr);
    return z;
  } else
  {
    pari_sp av=avma;
    GEN mg = B? B: FpX_invBarrett(y, p);
    GEN q1 = FpX_divrem_Barrett_noGC(x,mg,y,p,pr);
    if (!q1) {avma=av; return NULL;}
    if (!pr || pr==ONLY_DIVIDES) return gerepilecopy(av, q1);
    gerepileall(av,2,&q1,pr);
    return q1;
  }
}

GEN
FpX_rem(GEN x, GEN T, GEN p)
{
  GEN B, y = get_FpX_red(T, &B);
  long dy = degpol(y), dx = degpol(x), d = dx-dy;
  if (d < 0) return FpX_red(x,p);
  if (!B && d+3 < FpX_REM_BARRETT_LIMIT)
    return FpX_divrem_basecase(x,y,p,ONLY_REM);
  else if (lgefint(p)==3)
  {
    pari_sp av = avma;
    ulong pp = to_Flxq(&x, &T, p);
    return Flx_to_ZX_inplace(gerepileuptoleaf(av, Flx_rem(x, T, pp)));
  } else
  {
    pari_sp av = avma;
    GEN mg = B? B: FpX_invBarrett(y, p);
    return gerepileupto(av, FpX_divrem_Barrett_noGC(x, mg, y, p, ONLY_REM));
  }
}

/***********************************************************************/
/**                                                                   **/
/**                              FpXQ                                 **/
/**                                                                   **/
/***********************************************************************/

/* FpXQ are elements of Fp[X]/(T), represented by FpX*/

GEN
FpXQ_red(GEN x, GEN T, GEN p)
{
  GEN z = FpX_red(x,p);
  return FpX_rem(z, T,p);
}

GEN
FpXQ_mul(GEN x,GEN y,GEN T,GEN p)
{
  GEN z = FpX_mul(x,y,p);
  return FpX_rem(z, T, p);
}

GEN
FpXQ_sqr(GEN x, GEN T, GEN p)
{
  GEN z = FpX_sqr(x,p);
  return FpX_rem(z, T, p);
}

/* Inverse of x in Z/pZ[X]/(pol) or NULL if inverse doesn't exist
 * return lift(1 / (x mod (p,pol))) */
GEN
FpXQ_invsafe(GEN x, GEN y, GEN p)
{
  GEN V, z = FpX_extgcd(get_FpX_mod(y), x, p, NULL, &V);
  if (degpol(z)) return NULL;
  z = Fp_invsafe(gel(z,2), p);
  if (!z) return NULL;
  return FpX_Fp_mul(V, z, p);
}

GEN
FpXQ_inv(GEN x,GEN T,GEN p)
{
  pari_sp av = avma;
  GEN U = FpXQ_invsafe(x, T, p);
  if (!U) pari_err_INV("FpXQ_inv",x);
  return gerepileupto(av, U);
}

GEN
FpXQ_div(GEN x,GEN y,GEN T,GEN p)
{
  pari_sp av = avma;
  return gerepileupto(av, FpXQ_mul(x,FpXQ_inv(y,T,p),T,p));
}

struct _FpXQ {
  GEN T, p, aut;
};

static GEN
_FpXQ_add(void *data, GEN x, GEN y)
{
  (void) data;
  return ZX_add(x, y);
}
static GEN
_FpXQ_cmul(void *data, GEN P, long a, GEN x)
{
  (void) data;
  return ZX_Z_mul(x, gel(P,a+2));
}
static GEN
_FpXQ_sqr(void *data, GEN x)
{
  struct _FpXQ *D = (struct _FpXQ*)data;
  return FpXQ_sqr(x, D->T, D->p);
}
static GEN
_FpXQ_mul(void *data, GEN x, GEN y)
{
  struct _FpXQ *D = (struct _FpXQ*)data;
  return FpXQ_mul(x,y, D->T, D->p);
}
static GEN
_FpXQ_zero(void *data)
{
  struct _FpXQ *D = (struct _FpXQ*)data;
  return pol_0(get_FpX_var(D->T));
}
static GEN
_FpXQ_one(void *data)
{
  struct _FpXQ *D = (struct _FpXQ*)data;
  return pol_1(get_FpX_var(D->T));
}
static GEN
_FpXQ_red(void *data, GEN x)
{
  struct _FpXQ *D = (struct _FpXQ*)data;
  return FpX_red(x,D->p);
}

static struct bb_algebra FpXQ_algebra = { _FpXQ_red,_FpXQ_add,_FpXQ_mul,_FpXQ_sqr,_FpXQ_one,_FpXQ_zero };

/* x,pol in Z[X], p in Z, n in Z, compute lift(x^n mod (p, pol)) */
GEN
FpXQ_pow(GEN x, GEN n, GEN T, GEN p)
{
  struct _FpXQ D;
  pari_sp av;
  long s = signe(n);
  GEN y;
  if (!s) return pol_1(varn(x));
  if (is_pm1(n)) /* +/- 1 */
    return (s < 0)? FpXQ_inv(x,T,p): FpXQ_red(x,T,p);
  av = avma;
  if (!is_bigint(p))
  {
    ulong pp = to_Flxq(&x, &T, p);
    y = Flxq_pow(x, n, T, pp);
    return Flx_to_ZX_inplace(gerepileuptoleaf(av, y));
  }
  if (s < 0) x = FpXQ_inv(x,T,p);
  D.p = p; D.T = FpX_get_red(T,p);
  y = gen_pow(x, n, (void*)&D, &_FpXQ_sqr, &_FpXQ_mul);
  return gerepileupto(av, y);
}

GEN /*Assume n is very small*/
FpXQ_powu(GEN x, ulong n, GEN T, GEN p)
{
  struct _FpXQ D;
  pari_sp av;
  GEN y;
  if (!n) return pol_1(varn(x));
  if (n==1) return FpXQ_red(x,T,p);
  av = avma;
  if (!is_bigint(p))
  {
    ulong pp = to_Flxq(&x, &T, p);
    y = Flxq_powu(x, n, T, pp);
    return Flx_to_ZX_inplace(gerepileuptoleaf(av, y));
  }
  D.T = FpX_get_red(T, p); D.p = p;
  y = gen_powu(x, n, (void*)&D, &_FpXQ_sqr, &_FpXQ_mul);
  return gerepileupto(av, y);
}

/* generates the list of powers of x of degree 0,1,2,...,l*/
GEN
FpXQ_powers(GEN x, long l, GEN T, GEN p)
{
  struct _FpXQ D;
  int use_sqr;
  if (l>2 && lgefint(p) == 3) {
    pari_sp av = avma;
    ulong pp = to_Flxq(&x, &T, p);
    GEN z = FlxV_to_ZXV(Flxq_powers(x, l, T, pp));
    return gerepileupto(av, z);
  }
  use_sqr = (degpol(x)<<1)>=get_FpX_degree(T);
  D.T = FpX_get_red(T,p); D.p = p;
  return gen_powers(x, l, use_sqr, (void*)&D, &_FpXQ_sqr, &_FpXQ_mul,&_FpXQ_one);
}

GEN
FpXQ_matrix_pow(GEN y, long n, long m, GEN P, GEN l)
{
  return RgXV_to_RgM(FpXQ_powers(y,m-1,P,l),n);
}

GEN
FpX_Frobenius(GEN T, GEN p)
{
  return FpXQ_pow(pol_x(get_FpX_var(T)), p, T, p);
}

GEN
FpX_matFrobenius(GEN T, GEN p)
{
  long n = get_FpX_degree(T);
  return FpXQ_matrix_pow(FpX_Frobenius(T, p), n, n, T, p);
}

GEN
FpX_FpXQV_eval(GEN Q, GEN x, GEN T, GEN p)
{
  struct _FpXQ D;
  D.T = FpX_get_red(T,p); D.p = p;
  return gen_bkeval_powers(Q,degpol(Q),x,(void*)&D,&FpXQ_algebra,_FpXQ_cmul);
}

GEN
FpX_FpXQ_eval(GEN Q, GEN x, GEN T, GEN p)
{
  struct _FpXQ D;
  int use_sqr;
  if (lgefint(p) == 3)
  {
    pari_sp av = avma;
    ulong pp = to_Flxq(&x, &T, p);
    GEN z = Flx_Flxq_eval(ZX_to_Flx(Q, pp), x, T, pp);
    return Flx_to_ZX_inplace(gerepileuptoleaf(av, z));
  }
  use_sqr = (degpol(x)<<1) >= get_FpX_degree(T);
  D.T = FpX_get_red(T,p); D.p = p;
  return gen_bkeval(Q,degpol(Q),x,use_sqr,(void*)&D,&FpXQ_algebra,_FpXQ_cmul);
}

GEN
FpXC_FpXQV_eval(GEN P, GEN x, GEN T, GEN p)
{
  long i, l = lg(P);
  GEN res = cgetg(l, t_COL);
  for (i=1; i<l; i++)
    gel(res,i) = FpX_FpXQV_eval(gel(P,i), x, T, p);
  return res;
}

GEN
FpXM_FpXQV_eval(GEN Q, GEN x, GEN T, GEN p)
{
  long i, l = lg(Q);
  GEN y = cgetg(l, t_MAT);
  for (i=1; i<l; i++)
    gel(y,i) = FpXC_FpXQV_eval(gel(Q,i), x, T, p);
  return y;
}

GEN
FpXQ_autpowers(GEN aut, long f, GEN T, GEN p)
{
  pari_sp av = avma;
  long n = get_FpX_degree(T);
  long i, nautpow = brent_kung_optpow(n-1,f-2,1);
  long v = get_FpX_var(T);
  GEN autpow, V;
  T = FpX_get_red(T, p);
  autpow = FpXQ_powers(aut, nautpow,T,p);
  V = cgetg(f + 2, t_VEC);
  gel(V,1) = pol_x(v); if (f==0) return gerepileupto(av, V);
  gel(V,2) = gcopy(aut);
  for (i = 3; i <= f+1; i++)
    gel(V,i) = FpX_FpXQV_eval(gel(V,i-1),autpow,T,p);
  return gerepileupto(av, V);
}

static GEN
FpXQ_autpow_sqr(void *E, GEN x)
{
  struct _FpXQ *D = (struct _FpXQ*)E;
  return FpX_FpXQ_eval(x, x, D->T, D->p);
}

static GEN
FpXQ_autpow_mul(void *E, GEN x, GEN y)
{
  struct _FpXQ *D = (struct _FpXQ*)E;
  return FpX_FpXQ_eval(x, y, D->T, D->p);
}

GEN
FpXQ_autpow(GEN x, ulong n, GEN T, GEN p)
{
  struct _FpXQ D;
  D.T = FpX_get_red(T, p); D.p = p;
  if (n==0) return pol_x(varn(x));
  if (n==1) return ZX_copy(x);
  return gen_powu(x,n,(void*)&D,FpXQ_autpow_sqr,FpXQ_autpow_mul);
}

static GEN
FpXQ_autsum_mul(void *E, GEN x, GEN y)
{
  struct _FpXQ *D = (struct _FpXQ*)E;
  GEN T = D->T, p = D->p;
  GEN phi1 = gel(x,1), a1 = gel(x,2);
  GEN phi2 = gel(y,1), a2 = gel(y,2);
  ulong d = brent_kung_optpow(maxss(degpol(phi1),degpol(a1)),2,1);
  GEN V1 = FpXQ_powers(phi1, d, T, p);
  GEN phi3 = FpX_FpXQV_eval(phi2, V1, T, p);
  GEN aphi = FpX_FpXQV_eval(a2, V1, T, p);
  GEN a3 = FpXQ_mul(a1, aphi, T, p);
  return mkvec2(phi3, a3);
}
static GEN
FpXQ_autsum_sqr(void *E, GEN x)
{ return FpXQ_autsum_mul(E, x, x); }

GEN
FpXQ_autsum(GEN x, ulong n, GEN T, GEN p)
{
  struct _FpXQ D;
  D.T = FpX_get_red(T, p); D.p = p;
  return gen_powu(x,n,(void*)&D,FpXQ_autsum_sqr,FpXQ_autsum_mul);
}

static GEN
FpXQM_autsum_mul(void *E, GEN x, GEN y)
{
  struct _FpXQ *D = (struct _FpXQ*)E;
  GEN T = D->T, p = D->p;
  GEN phi1 = gel(x,1), a1 = gel(x,2);
  GEN phi2 = gel(y,1), a2 = gel(y,2);
  long g = lg(a2)-1, dT = get_FpX_degree(T);
  ulong d = brent_kung_optpow(dT-1, g*g+1, 1);
  GEN V1 = FpXQ_powers(phi1, d, T, p);
  GEN phi3 = FpX_FpXQV_eval(phi2, V1, T, p);
  GEN aphi = FpXM_FpXQV_eval(a2, V1, T, p);
  GEN a3 = FqM_mul(a1, aphi, T, p);
  return mkvec2(phi3, a3);
}
static GEN
FpXQM_autsum_sqr(void *E, GEN x)
{ return FpXQM_autsum_mul(E, x, x); }

GEN
FpXQM_autsum(GEN x, ulong n, GEN T, GEN p)
{
  struct _FpXQ D;
  D.T = FpX_get_red(T, p); D.p = p;
  return gen_powu(x, n, (void*)&D, FpXQM_autsum_sqr, FpXQM_autsum_mul);
}

static long
bounded_order(GEN p, GEN b, long k)
{
  long i;
  GEN a=modii(p,b);
  for(i=1;i<k;i++)
  {
    if (equali1(a))
      return i;
    a = Fp_mul(a,p,b);
  }
  return 0;
}

/*
  n = (p^d-a)\b
  b = bb*p^vb
  p^k = 1 [bb]
  d = m*k+r+vb
  u = (p^k-1)/bb;
  v = (p^(r+vb)-a)/b;
  w = (p^(m*k)-1)/(p^k-1)
  n = p^r*w*u+v
  w*u = p^vb*(p^(m*k)-1)/b
  n = p^(r+vb)*(p^(m*k)-1)/b+(p^(r+vb)-a)/b
*/

static GEN
FpXQ_pow_Frobenius(GEN x, GEN n, GEN aut, GEN T, GEN p)
{
  pari_sp av=avma;
  long d = get_FpX_degree(T);
  GEN an = absi(n), z, q;
  if (cmpii(an,p)<0 || cmpis(an,d)<=0)
    return FpXQ_pow(x, n, T, p);
  q = powiu(p, d);
  if (dvdii(q, n))
  {
    long vn = logint(an,p,NULL)-1;
    GEN autvn = vn==1 ? aut: FpXQ_autpow(aut,vn,T,p);
    z = FpX_FpXQ_eval(x,autvn,T,p);
  } else
  {
    GEN b = diviiround(q, an), a = subii(q, mulii(an,b));
    GEN bb, u, v, autk;
    long vb = Z_pvalrem(b,p,&bb);
    long m, r, k = is_pm1(bb) ? 1 : bounded_order(p,bb,d);
    if (!k || d-vb<k) return FpXQ_pow(x,n, T, p);
    m = (d-vb)/k; r = (d-vb)%k;
    u = diviiexact(subis(powiu(p,k),1),bb);
    v = diviiexact(subii(powiu(p,r+vb),a),b);
    autk = k==1 ? aut: FpXQ_autpow(aut,k,T,p);
    if (r)
    {
      GEN autr = r==1 ? aut: FpXQ_autpow(aut,r,T,p);
      z = FpX_FpXQ_eval(x,autr,T,p);
    } else z = x;
    if (m > 1) z = gel(FpXQ_autsum(mkvec2(autk, z), m, T, p), 2);
    if (!is_pm1(u)) z = FpXQ_pow(z, u, T, p);
    if (signe(v)) z = FpXQ_mul(z, FpXQ_pow(x, v, T, p), T, p);
  }
  return gerepileupto(av,signe(n)>0 ? z : FpXQ_inv(z,T,p));
}

/* assume T irreducible mod p */
int
FpXQ_issquare(GEN x, GEN T, GEN p)
{
  pari_sp av;
  long res;
  if (lg(x) == 2 || equalui(2, p)) return 1;
  if (lg(x) == 3) return Fq_issquare(gel(x,2), T, p);
  /* Ng = g^((q-1)/(p-1)) */
  av = avma; res = kronecker(FpXQ_norm(x,T,p), p) == 1;
  avma = av; return res;
}
int
Fp_issquare(GEN x, GEN p)
{
  if (equalui(2, p)) return 1;
  return kronecker(x, p) == 1;
}
/* assume T irreducible mod p */
int
Fq_issquare(GEN x, GEN T, GEN p)
{
  if (typ(x) != t_INT) return FpXQ_issquare(x, T, p);
  return (T && ! odd(get_FpX_degree(T))) || Fp_issquare(x, p);
}

/* discrete log in FpXQ for a in Fp^*, g in FpXQ^* of order ord */
GEN
Fp_FpXQ_log(GEN a, GEN g, GEN o, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN q,n_q,ord,ordp, op;

  if (equali1(a)) return gen_0;
  /* p > 2 */

  ordp = subis(p, 1); /* even */
  ord  = dlog_get_ord(o);
  if (!ord) ord = T? subis(powiu(p, get_FpX_degree(T)), 1): ordp;
  if (equalii(a, ordp)) /* -1 */
    return gerepileuptoint(av, shifti(ord,-1));
  ordp = gcdii(ordp,ord);
  op = typ(o)==t_MAT ? famat_Z_gcd(o,ordp) : ordp;

  q = NULL;
  if (T)
  { /* we want < g > = Fp^* */
    if (!equalii(ord,ordp)) {
      q = diviiexact(ord,ordp);
      g = FpXQ_pow(g,q,T,p);
    }
    g = constant_term(g);
  }
  n_q = Fp_log(a,g,op,p);
  if (lg(n_q)==1) return gerepileuptoleaf(av, n_q);
  if (q) n_q = mulii(q, n_q);
  return gerepileuptoint(av, n_q);
}

static GEN
_FpXQ_pow(void *data, GEN x, GEN n)
{
  struct _FpXQ *D = (struct _FpXQ*)data;
  return FpXQ_pow_Frobenius(x,n, D->aut, D->T, D->p);
}

static GEN
_FpXQ_rand(void *data)
{
  pari_sp av=avma;
  struct _FpXQ *D = (struct _FpXQ*)data;
  GEN z;
  do
  {
    avma=av;
    z=random_FpX(get_FpX_degree(D->T),get_FpX_var(D->T),D->p);
  } while (!signe(z));
  return z;
}

static GEN
_FpXQ_easylog(void *E, GEN a, GEN g, GEN ord)
{
  struct _FpXQ *s=(struct _FpXQ*) E;
  if (degpol(a)) return NULL;
  return Fp_FpXQ_log(constant_term(a),g,ord,s->T,s->p);
}

static const struct bb_group FpXQ_star={_FpXQ_mul,_FpXQ_pow,_FpXQ_rand,hash_GEN,ZX_equal,ZX_equal1,_FpXQ_easylog};

const struct bb_group *
get_FpXQ_star(void **E, GEN T, GEN p)
{
  struct _FpXQ *e = (struct _FpXQ *) stack_malloc(sizeof(struct _FpXQ));
  e->T = T; e->p  = p; e->aut =  FpX_Frobenius(T, p);
  *E = (void*)e; return &FpXQ_star;
}

GEN
FpXQ_order(GEN a, GEN ord, GEN T, GEN p)
{
  if (lgefint(p)==3)
  {
    pari_sp av=avma;
    ulong pp = to_Flxq(&a, &T, p);
    GEN z = Flxq_order(a, ord, T, pp);
    return gerepileuptoint(av,z);
  }
  else
  {
    void *E;
    const struct bb_group *S = get_FpXQ_star(&E,T,p);
    return gen_order(a,ord,E,S);
  }
}

GEN
FpXQ_log(GEN a, GEN g, GEN ord, GEN T, GEN p)
{
  pari_sp av=avma;
  if (lgefint(p)==3)
  {
    if (uel(p,2) == 2)
    {
      GEN z = F2xq_log(ZX_to_F2x(a), ZX_to_F2x(g), ord,
                                     ZX_to_F2x(get_FpX_mod(T)));
      return gerepileuptoleaf(av, z);
    }
    else
    {
      ulong pp = to_Flxq(&a, &T, p);
      GEN z = Flxq_log(a, ZX_to_Flx(g, pp), ord, T, pp);
      return gerepileuptoleaf(av, z);
    }
  }
  else
  {
    void *E;
    const struct bb_group *S = get_FpXQ_star(&E,T,p);
    GEN z = gen_PH_log(a,g,ord,E,S);
    return gerepileuptoleaf(av, z);
  }
}

GEN
Fq_log(GEN a, GEN g, GEN ord, GEN T, GEN p)
{
  if (!T) return Fp_log(a,g,ord,p);
  if (typ(g) == t_INT)
  {
    if (typ(a) == t_POL)
    {
      if (degpol(a)) return cgetg(1,t_VEC);
      a = gel(a,2);
    }
    return Fp_log(a,g,ord,p);
  }
  return typ(a) == t_INT? Fp_FpXQ_log(a,g,ord,T,p): FpXQ_log(a,g,ord,T,p);
}

GEN
FpXQ_sqrtn(GEN a, GEN n, GEN T, GEN p, GEN *zeta)
{
  pari_sp av = avma;
  GEN z;
  if (!signe(a))
  {
    long v=varn(a);
    if (signe(n) < 0) pari_err_INV("FpXQ_sqrtn",a);
    if (zeta) *zeta=pol_1(v);
    return pol_0(v);
  }
  if (lgefint(p)==3)
  {
    if (uel(p,2) == 2)
    {
      z = F2xq_sqrtn(ZX_to_F2x(a), n, ZX_to_F2x(get_Flx_mod(T)), zeta);
      if (!z) return NULL;
      z = F2x_to_ZX(z);
      if (!zeta) return gerepileuptoleaf(av, z);
      *zeta=F2x_to_ZX(*zeta);
    } else
    {
      ulong pp = to_Flxq(&a, &T, p);
      z = Flxq_sqrtn(a, n, T, pp, zeta);
      if (!z) return NULL;
      if (!zeta) return Flx_to_ZX_inplace(gerepileuptoleaf(av, z));
      z = Flx_to_ZX(z);
      *zeta=Flx_to_ZX(*zeta);
    }
  }
  else
  {
    void *E;
    const struct bb_group *S = get_FpXQ_star(&E,T,p);
    GEN o = addis(powiu(p,get_FpX_degree(T)),-1);
    z = gen_Shanks_sqrtn(a,n,o,zeta,E,S);
    if (!z) return NULL;
    if (!zeta) return gerepileupto(av, z);
  }
  gerepileall(av, 2, &z,zeta);
  return z;
}

GEN
FpXQ_sqrt(GEN a, GEN T, GEN p)
{
  return FpXQ_sqrtn(a, gen_2, T, p, NULL);
}

GEN
FpXQ_norm(GEN x, GEN TB, GEN p)
{
  pari_sp av = avma;
  GEN T = get_FpX_mod(TB);
  GEN y = FpX_resultant(T, x, p);
  GEN L = leading_term(T);
  if (gequal1(L) || signe(x)==0) return y;
  return gerepileupto(av, Fp_div(y, Fp_pows(L, degpol(x), p), p));
}

GEN
FpXQ_trace(GEN x, GEN TB, GEN p)
{
  pari_sp av = avma;
  GEN T = get_FpX_mod(TB);
  GEN dT = FpX_deriv(T,p);
  long n = degpol(dT);
  GEN z = FpXQ_mul(x, dT, TB, p);
  if (degpol(z)<n) { avma = av; return gen_0; }
  return gerepileuptoint(av, Fp_div(gel(z,2+n), gel(T,3+n),p));
}

GEN
FpXQ_charpoly(GEN x, GEN T, GEN p)
{
  pari_sp ltop=avma;
  long vT, v = fetch_var();
  GEN R;
  T = leafcopy(get_FpX_mod(T));
  vT = varn(T); setvarn(T, v);
  x = leafcopy(x); setvarn(x, v);
  R = FpX_FpXY_resultant(T, deg1pol_shallow(gen_1,FpX_neg(x,p),vT),p);
  (void)delete_var(); return gerepileupto(ltop,R);
}

GEN
FpXQ_minpoly(GEN x, GEN T, GEN p)
{
  pari_sp ltop=avma;
  GEN G,R=FpXQ_charpoly(x, T, p);
  GEN dR=FpX_deriv(R,p);
  while (signe(dR)==0)
  {
    R  = RgX_deflate(R,itos(p));
    dR = FpX_deriv(R,p);
  }
  G=FpX_gcd(R,dR,p);
  G=FpX_normalize(G,p);
  G=FpX_div(R,G,p);
  return gerepileupto(ltop,G);
}

GEN
FpXQ_conjvec(GEN x, GEN T, GEN p)
{
  pari_sp av=avma;
  long i;
  long n = get_FpX_degree(T), v = varn(x);
  GEN M = FpX_matFrobenius(T, p);
  GEN z = cgetg(n+1,t_COL);
  gel(z,1) = RgX_to_RgC(x,n);
  for (i=2; i<=n; i++) gel(z,i) = FpM_FpC_mul(M,gel(z,i-1),p);
  gel(z,1) = x;
  for (i=2; i<=n; i++) gel(z,i) = RgV_to_RgX(gel(z,i),v);
  return gerepilecopy(av,z);
}

/* p prime, p_1 = p-1, q = p^deg T, Lp = cofactors of some prime divisors
 * l_p of p-1, Lq = cofactors of some prime divisors l_q of q-1, return a
 * g in Fq such that
 * - Ng generates all l_p-Sylows of Fp^*
 * - g generates all l_q-Sylows of Fq^* */
static GEN
gener_FpXQ_i(GEN T, GEN p, GEN p_1, GEN Lp, GEN Lq)
{
  pari_sp av;
  long vT = varn(T), f = degpol(T), l = lg(Lq);
  GEN F = FpX_Frobenius(T, p);
  int p_is_2 = is_pm1(p_1);
  for (av = avma;; avma = av)
  {
    GEN t, g = random_FpX(f, vT, p);
    long i;
    if (degpol(g) < 1) continue;
    if (p_is_2)
      t = g;
    else
    {
      t = FpX_resultant(T, g, p); /* Ng = g^((q-1)/(p-1)), assuming T monic */
      if (kronecker(t, p) == 1) continue;
      if (lg(Lp) > 1 && !is_gener_Fp(t, p, p_1, Lp)) continue;
      t = FpXQ_pow(g, shifti(p_1,-1), T, p);
    }
    for (i = 1; i < l; i++)
    {
      GEN a = FpXQ_pow_Frobenius(t, gel(Lq,i), F, T, p);
      if (!degpol(a) && equalii(gel(a,2), p_1)) break;
    }
    if (i == l) return g;
  }
}

GEN
gener_FpXQ(GEN T, GEN p, GEN *po)
{
  long i, j, f = get_FpX_degree(T);
  GEN g, Lp, Lq, p_1, q_1, N, o;
  pari_sp av = avma;

  p_1 = subiu(p,1);
  if (f == 1) {
    GEN Lp, fa;
    o = p_1;
    fa = Z_factor(o);
    Lp = gel(fa,1);
    Lp = vecslice(Lp, 2, lg(Lp)-1); /* remove 2 for efficiency */

    g = cgetg(3, t_POL);
    g[1] = evalsigne(1) | evalvarn(get_FpX_var(T));
    gel(g,2) = pgener_Fp_local(p, Lp);
    if (po) *po = mkvec2(o, fa);
    return g;
  }
  if (lgefint(p) == 3)
  {
    ulong pp = to_Flxq(NULL, &T, p);
    g = gener_Flxq(T, pp, po);
    if (!po) return Flx_to_ZX_inplace(gerepileuptoleaf(av, g));
    g = Flx_to_ZX(g);
    gel(*po,2) = Flx_to_ZX(gel(*po,2));
    gerepileall(av, 2, &g, po);
    return g;
  }
  /* p now odd */
  q_1 = subiu(powiu(p,f), 1);
  N = diviiexact(q_1, p_1);
  Lp = odd_prime_divisors(p_1);
  for (i=lg(Lp)-1; i; i--) gel(Lp,i) = diviiexact(p_1, gel(Lp,i));
  o = factor_pn_1(p,f);
  Lq = leafcopy( gel(o, 1) );
  for (i = j = 1; i < lg(Lq); i++)
  {
    if (remii(p_1, gel(Lq,i)) == gen_0) continue;
    gel(Lq,j++) = diviiexact(N, gel(Lq,i));
  }
  setlg(Lq, j);
  g = gener_FpXQ_i(get_FpX_mod(T), p, p_1, Lp, Lq);
  if (!po) g = gerepilecopy(av, g);
  else {
    *po = mkvec2(q_1, o);
    gerepileall(av, 2, &g, po);
  }
  return g;
}

#if 0 /* generic version: slower */
GEN
gener_FpXQ2(GEN T, GEN p, GEN *po)
{
  pari_sp av = avma;
  void *E;
  long f = get_FpX_degree(T);
  GEN g, o = factor_pn_1(p,f);
  const struct bb_group *S = get_FpXQ_star(&E,T,p);
  g = gen_gener(o,E,S);
  if (!po) g = gerepilecopy(av, g);
  else {
    *po = mkvec2(powiu(p,f), o);
    gerepileall(av, 2, &g, po);
  }
  return g;
}
#endif

GEN
gener_FpXQ_local(GEN T, GEN p, GEN L)
{
  GEN Lp, Lq, p_1 = subiu(p,1), q_1, N, Q;
  long f, i, ip, iq, l = lg(L);
  T = get_FpX_mod(T);
  f = degpol(T);
  q_1 = subiu(powiu(p,f), 1);
  N = diviiexact(q_1, p_1);

  Q = is_pm1(p_1)? gen_1: shifti(p_1,-1);
  Lp = cgetg(l, t_VEC); ip = 1;
  Lq = cgetg(l, t_VEC); iq = 1;
  for (i=1; i < l; i++)
  {
    GEN a, b, ell = gel(L,i);
    if (equaliu(ell,2)) continue;
    a = dvmdii(Q, ell, &b);
    if (b == gen_0)
      gel(Lp,ip++) = a;
    else
      gel(Lq,iq++) = diviiexact(N,ell);
  }
  setlg(Lp, ip);
  setlg(Lq, iq);
  return gener_FpXQ_i(T, p, p_1, Lp, Lq);
}
