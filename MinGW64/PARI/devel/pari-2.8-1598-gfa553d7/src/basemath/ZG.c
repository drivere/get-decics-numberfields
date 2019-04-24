/* $Id$

Copyright (C) 2011  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

#include "pari.h"
#include "paripriv.h"

static int
cmp_G(void *E, GEN x, GEN y) { (void)E; return cmp_universal(x,y); }

/* a ZG is either a t_INT or a t_VEC of pairs [g,e] representing
 * \sum e_i [g_i], e_i in Z, g_i in G. */
GEN
ZG_normalize(GEN x)
{
  if (typ(x) == t_INT) return x;
  return sort_factor(x, NULL, &cmp_G);
}
GEN
ZG_add(GEN x, GEN y)
{
  if (typ(x) == t_INT)
  {
    if (!signe(x)) return y;
    if (typ(y) == t_INT)
    {
      if (!signe(y)) return x;
      return addii(x,y);
    }
    x = to_famat_shallow(gen_1,x);
  }
  else if (typ(y) == t_INT)
  {
    if (!signe(y)) return x;
    y = to_famat_shallow(gen_1,y);
  }
  x = merge_factor(x, y, NULL, &cmp_G);
  if (lg(gel(x,1)) == 1) return gen_0;
  return x;
}
GEN
ZG_neg(GEN x)
{
  if (typ(x) == t_INT) return negi(x);
  return mkmat2(gel(x,1),ZC_neg(gel(x,2)));
}
GEN
ZG_sub(GEN x, GEN y) { return ZG_add(x, ZG_neg(y)); }

/* x * c.[1], x in Z[G] */
GEN
ZG_Z_mul(GEN x, GEN c)
{
  if (is_pm1(c)) return signe(c) > 0? x: ZG_neg(x);
  if (typ(x) == t_INT) return mulii(x,c);
  return mkmat2(gel(x,1), ZC_Z_mul(gel(x,2), c));
}

GEN
ZG_mul(GEN x, GEN y)
{
  pari_sp av;
  GEN z, XG, XE;
  long i, l;
  if (typ(x) == t_INT) return ZG_Z_mul(y, x);
  if (typ(y) == t_INT) return ZG_Z_mul(x, y);
  av = avma;
  XG = gel(x,1); XE = gel(x,2); l = lg(XG);
  z = ZG_Z_mul(G_ZG_mul(gel(XG,1), y), gel(XE,1));
  for (i = 2; i < l; i++)
  {
    z = ZG_add(z, ZG_Z_mul(G_ZG_mul(gel(XG,i), y), gel(XE,i)));
    if (gc_needed(av,3))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ZG_mul, i = %ld/%ld",i,l-1);
      z = gerepilecopy(av, z);
    }
  }
  return z;
}
#if 0
static GEN
ZGV_add(GEN x, GEN y)
{
  long i, l;
  GEN v = cgetg_copy(x, &l);
  for (i = 1; i < l; i++) gel(v,i) = ZG_add(gel(x,i), gel(y,i));
  return v;
}
static GEN
ZGV_sub(GEN x, GEN y)
{
  long i, l;
  GEN v = cgetg_copy(x, &l);
  for (i = 1; i < l; i++) gel(v,i) = ZG_sub(gel(x,i), gel(y,i));
  return v;
}
#endif
GEN
ZG_G_mul(GEN x, GEN y)
{
  long i, l;
  GEN z, X;
  if (typ(x) == t_INT) return to_famat_shallow(y, x);
  X = gel(x,1);
  z = cgetg_copy(X, &l);
  for (i = 1; i < l; i++) gel(z,i) = gmul(gel(X,i), y);
  return ZG_normalize( mkmat2(z, shallowcopy(gel(x,2))) );
}
GEN
G_ZG_mul(GEN x, GEN y)
{
  long i, l;
  GEN z, Y;
  if (typ(y) == t_INT) return to_famat_shallow(x, y);
  Y = gel(y,1);
  z = cgetg_copy(Y, &l);
  for (i = 1; i < l; i++) gel(z,i) = gmul(x, gel(Y,i));
  return ZG_normalize( mkmat2(z, shallowcopy(gel(y,2))) );
}
GEN
ZGC_G_mul(GEN v, GEN x)
{
  long i, l;
  GEN w = cgetg_copy(v, &l);
  for (i = 1; i < l; i++) gel(w,i) = ZG_G_mul(gel(v,i), x);
  return w;
}
GEN
G_ZGC_mul(GEN x, GEN v)
{
  long i, l;
  GEN w = cgetg_copy(v, &l);
  for (i = 1; i < l; i++) gel(w,i) = G_ZG_mul(gel(v,i), x);
  return w;
}
GEN
ZGC_Z_mul(GEN v, GEN x)
{
  long i, l;
  GEN w = cgetg_copy(v, &l);
  for (i = 1; i < l; i++) gel(w,i) = ZG_Z_mul(gel(v,i), x);
  return w;
}
