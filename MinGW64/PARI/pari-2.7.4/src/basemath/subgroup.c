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

typedef struct slist {
  struct slist *next;
  long *data;
  long prec;
} slist;

typedef struct {
  GEN cyc, gen;
  ulong count;
  slist *list;
} sublist_t;

/* SUBGROUPS
 * G = Gp x I, with Gp a p-Sylow (I assumed small).
 * Compute subgroups of I by recursive calls
 * Loop through subgroups Hp of Gp using Birkhoff's algorithm.
 * If (I is non trivial)
 *   lift Hp to G (mul by exponent of I)
 *   for each subgp of I, lift it to G (mult by exponent of Gp)
 *   consider the group generated by the two subgroups (concat)
 *
 * type(H) = mu --> H = Z/p^mu[1] x ... x Z/p^mu[len(mu)] */
typedef struct subgp_iter {
  long *M, *L; /* mu = p-subgroup type, lambda = p-group type */
  GEN *powlist; /* [i] = p^i, i = 0.. */
  long *c, *maxc;
  GEN *a, *maxa, **g, **maxg;
  long *available;
  GEN **H; /* p-subgroup of type mu, in matrix form */
  GEN cyc; /* cyclic factors of G */
  GEN subq;/* subgrouplist(I) */
  GEN subqpart; /* J in subq s.t [I:J][Gp:Hp] <= indexbound */
  GEN bound; /* if != NULL, impose a "bound" on [G:H] (see boundtype) */
  long boundtype;
  long countsub; /* number of subgroups of type M (so far) */
  long count; /* number of p-subgroups so far [updated when M completed] */
  GEN expoI; /* exponent of I */

  long(*fun)(void*, GEN); /* callback applied to each subgroup */
  void *fundata; /* data for fun */
  long stop;
} subgp_iter;

/* MAX: [G:H] <= bound, EXACT: [G:H] = bound, TYPE: type(H) = bound */
enum { b_NONE, b_MAX, b_EXACT, b_TYPE };

#define len(x)      (x)[0]
#define setlen(x,l) len(x)=(l)

static void
printtyp(const long *typ) /*Used only for ddebugging */
{
  long i, l = len(typ);
  for (i=1; i<=l; i++) err_printf(" %lld ",typ[i]);
  err_printf("\n");
}

/* compute conjugate partition of typ */
static long*
conjugate(long *typ)
{
  long *t, i, k = len(typ), l, last;

  if (!k) { t = new_chunk(1); setlen(t,0); return t; }
  l = typ[1]; t = new_chunk(l+2);
  t[1] = k; last = k;
  for (i=2; i<=l; i++)
  {
    while (typ[last] < i) last--;
    t[i] = last;
  }
  t[i] = 0; setlen(t,l);
  return t;
}
/* ----subgp_iter 'fun' associated to subgrouplist ------------- */
static void
addcell(sublist_t *S, GEN H)
{
  long *pt,i,j,L, n = lg(H)-1;
  slist *cell;

  L = 3;
  for (j=1; j<=n; j++)
  { /* H in HNF, largest entries are on diagonal */
    long l = lgefint(gcoeff(H,j,j));
    if (l > L) L = l;
  }
  L -= 2;
  cell = (slist*) pari_malloc(sizeof(slist)
                              + ((n*(n+1)) >> 1) * sizeof(long) * L);
  S->list->next = cell; cell->data = pt = (long*) (cell + 1);
  cell->prec = L;
  for (j=1; j<=n; j++)
    for(i=1; i<=j; i++) {
      GEN z = gcoeff(H,i,j);
      long h, lz = lgefint(z) - 2;
      for (h = 0; h < L - lz; h++) *pt++ = 0;
      for (h = 0; h < lz; h++) *pt++ = z[h+2];
    }
  S->list = cell;
  S->count++;
}

static long
list_fun(void *E, GEN x)
{
  sublist_t *S = (sublist_t*)E;
  GEN H = ZM_hnfmodid(x, S->cyc);
  if (!S->gen || subgroup_conductor_ok(H, S->gen)) addcell(S, H);
  return 0;
}
/* -------------------------------------------------------------- */

/* treat subgroup Hp (not in HNF, T->fun should do it if desired) */
static void
treatsub(subgp_iter *T, GEN H)
{
  long i;
  if (!T->subq) {T->stop = T->fun(T->fundata, H); T->countsub++; }
  else
  { /* not a p group, add the trivial part */
    GEN Hp = gmul(T->expoI, H); /* lift H to G */
    long n = lg(T->subqpart)-1;
    for (i=1; i<=n; i++)
      if (T->fun(T->fundata, shallowconcat(Hp, gel(T->subqpart,i))))
        { T->stop = 1; break; }
    T->countsub += n;
  }
}

/* x a t_INT, x++. Could be optimized... */
static void
inc(GEN x) { affii(addis(x,1), x); }

/* assume t>0 and l>1 */
static void
dogroup(subgp_iter *T)
{
  const GEN *powlist = T->powlist;
  long *M = T->M;
  long *L = T->L;
  long *c = T->c;
  GEN *a = T->a,  *maxa = T->maxa;
  GEN **g = T->g, **maxg = T->maxg;
  GEN **H = T->H;
  pari_sp av;
  long i,j,k,r,n,t2,ind, t = len(M), l = len(L);

  t2 = (l==t)? t-1: t;
  n = t2 * l - (t2*(t2+1))/2; /* number of gamma_ij */
  for (i=1, r=t+1; ; i++)
  {
    if (T->available[i]) c[r++] = i;
    if (r > l) break;
  }
  if (DEBUGLEVEL>6) { err_printf("    column selection:"); printtyp(c); }
  /* a/g and maxa/maxg access the same data indexed differently */
  for (ind=0,i=1; i<=t; ind+=(l-i),i++)
  {
    maxg[i] = maxa + (ind - (i+1)); /* only access maxg[i][i+1..l] */
    g[i] = a + (ind - (i+1));
    for (r=i+1; r<=l; r++)
      if (c[r] < c[i])         maxg[i][r] = powlist[M[i]-M[r]-1];
      else if (L[c[r]] < M[i]) maxg[i][r] = powlist[L[c[r]]-M[r]];
      else                     maxg[i][r] = powlist[M[i]-M[r]];
  }
  /* allocate correct lg */
  for (i = 0; i<= n-1; i++) a[i] = icopy(maxa[i]);
  affui(0, a[n-1]); for (i=0; i<n-1; i++) affui(1, a[i]);
  av = avma;
  for(;!T->stop;)
  {
    inc(a[n-1]);
    if (cmpii(a[n-1], maxa[n-1]) > 0)
    {
      j=n-2; while (j>=0 && equalii(a[j], maxa[j])) j--;
      if (j < 0) return;

      inc(a[j]);
      for (k=j+1; k<n; k++) affsi(1, a[k]);
    }
    for (i=1; i<=t; i++)
    {
      for (r=1; r<i; r++) H[i][c[r]] = gen_0;
      H[i][c[r]] = powlist[L[c[r]] - M[r]];
      for (r=i+1; r<=l; r++)
      {
        GEN e = g[i][r];
        long d = L[c[r]] - M[i];
        if (c[r] < c[i])
          e = mulii(e, powlist[d+1]);
        else if (d > 0)
          e = mulii(e, powlist[d]);
        H[i][c[r]] = e;
      }
    }
    treatsub(T, (GEN)H); avma = av;
  }
}

/* T->c[1],...,T->c[r-1] filled */
static void
loop(subgp_iter *T, long r)
{
  long j;

  if (r > len(T->M)) {
    pari_sp av = avma; dogroup(T); avma = av;
    return;
  }

  if (r!=1 && (T->M[r-1] == T->M[r])) j = T->c[r-1]+1; else j = 1;
  for (  ; j<=T->maxc[r]; j++)
    if (T->available[j])
    {
      T->c[r] = j;  T->available[j] = 0;
      loop(T, r+1); T->available[j] = 1;
    }
}

static void
dopsubtyp(subgp_iter *T)
{
  pari_sp av = avma;
  long i,r, l = len(T->L), t = len(T->M);

  if (!t) { treatsub(T, mkmat( zerocol(l) )); avma = av; return; }
  if (l==1) /* imply t = 1 */
  {
    GEN p1 = gtomat(T->powlist[T->L[1]-T->M[1]]);
    treatsub(T, p1); avma = av; return;
  }
  T->c         = new_chunk(l+1); setlen(T->c, l);
  T->maxc      = new_chunk(l+1);
  T->available = new_chunk(l+1);
  T->a   = (GEN*)new_chunk(l*(t+1));
  T->maxa= (GEN*)new_chunk(l*(t+1));
  T->g    = (GEN**)new_chunk(t+1);
  T->maxg = (GEN**)new_chunk(t+1);

  if (DEBUGLEVEL>4) { err_printf("  subgroup:"); printtyp(T->M); }
  for (i=1; i<=t; i++)
  {
    for (r=1; r<=l; r++)
      if (T->M[i] > T->L[r]) break;
    T->maxc[i] = r-1;
  }
  T->H = (GEN**)cgetg(t+1, t_MAT);
  for (i=1; i<=t; i++) T->H[i] = (GEN*)cgetg(l+1, t_COL);
  for (i=1; i<=l; i++) T->available[i]=1;
  for (i=1; i<=t; i++) T->c[i]=0;
  /* go through all column selections */
  loop(T, 1); avma = av; return;
}

static long
weight(long *typ)
{
  long i, l = len(typ), w = 0;
  for (i=1; i<=l; i++) w += typ[i];
  return w;
}

static void
dopsub(subgp_iter *T, GEN p, GEN indexsubq)
{
  long *M, *L = T->L;
  long w,i,j,k,lsubq, wG = weight(L), wmin = 0, wmax = wG, n = len(L);

  if (DEBUGLEVEL>4) { err_printf("\ngroup:"); printtyp(L); }
  T->count = 0;
  switch(T->boundtype)
  {
  case b_MAX: /* upper bound */
    wmin = (long) (wG - (log(gtodouble(T->bound)) / log(gtodouble(p))));
    if (cmpii(powiu(p, wG - wmin), T->bound) > 0) wmin++;
    break;
  case b_EXACT: /* exact value */
    wmin = wmax = wG - Z_pval(T->bound, p);
    break;
  }
  T->M = M = new_chunk(n+1);
  if (T->subq)
  {
    lsubq = lg(T->subq);
    T->subqpart = T->bound? cgetg(lsubq, t_VEC): T->subq;
  }
  else
    lsubq = 0; /* -Wall */
  M[1] = -1; for (i=2; i<=n; i++) M[i]=0;
  for(;!T->stop;) /* go through all vectors mu_{i+1} <= mu_i <= lam_i */
  {
    M[1]++;
    if (M[1] > L[1])
    {
      for (j=2; j<=n; j++)
        if (M[j] < L[j] && M[j] < M[j-1]) break;
      if (j > n) return;

      M[j]++; for (k=1; k<j; k++) M[k]=M[j];
    }
    for (j=1; j<=n; j++)
      if (!M[j]) break;
    setlen(M, j-1); w = weight(M);
    if (w >= wmin && w <= wmax)
    {
      GEN p1 = gen_1;

      if (T->subq && T->bound) /* G not a p-group */
      {
        pari_sp av = avma;
        GEN indexH = powiu(p, wG - w);
        GEN B = divii(T->bound, indexH);
        k = 1;
        for (i=1; i<lsubq; i++)
          if (cmpii(gel(indexsubq,i), B) <= 0)
            T->subqpart[k++] = T->subq[i];
        setlg(T->subqpart, k); avma = av;
      }
      if (DEBUGLEVEL>4)
      {
        long *Lp = conjugate(L);
        long *Mp = conjugate(M);
        GEN BINMAT = matqpascal(len(L)+1, p);

        if (DEBUGLEVEL>7)
        {
          err_printf("    lambda = "); printtyp(L);
          err_printf("    lambda'= "); printtyp(Lp);
          err_printf("    mu = "); printtyp(M);
          err_printf("    mu'= "); printtyp(Mp);
        }
        for (j=1; j<=len(Mp); j++)
        {
          p1 = mulii(p1, powiu(p, Mp[j+1]*(Lp[j]-Mp[j])));
          p1 = mulii(p1, gcoeff(BINMAT, Lp[j]-Mp[j+1]+1, Mp[j]-Mp[j+1]+1));
        }
        err_printf("  alpha_lambda(mu,p) = %Ps\n",p1);
      }

      T->countsub = 0; dopsubtyp(T);
      T->count += T->countsub;

      if (DEBUGLEVEL>4)
      {
        err_printf("  countsub = %lld\n", T->countsub);
        if (T->subq) p1 = muliu(p1,lg(T->subqpart)-1);
        if (!equaliu(p1,T->countsub))
        {
          err_printf("  alpha = %Ps\n",p1);
          pari_err_BUG("forsubgroup (alpha != countsub)");
        }
      }
    }
  }
}

static void
parse_bound(subgp_iter *T)
{
  GEN b, B = T->bound;
  if (!B) { T->boundtype = b_NONE; return; }
  switch(typ(B))
  {
  case t_INT: /* upper bound */
    T->boundtype = b_MAX;
    break;
  case t_VEC: /* exact value */
    b = gel(B,1);
    if (lg(B) != 2 || typ(b) != t_INT) pari_err_TYPE("subgroup", B);
    T->boundtype = b_EXACT;
    T->bound = b;
    break;
  case t_COL: /* exact type */
    pari_err_IMPL("exact type in subgrouplist");
    if (lg(B) > len(T->L)+1) pari_err_TYPE("subgroup",B);
    T->boundtype = b_TYPE;
    break;
  default: pari_err_TYPE("subgroup",B);
  }
  if (signe(T->bound) <= 0)
    pari_err_DOMAIN("subgroup", "index bound", "<=", gen_0, T->bound);
}

static GEN
expand_sub(GEN x, long n)
{
  long i,j, m = lg(x);
  GEN p = matid(n-1), q,c;

  for (i=1; i<m; i++)
  {
    q = gel(p,i); c = gel(x,i);
    for (j=1; j<m; j++) gel(q,j) = gel(c,j);
    for (   ; j<n; j++) gel(q,j) = gen_0;
  }
  return p;
}

static GEN
init_powlist(long k, GEN p)
{
  GEN z = new_chunk(k+1);
  long i;
  gel(z,0) = gen_1; gel(z,1) = p;
  for (i=2; i<=k; i++) gel(z,i) = mulii(p, gel(z,i-1));
  return z;
}

static GEN subgrouplist_i(GEN cyc, GEN bound, GEN expoI, GEN gen);
static void
subgroup_engine(subgp_iter *T)
{
  pari_sp av = avma;
  GEN B,L,fa,primlist,p,listL,indexsubq = NULL;
  GEN cyc = T->cyc;
  long i,j,k,imax,lprim, n = lg(cyc);

  if (typ(cyc) != t_VEC)
  {
    if (typ(cyc) != t_MAT) pari_err_TYPE("forsubgroup",cyc);
    cyc = RgM_diagonal_shallow(cyc);
  }
  for (i=1; i<n-1; i++)
    if (!dvdii(gel(cyc,i), gel(cyc,i+1)))
      pari_err_TYPE("forsubgroup [not a group]", cyc);
  if (n == 1) {
    parse_bound(T);
    switch(T->boundtype)
    {
      case b_EXACT: if (!is_pm1(T->bound)) break;
      default: T->fun(T->fundata, cyc);
    }
    avma = av; return;
  }
  if (!signe(gel(cyc,1))) pari_err_TYPE("forsubgroup [infinite group]", cyc);
  fa = Z_factor(gel(cyc,1)); primlist = gel(fa,1);
  listL = cgetg_copy(primlist, &lprim);
  imax = k = 0;
  for (i=1; i<lprim; i++)
  {
    L = new_chunk(n); p = gel(primlist,i);
    for (j=1; j<n; j++)
    {
      L[j] = Z_pval(gel(cyc,j), p);
      if (!L[j]) break;
    }
    j--; setlen(L, j);
    if (j > k) { k = j; imax = i; }
    gel(listL,i) = L;
  }
  L = gel(listL,imax); p = gel(primlist,imax);
  k = L[1];
  T->L = L;
  T->powlist = (GEN*)init_powlist(k, p);
  B = T->bound;
  parse_bound(T);

  if (lprim == 2)
  {
    T->subq = NULL;
    if (T->boundtype == b_EXACT)
    {
      (void)Z_pvalrem(T->bound,p,&B);
      if (!is_pm1(B)) { avma = av; return; }
    }
  }
  else
  { /* not a p-group */
    GEN cycI = leafcopy(cyc);
    long lsubq;
    for (i=1; i<n; i++)
    {
      gel(cycI,i) = divii(gel(cycI,i), T->powlist[L[i]]);
      if (is_pm1(gel(cycI,i))) break;
    }
    setlg(cycI, i); /* cyclic factors of I */
    if (T->boundtype == b_EXACT)
    {
      (void)Z_pvalrem(T->bound,p,&B);
      B = mkvec(B);
    }
    T->expoI = gel(cycI,1);
    T->subq = subgrouplist_i(cycI, B, T->expoI, NULL);

    lsubq = lg(T->subq);
    for (i=1; i<lsubq; i++)
      gel(T->subq,i) = expand_sub(gel(T->subq,i), n);
    if (T->bound)
    {
      indexsubq = cgetg(lsubq,t_VEC);
      for (i=1; i<lsubq; i++)
        gel(indexsubq,i) = ZM_det_triangular(gel(T->subq,i));
    }
    /* lift subgroups of I to G */
    for (i=1; i<lsubq; i++)
      gel(T->subq,i) = gmul(T->powlist[k],gel(T->subq,i));
    if (DEBUGLEVEL>6)
      err_printf("(lifted) subgp of prime to %Ps part:\n%Ps\n",p, T->subq);
  }
  dopsub(T, p,indexsubq);
  if (DEBUGLEVEL>4) err_printf("nb subgroup = %lld\n",T->count);
  avma = av;
}

static GEN
get_snf(GEN x, long *N)
{
  GEN cyc;
  long n;
  switch(typ(x))
  {
    case t_MAT:
      if (!RgM_isdiagonal(x)) return NULL;
      cyc = RgM_diagonal_shallow(x); break;
    case t_VEC: if (lg(x) == 4 && typ(gel(x,2)) == t_VEC) x = gel(x,2);
    case t_COL: cyc = leafcopy(x); break;
    default: return NULL;
  }
  *N = lg(cyc)-1;
  for (n = *N; n > 0; n--) /* take care of trailing 1s */
  {
    GEN c = gel(cyc,n);
    if (typ(c) != t_INT || signe(c) <= 0) return NULL;
    if (!is_pm1(c)) break;
  }
  setlg(cyc, n+1);
  for ( ; n > 0; n--)
  {
    GEN c = gel(cyc,n);
    if (typ(c) != t_INT || signe(c) <= 0) return NULL;
  }
  return cyc;
}

void
forsubgroup(void *E, long call(void*, GEN), GEN cyc, GEN bound)
{
  subgp_iter T;
  long N;

  T.fun = call;
  T.cyc = get_snf(cyc,&N); if (!T.cyc) pari_err_TYPE("forsubgroup",cyc);
  T.bound = bound;
  T.fundata = E;
  T.stop = 0;
  subgroup_engine(&T);
}

void
forsubgroup0(GEN cyc, GEN bound, GEN code)
{
  push_lex(gen_0, code);
  forsubgroup((void*)code, &gp_evalvoid, cyc, bound);
  pop_lex(1);
}

static GEN
packtoi(long *pt, long L)
{
  long i, l;
  GEN z;
  for (i=0; i<L; i++, pt++)
    if (*pt) break;
  L -= i;
  if (!L) return gen_0;
  l = L+2; z = cgeti(l);
  z[1] = evalsigne(1) | evallgefint(l);
  for (i = 2; i<l; i++) z[i] = *pt++;
  return z;
}

static GEN
subgrouplist_i(GEN CYC, GEN bound, GEN expoI, GEN gen)
{
  pari_sp av = avma;
  subgp_iter T;
  sublist_t S;
  slist *list, *sublist;
  long ii,i,j,nbsub,n,N = 0; /* -Wall */
  GEN z, H, cyc;

  cyc = get_snf(CYC, &N);
  if (!cyc) pari_err_TYPE("subgrouplist",CYC);
  n = lg(cyc)-1; /* not necessarily = N */

  S.list = sublist = (slist*) pari_malloc(sizeof(slist));
  S.cyc = cyc;
  S.gen = gen;
  S.count = 0;
  T.fun = &list_fun;
  T.fundata = (void*)&S;
  T.stop = 0;

  T.cyc = cyc;
  T.bound = bound;
  T.expoI = expoI;

  subgroup_engine(&T);

  nbsub = (long)S.count;
  avma = av;
  z = cgetg(nbsub+1,t_VEC);
  for (ii=1; ii<=nbsub; ii++)
  {
    long *pt, L;
    list = sublist; sublist = list->next; pari_free(list);
    pt = sublist->data;
    L = sublist->prec;
    H = cgetg(N+1,t_MAT); gel(z,ii) = H;
    for (j=1; j<=n; j++)
    {
      gel(H,j) = cgetg(N+1, t_COL);
      for (i=1; i<=j; i++) { gcoeff(H,i,j) = packtoi(pt, L); pt += L; }
      for (   ; i<=N; i++) gcoeff(H,i,j) = gen_0;
    }
    for (   ; j<=N; j++) gel(H,j) = col_ei(N, j);
  }
  pari_free(sublist); return z;
}

GEN
subgrouplist(GEN cyc, GEN bound)
{
  return subgrouplist_i(cyc,bound,NULL,NULL);
}

GEN
subgroupcondlist(GEN cyc, GEN bound, GEN L)
{
  return subgrouplist_i(cyc,bound,NULL,L);
}
