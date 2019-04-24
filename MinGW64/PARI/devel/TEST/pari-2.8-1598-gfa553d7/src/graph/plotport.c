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
/*                         PLOT ROUTINES                           */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"
#include "rect.h"

void postdraw0(long *w, long *x, long *y, long lw, long scale);
static void PARI_get_psplot(void);

/* no need for THREAD: OK to share this */
static hashtable *rgb_colors = NULL;
PariRect *rectgraph[18]; /*NUMRECT*/

/* no need for THREAD: gp-specific */
static long current_color[18]; /*NUMRECT*/

PARI_plot pari_plot, pari_psplot;
PARI_plot *pari_plot_engine = &pari_plot;
long rectpoint_itype = 0, rectline_itype  = 0;

const long NUMRECT = 18;
const long RECUR_MAXDEPTH = 10;
const double RECUR_PREC = 0.001;
const long DEFAULT_COLOR = 1, AXIS_COLOR = 2;

INLINE long
DTOL(double t) { return (long)(t + 0.5); }

/********************************************************************/
/**                                                                **/
/**                         LOW-RES PLOT                           **/
/**                                                                **/
/********************************************************************/
#define ISCR 64
#define JSCR 22
static char
PICT(long j) {
  switch(j%3) {
    case 0:  return '_';
    case 1:  return 'x';
    default: return '"';
  }
}
static char
PICTZERO(long j) {
  switch(j%3) {
    case 0:  return ',';
    case 1:  return '-';
    default: return '`';
  }
}

static char *
dsprintf9(double d, char *buf)
{
  int i = 10;

  while (--i >= 0) {
    sprintf(buf, "%9.*g", i, d);
    if (strlen(buf) <= 9) return buf;
  }
  return buf; /* Should not happen? */
}

typedef unsigned char screen[ISCR+1][JSCR+1];

static void
fill_gap(screen scr, long i, int jnew, int jpre)
{
  int mid, i_up, i_lo, up, lo;

  if (jpre < jnew - 2) {
    up = jnew - 1; i_up = i;
    lo = jpre + 1; i_lo = i - 1;
  } else if (jnew < jpre - 2) {
    up = jpre - 1; i_up = i - 1;
    lo = jnew + 1; i_lo = i;
  } else return; /* if gap < 2, leave it as it is. */

  mid = (jpre+jnew)/2;
  if (mid>JSCR) mid=JSCR; else if (mid<0) mid=0;
  if (lo<0) lo=0;
  if (lo<=JSCR) while (lo <= mid) scr[i_lo][lo++] = ':';
  if (up>JSCR) up=JSCR;
  if (up>=0) while (up > mid) scr[i_up][up--] = ':';
}

static double
todbl(GEN x) { return rtodbl(gtofp(x, LOWDEFAULTPREC)); }

/* code is either a t_CLOSURE (from GP: ploth, etc.) or a t_POL/t_VEC of
 * two t_POLs from rectsplines */
static GEN
READ_EXPR(GEN code, GEN x) {
  if (typ(code)!=t_CLOSURE) return gsubst(code,0,x);
  set_lex(-1, x); return closure_evalgen(code);
}

void
plot(GEN a, GEN b, GEN code, GEN ysmlu,GEN ybigu, long prec)
{
  const char BLANK = ' ', YY = '|', XX_UPPER = '\'', XX_LOWER = '.';
  long jz, j, i, sig;
  pari_sp av = avma;
  int jnew, jpre = 0; /* for lint */
  GEN x, dx;
  double diff, dyj, ysml, ybig, y[ISCR+1];
  screen scr;
  char buf[80], z;

  sig=gcmp(b,a); if (!sig) return;
  if (sig<0) { x=a; a=b; b=x; }
  x = gtofp(a, prec); push_lex(x, code);
  dx = divru(gtofp(gsub(b,a),prec), ISCR-1);
  for (j=1; j<=JSCR; j++) scr[1][j]=scr[ISCR][j]=YY;
  for (i=2; i<ISCR; i++)
  {
    scr[i][1]   = XX_LOWER;
    scr[i][JSCR]= XX_UPPER;
    for (j=2; j<JSCR; j++) scr[i][j] = BLANK;
  }
  ysml = ybig = 0.; /* -Wall */
  for (i=1; i<=ISCR; i++)
  {
    pari_sp av2 = avma;
    y[i] = gtodouble( READ_EXPR(code,x) );
    avma = av2;
    if (i == 1)
      ysml = ybig = y[1];
    else
    {
      if (y[i] < ysml) ysml = y[i];
      if (y[i] > ybig) ybig = y[i];
    }
    x = addrr(x,dx);
  }
  avma = av;
  if (ysmlu) ysml = gtodouble(ysmlu);
  if (ybigu) ybig = gtodouble(ybigu);
  diff = ybig - ysml;
  if (!diff) { ybig += 1; diff= 1.; }
  dyj = ((JSCR-1)*3+2) / diff;
  /* work around bug in gcc-4.8 (32bit): plot(x=-5,5,sin(x)))) */
  jz = 3 - (long)(ysml*dyj + 0.5); /* 3 - DTOL(ysml*dyj) */
  z = PICTZERO(jz); jz /= 3;
  for (i=1; i<=ISCR; i++)
  {
    if (0<=jz && jz<=JSCR) scr[i][jz]=z;
    j = 3 + DTOL((y[i]-ysml)*dyj);
    jnew = j/3;
    if (i > 1) fill_gap(scr, i, jnew, jpre);
    if (0<=jnew && jnew<=JSCR) scr[i][jnew] = PICT(j);
    jpre = jnew;
  }
  pari_putc('\n');
  pari_printf("%s ", dsprintf9(ybig, buf));
  for (i=1; i<=ISCR; i++) pari_putc(scr[i][JSCR]);
  pari_putc('\n');
  for (j=(JSCR-1); j>=2; j--)
  {
    pari_puts("          ");
    for (i=1; i<=ISCR; i++) pari_putc(scr[i][j]);
    pari_putc('\n');
  }
  pari_printf("%s ", dsprintf9(ysml, buf));
  for (i=1; i<=ISCR; i++)  pari_putc(scr[i][1]);
  pari_putc('\n');
  {
    char line[10 + 32 + 32 + ISCR - 9];
    sprintf(line, "%10s%-9.7g%*.7g\n"," ",todbl(a),ISCR-9,todbl(b));
    pari_printf(line);
  }
  pop_lex(1);
}

/********************************************************************/
/**                                                                **/
/**                      RECTPLOT FUNCTIONS                        **/
/**                                                                **/
/********************************************************************/
void
init_graph(void)
{
  long n;
  for (n=0; n<NUMRECT; n++)
  {
    PariRect *e = (PariRect*) pari_malloc(sizeof(PariRect));
    e->head = e->tail = NULL;
    e->sizex = e->sizey = 0;
    current_color[n] = DEFAULT_COLOR;
    rectgraph[n] = e;
  }
}

void
free_graph(void)
{
  int i;
  for (i=0; i<NUMRECT; i++)
  {
    PariRect *e = rectgraph[i];
    if (RHead(e)) killrect(i);
    pari_free((void *)e);
  }
  if (rgb_colors)
  {
    pari_free((void*)rgb_colors->table);
    pari_free((void*)rgb_colors);
  }
  if (GP_DATA->colormap) pari_free(GP_DATA->colormap);
  if (GP_DATA->graphcolors) pari_free(GP_DATA->graphcolors);
}

static PariRect *
check_rect(long ne)
{
  const long m = NUMRECT-1;
  if (ne < 0)
    pari_err_DOMAIN("graphic function", "rectwindow", "<", gen_0, stoi(ne));
  if (ne > m)
    pari_err_DOMAIN("graphic function", "rectwindow", ">", stoi(m), stoi(ne));
  return rectgraph[ne];
}

static PariRect *
check_rect_init(long ne)
{
  PariRect *e = check_rect(ne);
  if (!RHead(e))
    pari_err_TYPE("graphic function [use plotinit() first]", stoi(ne));
  return e;
}

static long
initrect_get_arg(GEN x, long flag, long *dft)
{ /* FIXME: gequal0(x) undocumented backward compatibility hack */
  if (!x || gequal0(x) || flag) { PARI_get_plot(); return *dft - 1; }
  if (typ(x) != t_INT) pari_err_TYPE("initrect",x);
  return itos(x);
}
void
initrect_gen(long ne, GEN x, GEN y, long flag)
{
  const long m = NUMRECT-3;
  long xi, yi;

  xi = initrect_get_arg(x, flag, &pari_plot.width);
  yi = initrect_get_arg(y, flag, &pari_plot.height);
  if (flag) {
    if (x) xi = DTOL(xi * gtodouble(x));
    if (y) yi = DTOL(yi * gtodouble(y));
  }
  if (ne > m)
    pari_err_DOMAIN("graphic function", "rectwindow", ">", stoi(m), stoi(ne));
  initrect(ne, xi, yi);
}

static void
Rchain(PariRect *e, RectObj *z)
{
  if (!RHead(e)) RHead(e) = z; else RoNext(RTail(e)) = z;
  RTail(e) = z;
  RoNext(z) = NULL;
}

void
initrect(long ne, long x, long y)
{
  PariRect *e;
  RectObj *z;

  if (x <= 1) pari_err_DOMAIN("initrect", "x", "<=", gen_1, stoi(x));
  if (y <= 1) pari_err_DOMAIN("initrect", "y", "<=", gen_1, stoi(y));
  e = check_rect(ne); if (RHead(e)) killrect(ne);

  z = (RectObj*) pari_malloc(sizeof(RectObj));
  RoType(z) = ROt_NULL;
  Rchain(e, z);
  RXsize(e) = x; RXcursor(e) = 0;
  RYsize(e) = y; RYcursor(e) = 0;
  RXscale(e) = 1; RXshift(e) = 0;
  RYscale(e) = 1; RYshift(e) = 0;
  RHasGraph(e) = 0;
}

GEN
rectcursor(long ne)
{
  PariRect *e = check_rect_init(ne);
  return mkvec2s((long)RXcursor(e), (long)RYcursor(e));
}

static void
rectscale0(long ne, double x1, double x2, double y1, double y2)
{
  PariRect *e = check_rect_init(ne);
  double x, y;

  x = RXshift(e) + RXscale(e) * RXcursor(e);
  y = RYshift(e) + RYscale(e) * RYcursor(e);
  RXscale(e) = RXsize(e)/(x2-x1); RXshift(e) = -x1*RXscale(e);
  RYscale(e) = RYsize(e)/(y1-y2); RYshift(e) = -y2*RYscale(e);
  RXcursor(e) = (x - RXshift(e)) / RXscale(e);
  RYcursor(e) = (y - RYshift(e)) / RYscale(e);
}

void
rectscale(long ne, GEN x1, GEN x2, GEN y1, GEN y2)
{
  rectscale0(ne, gtodouble(x1), gtodouble(x2), gtodouble(y1), gtodouble(y2));
}

static void
rectmove0(long ne, double x, double y, long relative)
{
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj1P));

  if (relative) { RXcursor(e) += x; RYcursor(e) += y; }
  else          { RXcursor(e) = x; RYcursor(e) = y; }
  RoType(z) = ROt_MV;
  RoMVx(z) = RXcursor(e) * RXscale(e) + RXshift(e);
  RoMVy(z) = RYcursor(e) * RYscale(e) + RYshift(e);
  Rchain(e, z);
}

void
rectmove(long ne, GEN x, GEN y)
{
  rectmove0(ne,gtodouble(x),gtodouble(y),0);
}

void
rectrmove(long ne, GEN x, GEN y)
{
  rectmove0(ne,gtodouble(x),gtodouble(y),1);
}

void
rectpoint0(long ne, double x, double y,long relative) /* code = ROt_MV/ROt_PT */
{
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj1P));

  if (relative) { RXcursor(e) += x; RYcursor(e) += y; }
  else          { RXcursor(e) = x; RYcursor(e) = y; }
  RoPTx(z) = RXcursor(e)*RXscale(e) + RXshift(e);
  RoPTy(z) = RYcursor(e)*RYscale(e) + RYshift(e);
  RoType(z) = ( DTOL(RoPTx(z)) < 0
                || DTOL(RoPTy(z)) < 0 || DTOL(RoPTx(z)) > RXsize(e)
                || DTOL(RoPTy(z)) > RYsize(e) ) ? ROt_MV : ROt_PT;
  Rchain(e, z);
  RoCol(z) = current_color[ne];
}

void
rectpoint(long ne, GEN x, GEN y)
{
  rectpoint0(ne,gtodouble(x),gtodouble(y),0);
}

void
rectrpoint(long ne, GEN x, GEN y)
{
  rectpoint0(ne,gtodouble(x),gtodouble(y),1);
}

void
rectcolor(long ne, long c)
{
  long n = lg(GP_DATA->colormap)-2;
  check_rect(ne);
  if (c < 1) pari_err_DOMAIN("rectcolor", "color", "<", gen_1, stoi(c));
  if (c > n) pari_err_DOMAIN("rectcolor", "color", ">", stoi(n), stoi(c));
  current_color[ne] = c;
}

void
rectline0(long ne, double gx2, double gy2, long relative) /* code = ROt_MV/ROt_LN */
{
  double dx,dy,dxy,xmin,xmax,ymin,ymax,x1,y1,x2,y2;
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj2P));
  const double c = 1 + 1e-10;

  x1 = RXcursor(e)*RXscale(e) + RXshift(e);
  y1 = RYcursor(e)*RYscale(e) + RYshift(e);
  if (relative)
    { RXcursor(e)+=gx2; RYcursor(e)+=gy2; }
  else
    { RXcursor(e)=gx2; RYcursor(e)=gy2; }
  x2 = RXcursor(e)*RXscale(e) + RXshift(e);
  y2 = RYcursor(e)*RYscale(e) + RYshift(e);
  xmin = maxdd(mindd(x1,x2),0); xmax = mindd(maxdd(x1,x2),RXsize(e));
  ymin = maxdd(mindd(y1,y2),0); ymax = mindd(maxdd(y1,y2),RYsize(e));
  dxy = x1*y2 - y1*x2; dx = x2-x1; dy = y2-y1;
  if (dy)
  {
    if (dx*dy<0)
      { xmin = maxdd(xmin,(dxy+RYsize(e)*dx)/dy); xmax=mindd(xmax,dxy/dy); }
    else
      { xmin=maxdd(xmin,dxy/dy); xmax=mindd(xmax,(dxy+RYsize(e)*dx)/dy); }
  }
  if (dx)
  {
    if (dx*dy<0)
      { ymin=maxdd(ymin,(RXsize(e)*dy-dxy)/dx); ymax=mindd(ymax,-dxy/dx); }
    else
      { ymin=maxdd(ymin,-dxy/dx); ymax=mindd(ymax,(RXsize(e)*dy-dxy)/dx); }
  }
  RoLNx1(z) = xmin; RoLNx2(z) = xmax;
  if (dx*dy<0) { RoLNy1(z) = ymax; RoLNy2(z) = ymin; }
  else         { RoLNy1(z) = ymin; RoLNy2(z) = ymax; }
  RoType(z) = (xmin>xmax*c || ymin>ymax*c) ? ROt_MV : ROt_LN;
  Rchain(e, z);
  RoCol(z) = current_color[ne];
}

/* Given coordinates of ends of a line, and labels l1 l2 attached to the
   ends, plot ticks where the label coordinate takes "round" values */

static void
rectticks(PARI_plot *WW, long ne,
          double dx1, double dy1, double dx2, double dy2,
          double l1, double l2, long flags)
{
  long dx,dy,dxy,dxy1,x1,y1,x2,y2,nticks,n,n1,dn;
  double minstep, maxstep, step, l_min, l_max, minl, maxl, dl, dtx, dty, x, y;
  double ddx, ddy;
  const double mult[3] = { 2./1., 5./2., 10./5. };
  PariRect *e = check_rect_init(ne);
  int do_double = !(flags & TICKS_NODOUBLE);

  x1 = DTOL(dx1*RXscale(e) + RXshift(e));
  y1 = DTOL(dy1*RYscale(e) + RYshift(e));
  x2 = DTOL(dx2*RXscale(e) + RXshift(e));
  y2 = DTOL(dy2*RYscale(e) + RYshift(e));
  dx = x2 - x1;
  dy = y2 - y1;
  if (dx < 0) dx = -dx;
  if (dy < 0) dy = -dy;
  dxy1 = maxss(dx, dy);
  dx /= WW->hunit;
  dy /= WW->vunit;
  if (dx > 1000 || dy > 1000)
    dxy = 1000; /* avoid overflow */
  else
    dxy = (long)sqrt(dx*dx + dy*dy);
  nticks = (long) ((dxy + 2.5)/4);
  if (!nticks) return;

  /* Now we want to find nticks (or less) "round" numbers between l1 and l2.
     For our purpose round numbers have "last significant" digit either
        *) any;
        *) even;
        *) divisible by 5.
     We need to choose which alternative is better.
   */
  if (l1 < l2)
    l_min = l1, l_max = l2;
  else
    l_min = l2, l_max = l1;
  minstep = (l_max - l_min)/(nticks + 1);
  maxstep = 2.5*(l_max - l_min);
  step = exp(log(10) * floor(log10(minstep)));
  if (!(flags & TICKS_ENDSTOO)) {
    double d = 2*(l_max - l_min)/dxy1;        /* Two pixels off */

    l_min += d;
    l_max -= d;
  }
  for (n = 0; ; n++) {
    if (step >= maxstep) return;

    if (step >= minstep) {
      minl = ceil(l_min/step);
      maxl = floor(l_max/step);
      if (minl <= maxl && maxl - minl + 1 <= nticks) {
        nticks = (long) (maxl - minl + 1);
        l_min = minl * step;
        l_max = maxl * step; break;
      }
    }
    step *= mult[ n % 3 ];
  }
  /* Where to position doubleticks, variants:
     small: each 5, double: each 10        (n===2 mod 3)
     small: each 2, double: each 10        (n===1 mod 3)
     small: each 1, double: each  5 */
  dn = (n % 3 == 2)? 2: 5;
  n1 = ((long)minl) % dn; /* unused if do_double = FALSE */

  /* now l_min and l_max keep min/max values of l with ticks, and nticks is
     the number of ticks to draw. */
  if (nticks == 1) ddx = ddy = 0; /* unused: for lint */
  else {
    dl = (l_max - l_min)/(nticks - 1);
    ddx = (dx2 - dx1) * dl / (l2 - l1);
    ddy = (dy2 - dy1) * dl / (l2 - l1);
  }
  x = dx1 + (dx2 - dx1) * (l_min - l1) / (l2 - l1);
  y = dy1 + (dy2 - dy1) * (l_min - l1) / (l2 - l1);
  /* assume hunit and vunit form a square.  For clockwise ticks: */
  dtx = WW->hunit * dy/dxy * (y2 > y1 ? 1 : -1);        /* y-coord runs down */
  dty = WW->vunit * dx/dxy * (x2 > x1 ? 1 : -1);
  for (n = 0; n < nticks; n++) {
    RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj2P));
    double lunit = WW->hunit > 1 ? 1.5 : 2;
    double l = (do_double && (n + n1) % dn == 0) ? lunit: 1;

    RoLNx1(z) = RoLNx2(z) = x*RXscale(e) + RXshift(e);
    RoLNy1(z) = RoLNy2(z) = y*RYscale(e) + RYshift(e);

    if (flags & TICKS_CLOCKW) {
      RoLNx1(z) += dtx*l;
      RoLNy1(z) -= dty*l; /* y-coord runs down */
    }
    if (flags & TICKS_ACLOCKW) {
      RoLNx2(z) -= dtx*l;
      RoLNy2(z) += dty*l; /* y-coord runs down */
    }
    RoType(z) = ROt_LN;

    Rchain(e, z);
    RoCol(z) = current_color[ne];
    x += ddx;
    y += ddy;
  }
}

void
rectline(long ne, GEN gx2, GEN gy2)
{
  rectline0(ne, gtodouble(gx2), gtodouble(gy2),0);
}

void
rectrline(long ne, GEN gx2, GEN gy2)
{
  rectline0(ne, gtodouble(gx2), gtodouble(gy2),1);
}

void
rectbox0(long ne, double gx2, double gy2, long relative)
{
  double x1,y1,x2,y2,xmin,ymin,xmax,ymax;
  double xx,yy;
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj2P));

  x1 = RXcursor(e)*RXscale(e) + RXshift(e);
  y1 = RYcursor(e)*RYscale(e) + RYshift(e);
  if (relative)
  { xx = RXcursor(e)+gx2; yy = RYcursor(e)+gy2; }
  else
  {  xx = gx2; yy = gy2; }
  x2 = xx*RXscale(e) + RXshift(e);
  y2 = yy*RYscale(e) + RYshift(e);
  xmin = maxdd(mindd(x1,x2),0); xmax = mindd(maxdd(x1,x2),RXsize(e));
  ymin = maxdd(mindd(y1,y2),0); ymax = mindd(maxdd(y1,y2),RYsize(e));

  RoType(z) = ROt_BX;
  RoBXx1(z) = xmin; RoBXy1(z) = ymin;
  RoBXx2(z) = xmax; RoBXy2(z) = ymax;
  Rchain(e, z);
  RoCol(z) = current_color[ne];
}

void
rectbox(long ne, GEN gx2, GEN gy2)
{
  rectbox0(ne, gtodouble(gx2), gtodouble(gy2), 0);
}

void
rectrbox(long ne, GEN gx2, GEN gy2)
{
  rectbox0(ne, gtodouble(gx2), gtodouble(gy2), 1);
}

static void
freeobj(RectObj *z) {
  switch(RoType(z)) {
    case ROt_MP: case ROt_ML:
      pari_free(RoMPxs(z));
      pari_free(RoMPys(z)); break;
    case ROt_ST:
      pari_free(RoSTs(z)); break;
  }
  pari_free(z);
}


void
killrect(long ne)
{
  RectObj *z, *t;
  PariRect *e = check_rect_init(ne);

  current_color[ne]=DEFAULT_COLOR;
  z=RHead(e);
  RHead(e) = RTail(e) = NULL;
  RXsize(e) = RYsize(e) = 0;
  RXcursor(e) = RYcursor(e) = 0;
  RXscale(e) = RYscale(e) = 1;
  RXshift(e) = RYshift(e) = 0;
  while (z) { t = RoNext(z); freeobj(z); z = t; }
}

void
rectpoints0(long ne, double *listx, double *listy, long lx) /* code = ROt_MP */
{
  double *ptx, *pty, x, y;
  long i, cp=0;
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObjMP));

  RoMPxs(z) = ptx = (double*) pari_malloc(lx*sizeof(double));
  RoMPys(z) = pty = (double*) pari_malloc(lx*sizeof(double));
  for (i=0; i<lx; i++)
  {
    x = RXscale(e)*listx[i] + RXshift(e);
    y = RYscale(e)*listy[i] + RYshift(e);
    if (x>=0 && y>=0 && x<=RXsize(e) && y<=RYsize(e))
    {
      ptx[cp]=x; pty[cp]=y; cp++;
    }
  }
  RoType(z) = ROt_MP;
  RoMPcnt(z) = cp;
  Rchain(e, z);
  RoCol(z) = current_color[ne];
}

void
rectpoints(long ne, GEN listx, GEN listy)
{
  long i,lx, tx=typ(listx), ty=typ(listy);
  double *px,*py;

  if (!is_matvec_t(tx) || !is_matvec_t(ty)) {
    rectpoint(ne, listx, listy); return;
  }
  lx = lg(listx);
  if (tx == t_MAT) pari_err_TYPE("rectpoints",listx);
  if (ty == t_MAT) pari_err_TYPE("rectpoints",listy);
  if (lg(listy) != lx) pari_err_DIM("rectpoints");
  lx--; if (!lx) return;

  px = (double*) pari_malloc(lx*sizeof(double)); listx++;
  py = (double*) pari_malloc(lx*sizeof(double)); listy++;
  for (i=0; i<lx; i++)
  {
    px[i] = gtodouble(gel(listx,i));
    py[i] = gtodouble(gel(listy,i));
  }
  rectpoints0(ne,px,py,lx);
  pari_free(px); pari_free(py);
}

void
rectlines0(long ne, double *x, double *y, long lx, long flag) /* code = ROt_ML */
{
  long i,I;
  double *ptx,*pty;
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj2P));

  I = flag ? lx+1 : lx;
  ptx = (double*) pari_malloc(I*sizeof(double));
  pty = (double*) pari_malloc(I*sizeof(double));
  for (i=0; i<lx; i++)
  {
    ptx[i] = RXscale(e)*x[i] + RXshift(e);
    pty[i] = RYscale(e)*y[i] + RYshift(e);
  }
  if (flag)
  {
    ptx[i] = RXscale(e)*x[0] + RXshift(e);
    pty[i] = RYscale(e)*y[0] + RYshift(e);
  }
  Rchain(e, z);
  RoType(z) = ROt_ML;
  RoMLcnt(z) = lx;
  RoMLxs(z) = ptx;
  RoMLys(z) = pty;
  RoCol(z) = current_color[ne];
}

void
rectlines(long ne, GEN listx, GEN listy, long flag)
{
  long tx=typ(listx), ty=typ(listy), lx=lg(listx), i;
  double *x, *y;

  if (!is_matvec_t(tx) || !is_matvec_t(ty))
  {
    rectline(ne, listx, listy); return;
  }
  if (tx == t_MAT) pari_err_TYPE("rectlines",listx);
  if (ty == t_MAT) pari_err_TYPE("rectlines",listy);
  if (lg(listy) != lx) pari_err_DIM("rectlines");
  lx--; if (!lx) return;

  x = (double*) pari_malloc(lx*sizeof(double));
  y = (double*) pari_malloc(lx*sizeof(double));
  for (i=0; i<lx; i++)
  {
    x[i] = gtodouble(gel(listx,i+1));
    y[i] = gtodouble(gel(listy,i+1));
  }
  rectlines0(ne,x,y,lx,flag);
  pari_free(x); pari_free(y);
}

static void
put_label(long ne, long x, long y, double d, long dir)
{
  char c[16];
  sprintf(c,"%.5g", d);
  rectmove0(ne,(double)x,(double)y,0);
  rectstring3(ne, c, dir);
}

void
rectstring(long ne, char *str)
{
  rectstring3(ne,str,RoSTdirLEFT);
}

/* Allocate memory, then put string */
void
rectstring3(long ne, char *str, long dir) /* code = ROt_ST */
{
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObjST));
  long l = strlen(str);
  char *s = (char *) pari_malloc(l+1);

  memcpy(s,str,l+1);
  RoType(z) = ROt_ST;
  RoSTl(z) = l;
  RoSTs(z) = s;
  RoSTx(z) = RXscale(e)*RXcursor(e)+RXshift(e);
  RoSTy(z) = RYscale(e)*RYcursor(e)+RYshift(e);
  RoSTdir(z) = dir;
  Rchain(e, z);
  RoCol(z) = current_color[ne];
}

void
rectpointtype(long ne, long type) /* code = ROt_PTT */
{
 if (ne == -1) {
   rectpoint_itype = type;
 } else {
   PariRect *e = check_rect_init(ne);
   RectObj *z = (RectObj*) pari_malloc(sizeof(RectObjPN));

   RoType(z) = ROt_PTT;
   RoPTTpen(z) = type;
   Rchain(e, z);
 }
}

/*FIXME: this function is a noop, since no graphic driver implement
 * the ROt_PTS code. ne==-1 is a legacy, meaningless value. */
void
rectpointsize(long ne, GEN size) /* code = ROt_PTS */
{
 if (ne == -1) { /*do nothing*/ }
 else {
   PariRect *e = check_rect_init(ne);
   RectObj *z = (RectObj*) pari_malloc(sizeof(RectObjPS));

   RoType(z) = ROt_PTS;
   RoPTSsize(z) = gtodouble(size);
   Rchain(e, z);
 }
}

void
rectlinetype(long ne, long type)
{
 if (ne == -1) {
   rectline_itype = type;
 } else {
   PariRect *e = check_rect_init(ne);
   RectObj *z = (RectObj*) pari_malloc(sizeof(RectObjPN));

   RoType(z) = ROt_LNT;
   RoLNTpen(z) = type;
   Rchain(e, z);
 }
}

void
rectcopy_gen(long source, long dest, GEN xoff, GEN yoff, long flag)
{
  long xi, yi;
  if (flag & RECT_CP_RELATIVE) {
    double xd = gtodouble(xoff), yd = gtodouble(yoff);
    if (xd > 1) pari_err_DOMAIN("plotcopy","dx",">",gen_1,xoff);
    if (xd < 0) pari_err_DOMAIN("plotcopy","dx","<",gen_0,xoff);
    if (yd > 1) pari_err_DOMAIN("plotcopy","dy",">",gen_1,yoff);
    if (yd < 0) pari_err_DOMAIN("plotcopy","dy","<",gen_0,yoff);
    PARI_get_plot();
    xi = pari_plot.width - 1;
    yi = pari_plot.height - 1;
    xi = DTOL(xd*xi);
    yi = DTOL(yd*yi);
  } else {
    if (typ(xoff) != t_INT) pari_err_TYPE("plotcopy",xoff);
    if (typ(yoff) != t_INT) pari_err_TYPE("plotcopy",yoff);
    xi = itos(xoff);
    yi = itos(yoff);
  }
  if (flag & ~RECT_CP_RELATIVE) {
    PariRect *s = check_rect_init(source), *d = check_rect_init(dest);

    switch (flag & ~RECT_CP_RELATIVE) {
      case RECT_CP_NW:
        break;
      case RECT_CP_SW:
        yi = RYsize(d) - RYsize(s) - yi;
        break;
      case RECT_CP_SE:
        yi = RYsize(d) - RYsize(s) - yi;
        /* FALL THROUGH */
      case RECT_CP_NE:
        xi = RXsize(d) - RXsize(s) - xi;
        break;
    }
  }
  rectcopy(source, dest, xi, yi);
}

static void*
cp(void* R, size_t t)
{ void *o = pari_malloc(t); memcpy(o,R,t); return o; }

void
rectcopy(long source, long dest, long x, long y)
{
  PariRect *s = check_rect_init(source), *d = check_rect_init(dest);
  RectObj *R, *tail = RTail(d);
  long i;

  for (R = RHead(s); R; R = RoNext(R))
  {
    RectObj *o;
    switch(RoType(R))
    {
      case ROt_PT:
        o = (RectObj*)cp(R, sizeof(RectObj1P));
        RoPTx(o) += x; RoPTy(o) += y;
        break;
      case ROt_LN: case ROt_BX:
        o = (RectObj*)cp(R, sizeof(RectObj2P));
        RoLNx1(o) += x; RoLNy1(o) += y;
        RoLNx2(o) += x; RoLNy2(o) += y;
        break;
      case ROt_MP: case ROt_ML:
        o = (RectObj*)cp(R, sizeof(RectObjMP));
        RoMPxs(o) = (double*)cp(RoMPxs(R), sizeof(double)*RoMPcnt(o));
        RoMPys(o) = (double*)cp(RoMPys(R), sizeof(double)*RoMPcnt(o));
        for (i=0; i<RoMPcnt(o); i++) { RoMPxs(o)[i] += x; RoMPys(o)[i] += y; }
        break;
      case ROt_ST:
        o = (RectObj*)cp(R, sizeof(RectObjST));
        RoSTs(o) = (char*)cp(RoSTs(R),RoSTl(R)+1);
        RoSTx(o) += x; RoSTy(o) += y;
        break;
      default: /* ROt_PTT, ROt_LNT, ROt_PTS */
        o = (RectObj*)cp(R, sizeof(RectObjPN));
        break;
    }
    RoNext(tail) = o; tail = o;
  }
  RoNext(tail) = NULL; RTail(d) = tail;
}

enum {CLIPLINE_NONEMPTY = 1, CLIPLINE_CLIP_1 = 2, CLIPLINE_CLIP_2 = 4};
/* A simpler way is to clip by 4 half-planes */
static int
clipline(double xmin, double xmax, double ymin, double ymax,
         double *x1p, double *y1p, double *x2p, double *y2p)
{
  int xy_exch = 0, rc = CLIPLINE_NONEMPTY;
  double t, sl;
  double xi, xmn, xmx;
  double yi, ymn, ymx;
  int x1_is_ymn, x1_is_xmn;
  double x1 = *x1p, x2 = *x2p, y1 = *y1p, y2 = *y2p;

  if ((x1 < xmin &&  x2 < xmin) || (x1 > xmax && x2 > xmax))
    return 0;
  if (fabs(x1 - x2) < fabs(y1 - y2)) { /* Exchange x and y */
    xy_exch = 1;
    dswap(xmin, ymin); dswap(x1, y1);
    dswap(xmax, ymax); dswap(x2, y2);
  }

  /* Build y as a function of x */
  xi = x1;
  yi = y1;
  sl = x1==x2? 0: (y2 - yi)/(x2 - xi);

  if (x1 > x2) {
    x1_is_xmn = 0;
    xmn = x2;
    xmx = x1;
  } else {
    x1_is_xmn = 1;
    xmn = x1;
    xmx = x2;
  }

  if (xmn < xmin) {
    xmn = xmin;
    rc |= x1_is_xmn? CLIPLINE_CLIP_1: CLIPLINE_CLIP_2;
  }
  if (xmx > xmax) {
    xmx = xmax;
    rc |= x1_is_xmn? CLIPLINE_CLIP_2: CLIPLINE_CLIP_1;
  }
  if (xmn > xmx) return 0;

  ymn = yi + (xmn - xi)*sl;
  ymx = yi + (xmx - xi)*sl;

  if (sl < 0) t = ymn, ymn = ymx, ymx = t;
  if (ymn > ymax || ymx < ymin) return 0;

  if (rc & CLIPLINE_CLIP_1) x1 = x1_is_xmn? xmn: xmx;
  if (rc & CLIPLINE_CLIP_2) x2 = x1_is_xmn? xmx: xmn;

  /* Now we know there is an intersection, need to move x1 and x2 */
  x1_is_ymn = ((sl >= 0) == (x1 < x2));
  if (ymn < ymin) {
    double x = (ymin - yi)/sl + xi; /* slope != 0  ! */
    if (x1_is_ymn) x1 = x, rc |= CLIPLINE_CLIP_1;
    else           x2 = x, rc |= CLIPLINE_CLIP_2;
  }
  if (ymx > ymax) {
    double x = (ymax - yi)/sl + xi; /* slope != 0  ! */
    if (x1_is_ymn) x2 = x, rc |= CLIPLINE_CLIP_2;
    else           x1 = x, rc |= CLIPLINE_CLIP_1;
  }
  if (rc & CLIPLINE_CLIP_1) y1 = yi + (x1 - xi)*sl;
  if (rc & CLIPLINE_CLIP_2) y2 = yi + (x2 - xi)*sl;
  if (xy_exch) /* Exchange x and y */
    *x1p = y1, *x2p = y2, *y1p = x1, *y2p = x2;
  else
    *x1p = x1, *x2p = x2, *y1p = y1, *y2p = y2;
  return rc;
}

void
rectclip(long rect)
{
  PariRect *s = check_rect_init(rect);
  RectObj *next, *R = RHead(s), **prevp = &RHead(s);
  double xmin = 0, xmax = RXsize(s);
  double ymin = 0, ymax = RYsize(s);

  for (; R; R = next) {
    int did_clip = 0;
#define REMOVE() { *prevp = next; freeobj(R); break; }
#define NEXT() { prevp = &RoNext(R); break; }

    next = RoNext(R);
    switch(RoType(R)) {
      case ROt_PT:
        if ( DTOL(RoPTx(R)) < xmin || DTOL(RoPTx(R)) > xmax
          || DTOL(RoPTy(R)) < ymin || DTOL(RoPTy(R)) > ymax) REMOVE();
        NEXT();
      case ROt_BX:
        if (RoLNx1(R) < xmin) RoLNx1(R) = xmin, did_clip = 1;
        if (RoLNx2(R) < xmin) RoLNx2(R) = xmin, did_clip = 1;
        if (RoLNy1(R) < ymin) RoLNy1(R) = ymin, did_clip = 1;
        if (RoLNy2(R) < ymin) RoLNy2(R) = ymin, did_clip = 1;
        if (RoLNx1(R) > xmax) RoLNx1(R) = xmax, did_clip = 1;
        if (RoLNx2(R) > xmax) RoLNx2(R) = xmax, did_clip = 1;
        if (RoLNy1(R) > ymax) RoLNy1(R) = ymax, did_clip = 1;
        if (RoLNy2(R) > ymax) RoLNy2(R) = ymax, did_clip = 1;
        /* Remove zero-size clipped boxes */
        if (did_clip && RoLNx1(R) == RoLNx2(R)
                     && RoLNy1(R) == RoLNy2(R)) REMOVE();
        NEXT();
      case ROt_LN:
        if (!clipline(xmin, xmax, ymin, ymax,
                      &RoLNx1(R), &RoLNy1(R),
                      &RoLNx2(R), &RoLNy2(R))) REMOVE();
        NEXT();
      case ROt_MP: {
        int c = RoMPcnt(R), f = 0, t = 0;

        while (f < c) {
          if ( DTOL(RoMPxs(R)[f]) >= xmin && DTOL(RoMPxs(R)[f]) <= xmax
            && DTOL(RoMPys(R)[f]) >= ymin && DTOL(RoMPys(R)[f]) <= ymax) {
            if (t != f) {
              RoMPxs(R)[t] = RoMPxs(R)[f];
              RoMPys(R)[t] = RoMPys(R)[f];
            }
            t++;
          }
          f++;
        }
        if (t == 0) REMOVE();
        RoMPcnt(R) = t;
        NEXT();
      }
      case ROt_ML: {
        /* Hard case. Break a multiline into several pieces
         * if some part is clipped. */
        int c = RoMPcnt(R) - 1;
        int f = 0, t = 0, had_lines = 0, had_hole = 0, rc;
        double ox = RoMLxs(R)[0], oy = RoMLys(R)[0], oxn, oyn;

        while (f < c) {
        /* Endpoint of this segment is startpoint of next one: need to
         * preserve it if it is clipped. */
          oxn = RoMLxs(R)[f+1];
          oyn = RoMLys(R)[f+1];
          rc = clipline(xmin, xmax, ymin, ymax,
                  &ox, &oy, /* &RoMLxs(R)[f], &RoMLys(R)[f], */
                  &RoMLxs(R)[f+1], &RoMLys(R)[f+1]);
          RoMLxs(R)[f] = ox; ox = oxn;
          RoMLys(R)[f] = oy; oy = oyn;
          if (!rc) {
            if (had_lines) had_hole = 1;
            f++; continue;
          }

          if (!had_lines || (!(rc & CLIPLINE_CLIP_1) && !had_hole) ) {
            /* Continuous */
            had_lines = 1;
            if (t != f) {
              if (t == 0) {
                RoMPxs(R)[t] = RoMPxs(R)[f];
                RoMPys(R)[t] = RoMPys(R)[f];
              }
              RoMPxs(R)[t+1] = RoMPxs(R)[f+1];
              RoMPys(R)[t+1] = RoMPys(R)[f+1];
            }
            t++;
            f++;
            if (rc & CLIPLINE_CLIP_2) had_hole = 1, RoMLcnt(R) = t+1;
            continue;
          }
          /* Is not continuous, automatically R is not pari_free()ed.  */
          t++;
          RoMLcnt(R) = t;
          if (rc & CLIPLINE_CLIP_2) { /* Needs separate entry */
            RectObj *n = (RectObj*) pari_malloc(sizeof(RectObj2P));

            RoType(n) = ROt_LN;
            RoCol(n) = RoCol(R);
            RoLNx1(n) = RoMLxs(R)[f];        RoLNy1(n) = RoMLys(R)[f];
            RoLNx2(n) = RoMLxs(R)[f+1];        RoLNy2(n) = RoMLys(R)[f+1];
            RoNext(n) = next;
            RoNext(R) = n;
            /* Restore the unclipped value: */
            RoMLxs(R)[f+1] = oxn;        RoMLys(R)[f+1] = oyn;
            f++;
            prevp = &RoNext(n);
          }
          if (f + 1 < c) {                /* Are other lines */
            RectObj *n = (RectObj*) pari_malloc(sizeof(RectObjMP));
            RoType(n) = ROt_ML;
            RoCol(n) = RoCol(R);
            RoMLcnt(n) = c - f;
            RoMLxs(n) = (double*) pari_malloc(sizeof(double)*(c - f));
            RoMLys(n) = (double*) pari_malloc(sizeof(double)*(c - f));
            memcpy(RoMPxs(n),RoMPxs(R) + f, sizeof(double)*(c - f));
            memcpy(RoMPys(n),RoMPys(R) + f, sizeof(double)*(c - f));
            RoMPxs(n)[0] = oxn;
            RoMPys(n)[0] = oyn;
            RoNext(n) = next;
            RoNext(R) = n;
            next = n;
          }
          break;
        }
        if (t == 0) REMOVE();
        NEXT();
      }
    }
#undef REMOVE
#undef NEXT
  }
}

/********************************************************************/
/**                                                                **/
/**                        HI-RES PLOT                             **/
/**                                                                **/
/********************************************************************/
void
Printx(dblPointList *f)
{
  long i;
  printf("x: [%0.5g,%0.5g], y: [%0.5g,%0.5g]\n",
         f->xsml, f->xbig, f->ysml, f->ybig);
  for (i = 0; i < f->nb; i++) printf("%0.5g ", f->d[i]);
  printf("\n");
}

static void
Appendx(dblPointList *f, dblPointList *l,double x)
{
  (l->d)[l->nb++]=x;
  if (x < f->xsml) f->xsml = x;
  if (x > f->xbig) f->xbig = x;
}

static void
Appendy(dblPointList *f, dblPointList *l,double y)
{
  (l->d)[l->nb++]=y;
  if (y < f->ysml) f->ysml = y;
  if (y > f->ybig) f->ybig = y;
}

static void
get_xy(long cplx, GEN t, double *x, double *y)
{
  if (cplx)
  {
    if (typ(t) == t_VEC)
    {
      if (lg(t) != 2) pari_err_DIM("get_xy");
      t = gel(t,1);
    }
    *x = gtodouble( real_i(t) );
    *y = gtodouble( imag_i(t) );
  }
  else
  {
    if (typ(t) != t_VEC || lg(t) != 3) pari_err_DIM("get_xy");
    *x = gtodouble( gel(t,1) );
    *y = gtodouble( gel(t,2) );
  }
}
/* t a t_VEC (possibly a scalar if cplx), get next (x,y) coordinate starting
 * at index *i [update i] */
static void
get_xy_from_vec(long cplx, GEN t, long *i, double *x, double *y)
{
  if (cplx)
  {
    GEN z;
    if (typ(t) == t_VEC) z = gel(t,(*i)++); else { z = t; (*i)++; }
    *x = gtodouble( real_i(z) );
    *y = gtodouble( imag_i(z) );
  }
  else
  {
    *x = gtodouble( gel(t, (*i)++) );
    *y = gtodouble( gel(t, (*i)++) );
  }
}
/* X,Y t_VEC, get next (x,y) coordinate starting at index i
 * Y ignored if (cplx) */
static void
get_xy_from_vec2(long cplx, GEN X, GEN Y, long i, double *x, double *y)
{
  if (cplx)
  {
    GEN z = gel(X,i);
    *x = gtodouble( real_i(z) );
    *y = gtodouble( imag_i(z) );
  }
  else
  {
    *x = gtodouble( gel(X, i) );
    *y = gtodouble( gel(Y, i) );
  }
}

/* Convert data from GEN to double before we call rectplothrawin. */
static dblPointList*
gtodblList(GEN data, long flags)
{
  dblPointList *l;
  double xsml, xbig, ysml, ybig;
  long nl=lg(data)-1, lx1, i, j;
  const long param = (flags & (PLOT_PARAMETRIC|PLOT_COMPLEX));
  const long cplx = (flags & PLOT_COMPLEX);

  if (! is_vec_t(typ(data))) pari_err_TYPE("gtodblList",data);
  if (!nl) return NULL;
  lx1 = lg(gel(data,1));
  if (!param && lx1 == 1) return NULL;

  if (nl == 1 && !cplx) pari_err_DIM("gtodblList");
  /* Allocate memory, then convert coord. to double */
  l = (dblPointList*)pari_malloc((cplx? 2*nl: nl)*sizeof(dblPointList));
  for (i=0; i<nl; i += (cplx? 1: 2))
  {
    dblPointList *LX = l + i, *LY = l + (i+1);
    GEN x = gel(data,i+1), y;
    long lx = lg(x);
    if (!is_vec_t(typ(x))) pari_err_TYPE("gtodblList",x);
    if (cplx) y = NULL;
    else
    {
      y = gel(data,i+2);
      if (!is_vec_t(typ(y))) pari_err_TYPE("gtodblList",y);
      if (lg(y) != lx || (!param && lx != lx1)) pari_err_DIM("gtodblList");
    }

    lx--;
    LX->d = (double*)pari_malloc(lx*sizeof(double));
    LY->d = (double*)pari_malloc(lx*sizeof(double));
    for (j=1; j<=lx; j++)
    {
      double xx, yy;
      get_xy_from_vec2(cplx, x,y, j, &xx,&yy);
      LX->d[j-1] = xx;
      LY->d[j-1] = yy;
    }
    LX->nb = LY->nb = lx;
  }

  /* Now compute extremas */
  if (param)
  {
    l[0].nb = cplx? nl: nl/2;
    for (i=0; i < l[0].nb; i+=2)
      if (l[i+1].nb) break;
    if (i >= l[0].nb) { pari_free(l); return NULL; }
    xsml = xbig = l[i  ].d[0];
    ysml = ybig = l[i+1].d[0];
    for (; i < l[0].nb; i+=2)
    {
      dblPointList *LX = l + i, *LY = l + (i+1);
      for (j=0; j < LY->nb; j++)
      {
        double x = LX->d[j], y = LY->d[j];
        if (x < xsml) xsml = x; else if (x > xbig) xbig = x;
        if (y < ysml) ysml = y; else if (y > ybig) ybig = y;
      }
    }
  }
  else
  {
    l[0].nb = nl-1;
    xsml = xbig = l[0].d[0];
    ysml = ybig = l[1].d[0];
    for (j=0; j < l[1].nb; j++)
    {
      double x = l[0].d[j];
      if (x < xsml) xsml = x; else if (x > xbig) xbig = x;
    }
    for (i=1; i <= l[0].nb; i++)
      for (j=0; j < l[i].nb; j++)
      {
        double y = l[i].d[j];
        if (y < ysml) ysml = y; else if (y > ybig) ybig = y;
      }
  }
  l[0].xsml = xsml; l[0].xbig = xbig;
  l[0].ysml = ysml; l[0].ybig = ybig; return l;
}

/* (x+y)/2 */
static GEN
rmiddle(GEN x, GEN y) { GEN z = addrr(x,y); shiftr_inplace(z,-1); return z; }

static void
single_recursion(dblPointList *pl,GEN code,GEN xleft,double yleft,
  GEN xright,double yright,long depth)
{
  GEN xx;
  pari_sp av = avma;
  double yy, dy=pl[0].ybig - pl[0].ysml;

  if (depth==RECUR_MAXDEPTH) return;

  xx = rmiddle(xleft,xright);
  yy = gtodouble(READ_EXPR(code,xx));

  if (dy && fabs(yleft+yright-2*yy)< dy*RECUR_PREC) return;
  single_recursion(pl,code, xleft,yleft, xx,yy, depth+1);

  Appendx(&pl[0],&pl[0],rtodbl(xx));
  Appendy(&pl[0],&pl[1],yy);

  single_recursion(pl,code, xx,yy, xright,yright, depth+1);
  avma = av;
}

static void
param_recursion(long cplx, dblPointList *pl,GEN code,GEN tleft,double xleft,
  double yleft, GEN tright,double xright,double yright, long depth)
{
  GEN tt, p1;
  pari_sp av=avma;
  double xx, dy=pl[0].ybig - pl[0].ysml;
  double yy, dx=pl[0].xbig - pl[0].xsml;

  if (depth==RECUR_MAXDEPTH) return;

  tt = rmiddle(tleft,tright);
  p1 = READ_EXPR(code,tt);
  get_xy(cplx, p1, &xx,&yy);

  if (dx && dy && fabs(xleft+xright-2*xx) < dx*RECUR_PREC
               && fabs(yleft+yright-2*yy) < dy*RECUR_PREC) return;
  param_recursion(cplx, pl,code, tleft,xleft,yleft, tt,xx,yy, depth+1);

  Appendx(&pl[0],&pl[0],xx);
  Appendy(&pl[0],&pl[1],yy);

  param_recursion(cplx, pl,code, tt,xx,yy, tright,xright,yright, depth+1);
  avma = av;
}

/* Graph 'code' for parameter values in [a,b], using 'testpoints' sample
 * points (0 = use a default value); code is either a t_CLOSURE (from GP:
 * ploth, etc.) or a t_POL/t_VEC of two t_POLs from rectsplines. Returns a
 * dblPointList of (absolute) coordinates. */
static dblPointList *
rectplothin(GEN a, GEN b, GEN code, long prec, ulong flags, long testpoints)
{
  const double INF = 1./0.;
  const long param = flags & (PLOT_PARAMETRIC|PLOT_COMPLEX);
  const long recur = flags & PLOT_RECURSIVE;
  const long cplx = flags & PLOT_COMPLEX;
  GEN t,dx,x;
  dblPointList *pl;
  long tx, i, j, sig, nc, nl, ncoords, nbpoints, non_vec = 0;
  pari_sp av = avma;

  sig = gcmp(b,a); if (!sig) return NULL;
  if (sig < 0) swap(a, b);
  if (testpoints)
  {
    if (testpoints < 2)
      pari_err_DOMAIN("ploth", "#points", "<", gen_2, stoi(testpoints));
  }
  else
  {
    if (recur) testpoints = 8;
    else       testpoints = param? 1500: 1000;
  }
  /* compute F(a) to determine nc = #curves; nl = #coord. lists */
  x = gtofp(a, prec);
  if (typ(code) == t_CLOSURE) push_lex(x, code);
  t = READ_EXPR(code,x); tx = typ(t);
  if (param)
  {
    if (cplx) nc = nl = (tx == t_VEC)? lg(t)-1: 1;
    else
    {
      if (tx != t_VEC)
        pari_err_TYPE("ploth [not a t_VEC with PLOT_PARAMETRIC]", t);
      nl = lg(t)-1;
      nc = nl/2;
      if (odd(nl))
        pari_err_TYPE("ploth [parametric ploc with odd # of components]",t);
    }
  }
  else
  {
    if (!is_matvec_t(tx)) { nl = 2; non_vec = 1; }
    else
    {
      if (tx != t_VEC) pari_err_TYPE("ploth [not a t_VEC]",t);
      nl = lg(t);
    }
    nc = nl-1;
  }
  if (!nc) { avma = av; return NULL; }
  if (recur && nc > 1)
    pari_err_TYPE("ploth [multi-curves cannot be plot recursively]",t);

  ncoords = cplx? 2*nl: nl;
  nbpoints = recur? testpoints << RECUR_MAXDEPTH: testpoints;
  pl=(dblPointList*) pari_malloc(ncoords*sizeof(dblPointList));
  /* set [xy]sml,[xy]big to default values */
  if (param)
  {
    pl[0].xsml = INF;
    pl[0].xbig =-INF;
  } else {
    pl[0].xsml = gtodouble(a);
    pl[0].xbig = gtodouble(b);
  }
  pl[0].ysml = INF;
  pl[0].ybig =-INF;
  for (i = 0; i < ncoords; i++)
  {
    pl[i].d = (double*)pari_malloc((nbpoints+1)*sizeof(double));
    pl[i].nb=0;
  }
  dx = divru(gtofp(gsub(b,a),prec), testpoints-1);
  if (recur) /* recursive plot */
  {
    double yleft, yright = 0;
    if (param)
    {
      GEN tleft = cgetr(prec), tright = cgetr(prec);
      double xleft, xright = 0;
      pari_sp av2 = avma;
      affgr(a,tleft);
      t = READ_EXPR(code,tleft);
      get_xy(cplx,t, &xleft,&yleft);
      for (i=0; i<testpoints-1; i++, avma = av2)
      {
        if (i) { affrr(tright,tleft); xleft = xright; yleft = yright; }
        addrrz(tleft,dx,tright);
        t = READ_EXPR(code,tright);
        get_xy(cplx,t, &xright,&yright);
        Appendx(&pl[0],&pl[0],xleft);
        Appendy(&pl[0],&pl[1],yleft);
        param_recursion(cplx, pl,code, tleft,xleft,yleft, tright,xright,yright, 0);
      }
      Appendx(&pl[0],&pl[0],xright);
      Appendy(&pl[0],&pl[1],yright);
    }
    else /* single curve */
    {
      GEN xleft = cgetr(prec), xright = cgetr(prec);
      pari_sp av2 = avma;
      affgr(a,xleft);
      yleft = gtodouble(READ_EXPR(code,xleft));
      for (i=0; i<testpoints-1; i++, avma = av2)
      {
        addrrz(xleft,dx,xright);
        yright = gtodouble(READ_EXPR(code,xright));

        Appendx(&pl[0],&pl[0],rtodbl(xleft));
        Appendy(&pl[0],&pl[1],yleft);

        single_recursion(pl,code,xleft,yleft,xright,yright,0);
        affrr(xright,xleft); yleft = yright;
      }
      Appendx(&pl[0],&pl[0],rtodbl(xright));
      Appendy(&pl[0],&pl[1],yright);
    }
  }
  else /* non-recursive plot */
  {
    pari_sp av2 = avma;
    if (param)
    {
      for (i=0; i<testpoints; i++, affrr(addrr(x,dx), x), avma = av2)
      {
        long k, nt;
        t = READ_EXPR(code,x);
        if (typ(t) != t_VEC)
        {
          if (cplx) nt = 1;
          else nt = 0; /* trigger error */
        }
        else
          nt = lg(t)-1;
        if (nt != nl) pari_err_DIM("rectploth");
        k = 0; j = 1;
        while (j <= nl)
        {
          double xx, yy;
          get_xy_from_vec(cplx, t, &j, &xx, &yy);
          Appendx(&pl[0], &pl[k++], xx);
          Appendy(&pl[0], &pl[k++], yy);
        }
      }
    }
    else if (non_vec)
      for (i=0; i<testpoints; i++, affrr(addrr(x,dx), x), avma = av2)
      {
        t = READ_EXPR(code,x);
        pl[0].d[i] = gtodouble(x);
        Appendy(&pl[0],&pl[1], gtodouble(t));
      }
    else /* vector of non-parametric curves */
      for (i=0; i<testpoints; i++, affrr(addrr(x,dx), x), avma = av2)
      {
        t = READ_EXPR(code,x);
        if (typ(t) != t_VEC || lg(t) != nl) pari_err_DIM("rectploth");
        pl[0].d[i] = gtodouble(x);
        for (j=1; j<nl; j++) Appendy(&pl[0],&pl[j], gtodouble(gel(t,j)));
      }
  }
  if (typ(code) == t_CLOSURE) pop_lex(1);
  pl[0].nb = nc; avma = av; return pl;
}

/* Uses highlevel plotting functions to implement splines as
   a low-level plotting function. */
static void
rectsplines(long ne, double *x, double *y, long lx, long flag)
{
  long i, j;
  pari_sp av0 = avma;
  GEN X = pol_x(0), xa = cgetg(lx+1, t_VEC), ya = cgetg(lx+1, t_VEC);
  GEN tas, pol3;
  long param = flag & PLOT_PARAMETRIC;

  if (lx < 4) pari_err(e_MISC, "Too few points (%ld) for spline plot", lx);
  for (i = 1; i <= lx; i++) {
    gel(xa,i) = dbltor(x[i-1]);
    gel(ya,i) = dbltor(y[i-1]);
  }
  if (param) {
    tas = new_chunk(4);
    for (j = 1; j <= 4; j++) gel(tas,j-1) = utoipos(j);
    pol3 = cgetg(3, t_VEC);
  }
  else
    tas = pol3 = NULL; /* gcc -Wall */
  for (i = 0; i <= lx - 4; i++) {
    pari_sp av = avma;

    xa++; ya++;
    if (param) {
      gel(pol3,1) = polint_i(tas, xa, X, 4, NULL);
      gel(pol3,2) = polint_i(tas, ya, X, 4, NULL);
    } else {
      pol3 = polint_i(xa, ya, X, 4, NULL);
      tas = xa;
    }
    /* Start with 3 points */
    rectploth(ne, i==   0 ? gel(tas,0) : gel(tas,1),
                  i==lx-4 ? gel(tas,3) : gel(tas,2), pol3,
                  DEFAULTPREC, PLOT_RECURSIVE | PLOT_NO_RESCALE
                  | PLOT_NO_FRAME | PLOT_NO_AXE_Y | PLOT_NO_AXE_X | param, 2);
    avma = av;
  }
  avma = av0;
}

static void
set_range(double m, double M, double *sml, double *big)
{
  if (M - m < 1.e-9)
  {
    double d = fabs(m)/10; if (!d) d = 0.1;
    M += d; m -= d;
  }
  *sml = m; *big = M;
}
/* Plot a dblPointList. Complete with axes, bounding box, etc.
 *
 * data is an array of structs. Its meaning depends on flags :
 *
 * + data[0] contains global extremas, the number of curves to plot
 *   (data[0].nb) and a list of doubles (first set of x-coordinates).
 *
 * + data[i].nb (i>0) contains the number of points in the list
 *   data[i].d (hopefully, data[2i].nb=data[2i+1].nb when i>0...)
 *
 * + If flags contain PLOT_PARAMETRIC, the array length should be
 *   even, and successive pairs (data[2i].d, data[2i+1].d) represent
 *   curves to plot.
 *
 * + If there is no such flag, the first element is an array with
 *   x-coordinates and the following ones contain y-coordinates.
 * If grect >= 0, output to this rectwindow. Otherwise draw immediately to
 * screen (grect=-1) or to screen (grect=-2), using two drawing rectangles:
 * one for labels, another for graphs.*/
static GEN
rectplothrawin(long grect, dblPointList *data, long flags)
{
  const long param = flags & (PLOT_PARAMETRIC|PLOT_COMPLEX);
  const pari_sp av = avma;
  PARI_plot *W;
  dblPointList y,x;
  double xsml, xbig, ysml, ybig;
  long ltype, max_graphcolors;
  long i,nc,nbpoints, w[2], wx[2], wy[2];

  if (!data) return cgetg(1,t_VEC);
  x = data[0]; nc = x.nb;
  set_range(x.xsml, x.xbig, &xsml, &xbig);
  set_range(x.ysml, x.ybig, &ysml, &ybig);
  if (grect >= 0) /* output to rectwindow, no labels */
    W = NULL;
  else
  {
    const long srect = NUMRECT-2;
    long lm, rm, tm, bm;

    if (grect == -1) /* output to screen */
    { W = &pari_plot; PARI_get_plot(); }
    else /* output to file */
    { W = &pari_psplot; PARI_get_psplot(); }
    grect = NUMRECT-1;
    /* left/right/top/bottom margin */
    lm = W->fwidth*10;
    rm = W->hunit-1;
    tm = W->vunit-1;
    bm = W->vunit+W->fheight-1;
    w[0] = srect; wx[0] = 0;  wy[0] = 0;
    w[1] = grect;   wx[1] = lm; wy[1] = tm;
   /* Window (width x height) is given in pixels, correct pixels are 0..n-1,
    * whereas rect functions work with windows whose pixel range is [0,n] */
    initrect(srect, W->width - 1, W->height - 1);
    rectlinetype(srect,-2); /* Frame */
    current_color[srect] = DEFAULT_COLOR;
    initrect(grect, W->width - (lm+rm) - 1, W->height - (tm+bm) - 1);
    /* draw labels on srect */
    put_label(srect, lm, 0, ybig, RoSTdirRIGHT|RoSTdirHGAP|RoSTdirTOP);
    put_label(srect, lm, W->height-bm, ysml, RoSTdirRIGHT|RoSTdirHGAP|RoSTdirVGAP);
    put_label(srect, lm, W->height - bm, xsml, RoSTdirLEFT|RoSTdirTOP);
    put_label(srect, W->width-rm-1, W->height-bm, xbig, RoSTdirRIGHT|RoSTdirTOP);
  }
  RHasGraph(check_rect(grect)) = 1;

  if (!(flags & PLOT_NO_RESCALE))
    rectscale0(grect, xsml, xbig, ysml, ybig);

  if (!(flags & PLOT_NO_FRAME))
  {
    int do_double = (flags & PLOT_NODOUBLETICK) ? TICKS_NODOUBLE : 0;
    PARI_plot *pl = W;
    if (!pl) { PARI_get_plot(); pl = &pari_plot; }

    rectlinetype(grect, -2); /* Frame. */
    current_color[grect] = DEFAULT_COLOR;
    rectmove0(grect,xsml,ysml,0);
    rectbox0(grect,xbig,ybig,0);
    if (!(flags & PLOT_NO_TICK_X)) {
      rectticks(pl, grect, xsml, ysml, xbig, ysml, xsml, xbig,
        TICKS_CLOCKW | do_double);
      rectticks(pl, grect, xbig, ybig, xsml, ybig, xbig, xsml,
        TICKS_CLOCKW | do_double);
    }
    if (!(flags & PLOT_NO_TICK_Y)) {
      rectticks(pl, grect, xbig, ysml, xbig, ybig, ysml, ybig,
        TICKS_CLOCKW | do_double);
      rectticks(pl, grect, xsml, ybig, xsml, ysml, ybig, ysml,
        TICKS_CLOCKW | do_double);
    }
  }

  if (!(flags & PLOT_NO_AXE_Y) && (xsml<=0 && xbig >=0))
  {
    rectlinetype(grect, -1); /* Axes. */
    current_color[grect] = AXIS_COLOR;
    rectmove0(grect,0.0,ysml,0);
    rectline0(grect,0.0,ybig,0);
  }

  if (!(flags & PLOT_NO_AXE_X) && (ysml<=0 && ybig >=0))
  {
    rectlinetype(grect, -1); /* Axes. */
    current_color[grect] = AXIS_COLOR;
    rectmove0(grect,xsml,0.0,0);
    rectline0(grect,xbig,0.0,0);
  }

  if (param) {
    i = 0;
    flags |= PLOT_PARAMETRIC;
    flags &= (~PLOT_COMPLEX); /* turn COMPLEX to PARAMETRIC*/
  } else i = 1;
  max_graphcolors = lg(GP_DATA->graphcolors)-1;
  for (ltype = 0; ltype < nc; ltype++)
  {
    current_color[grect] = GP_DATA->graphcolors[1+(ltype%max_graphcolors)];
    if (param) x = data[i++];

    y = data[i++]; nbpoints = y.nb;
    if (flags & (PLOT_POINTS_LINES|PLOT_POINTS)) {
      rectlinetype(grect, rectpoint_itype + ltype); /* Graphs */
      rectpointtype(grect,rectpoint_itype + ltype); /* Graphs */
      rectpoints0(grect,x.d,y.d,nbpoints);
      if (!(flags & PLOT_POINTS_LINES)) continue;
    }

    if (flags & PLOT_SPLINES) {
      /* rectsplines will call us back with ltype == 0 */
      int old = rectline_itype;

      rectline_itype = rectline_itype + ltype;
      rectsplines(grect,x.d,y.d,nbpoints,flags);
      rectline_itype = old;
    } else {
      rectlinetype(grect, rectline_itype + ltype); /* Graphs */
      rectlines0(grect,x.d,y.d,nbpoints,0);
    }
  }
  for (i--; i>=0; i--) pari_free(data[i].d);
  pari_free(data);

  if (W)
  {
    if (W == &pari_plot)
      rectdraw0(w,wx,wy,2);
    else
      postdraw0(w,wx,wy,2, 0);
    killrect(w[1]);
    killrect(w[0]);
  }
  avma = av;
  retmkvec4(dbltor(xsml), dbltor(xbig), dbltor(ysml), dbltor(ybig));
}

/*************************************************************************/
/*                                                                       */
/*                          HI-RES FUNCTIONS                             */
/*                                                                       */
/*************************************************************************/

GEN
rectploth(long ne, GEN a,GEN b,GEN code, long prec,ulong flags,long tpts)
{
  dblPointList *pl = rectplothin(a,b, code, prec, flags, tpts);
  return rectplothrawin(ne, pl, flags);
}

GEN
rectplothraw(long ne, GEN data, long flags)
{
  dblPointList *pl = gtodblList(data,flags);
  return rectplothrawin(ne, pl, flags);
}

static long
plothraw_flags(long fl)
{
  switch(fl)
  {
    case 0: return PLOT_PARAMETRIC|PLOT_POINTS;
    case 1: return PLOT_PARAMETRIC;
    default:return PLOT_PARAMETRIC|fl;
  }
}
static GEN
plothraw0(long ne, GEN listx, GEN listy, long flags)
{
  pari_sp av = avma;
  GEN z = rectplothraw(ne, mkvec2(listx,listy), plothraw_flags(flags));
  return gerepileupto(av, z);
}

GEN
plothraw(GEN listx, GEN listy, long flags)
{ return plothraw0(-1, listx, listy, flags); }

GEN
ploth(GEN a, GEN b, GEN code, long prec,long flags,long numpoints)
{ return rectploth(-1, a,b,code,prec,flags,numpoints); }
GEN
ploth2(GEN a, GEN b, GEN code, long prec)
{ return rectploth(-1, a,b,code,prec,PLOT_PARAMETRIC,0); }
GEN
plothmult(GEN a, GEN b, GEN code, long prec)
{ return rectploth(-1, a,b,code,prec,0,0); }

GEN
postplothraw(GEN listx, GEN listy, long flags)
{ return plothraw0(-2, listx, listy, flags); }
GEN
postploth(GEN a, GEN b, GEN code, long prec,long flags, long numpoints)
{ return rectploth(-2, a,b,code,prec, flags,numpoints); }
GEN
postploth2(GEN a, GEN b, GEN code, long prec, long numpoints)
{ return rectploth(-2, a,b,code,prec, PLOT_PARAMETRIC,numpoints); }

GEN
plothsizes(void) { return plothsizes_flag(0); }
GEN
plothsizes_flag(long flag)
{
  GEN vect = cgetg(1+6,t_VEC);

  PARI_get_plot();
  gel(vect,1) = stoi(pari_plot.width);
  gel(vect,2) = stoi(pari_plot.height);
  if (flag) {
    gel(vect,3) = dbltor(pari_plot.hunit*1.0/pari_plot.width);
    gel(vect,4) = dbltor(pari_plot.vunit*1.0/pari_plot.height);
    gel(vect,5) = dbltor(pari_plot.fwidth*1.0/pari_plot.width);
    gel(vect,6) = dbltor(pari_plot.fheight*1.0/pari_plot.height);
  } else {
    gel(vect,3) = stoi(pari_plot.hunit);
    gel(vect,4) = stoi(pari_plot.vunit);
    gel(vect,5) = stoi(pari_plot.fwidth);
    gel(vect,6) = stoi(pari_plot.fheight);
  }
  return vect;
}

void
plot_count(long *w, long lw, col_counter rcolcnt)
{
  RectObj *O;
  long col, i;

  for (col = 1; col < lg(GP_DATA->colormap)-1; col++)
    for (i = 0; i < ROt_MAX; i++) rcolcnt[col][i] = 0;
  for (i = 0; i < lw; i++)
  {
    PariRect *e = rectgraph[w[i]];
    for (O = RHead(e); O; O=RoNext(O))
      switch(RoType(O))
      {
        case ROt_MP : rcolcnt[RoCol(O)][ROt_PT] += RoMPcnt(O);
                      break;                 /* Multiple Point */
        case ROt_PT :                        /* Point */
        case ROt_LN :                        /* Line */
        case ROt_BX :                        /* Box */
        case ROt_ML :                        /* Multiple lines */
        case ROt_ST : rcolcnt[RoCol(O)][RoType(O)]++;
                      break;                 /* String */
      }
  }
}
/*************************************************************************/
/*                                                                       */
/*                         POSTSCRIPT OUTPUT                             */
/*                                                                       */
/*************************************************************************/

static void
PARI_get_psplot(void)
{
  if (pari_psplot.init) return;
  pari_psplot.init = 1;

  pari_psplot.width = 1120 - 60; /* 1400 - 60 for hi-res */
  pari_psplot.height=  800 - 40; /* 1120 - 60 for hi-res */
  pari_psplot.fheight= 15;
  pari_psplot.fwidth = 6;
  pari_psplot.hunit = 5;
  pari_psplot.vunit = 5;
}

static void
gendraw(GEN list, long ps, long flag)
{
  long i,n,ne,*w,*x,*y;

  if (typ(list) != t_VEC) pari_err_TYPE("rectdraw",list);
  n = lg(list)-1; if (!n) return;
  if (n%3) pari_err_DIM("rectdraw");
  n = n/3;
  w = (long*)pari_malloc(n*sizeof(long));
  x = (long*)pari_malloc(n*sizeof(long));
  y = (long*)pari_malloc(n*sizeof(long));
  if (flag) PARI_get_plot();
  for (i=0; i<n; i++)
  {
    GEN win = gel(list,3*i+1), x0 = gel(list,3*i+2), y0 = gel(list,3*i+3);
    long xi, yi;
    if (typ(win)!=t_INT) pari_err_TYPE("rectdraw",win);
    if (flag) {
      xi = DTOL(gtodouble(x0)*(pari_plot.width - 1));
      yi = DTOL(gtodouble(y0)*(pari_plot.height - 1));
    } else {
      xi = gtos(x0);
      yi = gtos(y0);
    }
    x[i] = xi;
    y[i] = yi;
    ne = itos(win); check_rect(ne);
    w[i] = ne;
  }
  if (ps) postdraw0(w,x,y,n,flag); else rectdraw0(w,x,y,n);
  pari_free(x); pari_free(y); pari_free(w);
}

void
postdraw(GEN list) { gendraw(list, 1, 0); }

void
rectdraw(GEN list) { gendraw(list, 0, 0); }

void
postdraw_flag(GEN list, long flag) { gendraw(list, 1, flag); }

void
rectdraw_flag(GEN list, long flag) { gendraw(list, 0, flag); }

static void
ps_sc(void *data, long col)
{
  long l = lg(GP_DATA->colormap)-1;
  int r, g, b;
  if (col >= l)
  {
    pari_warn(warner,"non-existent color: %ld", col);
    col = l-1;
  }
  color_to_rgb(gel(GP_DATA->colormap,col+1), &r, &g, &b);
  fprintf((FILE*)data,"%f %f %f setrgbcolor\n", r/255., g/255., b/255.);
}

static void
ps_point(void *data, long x, long y)
{
  fprintf((FILE*)data,"%ld %ld p\n",y,x);
}

static void
ps_line(void *data, long x1, long y1, long x2, long y2)
{
  fprintf((FILE*)data,"%ld %ld m %ld %ld l\n",y1,x1,y2,x2);
  fprintf((FILE*)data,"stroke\n");
}

static void
ps_rect(void *data, long x, long y, long w, long h)
{
  fprintf((FILE*)data,"%ld %ld m %ld %ld l %ld %ld l %ld %ld l closepath\n",y,x, y,x+w, y+h,x+w, y+h,x);
}

static void
ps_points(void *data, long nb, struct plot_points *p)
{
  long i;
  for (i=0; i<nb; i++) ps_point(data, p[i].x, p[i].y);
}

static void
ps_lines(void *data, long nb, struct plot_points *p)
{
  FILE *psfile = (FILE*)data;
  long i;
  fprintf(psfile,"%ld %ld m\n",p[0].y,p[0].x);
  for (i=1; i<nb; i++) fprintf(psfile, "%ld %ld l\n", p[i].y, p[i].x);
  fprintf(psfile,"stroke\n");
}

static void
ps_string(void *data, long x, long y, char *s, long length)
{
  FILE *psfile = (FILE*)data;
  (void)length;
  if (strpbrk(s, "(\\)")) {
    fprintf(psfile,"(");
    while (*s) {
      if ( *s=='(' || *s==')' || *s=='\\' ) fputc('\\', psfile);
      fputc(*s, psfile);
      s++;
    }
  } else
    fprintf(psfile,"(%s", s);
  fprintf(psfile,") %ld %ld m 90 rotate show -90 rotate\n", y, x);
}

void
psplot_init(struct plot_eng *S, FILE *f, double xscale, double yscale, long fontsize)
{
  PARI_get_psplot();
  /* Definitions taken from post terminal of Gnuplot. */
  fprintf(f, "%%!\n\
50 50 translate\n\
/p {moveto 0 2 rlineto 2 0 rlineto 0 -2 rlineto closepath fill} def\n\
/l {lineto} def\n\
/m {moveto} def\n"
"/Times-Roman findfont %ld scalefont setfont\n"
"%g %g scale\n", fontsize, yscale, xscale);

  S->sc = &ps_sc;
  S->pt = &ps_point;
  S->ln = &ps_line;
  S->bx = &ps_rect;
  S->mp = &ps_points;
  S->ml = &ps_lines;
  S->st = &ps_string;
  S->pl = &pari_psplot;
  S->data = (void*)f;
}

void
postdraw0(long *w, long *x, long *y, long lw, long scale)
{
  struct plot_eng plot;
  FILE *psfile;
  double xscale = 0.65, yscale = 0.65;
  long fontsize = 16;

  psfile = fopen(current_psfile, "a");
  if (!psfile) pari_err_FILE("postscript file",current_psfile);
  if (scale) {
    double psxscale, psyscale;
    PARI_get_psplot();
    PARI_get_plot();
    psxscale = pari_psplot.width * 1.0/pari_plot.width ;
    psyscale = pari_psplot.height* 1.0/pari_plot.height;
    fontsize = (long) (fontsize/psxscale);
    xscale *= psxscale;
    yscale *= psyscale;
  }
  psplot_init(&plot, psfile, xscale, yscale, fontsize);
  gen_rectdraw0(&plot, w, x, y, lw, 1, 1);
  fprintf(psfile,"stroke showpage\n"); fclose(psfile);
}

#define RoColT(R) minss(numcolors,RoCol(R))

void
gen_rectdraw0(struct plot_eng *eng, long *w, long *x, long *y, long lw, double xs, double ys)
{
  void *data = eng->data;
  long i, j;
  long hgapsize = eng->pl->hunit, fheight = eng->pl->fheight;
  long vgapsize = eng->pl->vunit,  fwidth = eng->pl->fwidth;
  long numcolors = lg(GP_DATA->colormap)-1;
  for(i=0; i<lw; i++)
  {
    PariRect *e = rectgraph[w[i]];
    RectObj *R;
    long x0 = x[i], y0 = y[i];
    for (R = RHead(e); R; R = RoNext(R))
    {
      switch(RoType(R))
      {
      case ROt_PT:
        eng->sc(data,RoColT(R));
        eng->pt(data, DTOL((RoPTx(R)+x0)*xs), DTOL((RoPTy(R)+y0)*ys));
        break;
      case ROt_LN:
        eng->sc(data,RoColT(R));
        eng->ln(data, DTOL((RoLNx1(R)+x0)*xs),
                      DTOL((RoLNy1(R)+y0)*ys),
                      DTOL((RoLNx2(R)+x0)*xs),
                      DTOL((RoLNy2(R)+y0)*ys));
        break;
      case ROt_BX:
        eng->sc(data,RoColT(R));
        eng->bx(data,
                DTOL((RoBXx1(R)+x0)*xs),
                DTOL((RoBXy1(R)+y0)*ys),
                DTOL((RoBXx2(R)-RoBXx1(R))*xs),
                DTOL((RoBXy2(R)-RoBXy1(R))*ys));
        break;
      case ROt_MP:
        {
          double *ptx = RoMPxs(R);
          double *pty = RoMPys(R);
          long     nb = RoMPcnt(R);
          struct plot_points *points =
            (struct plot_points *) pari_malloc(sizeof(*points)*nb);
          for(j=0;j<nb;j++)
          {
            points[j].x = DTOL((ptx[j]+x0)*xs);
            points[j].y = DTOL((pty[j]+y0)*ys);
          }
          eng->sc(data,RoColT(R));
          eng->mp(data, nb, points);
          pari_free(points);
          break;
        }
      case ROt_ML:
        {
          double *ptx = RoMLxs(R);
          double *pty = RoMLys(R);
          long     nb = RoMLcnt(R);
          struct plot_points *points =
            (struct plot_points *) pari_malloc(sizeof(*points)*nb);
          for(j=0;j<nb;j++)
          {
            points[j].x = DTOL((ptx[j]+x0)*xs);
            points[j].y = DTOL((pty[j]+y0)*ys);
          }
          eng->sc(data,RoColT(R));
          eng->ml(data, nb, points);
          pari_free(points);
          break;
        }
      case ROt_ST:
        {
          long dir = RoSTdir(R);
          long hjust = dir & RoSTdirHPOS_mask, hgap  = dir & RoSTdirHGAP;
          long vjust = dir & RoSTdirVPOS_mask, vgap  = dir & RoSTdirVGAP;
          char *text = RoSTs(R);
          long l     = RoSTl(R);
          long x, y;
          long shift = (hjust == RoSTdirLEFT ? 0 :
              (hjust == RoSTdirRIGHT ? 2 : 1));
          if (hgap)
            hgap = (hjust == RoSTdirLEFT) ? hgapsize : -hgapsize;
          if (vgap)
            vgap = (vjust == RoSTdirBOTTOM) ? 2*vgapsize : -2*vgapsize;
          if (vjust != RoSTdirBOTTOM)
            vgap -= ((vjust == RoSTdirTOP) ? 2 : 1)*(fheight - 1);
          x = DTOL((RoSTx(R) + x0 + hgap - (l * fwidth * shift)/2)*xs);
          y = DTOL((RoSTy(R) + y0 - vgap/2)*ys);
          eng->sc(data,RoColT(R));
          eng->st(data, x, y, text, l);
          break;
        }
      default:
        break;
      }
    }
  }
}

/*************************************************************************/
/*                                                                       */
/*                           RGB COLORS                                  */
/*                                                                       */
/*************************************************************************/
/* generated from /etc/X11/rgb.txt by the following perl script
#!/usr/bin/perl
while(<>)
{
  ($hex, $name) = split(/\t\t/, $_);
  $hex =~ s/^ +//; chomp($name); $name =~ s, *,,g;
  $hex = sprintf("0x%02x%02x%02x", split(/\s+/, $hex));
  $name = lc($name); next if ($done{$name});
  $done{$name} = 1;
  print "COL(\"$name\", $hex),\n";
}
*/

#define COL(x,y) {(void*)x,(void*)y,0,NULL}
static hashentry col_list[] = {
COL("", 0x000000),
COL("snow", 0xfffafa),
COL("ghostwhite", 0xf8f8ff),
COL("whitesmoke", 0xf5f5f5),
COL("gainsboro", 0xdcdcdc),
COL("floralwhite", 0xfffaf0),
COL("oldlace", 0xfdf5e6),
COL("linen", 0xfaf0e6),
COL("antiquewhite", 0xfaebd7),
COL("papayawhip", 0xffefd5),
COL("blanchedalmond", 0xffebcd),
COL("bisque", 0xffe4c4),
COL("peachpuff", 0xffdab9),
COL("navajowhite", 0xffdead),
COL("moccasin", 0xffe4b5),
COL("cornsilk", 0xfff8dc),
COL("ivory", 0xfffff0),
COL("lemonchiffon", 0xfffacd),
COL("seashell", 0xfff5ee),
COL("honeydew", 0xf0fff0),
COL("mintcream", 0xf5fffa),
COL("azure", 0xf0ffff),
COL("aliceblue", 0xf0f8ff),
COL("lavender", 0xe6e6fa),
COL("lavenderblush", 0xfff0f5),
COL("mistyrose", 0xffe4e1),
COL("white", 0xffffff),
COL("black", 0x000000),
COL("darkslategray", 0x2f4f4f),
COL("darkslategrey", 0x2f4f4f),
COL("dimgray", 0x696969),
COL("dimgrey", 0x696969),
COL("slategray", 0x708090),
COL("slategrey", 0x708090),
COL("lightslategray", 0x778899),
COL("lightslategrey", 0x778899),
COL("gray", 0xbebebe),
COL("grey", 0xbebebe),
COL("lightgrey", 0xd3d3d3),
COL("lightgray", 0xd3d3d3),
COL("midnightblue", 0x191970),
COL("navy", 0x000080),
COL("navyblue", 0x000080),
COL("cornflowerblue", 0x6495ed),
COL("darkslateblue", 0x483d8b),
COL("slateblue", 0x6a5acd),
COL("mediumslateblue", 0x7b68ee),
COL("lightslateblue", 0x8470ff),
COL("mediumblue", 0x0000cd),
COL("royalblue", 0x4169e1),
COL("blue", 0x0000ff),
COL("dodgerblue", 0x1e90ff),
COL("deepskyblue", 0x00bfff),
COL("skyblue", 0x87ceeb),
COL("lightskyblue", 0x87cefa),
COL("steelblue", 0x4682b4),
COL("lightsteelblue", 0xb0c4de),
COL("lightblue", 0xadd8e6),
COL("powderblue", 0xb0e0e6),
COL("paleturquoise", 0xafeeee),
COL("darkturquoise", 0x00ced1),
COL("mediumturquoise", 0x48d1cc),
COL("turquoise", 0x40e0d0),
COL("cyan", 0x00ffff),
COL("lightcyan", 0xe0ffff),
COL("cadetblue", 0x5f9ea0),
COL("mediumaquamarine", 0x66cdaa),
COL("aquamarine", 0x7fffd4),
COL("darkgreen", 0x006400),
COL("darkolivegreen", 0x556b2f),
COL("darkseagreen", 0x8fbc8f),
COL("seagreen", 0x2e8b57),
COL("mediumseagreen", 0x3cb371),
COL("lightseagreen", 0x20b2aa),
COL("palegreen", 0x98fb98),
COL("springgreen", 0x00ff7f),
COL("lawngreen", 0x7cfc00),
COL("green", 0x00ff00),
COL("chartreuse", 0x7fff00),
COL("mediumspringgreen", 0x00fa9a),
COL("greenyellow", 0xadff2f),
COL("limegreen", 0x32cd32),
COL("yellowgreen", 0x9acd32),
COL("forestgreen", 0x228b22),
COL("olivedrab", 0x6b8e23),
COL("darkkhaki", 0xbdb76b),
COL("khaki", 0xf0e68c),
COL("palegoldenrod", 0xeee8aa),
COL("lightgoldenrodyellow", 0xfafad2),
COL("lightyellow", 0xffffe0),
COL("yellow", 0xffff00),
COL("gold", 0xffd700),
COL("lightgoldenrod", 0xeedd82),
COL("goldenrod", 0xdaa520),
COL("darkgoldenrod", 0xb8860b),
COL("rosybrown", 0xbc8f8f),
COL("indianred", 0xcd5c5c),
COL("saddlebrown", 0x8b4513),
COL("sienna", 0xa0522d),
COL("peru", 0xcd853f),
COL("burlywood", 0xdeb887),
COL("beige", 0xf5f5dc),
COL("wheat", 0xf5deb3),
COL("sandybrown", 0xf4a460),
COL("tan", 0xd2b48c),
COL("chocolate", 0xd2691e),
COL("firebrick", 0xb22222),
COL("brown", 0xa52a2a),
COL("darksalmon", 0xe9967a),
COL("salmon", 0xfa8072),
COL("lightsalmon", 0xffa07a),
COL("orange", 0xffa500),
COL("darkorange", 0xff8c00),
COL("coral", 0xff7f50),
COL("lightcoral", 0xf08080),
COL("tomato", 0xff6347),
COL("orangered", 0xff4500),
COL("red", 0xff0000),
COL("hotpink", 0xff69b4),
COL("deeppink", 0xff1493),
COL("pink", 0xffc0cb),
COL("lightpink", 0xffb6c1),
COL("palevioletred", 0xdb7093),
COL("maroon", 0xb03060),
COL("mediumvioletred", 0xc71585),
COL("violetred", 0xd02090),
COL("magenta", 0xff00ff),
COL("violet", 0xee82ee),
COL("plum", 0xdda0dd),
COL("orchid", 0xda70d6),
COL("mediumorchid", 0xba55d3),
COL("darkorchid", 0x9932cc),
COL("darkviolet", 0x9400d3),
COL("blueviolet", 0x8a2be2),
COL("purple", 0xa020f0),
COL("mediumpurple", 0x9370db),
COL("thistle", 0xd8bfd8),
COL("snow1", 0xfffafa),
COL("snow2", 0xeee9e9),
COL("snow3", 0xcdc9c9),
COL("snow4", 0x8b8989),
COL("seashell1", 0xfff5ee),
COL("seashell2", 0xeee5de),
COL("seashell3", 0xcdc5bf),
COL("seashell4", 0x8b8682),
COL("antiquewhite1", 0xffefdb),
COL("antiquewhite2", 0xeedfcc),
COL("antiquewhite3", 0xcdc0b0),
COL("antiquewhite4", 0x8b8378),
COL("bisque1", 0xffe4c4),
COL("bisque2", 0xeed5b7),
COL("bisque3", 0xcdb79e),
COL("bisque4", 0x8b7d6b),
COL("peachpuff1", 0xffdab9),
COL("peachpuff2", 0xeecbad),
COL("peachpuff3", 0xcdaf95),
COL("peachpuff4", 0x8b7765),
COL("navajowhite1", 0xffdead),
COL("navajowhite2", 0xeecfa1),
COL("navajowhite3", 0xcdb38b),
COL("navajowhite4", 0x8b795e),
COL("lemonchiffon1", 0xfffacd),
COL("lemonchiffon2", 0xeee9bf),
COL("lemonchiffon3", 0xcdc9a5),
COL("lemonchiffon4", 0x8b8970),
COL("cornsilk1", 0xfff8dc),
COL("cornsilk2", 0xeee8cd),
COL("cornsilk3", 0xcdc8b1),
COL("cornsilk4", 0x8b8878),
COL("ivory1", 0xfffff0),
COL("ivory2", 0xeeeee0),
COL("ivory3", 0xcdcdc1),
COL("ivory4", 0x8b8b83),
COL("honeydew1", 0xf0fff0),
COL("honeydew2", 0xe0eee0),
COL("honeydew3", 0xc1cdc1),
COL("honeydew4", 0x838b83),
COL("lavenderblush1", 0xfff0f5),
COL("lavenderblush2", 0xeee0e5),
COL("lavenderblush3", 0xcdc1c5),
COL("lavenderblush4", 0x8b8386),
COL("mistyrose1", 0xffe4e1),
COL("mistyrose2", 0xeed5d2),
COL("mistyrose3", 0xcdb7b5),
COL("mistyrose4", 0x8b7d7b),
COL("azure1", 0xf0ffff),
COL("azure2", 0xe0eeee),
COL("azure3", 0xc1cdcd),
COL("azure4", 0x838b8b),
COL("slateblue1", 0x836fff),
COL("slateblue2", 0x7a67ee),
COL("slateblue3", 0x6959cd),
COL("slateblue4", 0x473c8b),
COL("royalblue1", 0x4876ff),
COL("royalblue2", 0x436eee),
COL("royalblue3", 0x3a5fcd),
COL("royalblue4", 0x27408b),
COL("blue1", 0x0000ff),
COL("blue2", 0x0000ee),
COL("blue3", 0x0000cd),
COL("blue4", 0x00008b),
COL("dodgerblue1", 0x1e90ff),
COL("dodgerblue2", 0x1c86ee),
COL("dodgerblue3", 0x1874cd),
COL("dodgerblue4", 0x104e8b),
COL("steelblue1", 0x63b8ff),
COL("steelblue2", 0x5cacee),
COL("steelblue3", 0x4f94cd),
COL("steelblue4", 0x36648b),
COL("deepskyblue1", 0x00bfff),
COL("deepskyblue2", 0x00b2ee),
COL("deepskyblue3", 0x009acd),
COL("deepskyblue4", 0x00688b),
COL("skyblue1", 0x87ceff),
COL("skyblue2", 0x7ec0ee),
COL("skyblue3", 0x6ca6cd),
COL("skyblue4", 0x4a708b),
COL("lightskyblue1", 0xb0e2ff),
COL("lightskyblue2", 0xa4d3ee),
COL("lightskyblue3", 0x8db6cd),
COL("lightskyblue4", 0x607b8b),
COL("slategray1", 0xc6e2ff),
COL("slategray2", 0xb9d3ee),
COL("slategray3", 0x9fb6cd),
COL("slategray4", 0x6c7b8b),
COL("lightsteelblue1", 0xcae1ff),
COL("lightsteelblue2", 0xbcd2ee),
COL("lightsteelblue3", 0xa2b5cd),
COL("lightsteelblue4", 0x6e7b8b),
COL("lightblue1", 0xbfefff),
COL("lightblue2", 0xb2dfee),
COL("lightblue3", 0x9ac0cd),
COL("lightblue4", 0x68838b),
COL("lightcyan1", 0xe0ffff),
COL("lightcyan2", 0xd1eeee),
COL("lightcyan3", 0xb4cdcd),
COL("lightcyan4", 0x7a8b8b),
COL("paleturquoise1", 0xbbffff),
COL("paleturquoise2", 0xaeeeee),
COL("paleturquoise3", 0x96cdcd),
COL("paleturquoise4", 0x668b8b),
COL("cadetblue1", 0x98f5ff),
COL("cadetblue2", 0x8ee5ee),
COL("cadetblue3", 0x7ac5cd),
COL("cadetblue4", 0x53868b),
COL("turquoise1", 0x00f5ff),
COL("turquoise2", 0x00e5ee),
COL("turquoise3", 0x00c5cd),
COL("turquoise4", 0x00868b),
COL("cyan1", 0x00ffff),
COL("cyan2", 0x00eeee),
COL("cyan3", 0x00cdcd),
COL("cyan4", 0x008b8b),
COL("darkslategray1", 0x97ffff),
COL("darkslategray2", 0x8deeee),
COL("darkslategray3", 0x79cdcd),
COL("darkslategray4", 0x528b8b),
COL("aquamarine1", 0x7fffd4),
COL("aquamarine2", 0x76eec6),
COL("aquamarine3", 0x66cdaa),
COL("aquamarine4", 0x458b74),
COL("darkseagreen1", 0xc1ffc1),
COL("darkseagreen2", 0xb4eeb4),
COL("darkseagreen3", 0x9bcd9b),
COL("darkseagreen4", 0x698b69),
COL("seagreen1", 0x54ff9f),
COL("seagreen2", 0x4eee94),
COL("seagreen3", 0x43cd80),
COL("seagreen4", 0x2e8b57),
COL("palegreen1", 0x9aff9a),
COL("palegreen2", 0x90ee90),
COL("palegreen3", 0x7ccd7c),
COL("palegreen4", 0x548b54),
COL("springgreen1", 0x00ff7f),
COL("springgreen2", 0x00ee76),
COL("springgreen3", 0x00cd66),
COL("springgreen4", 0x008b45),
COL("green1", 0x00ff00),
COL("green2", 0x00ee00),
COL("green3", 0x00cd00),
COL("green4", 0x008b00),
COL("chartreuse1", 0x7fff00),
COL("chartreuse2", 0x76ee00),
COL("chartreuse3", 0x66cd00),
COL("chartreuse4", 0x458b00),
COL("olivedrab1", 0xc0ff3e),
COL("olivedrab2", 0xb3ee3a),
COL("olivedrab3", 0x9acd32),
COL("olivedrab4", 0x698b22),
COL("darkolivegreen1", 0xcaff70),
COL("darkolivegreen2", 0xbcee68),
COL("darkolivegreen3", 0xa2cd5a),
COL("darkolivegreen4", 0x6e8b3d),
COL("khaki1", 0xfff68f),
COL("khaki2", 0xeee685),
COL("khaki3", 0xcdc673),
COL("khaki4", 0x8b864e),
COL("lightgoldenrod1", 0xffec8b),
COL("lightgoldenrod2", 0xeedc82),
COL("lightgoldenrod3", 0xcdbe70),
COL("lightgoldenrod4", 0x8b814c),
COL("lightyellow1", 0xffffe0),
COL("lightyellow2", 0xeeeed1),
COL("lightyellow3", 0xcdcdb4),
COL("lightyellow4", 0x8b8b7a),
COL("yellow1", 0xffff00),
COL("yellow2", 0xeeee00),
COL("yellow3", 0xcdcd00),
COL("yellow4", 0x8b8b00),
COL("gold1", 0xffd700),
COL("gold2", 0xeec900),
COL("gold3", 0xcdad00),
COL("gold4", 0x8b7500),
COL("goldenrod1", 0xffc125),
COL("goldenrod2", 0xeeb422),
COL("goldenrod3", 0xcd9b1d),
COL("goldenrod4", 0x8b6914),
COL("darkgoldenrod1", 0xffb90f),
COL("darkgoldenrod2", 0xeead0e),
COL("darkgoldenrod3", 0xcd950c),
COL("darkgoldenrod4", 0x8b6508),
COL("rosybrown1", 0xffc1c1),
COL("rosybrown2", 0xeeb4b4),
COL("rosybrown3", 0xcd9b9b),
COL("rosybrown4", 0x8b6969),
COL("indianred1", 0xff6a6a),
COL("indianred2", 0xee6363),
COL("indianred3", 0xcd5555),
COL("indianred4", 0x8b3a3a),
COL("sienna1", 0xff8247),
COL("sienna2", 0xee7942),
COL("sienna3", 0xcd6839),
COL("sienna4", 0x8b4726),
COL("burlywood1", 0xffd39b),
COL("burlywood2", 0xeec591),
COL("burlywood3", 0xcdaa7d),
COL("burlywood4", 0x8b7355),
COL("wheat1", 0xffe7ba),
COL("wheat2", 0xeed8ae),
COL("wheat3", 0xcdba96),
COL("wheat4", 0x8b7e66),
COL("tan1", 0xffa54f),
COL("tan2", 0xee9a49),
COL("tan3", 0xcd853f),
COL("tan4", 0x8b5a2b),
COL("chocolate1", 0xff7f24),
COL("chocolate2", 0xee7621),
COL("chocolate3", 0xcd661d),
COL("chocolate4", 0x8b4513),
COL("firebrick1", 0xff3030),
COL("firebrick2", 0xee2c2c),
COL("firebrick3", 0xcd2626),
COL("firebrick4", 0x8b1a1a),
COL("brown1", 0xff4040),
COL("brown2", 0xee3b3b),
COL("brown3", 0xcd3333),
COL("brown4", 0x8b2323),
COL("salmon1", 0xff8c69),
COL("salmon2", 0xee8262),
COL("salmon3", 0xcd7054),
COL("salmon4", 0x8b4c39),
COL("lightsalmon1", 0xffa07a),
COL("lightsalmon2", 0xee9572),
COL("lightsalmon3", 0xcd8162),
COL("lightsalmon4", 0x8b5742),
COL("orange1", 0xffa500),
COL("orange2", 0xee9a00),
COL("orange3", 0xcd8500),
COL("orange4", 0x8b5a00),
COL("darkorange1", 0xff7f00),
COL("darkorange2", 0xee7600),
COL("darkorange3", 0xcd6600),
COL("darkorange4", 0x8b4500),
COL("coral1", 0xff7256),
COL("coral2", 0xee6a50),
COL("coral3", 0xcd5b45),
COL("coral4", 0x8b3e2f),
COL("tomato1", 0xff6347),
COL("tomato2", 0xee5c42),
COL("tomato3", 0xcd4f39),
COL("tomato4", 0x8b3626),
COL("orangered1", 0xff4500),
COL("orangered2", 0xee4000),
COL("orangered3", 0xcd3700),
COL("orangered4", 0x8b2500),
COL("red1", 0xff0000),
COL("red2", 0xee0000),
COL("red3", 0xcd0000),
COL("red4", 0x8b0000),
COL("debianred", 0xd70751),
COL("deeppink1", 0xff1493),
COL("deeppink2", 0xee1289),
COL("deeppink3", 0xcd1076),
COL("deeppink4", 0x8b0a50),
COL("hotpink1", 0xff6eb4),
COL("hotpink2", 0xee6aa7),
COL("hotpink3", 0xcd6090),
COL("hotpink4", 0x8b3a62),
COL("pink1", 0xffb5c5),
COL("pink2", 0xeea9b8),
COL("pink3", 0xcd919e),
COL("pink4", 0x8b636c),
COL("lightpink1", 0xffaeb9),
COL("lightpink2", 0xeea2ad),
COL("lightpink3", 0xcd8c95),
COL("lightpink4", 0x8b5f65),
COL("palevioletred1", 0xff82ab),
COL("palevioletred2", 0xee799f),
COL("palevioletred3", 0xcd6889),
COL("palevioletred4", 0x8b475d),
COL("maroon1", 0xff34b3),
COL("maroon2", 0xee30a7),
COL("maroon3", 0xcd2990),
COL("maroon4", 0x8b1c62),
COL("violetred1", 0xff3e96),
COL("violetred2", 0xee3a8c),
COL("violetred3", 0xcd3278),
COL("violetred4", 0x8b2252),
COL("magenta1", 0xff00ff),
COL("magenta2", 0xee00ee),
COL("magenta3", 0xcd00cd),
COL("magenta4", 0x8b008b),
COL("orchid1", 0xff83fa),
COL("orchid2", 0xee7ae9),
COL("orchid3", 0xcd69c9),
COL("orchid4", 0x8b4789),
COL("plum1", 0xffbbff),
COL("plum2", 0xeeaeee),
COL("plum3", 0xcd96cd),
COL("plum4", 0x8b668b),
COL("mediumorchid1", 0xe066ff),
COL("mediumorchid2", 0xd15fee),
COL("mediumorchid3", 0xb452cd),
COL("mediumorchid4", 0x7a378b),
COL("darkorchid1", 0xbf3eff),
COL("darkorchid2", 0xb23aee),
COL("darkorchid3", 0x9a32cd),
COL("darkorchid4", 0x68228b),
COL("purple1", 0x9b30ff),
COL("purple2", 0x912cee),
COL("purple3", 0x7d26cd),
COL("purple4", 0x551a8b),
COL("mediumpurple1", 0xab82ff),
COL("mediumpurple2", 0x9f79ee),
COL("mediumpurple3", 0x8968cd),
COL("mediumpurple4", 0x5d478b),
COL("thistle1", 0xffe1ff),
COL("thistle2", 0xeed2ee),
COL("thistle3", 0xcdb5cd),
COL("thistle4", 0x8b7b8b),
COL("gray0", 0x000000),
COL("grey0", 0x000000),
COL("gray1", 0x030303),
COL("grey1", 0x030303),
COL("gray2", 0x050505),
COL("grey2", 0x050505),
COL("gray3", 0x080808),
COL("grey3", 0x080808),
COL("gray4", 0x0a0a0a),
COL("grey4", 0x0a0a0a),
COL("gray5", 0x0d0d0d),
COL("grey5", 0x0d0d0d),
COL("gray6", 0x0f0f0f),
COL("grey6", 0x0f0f0f),
COL("gray7", 0x121212),
COL("grey7", 0x121212),
COL("gray8", 0x141414),
COL("grey8", 0x141414),
COL("gray9", 0x171717),
COL("grey9", 0x171717),
COL("gray10", 0x1a1a1a),
COL("grey10", 0x1a1a1a),
COL("gray11", 0x1c1c1c),
COL("grey11", 0x1c1c1c),
COL("gray12", 0x1f1f1f),
COL("grey12", 0x1f1f1f),
COL("gray13", 0x212121),
COL("grey13", 0x212121),
COL("gray14", 0x242424),
COL("grey14", 0x242424),
COL("gray15", 0x262626),
COL("grey15", 0x262626),
COL("gray16", 0x292929),
COL("grey16", 0x292929),
COL("gray17", 0x2b2b2b),
COL("grey17", 0x2b2b2b),
COL("gray18", 0x2e2e2e),
COL("grey18", 0x2e2e2e),
COL("gray19", 0x303030),
COL("grey19", 0x303030),
COL("gray20", 0x333333),
COL("grey20", 0x333333),
COL("gray21", 0x363636),
COL("grey21", 0x363636),
COL("gray22", 0x383838),
COL("grey22", 0x383838),
COL("gray23", 0x3b3b3b),
COL("grey23", 0x3b3b3b),
COL("gray24", 0x3d3d3d),
COL("grey24", 0x3d3d3d),
COL("gray25", 0x404040),
COL("grey25", 0x404040),
COL("gray26", 0x424242),
COL("grey26", 0x424242),
COL("gray27", 0x454545),
COL("grey27", 0x454545),
COL("gray28", 0x474747),
COL("grey28", 0x474747),
COL("gray29", 0x4a4a4a),
COL("grey29", 0x4a4a4a),
COL("gray30", 0x4d4d4d),
COL("grey30", 0x4d4d4d),
COL("gray31", 0x4f4f4f),
COL("grey31", 0x4f4f4f),
COL("gray32", 0x525252),
COL("grey32", 0x525252),
COL("gray33", 0x545454),
COL("grey33", 0x545454),
COL("gray34", 0x575757),
COL("grey34", 0x575757),
COL("gray35", 0x595959),
COL("grey35", 0x595959),
COL("gray36", 0x5c5c5c),
COL("grey36", 0x5c5c5c),
COL("gray37", 0x5e5e5e),
COL("grey37", 0x5e5e5e),
COL("gray38", 0x616161),
COL("grey38", 0x616161),
COL("gray39", 0x636363),
COL("grey39", 0x636363),
COL("gray40", 0x666666),
COL("grey40", 0x666666),
COL("gray41", 0x696969),
COL("grey41", 0x696969),
COL("gray42", 0x6b6b6b),
COL("grey42", 0x6b6b6b),
COL("gray43", 0x6e6e6e),
COL("grey43", 0x6e6e6e),
COL("gray44", 0x707070),
COL("grey44", 0x707070),
COL("gray45", 0x737373),
COL("grey45", 0x737373),
COL("gray46", 0x757575),
COL("grey46", 0x757575),
COL("gray47", 0x787878),
COL("grey47", 0x787878),
COL("gray48", 0x7a7a7a),
COL("grey48", 0x7a7a7a),
COL("gray49", 0x7d7d7d),
COL("grey49", 0x7d7d7d),
COL("gray50", 0x7f7f7f),
COL("grey50", 0x7f7f7f),
COL("gray51", 0x828282),
COL("grey51", 0x828282),
COL("gray52", 0x858585),
COL("grey52", 0x858585),
COL("gray53", 0x878787),
COL("grey53", 0x878787),
COL("gray54", 0x8a8a8a),
COL("grey54", 0x8a8a8a),
COL("gray55", 0x8c8c8c),
COL("grey55", 0x8c8c8c),
COL("gray56", 0x8f8f8f),
COL("grey56", 0x8f8f8f),
COL("gray57", 0x919191),
COL("grey57", 0x919191),
COL("gray58", 0x949494),
COL("grey58", 0x949494),
COL("gray59", 0x969696),
COL("grey59", 0x969696),
COL("gray60", 0x999999),
COL("grey60", 0x999999),
COL("gray61", 0x9c9c9c),
COL("grey61", 0x9c9c9c),
COL("gray62", 0x9e9e9e),
COL("grey62", 0x9e9e9e),
COL("gray63", 0xa1a1a1),
COL("grey63", 0xa1a1a1),
COL("gray64", 0xa3a3a3),
COL("grey64", 0xa3a3a3),
COL("gray65", 0xa6a6a6),
COL("grey65", 0xa6a6a6),
COL("gray66", 0xa8a8a8),
COL("grey66", 0xa8a8a8),
COL("gray67", 0xababab),
COL("grey67", 0xababab),
COL("gray68", 0xadadad),
COL("grey68", 0xadadad),
COL("gray69", 0xb0b0b0),
COL("grey69", 0xb0b0b0),
COL("gray70", 0xb3b3b3),
COL("grey70", 0xb3b3b3),
COL("gray71", 0xb5b5b5),
COL("grey71", 0xb5b5b5),
COL("gray72", 0xb8b8b8),
COL("grey72", 0xb8b8b8),
COL("gray73", 0xbababa),
COL("grey73", 0xbababa),
COL("gray74", 0xbdbdbd),
COL("grey74", 0xbdbdbd),
COL("gray75", 0xbfbfbf),
COL("grey75", 0xbfbfbf),
COL("gray76", 0xc2c2c2),
COL("grey76", 0xc2c2c2),
COL("gray77", 0xc4c4c4),
COL("grey77", 0xc4c4c4),
COL("gray78", 0xc7c7c7),
COL("grey78", 0xc7c7c7),
COL("gray79", 0xc9c9c9),
COL("grey79", 0xc9c9c9),
COL("gray80", 0xcccccc),
COL("grey80", 0xcccccc),
COL("gray81", 0xcfcfcf),
COL("grey81", 0xcfcfcf),
COL("gray82", 0xd1d1d1),
COL("grey82", 0xd1d1d1),
COL("gray83", 0xd4d4d4),
COL("grey83", 0xd4d4d4),
COL("gray84", 0xd6d6d6),
COL("grey84", 0xd6d6d6),
COL("gray85", 0xd9d9d9),
COL("grey85", 0xd9d9d9),
COL("gray86", 0xdbdbdb),
COL("grey86", 0xdbdbdb),
COL("gray87", 0xdedede),
COL("grey87", 0xdedede),
COL("gray88", 0xe0e0e0),
COL("grey88", 0xe0e0e0),
COL("gray89", 0xe3e3e3),
COL("grey89", 0xe3e3e3),
COL("gray90", 0xe5e5e5),
COL("grey90", 0xe5e5e5),
COL("gray91", 0xe8e8e8),
COL("grey91", 0xe8e8e8),
COL("gray92", 0xebebeb),
COL("grey92", 0xebebeb),
COL("gray93", 0xededed),
COL("grey93", 0xededed),
COL("gray94", 0xf0f0f0),
COL("grey94", 0xf0f0f0),
COL("gray95", 0xf2f2f2),
COL("grey95", 0xf2f2f2),
COL("gray96", 0xf5f5f5),
COL("grey96", 0xf5f5f5),
COL("gray97", 0xf7f7f7),
COL("grey97", 0xf7f7f7),
COL("gray98", 0xfafafa),
COL("grey98", 0xfafafa),
COL("gray99", 0xfcfcfc),
COL("grey99", 0xfcfcfc),
COL("gray100", 0xffffff),
COL("grey100", 0xffffff),
COL("darkgrey", 0xa9a9a9),
COL("darkgray", 0xa9a9a9),
COL("darkblue", 0x00008b),
COL("darkcyan", 0x008b8b),
COL("darkmagenta", 0x8b008b),
COL("darkred", 0x8b0000),
COL("lightgreen", 0x90ee90),
COL(NULL,0) /* sentinel */
};
#undef COL

static void
colorname_to_rgb(const char *s, int *r, int *g, int *b)
{
  hashentry *ep;
  long rgb;

  if (!rgb_colors) rgb_colors = hashstr_import_static(col_list, 1000);
  ep = hash_search(rgb_colors, (void*)s);
  if (!ep) pari_err(e_MISC, "unknown color %s", s);
  rgb = (long)ep->val;
  *b = rgb & 0xff; rgb >>= 8;
  *g = rgb & 0xff; rgb >>= 8;
  *r = rgb;
}

void
color_to_rgb(GEN c, int *r, int *g, int *b)
{
  switch(typ(c))
  {
    case t_STR:
      colorname_to_rgb(GSTR(c), r,g,b);
      break;
    default: /* t_VECSMALL: */
      *r = c[1]; *g = c[2]; *b = c[3];
      break;
  }
}
