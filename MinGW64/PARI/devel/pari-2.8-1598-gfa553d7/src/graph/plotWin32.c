/* Copyright (C) 2009  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* Written by Vasili Burdo */

#include <windows.h>
#include <time.h>
#include "pari.h"
#include "paripriv.h"
#include "rect.h"

static void SetForeground(void *data, long col)
{
  int r,g,b;
  color_to_rgb(gel(GP_DATA->colormap,col), &r, &g, &b);

  HPEN hOldPen = SelectObject((HDC)data, CreatePen(PS_SOLID, 2, RGB(r,g,b)));
  if( hOldPen ) DeleteObject(hOldPen);
}

static void DrawPoint(void *data, long x, long y)
{
  Ellipse((HDC)data,x-1,y-1,x+1,y+1);
}

static void DrawLine(void *data, long x1, long y1, long x2, long y2)
{
  MoveToEx((HDC)data, x1, y1, NULL);
  LineTo((HDC)data,x2,y2);
}

static void DrawRectangle(void *data, long x, long y, long w, long h)
{
  RECT rc;
  rc.left = x; rc.right  = x+w;
  rc.top  = y; rc.bottom = y+h;
  FrameRect((HDC)data, &rc, GetStockObject(HOLLOW_BRUSH));
}

static void DrawPoints(void *data, long nb, struct plot_points *p)
{
  long i;
  for (i=0; i<nb; ++i)
    DrawPoint(data,p[i].x,p[i].y);
}

static void DrawLines(void *data, long nb, struct plot_points *p)
{
  long i;
  MoveToEx((HDC)data, p[0].x, p[0].y, NULL);
  for(i=1; i<nb; ++i)
    LineTo((HDC)data,p[i].x,p[i].y);
}

static void DrawString(void *data, long x, long y, char *text, long numtext)
{
  TextOut((HDC)data, x, y, text, numtext);
}

void rectdraw0(long *w, long *x, long *y, long lw)
{
  char tmppath[MAX_PATH], fname[MAX_PATH];
  struct plot_eng plotWin32;
  HDC hEmf;

  GetTempPath(sizeof(tmppath), tmppath);
  sprintf(fname, "%s\\gp-ploth-%lx.emf", tmppath, time(NULL)/(24*60*60)*1000+GetTickCount());

  hEmf = CreateEnhMetaFile(GetDC(NULL), fname, NULL, NULL);
  SetMapMode(hEmf, MM_TEXT);
  SelectObject(hEmf, GetStockObject(DEFAULT_GUI_FONT));
  SetBkColor(hEmf, RGB(255,255,255));
  SetBkMode(hEmf, TRANSPARENT);

  plotWin32.sc=&SetForeground;
  plotWin32.pt=&DrawPoint;
  plotWin32.ln=&DrawLine;
  plotWin32.bx=&DrawRectangle;
  plotWin32.mp=&DrawPoints;
  plotWin32.ml=&DrawLines;
  plotWin32.st=&DrawString;
  plotWin32.pl=&pari_plot;
  plotWin32.data=(void*)hEmf;

  gen_rectdraw0(&plotWin32, w, x, y, lw, 1, 1);
  DeleteEnhMetaFile(CloseEnhMetaFile(hEmf));

  ShellExecute(NULL,NULL,fname,NULL,NULL,SW_SHOWDEFAULT);
}

void
PARI_get_plot(void)
{
  HDC hdc;
  TEXTMETRIC tm;
  if (pari_plot.init) return;      /* pari_plot is already set */

  pari_plot.init    = 1;
  pari_plot.width   = GetSystemMetrics(SM_CXSCREEN)/2;
  pari_plot.height  = GetSystemMetrics(SM_CYSCREEN)/2;
  pari_plot.hunit   = pari_plot.width/100;
  pari_plot.vunit   = pari_plot.height/100;

  hdc = GetDC(0);
  SelectObject(hdc, GetStockObject(DEFAULT_GUI_FONT));
  GetTextMetrics(hdc, &tm);
  ReleaseDC(0,hdc);

  pari_plot.fwidth  = tm.tmAveCharWidth;
  pari_plot.fheight = tm.tmHeight;
}
