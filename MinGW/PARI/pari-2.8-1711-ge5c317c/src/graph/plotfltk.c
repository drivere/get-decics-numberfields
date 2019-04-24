/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */
/////////////////////////////////////////////////////////////////////////////
//
//  High resolution plot using FLTK library
//  Bill Allombert 2003
//
//  Based on plotQt by Nils-Peter Skoruppa (www.countnumber.de)
/////////////////////////////////////////////////////////////////////////////
extern "C" {
#include "pari.h"
#include "paripriv.h"
#include "rect.h"
}

#include <FL/Fl.H>
#include <FL/Fl_Window.H>
#include <FL/fl_draw.H>

static long numcolors;

class Plotter: public Fl_Window {

public:
    Plotter( long *w, long *x, long *y, long lw, const char* name = 0);

private:
    void draw();
    int handle(int event);

private:
    long *my_w;                        // map into rectgraph indexes
    long *my_x;                        // x, y: array of x,y-coordinates of the
    long *my_y;                        // top left corners of the rectwindows
    long my_lw;                        // lw: number of rectwindows
    Fl_Color *color;
};

static Fl_Color
rgb_color(int R, int G, int B)
{
  return fl_color_cube(R*FL_NUM_RED/256, G*FL_NUM_GREEN/256, B*FL_NUM_BLUE/256);
}

Plotter::Plotter( long *w, long *x, long *y, long lw,
             const char* name)
        : Fl_Window(pari_plot.width, pari_plot.height, "PARI/GP")

{
    long i;

    this->my_w=w; this->my_x=x; this->my_y=y; this->my_lw=lw;
    numcolors = lg(GP_DATA->colormap)-1;
    color = (Fl_Color*)pari_malloc(numcolors*sizeof(Fl_Color));
    for (i = 1; i < lg(GP_DATA->colormap); i++)
    {
      int r, g, b;
      color_to_rgb(gel(GP_DATA->colormap,i), &r, &g, &b);
      color[i-1] = rgb_color(r, g, b);
    }
}

static void DrawPoint(void *data, long x, long y)
{
  (void)data;
  fl_point(x,y);
}

static void DrawLine(void *data, long x1, long y1, long x2, long y2)
{
  (void)data;
  fl_line(x1,y1, x2,y2);
}

static void DrawRectangle(void *data, long x, long y, long w, long h)
{
  (void)data;
  fl_rect(x,y,w,h);
}

static void DrawPoints(void *data, long nb, struct plot_points *p)
{
  long i;
  (void)data;
  for (i=0; i<nb; i++) fl_point(p[i].x, p[i].y);
}

static void SetForeground(void *data, long col)
{
  Fl_Color *color = (Fl_Color*)data;
  fl_color(color[col]);
}

static void DrawLines(void *data, long nb, struct plot_points *p)
{
  long i;
  (void)data;
  for (i=1; i<nb; i++) fl_line(p[i-1].x, p[i-1].y, p[i].x, p[i].y);
}

static void DrawString(void *data, long x, long y, char *text, long numtext)
{
  (void)data;
  fl_draw(text,numtext,x,y);
}

void Plotter::draw()
{
  struct plot_eng pl;

  double xs = double(this->w())/pari_plot.width;
  double ys = double(this->h())/pari_plot.height;

  fl_font(FL_COURIER, int(pari_plot.fheight * xs));
  fl_color(color[0]); // transparent window on Windows otherwise
  fl_rectf(0, 0, this->w(), this->h());
  pl.sc = &SetForeground;
  pl.pt = &DrawPoint;
  pl.ln = &DrawLine;
  pl.bx = &DrawRectangle;
  pl.mp = &DrawPoints;
  pl.ml = &DrawLines;
  pl.st = &DrawString;
  pl.pl = &pari_plot;
  pl.data = (void*)color;
  gen_rectdraw0(&pl, my_w, my_x, my_y, my_lw, xs, ys);
}

int Plotter::handle(int event)
{
  switch(event)
  {
  case FL_PUSH:
    switch(Fl::event_button())
    {
    case 1:
     exit(0);
    case 2:
     {
       static int flag=0;
       static int my_x;
       static int my_y;
       static int my_w;
       static int my_h;
       flag=1-flag;
       if (flag)
       {
         my_x=this->x();
         my_y=this->y();
         my_w=this->w();
         my_h=this->h();
         this->fullscreen();
       }
       else
       {
         this->fullscreen_off(my_x,my_y,my_w,my_h);
         this->size_range(1,1);
       }
       return 1;
     }
    }
  case FL_KEYUP:
    switch(Fl::event_key())
    {
    case 'q':
      switch(Fl::event_shift())
      {
        case 0:
        case FL_CTRL:
          exit(0);
      }
      break;
    case 'c':
      if (Fl::event_state() == FL_CTRL) exit(0);
      break;
    }
  default:
    return 0;
  }
}

//
// Implementation of the two architecture-dependent functions
// (from rect.h) requested by pari's plotting routines
//

void
rectdraw0(long *w, long *x, long *y, long lw)
{
    Plotter *win;

    if (pari_daemon()) return;  // parent process returns

    pari_close();
    PARI_get_plot();

    Fl::visual(FL_DOUBLE|FL_INDEX);
    win = new Plotter( w, x, y, lw);
    win->size_range(1,1);
    win->box(FL_FLAT_BOX);
    win->end();
    win->show();
    Fl::run();
    exit(0);
}

void
PARI_get_plot(void)
/* This function initialises the structure rect.h: pari_plot */
{
    if (pari_plot.init) return;      // pari_plot is already set
    pari_plot.width   = 400;         // width and
    pari_plot.height  = 300;         //  height of plot window
    pari_plot.hunit   = 3;           //
    pari_plot.vunit   = 3;           //
    pari_plot.fwidth  = 6;           // font width
    pari_plot.fheight = 9;           //   and height
    pari_plot.init    = 1;           // flag: pari_plot is set now!
}
