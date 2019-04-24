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
//  High resolution plot using Trolltech's Qt library
//
//  You may possibly want to use this file with a "Qt Free Edition"
//  which is distributed under the terms of the Q PUBLIC LICENSE (QPL),
//  or with a "Qt/Embedded Free Edition" which is
//  distributed under the terms of the GNU General Public License (GPL).
//  Please check http://www.trolltech.com for details.
//
//                            ---Nils-Peter Skoruppa (www.countnumber.de)
/////////////////////////////////////////////////////////////////////////////
#ifdef __QPE__
#include <Qt/qpeapplication.h>
#else
#include <Qt/qapplication.h>
#endif
#include <Qt/qwidget.h>
#include <Qt/qpainter.h>
#include <Qt/qcolor.h>
#include <Qt/qdesktopwidget.h>
#include <Qt/qevent.h>
#include <Qt/qpixmap.h>
#include <Qt/qsignalmapper.h>
#include <Qt/qimage.h>
#include <Qt/qimagewriter.h>
#include <Qt/qmainwindow.h>
#include <Qt/qmenubar.h>
#include <Qt/qtoolbar.h>
#include <Qt/qaction.h>
#include <Qt/qfiledialog.h>
#include <Qt/qmessagebox.h>
#include <Qt/qfile.h>
#include <Qt/qstatusbar.h>
#include <Qt/qimage.h>
#include <Qt/qlabel.h>
#include <Qt/qspinbox.h>
#include <Qt/qlayout.h>

extern "C" {
#include "pari.h"
#include "paripriv.h"
#undef grem
#include "rect.h"
}

using namespace Qt;

class Plotter: public QWidget {

#ifdef __FANCY_WIN__
     Q_OBJECT

signals:
    void clicked();

protected:
    void mouseReleaseEvent( QMouseEvent*);
#endif

public:
    Plotter( long *w, long *x, long *y, long lw,
             QWidget* parent = 0);
    void save( const QString& s = *plotFile + ".xpm",//QString("pariplot.xpm"),
               const QString& f = QString( "XPM"));

protected:
    void paintEvent( QPaintEvent *);
    //void resizeEvent ( QResizeEvent *);
#ifndef __FANCY_WIN__
    void keyPressEvent( QKeyEvent *);
#endif

private:
    long *w;                           // map into rectgraph indexes
    long *x;                           // x, y: array of x,y-coorinates of the
    long *y;                           //   top left corners of the rectwindows
    long lw;                           // lw: number of rectwindows
    long numcolors;
    QColor *color;
    QFont font;
    static QString *plotFile;
    void draw(QPainter *p);

// public:
//     static void setPlotFile( const char *);
};


QString *Plotter::plotFile = new QString( "pariplot");


Plotter::Plotter( long *w, long *x, long *y, long lw,
                  QWidget* parent)
    : QWidget( parent), font( "lucida", 9) {

    long i;

    this->w=w; this->x=x; this->y=y; this->lw=lw;
#ifndef __FANCY_WIN__
    this->resize( pari_plot.width, pari_plot.height);
    this->setCaption( "Pari QtPlot");
#endif
    this->setFont( font);
    numcolors = lg(GP_DATA->colormap)-1;
    color = (QColor*)gpmalloc(numcolors*sizeof(QColor));
    for (i = 1; i < lg(GP_DATA->colormap); i++)
    {
      int r, g, b;
      color_to_rgb(gel(GP_DATA->colormap,i), &r, &g, &b);
      color[i-1] = QColor(r, g, b);
    }
    QPalette palette;
    palette.setColor(backgroundRole(), color[0]);
    setPalette(palette);
}

// void Plotter::setPlotFile( const char *s) {

//     delete Plotter::plotFile;
//     Plotter::plotFile = new QString( s);
// }

struct data_qt
{
  QPainter *p;
  long numcolors;
  QColor *color;
};

static void SetForeground(void *data, long col)
{
   struct data_qt *d = (struct data_qt *) data;
   d->p->setPen(d->color[col]);
}

static void DrawPoint(void *data, long x, long y)
{
   struct data_qt *d = (struct data_qt *) data;
   d->p->drawPoint(x, y);
}

static void DrawLine(void *data, long x1, long y1, long x2, long y2)
{
   struct data_qt *d = (struct data_qt *) data;
   d->p->drawLine(x1, y1, x2, y2);
}

static void DrawRectangle(void *data, long x, long y, long w, long h)
{
   struct data_qt *d = (struct data_qt *) data;
   d->p->drawRect(x, y, w, h);
}

static void DrawPoints(void *data, long nb, struct plot_points *p)
{
   struct data_qt *d = (struct data_qt *) data;
   QPolygon xp=QPolygon(nb);
   long i;
   for (i=0;i<nb;i++)
     xp.setPoint(i,p[i].x, p[i].y);
   d->p->drawPoints(xp);
}

static void DrawLines(void *data, long nb, struct plot_points *p)
{
   struct data_qt *d = (struct data_qt *) data;
   QPolygon xp=QPolygon(nb);
   long i;
   for (i=0;i<nb;i++)
     xp.setPoint(i,p[i].x, p[i].y);
   d->p->drawPolyline(xp);
}

static void DrawString(void *data, long x, long y, char *text, long numtext)
{
  struct data_qt *d = (struct data_qt *) data;
  d->p->drawText(x, y, QString(text).left(numtext));
}

void Plotter::draw(QPainter *p){
  struct plot_eng plotQt;
  struct data_qt d;
  d.p= p;
  d.numcolors = numcolors;
  d.color=color;
  plotQt.sc=&SetForeground;
  plotQt.pt=&DrawPoint;
  plotQt.ln=&DrawLine;
  plotQt.bx=&DrawRectangle;
  plotQt.mp=&DrawPoints;
  plotQt.ml=&DrawLines;
  plotQt.st=&DrawString;
  plotQt.pl=&pari_plot;
  plotQt.data=(void *)&d;
  double xs = double(this->width()) / pari_plot.width,
         ys = double(this->height()) / pari_plot.height;
  gen_rectdraw0(&plotQt, this->w, this->x, this->y,this->lw,xs,ys);
}

void Plotter::save( const QString& s, const QString& f)
{
    QPixmap pm( this->width(), this->height());
    QPainter p;
    p.begin(&pm);
        p.initFrom(this);
        p.fillRect( 0, 0, pm.width(), pm.height(), color[0]);
        draw(&p);
    p.end();
    pm.save( s, f.toAscii().data());
}



void Plotter::paintEvent( QPaintEvent *) {

    QPainter p;
    p.begin( this);
    this->draw(&p);
    p.end();
}

//void Plotter::resizeEvent( QResizeEvent *) { }

#ifndef __FANCY_WIN__
void Plotter::keyPressEvent( QKeyEvent *e) {

    switch ( tolower( e->ascii())) {
        case 's':
            save();
            this->setCaption( "Pari QtPlot: " + *plotFile);
            break;
    }
}
#endif


#ifdef __FANCY_WIN__
void Plotter::mouseReleaseEvent( QMouseEvent*) {

    emit clicked();
}
#endif



#ifdef __FANCY_WIN__
//
// The envelope for an instance of plotter
//




/* XPM */
static const char * const fullscreen_xpm[] = {
"14 14 2 1",
"         c None",
".        c #000000",
"..............",
".     ..     .",
".     ..     .",
".    ....    .",
".     ..     .",
".  .  ..  .  .",
"..............",
"..............",
".  .  ..  .  .",
".     ..     .",
".    ....    .",
".     ..     .",
".     ..     .",
".............."};

/*
class SaveAsDialog: public
#ifdef __QPE__
//QDialog
#else
QFileDialog
#endif
{

    Q_OBJECT

public:
    SaveAsDialog( const QString & c = QString::null,
                  const QString & s = QString::null, int w = 0, int h = 0,
                  QWidget *parent = 0, const char *name = 0, WFlags f = 0);
    ~SaveAsDialog();
#ifdef __QPE__
    QString selectedFile() { return nameW->text();}
#endif
    int picWidth() { return widthW->value();}
    int picHeight() { return heightW->value();}

private:
    QLineEdit *nameW;
    QSpinBox *widthW, *heightW;

};


SaveAsDialog::SaveAsDialog( const QString & c, const QString & s, int w, int h,
                            QWidget *parent, const char *name, WFlags f)
#ifdef __QPE__
    // simplistic dialog in case of QPE ( fancy alternative: class FileSelector)

    : QDialog( parent, name, TRUE, f) {

    if( c) this->setCaption( c);
    nameW = new QLineEdit( this);
    if( s) nameW->setText( s);
    widthW = new QSpinBox( 1, 65536, 1, this);
    if( w > 0) widthW->setValue( w);
    heightW = new QSpinBox( 1, 65536, 1, this);
    if( h > 0) heightW->setValue( h);

    QVBoxLayout *top = new QVBoxLayout( this, 10);
    QGridLayout *contents = new QGridLayout( 3, 2);

    top->addLayout( contents);

    QLabel *l;
    l = new QLabel( nameW, "Name : ", this);
    l->setAlignment( AlignRight | AlignVCenter);
    contents->addWidget( l, 0, 0);
    contents->addWidget( nameW, 0, 1);
    l = new QLabel( widthW, "Width : ", this);
    l->setAlignment( AlignRight | AlignVCenter);
    contents->addWidget( l, 1, 0);
    contents->addWidget( widthW, 1, 1);
    l = new QLabel( heightW, "Height : ", this);
    l->setAlignment( AlignRight | AlignVCenter);
    contents->addWidget( l, 2, 0);
    contents->addWidget( heightW, 2, 1);

    top->activate();
    this->resize( 160, this->height()); // hack!!!
#else
    : QFileDialog( parent, name, TRUE) {

    if( c) this->setFilters( c);
    if( s) this->setSelection( s);

    QLabel *l;
    QWidget *wt = new QWidget( this);
    QHBoxLayout *spinBoxes = new QHBoxLayout( wt, 5);
    widthW = new QSpinBox( 1, 65536, 1, wt);
    l  = new QLabel( widthW, "&width ", wt);
    spinBoxes->addWidget( l);
    spinBoxes->addWidget( widthW);
    if( w > 0) widthW->setValue( w);
    heightW = new QSpinBox( 1, 65536, 1, wt);
    spinBoxes->addSpacing(10);
    l  = new QLabel( heightW, "&height ", wt);
    l->setAlignment( AlignRight | AlignVCenter);
    spinBoxes->addWidget( l);
    spinBoxes->addWidget( heightW);
    if( h > 0) heightW->setValue( h);
    l = new QLabel( "Resolution:", this);
    QFileDialog::addWidgets( l, wt, 0);
#endif
}


SaveAsDialog::~SaveAsDialog() {
}
*/


class PlotWindow: public QMainWindow {

     Q_OBJECT

public:
    PlotWindow( long *w, long *x, long *y, long lw,
                QWidget* parent = 0, const char* name = 0);
    ~PlotWindow();

#ifndef __QPE__
protected:
    void resizeEvent( QResizeEvent *);
#endif

private slots:
    void fullScreen();
    void normalView();
    void save();
    void save( int);

private:
    static const QList<QByteArray> file_formats;
    Plotter *plr;
    QString saveFileName;
    int saveFileFormat;
#ifndef __QPE__
    QLabel *res;
    QMenu* menuFile;
    QMenu* menuView;
    QMenu* menuFormat;
    QAction* quitAction;
    QAction* saveAction;
    QAction* fullScreenAction;
    QSignalMapper* signalMapper;
    QIcon* icon;
#endif
};


const QList<QByteArray> PlotWindow::file_formats = QImageWriter::supportedImageFormats();


PlotWindow::PlotWindow( long *w, long *x, long *y, long lw,
                        QWidget* parent, const char* name)
    : QMainWindow( parent),
      saveFileName( "pariplot"), saveFileFormat( 0) {

    setWindowTitle( "Pari QtPlot");

        QPalette palette;
        palette.setColor(this->backgroundRole(), white);
        this->setPalette(palette);

        menuFile = menuBar()->addMenu("&File");

        saveAction = new QAction("&Save",this);
        saveAction->setShortcut(QKeySequence(CTRL+Key_S));
        connect (saveAction, SIGNAL(triggered()), this, SLOT(save()));
        menuFile->addAction(saveAction);

        menuFormat = menuFile->addMenu("Save &as");

        signalMapper = new QSignalMapper(this);

        for( int i = 0; i < file_formats.count(); i++)
        {
        QAction* tmpAction;
        tmpAction = new QAction(QString(file_formats.at(i)),this);
        connect (tmpAction, SIGNAL(triggered()), signalMapper, SLOT(map()));
        signalMapper->setMapping(tmpAction,i);
        menuFormat->addAction(tmpAction);
        }

        connect (signalMapper, SIGNAL(mapped(int)), this,SLOT(save(int)));

        quitAction = new QAction("&Quit",this);
        quitAction->setShortcut(QKeySequence(CTRL+Key_Q));
        connect (quitAction, SIGNAL(triggered()), this, SLOT(close()));
        menuFile->addAction(quitAction);

        menuView = menuBar()->addMenu("&View");

        fullScreenAction = new QAction("Use &full screen", this);
        fullScreenAction->setShortcut(QKeySequence(CTRL+Key_F));
        icon = new QIcon();
        icon->addPixmap(QPixmap( (const char ** )fullscreen_xpm));
        fullScreenAction->setIcon(*icon);
        connect(fullScreenAction, SIGNAL( triggered()), this, SLOT( fullScreen()));
        menuView->addAction(fullScreenAction);

    // Setting up an instance of plotter
    plr = new Plotter( w, x, y, lw, this);
    connect( plr, SIGNAL(clicked()), this, SLOT( normalView()));
    this->setCentralWidget( plr);

#ifndef __QPE__
    this->resize( pari_plot.width,
                  pari_plot.height + 24);
    res = new QLabel( );
    statusBar()->addWidget( res);
#endif
}


PlotWindow::~PlotWindow() {
}


#ifndef __QPE__
void PlotWindow::resizeEvent( QResizeEvent *e) {

    QMainWindow::resizeEvent( e);
    res->setText( QString( "Resolution: ") +
                  QString::number( plr->width()) + "x" +
                  QString::number( plr->height()));
    res->setFixedSize( res->sizeHint());
}
#endif


void PlotWindow::fullScreen() {
    plr->setParent( 0);
    plr->showMaximized();
    plr->show();

}


void PlotWindow::normalView() {

    if ( !plr->parentWidget()) {
        plr->setParent( this);
        this->setCentralWidget( plr);
        plr->show();
    }
}


void PlotWindow::save() {

    QString ff = QString( file_formats.at( saveFileFormat));
    QString fn = saveFileName + "." + ff.toLower();
    plr->save( fn, ff);
    setWindowTitle( QString( "Pari QtPlot:") + fn);
#ifndef __QPE__
    //statusBar()->message( QString( "File %1 saved" ).arg( fn), 2000 );
#endif
}


void PlotWindow::save( int id)
{
        QString ff( file_formats.at( id));
        QString s( ff + " (*." + ff.toLower() +");;All (*)");
        QString fn = QFileDialog::getSaveFileName(this, saveFileName + "." + ff,
        saveFileName + "." + ff, s);
        if ( !fn.isEmpty() )
        {
                saveFileName = fn;
                int p;
                if( (p = saveFileName.lastIndexOf( "." + ff, -1)) >=0)
                        saveFileName.truncate( p);
                saveFileFormat = id;
                save();
        }
}


#include "plotQt4.moc.cpp"
#endif // __FANCY_WIN__



//
// Implementation of the two architecture-dependent functions
// (from rect.h) requested by pari's plotting routines
//


void
rectdraw0(long *w, long *x, long *y, long lw)
{
    if (pari_daemon()) return;  // parent process returns

    pari_close();
    PARI_get_plot();

    // launch Qt window
    int argc = 1;                         // set argc = 2 for cross
    char * argv[] = { "gp", "-qws"}; // development using qvfb
#ifdef __QPE__
    QPEApplication
#else
    QApplication
#endif
        a( argc, argv);
#ifdef __FANCY_WIN__
    PlotWindow *win = new PlotWindow(w, x, y, lw);
#else
    Plotter *win = new Plotter( w, x, y, lw);
#endif
#ifdef __QPE__
    a.showMainWidget( win);
#else
    //a.setMainWidget( win);
    win->show();
#endif
    a.exec();
    exit( 0);
}

void
PARI_get_plot(void)
/* This function initialises the structure rect.h: pari_plot */
{
    if (pari_plot.init) return;      // pari_plot is already set
#ifdef __QPE__
    pari_plot.width   = 240;         // width and
    pari_plot.height  = 320;         //  height of plot window
#else
    pari_plot.width   = 400;         // width and
    pari_plot.height  = 300;         //  height of plot window
#endif
    pari_plot.hunit   = 3;           //
    pari_plot.vunit   = 3;           //
    pari_plot.fwidth  = 6;           // font width
    pari_plot.fheight = 9;           //   and height
    pari_plot.init    = 1;           // flag: pari_plot is set now!
}
