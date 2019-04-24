#ifndef SEARCHROUTINES_H
#define SEARCHROUTINES_H

#include "pari.h"
#ifdef long
#  undef long
#endif

using namespace std;

  // Function prototypes
int  MartinetSearch(char*,char*,int,int,pari_long,pari_long,pari_long,pari_long,pari_long*);
void Mart52Engine_Std(GEN,pari_long,    int,int,pari_long,pari_long,pari_long,pari_long,pari_long,pari_long,pari_long,pari_long,float,float,float,float,int,int,pari_long,pari_long*,ofstream&);
void Mart52Engine_Tgt(GEN,pari_long,GEN,int,int,pari_long,pari_long,pari_long,pari_long,pari_long,pari_long,pari_long,pari_long,float,float,float,float,int,int,pari_long,pari_long*,ofstream&);
void Get_Pohst_Bounds_n10(double,double,double*);
void Get_Pohst_Bounds_n5(double,double,double*);

#endif
