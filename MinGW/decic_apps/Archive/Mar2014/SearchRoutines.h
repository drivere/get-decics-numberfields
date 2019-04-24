#ifndef SEARCHROUTINES_H
#define SEARCHROUTINES_H

#include <iostream>
#include <pari.h>
#include "GetBoundedDecics.h"

using namespace std;

  // Function prototypes
int  MartinetSearch(char*,char*,int,int,long,long,long,long,long long*);
void Mart52Engine_Std(GEN,long,    int,int,long,long,long,long,long,long,long,long,float,float,float,float,int,int,long,long long*,ofstream&);
void Mart52Engine_Tgt(GEN,long,GEN,int,int,long,long,long,long,long,long,long,long,float,float,float,float,int,int,long,long long*,ofstream&);
void Get_Pohst_Bounds_n10(double,double,double*);
void Get_Pohst_Bounds_n5(double,double,double*);

#endif
