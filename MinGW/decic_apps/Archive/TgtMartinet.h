#ifndef TGTMARTINET_H
#define TGTMARTINET_H

//#include <iostream>
#include "pari.h"
#ifdef long
#  undef long
#endif
#include "GetDecics.h"

using namespace std;

  // Function prototypes
int  TgtMartinet(char*,char*,int,pari_long,pari_long,pari_long,pari_long*);
void Mart52Engine_Tgt(GEN,GEN,pari_long,pari_long,int,pari_long,pari_long,pari_long,pari_long*,ofstream&);
void Get_Pohst_Bounds_n10(double,double,double*);
void Get_Pohst_Bounds_n5(double,double,double*);
void Write_Cvec_Stats(GEN);

#endif
