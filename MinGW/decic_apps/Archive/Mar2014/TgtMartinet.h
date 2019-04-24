#ifndef TGTMARTINET_H
#define TGTMARTINET_H

#include <iostream>
#include <pari.h>
#include "GetDecics.h"

using namespace std;

  // Function prototypes
int  TgtMartinet(char*,char*,int,long,long,long,long long*);
void Mart52Engine_Tgt(GEN,GEN,long,long,int,long,long,long,long long*,ofstream&);
void Get_Pohst_Bounds_n10(double,double,double*);
void Get_Pohst_Bounds_n5(double,double,double*);
void Write_Cvec_Stats(GEN);

#endif
