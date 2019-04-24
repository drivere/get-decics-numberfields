#ifndef TGTMARTINET_H
#define TGTMARTINET_H


#include "pari.h"
#ifdef long
#  undef long
#endif

using namespace std;

  // Function prototypes
int  TgtMartinet(char*, char*, int, pari_long, pari_long, pari_long, pari_long, pari_long, pari_long, 
                 pari_long, pari_long, pari_long, pari_long*);
void Mart52Engine_Tgt(GEN, GEN, pari_long, pari_long, int, pari_long, pari_long, pari_long, pari_long, 
                      pari_long, pari_long, pari_long, pari_long, pari_long, pari_long*, ofstream&);
void testPolys(long long*, int, pari_long*, pari_long*, ofstream&);
void Get_Pohst_Bounds_n10(double, double, double*);
void Get_Pohst_Bounds_n5(double, double, double*);
void Write_Cvec_Stats(GEN);

extern "C" int polDiscTest_gpuCuda(long long*, int, char*, int, int*);
extern "C" int polDiscTest_gpuOpenCL(long long*, int, char*, int, int*);
extern "C" int polDiscTest_cpu(long long*, int, char*, int, int*);


#endif
