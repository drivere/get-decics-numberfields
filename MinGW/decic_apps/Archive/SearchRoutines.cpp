//******************************************************************************
//* This program finds all decic52 fields with discriminant bounded by B,      *
//* where B is hard coded at the top of the program.  Input parameters are     *
//* read from FilenameIn and the fields are written to FilenameOut.            *
//******************************************************************************

#ifdef MINGW64
  typedef unsigned long long pari_ulong;  // We want pari longs to be 8 bytes
  typedef long long pari_long;
#else
  typedef unsigned long pari_ulong;
  typedef long pari_long;
#endif

#include <string>
#include <iostream>
#include <fstream>
#include <math.h>

#ifdef _WIN32
#  include <windows.h>
#endif

#include "boinc_api.h"
#include "pari.h"
#ifdef long
#  undef long
#endif
#include "GetBoundedDecics.h"
#include "SearchRoutines.h"

//using namespace std;
using std::ifstream;
using std::ofstream;


#ifndef LONG_IS_64BIT
  #define MY_PRECISION  12
#else
  #define MY_PRECISION  7
#endif

#define MAX_PRIME 10000000  // 10 million

#define MAX_a5_VALUES_TO_DISPLAY 10


//#define DISC_BOUND   10000000000.0  // This is 10^10
#define DISC_BOUND  120000000000.0  // This is 12*10^10

  // Global variables
GEN Disc_Bound_Pari,Q,QHQ;
double Ca1_pre;


int MartinetSearch(char *FilenameIn, char *FilenameOut, int ChkPntFlag, int a5_Start_Idx,
                   pari_long a22_Start, pari_long a21_Start, pari_long a32_Start, pari_long a31_Start, pari_long *StatVec)
  {
  int  i,TgtFlag,Idx,NumVals_a5,a11,a12,r1,r2;
  pari_long dK,a21_L,a21_U,a22_L,a22_U,a32_L,a32_U,ltop;
  pari_long *a51,*a52;
  GEN  K,dLg=0,sig1w,sig2w,sig1a1,sig2a1;
  float Delta_a5, Delta_a22, Delta_a21, Delta_a32;
  string DataStr;
  char *charStr;

  fprintf(stderr, "Entering MartinetSearch routine...\n");
  pari_init(300000000,MAX_PRIME);  // Reserve 300 MB for the pari stack


  Disc_Bound_Pari = dbltor(DISC_BOUND);  // Convert to a pari real
  charStr = GENtostr(Disc_Bound_Pari);
  fprintf(stderr, "Disc Bound = %s\n",charStr);
  free(charStr);


    // Open the input file
  fprintf(stderr, "Reading file %s:\n",FilenameIn);
  ifstream infile;
  infile.open(FilenameIn);
  if(!infile)
    {
    fprintf(stderr, "Could not read file.  Aborting.\n");
    exit(1);
    }

    // Now read from the input file.

    // The 1st line is the data representing the base field K.
  getline(infile,DataStr);
  K = gp_read_str((char*)(DataStr.c_str()));
  charStr = GENtostr((GEN)K[1]);
  fprintf(stderr, "    K = %s\n",charStr);
  free(charStr);

    // The 2nd line is the targetted flag (1 means do a targettted search).
  getline(infile,DataStr);
  TgtFlag = atoi(DataStr.c_str());
  fprintf(stderr, "    TgtFlag = %d\n",TgtFlag);

    // dL is only present if TgtFlag is set.
  if(TgtFlag==1)
    {
    getline(infile,DataStr);
    dLg = gp_read_str((char*)(DataStr.c_str()));
    fprintf(stderr, "    dL = %s\n",DataStr.c_str());
    }

    // The next line is the index value for a1.
  getline(infile,DataStr);
  Idx = itos(gp_read_str((char*)(DataStr.c_str())));
  fprintf(stderr, "    a1 Index = %d\n",Idx);


  getline(infile,DataStr);
  NumVals_a5 = atoi(DataStr.c_str());
  fprintf(stderr, "    NumVals_a5 = %d\n",NumVals_a5);

  a51 = new pari_long[NumVals_a5];
  if(!a51)  { cout << "Memory allocation error for a51\n"; exit(1); }
  a52 = new pari_long[NumVals_a5];
  if(!a52)  { cout << "Memory allocation error for a52\n"; exit(1); }

  for(i=0;i<NumVals_a5;++i)
    {
    infile >> a51[i] >> a52[i];
    }

  fprintf(stderr, "    a5 values:\n");
  if(NumVals_a5<=MAX_a5_VALUES_TO_DISPLAY)
    {
    for(i=0;i<NumVals_a5;++i)
      {
      fprintf(stderr, "        %ld + %ldw\n",a51[i],a52[i]);
      }
    }
  else
    {
    fprintf(stderr, "        Output suppressed.\n");
    }

  if(NumVals_a5==1)    // Then load the limits for a22
    {
    infile >> a22_L >> a22_U;
    fprintf(stderr, "    a22_L = %ld\n",a22_L);
    fprintf(stderr, "    a22_U = %ld\n",a22_U);
    pari_long NumVals_a22 = a22_U - a22_L + 1;
    Delta_a22 = 1.0 / NumVals_a22;
    if(NumVals_a22==1)  // Then load the limits for a21
      {
      infile >> a21_L >> a21_U;
      fprintf(stderr, "    a21_L = %ld\n",a21_L);
      fprintf(stderr, "    a21_U = %ld\n",a21_U);
      pari_long NumVals_a21 = a21_U - a21_L + 1;
      Delta_a21 = 1.0 / NumVals_a21;
      if(NumVals_a21==1)  // Then load the limits for a32
        {
        infile >> a32_L;
        if(infile.eof())  // Then this is an old style WU (a32_L,a32_U are not present)
          {  // Set to extreme values.  This will allow normal limits to be assigned later.
          a32_L = -1000000000;
          a32_U =  1000000000;
          Delta_a32 = -1;
          }
        else
          {
          infile >> a32_U;
          fprintf(stderr, "    a32_L = %ld\n",a32_L);
          fprintf(stderr, "    a32_U = %ld\n",a32_U);
          pari_long NumVals_a32 = a32_U - a32_L + 1;
          Delta_a32 = 1.0 / NumVals_a32;
          }
        }
      else
        {  // Set to extreme values.  This will allow normal limits to be assigned later.
        a32_L = -1000000000;
        a32_U =  1000000000;
        Delta_a32 = -1;
        }
      }
    else  // NumVals_a22>1
      {  // Set to extreme values.  This will allow normal limits to be assigned later.
      a21_L = -1000000000;
      a21_U =  1000000000;
      Delta_a21 = -1;
      a32_L = -1000000000;
      a32_U =  1000000000;
      Delta_a32 = -1;
      }
    }
  else  // NumVals_a5>1
    {  // Set to extreme values.  This will allow normal limits to be assigned later.
    a22_L = -1000000000;
    a22_U =  1000000000;
    Delta_a22 = -1;
    a21_L = -1000000000;
    a21_U =  1000000000;
    Delta_a21 = -1;
    a32_L = -1000000000;
    a32_U =  1000000000;
    Delta_a32 = -1;
    }

    // Save off initial values from file
  pari_long a21L_Orig = a21_L;
  pari_long a22L_Orig = a22_L;
  pari_long a32L_Orig = a32_L;


    // That is all the inputs, so close the input file.
  infile.close();


  Delta_a5  = 1.0 / NumVals_a5;


    // Save the current top of the pari stack.
  ltop = avma;


  r1 = itos(gmael(K,2,1));  // K[2]=[r1,r2]
  r2 = itos(gmael(K,2,2));
  dK = abs(itos((GEN)K[3]));
  fprintf(stderr, "|dK| = %ld\n",dK);
  fprintf(stderr, "Signature = [%d,%d]\n",r1,r2);

    // Get the embeddings applied to the integral basis (as complex numbers).
    // Here sig1w[i] = sig1 applied to w_i.  The others are similarly defined.
  sig1w = cgetg(3,t_VEC);
  sig2w = cgetg(3,t_VEC);
  for(i=1;i<=2;++i)
    {       // Note: K[5][1]=[[sig_i(w_j)]]
    sig1w[i] = (pari_long)gmael4(K,5,1,i,1);  // This is sig1(w_i)
    if(r1==2)  sig2w[i] = (pari_long)gmael4(K,5,1,i,2);  // This is sig2(w_i)
    else  sig2w[i] = (pari_long)gconj((GEN)sig1w[i]);
    }
  //fprintf(stderr, "sig1w = %s\n",GENtostr(sig1w));
  //fprintf(stderr, "sig2w = %s\n",GENtostr(sig2w));


    // Compute the 1st part of Ca1 bound.
  a12 = (Idx-1)%3;
  a11 = (Idx-a12-1)/3;
  if(a11==2 && a12==2 && (dK%4)!=0)  // a1=2+2w and 4 does not divide dK
    {
    a11 = -1;
    sig1a1 = gadd( gmulsg(-1,(GEN)sig1w[1]),gmulsg(a12,(GEN)sig1w[2]) );
    sig2a1 = gadd( gmulsg(-1,(GEN)sig2w[1]),gmulsg(a12,(GEN)sig2w[2]) );
    }
  else
    {
    sig1a1 = gadd( gmulsg(a11,(GEN)sig1w[1]),gmulsg(a12,(GEN)sig1w[2]) );
    sig2a1 = gadd( gmulsg(a11,(GEN)sig2w[1]),gmulsg(a12,(GEN)sig2w[2]) );
    }
  Ca1_pre = ( gtodouble(gsqr(gabs(sig1a1,DEFAULTPREC))) + 
              gtodouble(gsqr(gabs(sig2a1,DEFAULTPREC))) )/5.0;


  fprintf(stderr, "a11 = %d\n",a11);
  fprintf(stderr, "a12 = %d\n",a12);
  charStr = GENtostr(sig1a1);
  fprintf(stderr, "sig1a1 = %s\n",charStr);
  free(charStr);
  charStr = GENtostr(sig2a1);
  fprintf(stderr, "sig2a1 = %s\n",charStr);
  free(charStr);
  fprintf(stderr, "Ca1_pre = %lf\n",Ca1_pre);


    // Create the Q matrix.
  Q = cgetg(3,t_MAT);
  Q[1] = (pari_long)mkcol2((GEN)sig1w[1],(GEN)sig2w[1]);
  Q[2] = (pari_long)mkcol2((GEN)sig1w[2],(GEN)sig2w[2]);
  Q = gerepilecopy(ltop,Q);

    // Compute QHQ
  ltop = avma;
  QHQ = gmul(gconj(gtrans(Q)),Q);
  QHQ = gerepilecopy(ltop,QHQ);

  //fprintf(stderr, "  Q = %s\n",GENtostr(Q));
  //fprintf(stderr, "  QHQ = %s\n",GENtostr(QHQ));

    // Open the output file for appending.
  fprintf(stderr, "Opening output file %s\n",FilenameOut);
  ofstream outfile;
  outfile.open(FilenameOut,ios::app);
  if(!outfile)
    {
    fprintf(stderr, "Could not open output file.  Aborting.\n");
    exit(1);
    }

  fprintf(stderr, "Now starting the Martinet search:\n");

  for(i=a5_Start_Idx;i<=NumVals_a5-1;++i)
    {
    fprintf(stderr, "\nDoing case a5 = %ld + %ldw...\n",a51[i],a52[i]);

      // This will reset the loop counter after the first pass
    if(ChkPntFlag)
      {
      a22_L = a22_Start;
      a21_L = a21_Start;
      a32_L = a32_Start;
      }
    else
      {
      a22_L = a22L_Orig;
      a21_L = a21L_Orig;
      a32_L = a32L_Orig;
      }

    if(TgtFlag==1)
      {
      Mart52Engine_Tgt(K, dK, dLg, a11, a12, a51[i], a52[i], a22_L, a22_U, a21_L, a21_U, a32_L, a32_U, 
          Delta_a5, Delta_a22, Delta_a21, Delta_a32, ChkPntFlag, i, a31_Start, StatVec, outfile);
      }
    else
      {
      Mart52Engine_Std(K, dK, a11, a12, a51[i], a52[i], a22_L, a22_U, a21_L, a21_U, a32_L, a32_U, 
          Delta_a5, Delta_a22, Delta_a21, Delta_a32, ChkPntFlag, i, a31_Start, StatVec, outfile);
      }

      // Reset the check point flag after the first pass
    ChkPntFlag = 0;

    }

  fprintf(stderr, "The search has finished.\n");


  pari_long PolyCount   = StatVec[0];
  pari_long Test1_Count = StatVec[1];
  pari_long Test2_Count = StatVec[2];
  pari_long Test3_Count = StatVec[3];
  pari_long Time_sec    = StatVec[4];

  float Percent1 = 0;
  float Percent2 = 0;
  float Percent3 = 0;

  if(TgtFlag==1)
    {
    if(PolyCount!=0)    Percent1 = 100.0*Test1_Count/PolyCount;
    if(Test1_Count!=0)  Percent2 = 100.0*Test2_Count/Test1_Count;
    if(Test2_Count!=0)  Percent3 = 100.0*Test3_Count/Test2_Count;
    outfile << "#   The search is complete. Stats:\n";
    outfile << "#   Inspected " << PolyCount << " polynomials.\n";
    outfile << "#   Num Polys passing PolDisc test = " << Test1_Count << " (" << Percent1 << "%).\n";
    outfile << "#   Num Polys passing irreducibility test = " << Test2_Count << " (" << Percent2 << "%).\n";
    outfile << "#   Num Polys passing field disc test = " << Test3_Count << " (" << Percent3 << "%).\n";
    }
  else
    {
    if(PolyCount!=0)    Percent2 = 100.0*Test2_Count/PolyCount;
    if(Test2_Count!=0)  Percent3 = 100.0*Test3_Count/Test2_Count;
    outfile << "#   The search is complete. Stats:\n";
    outfile << "#   Inspected " << PolyCount << " polynomials.\n";
    outfile << "#   Num Polys passing irreducibility test = " << Test2_Count << " (" << Percent2 << "%).\n";
    outfile << "#   Num Polys passing discriminant bound = " << Test3_Count << " (" << Percent3 << "%).\n";
    }
  outfile << "#   Elapsed Time = " << Time_sec << " (sec)\n";
  outfile.flush();

  outfile.close();

  pari_close();

  delete a51;
  delete a52;

  return 0;

  }  // End of MartinetSearch





//******************************************************************************
//* This subroutine does a standard Martinet search.  It assumes that the      *
//* following global variables have been precomputed: Q, QHQ, Ca1_pre.         *
//******************************************************************************

void Mart52Engine_Std(GEN K, pari_long dK, int a11, int a12, pari_long a51, pari_long a52, pari_long a22_L0, pari_long a22_U0, 
                      pari_long a21_L0, pari_long a21_U0, pari_long a32_L0, pari_long a32_U0, float Delta_a5, float Delta_a22, 
                      float Delta_a21, float Delta_a32, int ChkPntFlag, int a5_Idx, pari_long a31_Start,
                      pari_long *StatVec, ofstream& outfile)
  {
  pari_long ltop,ltop1,ltop2,ltop3;
  pari_long PolyCount,Test1_Count,Test2_Count,Test3_Count,Time_sec;
  pari_long a1sq_1,a1sq_2,a1cb_1,a1cb_2,a1_4th_1,a1_4th_2;
  pari_long a2sq_1,a2sq_2,a1a2_1,a1a2_2,a1sq_a2_1,a1sq_a2_2,a1a3_1,a1a3_2;
  pari_long a21,a22,a21sq,a22sq,a21a22;
  pari_long a31,a32,a31sq,a32sq,a31a32;
  pari_long a41,a42,a41sq,a42sq,a41a42;
  pari_long a51sq,a52sq,a51a52;
  pari_long a21_L,a21_U,a22_L,a22_U,a31_L,a31_U,a32_L,a32_U,a41_L,a41_U,a42_L,a42_U;
  pari_long b1,b2,b1b,b2b,b1c,b2c,s22,s32,s42;
  pari_long s[10],Sum,Sum3,Sum4,bb1,bb2,bb3,bb4,bb5,bb6,bb7,bb8,bb9,bb10;
  pari_long bb2_L,bb2_U,bb3_L,bb3_U,bb4_L,bb4_U,bb5_L,bb5_U,bb6_L,bb6_U,bb7_L,bb7_U;
  pari_long bb8_L,bb8_U,bb9_L,bb9_U,bb9_L0,bb9_U0;
  pari_long bb2_pre,bb3_pre,bb4_pre,bb5_pre,bb6_pre,bb7_pre,bb8_pre;
  pari_long bb4_pre2,bb5_pre2,bb6_pre2,bvec_pre_1,bvec_pre_2;
  pari_long wsq_1,wsq_2,Tr_w,Nm_w,r2;
  double lambda1,lambda2,lambda1c,lambda2c;
  double tq[5],tqc[5],t[10],t11,t12,t22,bb8_Upre,tmpdbl;
  double Bnd2,Ca1,B1,B_s2,B_s3,B_s4,B_a4,B_a4c,a32_pre,a42_pre,B_s2_sqrt;
  double s1a2_mag,s2a2_mag,s1a3_mag,s2a3_mag,s1a4_mag,s2a4_mag;
  double s1a5_mag,s2a5_mag,s1a5_mag_sq,s2a5_mag_sq,s1a5_mag_2_5ths,s2a5_mag_2_5ths;
  GEN  w_alg,w_sq,w,wc,f_L,PolDisc;
  char *OutStr;


  // Start the pari timer
  timer();

  ltop = avma;

  PolyCount   = StatVec[0];
  Test1_Count = StatVec[1];
  Test2_Count = StatVec[2];
  Test3_Count = StatVec[3];
  Time_sec    = StatVec[4];


  pari_long NumVals_a5  = (pari_long)floor(1.0/Delta_a5  + .5);
  float a5_frac_done = Delta_a5*a5_Idx;

  Bnd2 = 2.0*pow(DISC_BOUND/(25.0*dK),.125);   // 2nd part of Martinet bound

  if(NumVals_a5<=MAX_a5_VALUES_TO_DISPLAY)
    {
    fprintf(stderr, "  2nd part of Martinet bound = %lf.\n",Bnd2);
    }

  t11 = sqrt(gtodouble(real_i(gmael(QHQ,1,1))));
  t12 = gtodouble(real_i(gmael(QHQ,2,1)))/t11;
  t22 = sqrt(gtodouble(real_i(gmael(QHQ,2,2)))-t12*t12);


    // Get w and the components of w^2.
    // Also compute the trace and norm of w.
  w_alg = basistoalg(K,mkcol2(gen_0,gen_1));
  w_sq  = algtobasis(K,gsqr(w_alg));
  wsq_1 = itos((GEN)w_sq[1]);
  wsq_2 = itos((GEN)w_sq[2]);
  w  = gmael(Q,2,1);  // row 1, col 2   Note: these are complex numbers.
  wc = gmael(Q,2,2);  // row 2, col 2
  Tr_w = (pari_long)floor(gtodouble(real_i(gadd(w,wc)))+.5);
  Nm_w = (pari_long)floor(gtodouble(real_i(gmul(w,wc)))+.5);


    // Compute the parameters lambda1 and lambda2
  r2 = itos(gmael(K,2,2));  // K[2]=[r1,r2]
  if(r2==1)  // Then the subfield is complex. [ie K=Q(sqrt(m)) where m<0]
    {
    lambda1  = (double)Tr_w;
    lambda2  = (double)Nm_w;
    lambda1c = lambda1;
    lambda2c = lambda2;
    }
  else  // w and wc are real (but stored as complex)
    {
    lambda1  = 2.0*gtodouble(real_i(w));
    lambda2  = gtodouble(real_i(gsqr(w)));
    lambda1c = 2.0*gtodouble(real_i(wc));
    lambda2c = gtodouble(real_i(gsqr(wc)));
    }

  a1sq_1 = a11*a11 + a12*a12*wsq_1;
  a1sq_2 = 2*a11*a12 + a12*a12*wsq_2;

  a1cb_1 = a11*a1sq_1 + a12*a1sq_2*wsq_1;
  a1cb_2 = a11*a1sq_2 + a12*a1sq_1 + a12*a1sq_2*wsq_2;

  a1_4th_1 = a11*a1cb_1 + a12*a1cb_2*wsq_1;
  a1_4th_2 = a11*a1cb_2 + a12*a1cb_1 + a12*a1cb_2*wsq_2;

  Ca1 = Ca1_pre + Bnd2;

  if(NumVals_a5<=MAX_a5_VALUES_TO_DISPLAY)
    {
    fprintf(stderr, "  Martinet bound = %lf.\n",Ca1);
    }

    // Compute bound on s2
  if(r2==1)  B_s2 = .5*Ca1*Ca1;
  else       B_s2 = Ca1*Ca1;
  B_s2_sqrt = sqrt(B_s2);

  b1 = a1sq_1;
  b2 = a1sq_2;

  bb1  = 2*a11 + a12*Tr_w;
  s[1] = -bb1;
  bb2_L = (pari_long) ceil(.5*(bb1*bb1-Ca1));
  bb2_U = (pari_long)floor(.5*(.8*bb1*bb1 + Ca1));
  bb2_pre = a11*a11 + a11*a12*Tr_w + a12*a12*Nm_w;

  a51sq  = a51*a51;
  a52sq  = a52*a52;
  a51a52 = a51*a52;
  s1a5_mag_sq = a51sq + lambda1*a51a52  + lambda2*a52sq;
  s2a5_mag_sq = a51sq + lambda1c*a51a52 + lambda2c*a52sq;
  s1a5_mag_2_5ths = pow(s1a5_mag_sq,.2);
  s2a5_mag_2_5ths = pow(s2a5_mag_sq,.2);
  s1a5_mag = sqrt(s1a5_mag_sq);
  s2a5_mag = sqrt(s2a5_mag_sq);

  bb5_pre = 2*a51 + a52*Tr_w;  // a5 + a5conj
  bb6_pre = 2*a11*a51 + (a11*a52+a12*a51)*Tr_w + 2*a12*a52*Nm_w;
  bb10 = a51sq + a51a52*Tr_w + a52sq*Nm_w;

    // Compute bound on s3, s4, and s_{-1} for relative quintic
  if(r2==1)
    {
    Get_Pohst_Bounds_n5(.5*Ca1,s1a5_mag,tq);
    tqc[1] = tq[1]; tqc[3] = tq[3]; tqc[4] = tq[4];
    B_s3 = 2.0*tq[3]*tq[3];
    B_s4 = 2.0*tq[4]*tq[4];
    }
  else
    {
    Get_Pohst_Bounds_n5(Ca1 - 5.0*s2a5_mag_2_5ths,s1a5_mag,tq);
    Get_Pohst_Bounds_n5(Ca1 - 5.0*s1a5_mag_2_5ths,s2a5_mag,tqc);
    B_s3 = tq[3]*tq[3] + tqc[3]*tqc[3];
    B_s4 = tq[4]*tq[4] + tqc[4]*tqc[4];
    }

  B_a4 = tq[1]*s1a5_mag;
  if(B_a4>tq[4])  B_a4 = tq[4];
  B_a4c = tqc[1]*s2a5_mag;
  if(B_a4c>tqc[4])  B_a4c = tqc[4];

  a32_pre = sqrt(B_s3)/t22;
  a42_pre = sqrt(B_s4)/t22;

    // Compute bounds on sk for decic (k=3,4,5,6,7,8,9,-1,-2).
  Get_Pohst_Bounds_n10(Ca1,abs(bb10),t);  // t[k]  is bound on sk when k>0.
                                          // t[-k] is bound on sk when k<0.

  bb9_U0 = (pari_long)floor(abs(bb10)*t[1]);
  bb9_L0 = -bb9_U0;
  bb8_Upre = .5*abs(bb10)*t[2];

  a22_L = (pari_long) ceil(.5*(b2-B_s2_sqrt/t22));
  a22_U = (pari_long)floor(.5*(b2+B_s2_sqrt/t22));

    // A negative Delta_a22 means it was not computed earlier.
    // Compute it from the pre-checkpoint values.
  if(Delta_a22<0)  Delta_a22 = 1.0 / (a22_U - a22_L + 1.0);

    // Modify a22 limits based on initial inputs
  a22_L = max(a22_L,a22_L0);
  a22_U = min(a22_U,a22_U0);

  pari_long NumVals_a22 = (pari_long)floor(1.0/Delta_a22 + .5);
  pari_long a22_L_Orig  = a22_U - NumVals_a22 + 1;


  if(NumVals_a5<=MAX_a5_VALUES_TO_DISPLAY)
    {
    fprintf(stderr, "  a22_L = %ld.\n",a22_L);
    fprintf(stderr, "  a22_U = %ld.\n",a22_U);
    }

  for(a22=a22_L;a22<=a22_U;++a22)
    {
    float a22_frac_done = Delta_a22*(a22-a22_L_Orig);

    if(NumVals_a5<=MAX_a5_VALUES_TO_DISPLAY)
      {
      fprintf(stderr, "  a22 = %ld.\n",a22);
      }

    s22 = b2-2*a22;
    B1 = sqrt(B_s2-t22*t22*s22*s22);
    a21_L = (pari_long) ceil(.5*(b1+(-B1+t12*s22)/t11));
    a21_U = (pari_long)floor(.5*(b1+( B1+t12*s22)/t11));

      // If there is more than 1 a22, then Delta_a21 will change for each a22.
      // When there is only 1 a22, Delta_a21 is computed externally, so don't change it.
    if(NumVals_a22>1 || Delta_a21<0)  Delta_a21 = 1.0 / (a21_U - a21_L + 1.0);

      // Modify a21 limits based on initial inputs (checkpointed values)
    a21_L = max(a21_L,a21_L0);
    a21_U = min(a21_U,a21_U0);

    pari_long NumVals_a21 = (pari_long)floor(1.0/Delta_a21 + .5);
    pari_long a21_L_Orig  = a21_U - NumVals_a21 + 1;

      // This will reset the a21 starting value after the first pass
    if(ChkPntFlag==0)  a21_L = a21_L_Orig;

    if(NumVals_a5==1)
      {
      fprintf(stderr, "    a21_L = %ld.\n",a21_L);
      fprintf(stderr, "    a21_U = %ld.\n",a21_U);
      }

    ltop3 = avma;

    for(a21=a21_L;a21<=a21_U;++a21)
      {
      float a21_frac_done = Delta_a21*(a21-a21_L_Orig);

      if(NumVals_a5==1 && NumVals_a22==1)  fprintf(stderr, "    a21 = %ld.\n",a21);

      a21sq  = a21*a21;
      a22sq  = a22*a22;
      a21a22 = a21*a22;
      s1a2_mag = sqrt(a21sq + lambda1*a21a22  + lambda2*a22sq);
      s2a2_mag = sqrt(a21sq + lambda1c*a21a22 + lambda2c*a22sq);

      if( (s1a2_mag+s2a2_mag) <= 2.0*Ca1 )
        {

        bb2 = bb2_pre + 2*a21 + a22*Tr_w;

        if(bb2>=bb2_L && bb2<=bb2_U)
          {
          a2sq_1 = a21sq + a22sq*wsq_1;
          a2sq_2 = 2*a21a22 + a22sq*wsq_2;
          a1a2_1 = a11*a21 + a12*a22*wsq_1;
          a1a2_2 = a11*a22 + a12*a21 + a12*a22*wsq_2;
          a1sq_a2_1 = a1sq_1*a21 + a1sq_2*a22*wsq_1;
          a1sq_a2_2 = a1sq_1*a22 + a1sq_2*a21 + a1sq_2*a22*wsq_2;

            // Compute bvec_pre = a1^4 - 4*a1^2*a2 + 2*a2^2
          bvec_pre_1 = a1_4th_1 - 4*a1sq_a2_1 + 2*a2sq_1;
          bvec_pre_2 = a1_4th_2 - 4*a1sq_a2_2 + 2*a2sq_2;

            // Compute [b1b,b2b] = 3*a1*a2-a1^3
          b1b = 3*a1a2_1 - a1cb_1;
          b2b = 3*a1a2_2 - a1cb_2;

          s[2] = bb1*bb1 - 2*bb2;

          bb3_pre = 2*a11*a21 + (a11*a22+a12*a21)*Tr_w + 2*a12*a22*Nm_w;
          bb4_pre = a21sq + a21a22*Tr_w + a22sq*Nm_w;
          bb7_pre = 2*a21*a51 + (a21*a52+a22*a51)*Tr_w + 2*a22*a52*Nm_w;

            // Compute bounds for bb3
          Sum3 = bb2*s[1] + bb1*s[2];
          bb3_L = (pari_long)ceil((-t[3] - Sum3)/3.0);
          bb3_U = (pari_long)floor((t[3] - Sum3)/3.0);


          a32_L = (pari_long) ceil( (b2b-a32_pre) / 3.0 );
          a32_U = (pari_long)floor( (b2b+a32_pre) / 3.0 );


            // If there is more than 1 a21, then Delta_a32 will change for each a21.
            // When there is only 1 a21, Delta_a32 is computed externally, so don't change it.
          if(NumVals_a21>1 || Delta_a32<0)  Delta_a32 = 1.0 / (a32_U - a32_L + 1.0);

            // Modify a32 limits based on initial inputs (checkpointed values)
          a32_L = max(a32_L,a32_L0);
          a32_U = min(a32_U,a32_U0);

          pari_long NumVals_a32 = (pari_long)floor(1.0/Delta_a32 + .5);
          pari_long a32_L_Orig  = a32_U - NumVals_a32 + 1;

            // This will reset the a32 starting value after the first looping pass
          if(ChkPntFlag==0)  a32_L = a32_L_Orig;

          if(NumVals_a5==1 && NumVals_a22==1)
            {
            fprintf(stderr, "      a32_L = %ld.\n",a32_L);
            fprintf(stderr, "      a32_U = %ld.\n",a32_U);
            }


          for(a32=a32_L;a32<=a32_U;++a32)
            {
            float a32_frac_done = Delta_a32*(a32-a32_L_Orig);

            //fprintf(stderr, "        a32 = %ld.\n",a32);
            s32 = b2b-3*a32;
            B1 = sqrt(B_s3-t22*t22*s32*s32);
            a31_L = (pari_long) ceil( (b1b+(-B1+t12*s32)/t11) / 3.0 );
            a31_U = (pari_long)floor( (b1b+( B1+t12*s32)/t11) / 3.0 );

            pari_long NumVals_a31 = a31_U-a31_L+1;
            if(NumVals_a31<1) NumVals_a31 = 1;
            pari_long a31_L_Orig = a31_L;

            // If ChkPntFlag is set then this case has been previously checkpointed,
            // so use the checkpoint value for a31.  But only do this once!
            if(ChkPntFlag)
              {
              a31_L = max(a31_L,a31_Start);
              ChkPntFlag = 0;
              }

            //fprintf(stderr, "            a31_L = %ld.\n",a31_L);
            //fprintf(stderr, "            a31_U = %ld.\n",a31_U);

            ltop2 = avma;

            for(a31=a31_L;a31<=a31_U;++a31)
              {
              //fprintf(stderr, "              a31 = %ld.\n",a31);
              a31sq  = a31*a31;
              a32sq  = a32*a32;
              a31a32 = a31*a32;
              s1a3_mag = sqrt(a31sq + lambda1*a31a32  + lambda2*a32sq);
              s2a3_mag = sqrt(a31sq + lambda1c*a31a32 + lambda2c*a32sq);

              if( (s1a3_mag<=2*tq[3]) && (s2a3_mag<=2*tqc[3]) )
                {

                bb3 = bb3_pre + 2*a31 + a32*Tr_w;

                if(bb3>=bb3_L && bb3<=bb3_U)
                  {
                  a1a3_1 = a11*a31 + a12*a32*wsq_1;
                  a1a3_2 = a11*a32 + a12*a31 + a12*a32*wsq_2;

                    // Set [b1c,b2c] = a1^4 + 4*a1*a3 - 4*a1^2*a2 + 2*a2^2
                  b1c = 4*a1a3_1 + bvec_pre_1;
                  b2c = 4*a1a3_2 + bvec_pre_2;
                  a42_L = (pari_long) ceil( (b2c-a42_pre) / 4.0 );
                  a42_U = (pari_long)floor( (b2c+a42_pre) / 4.0 );

                  //fprintf(stderr, "                a42_L = %ld.\n",a42_L);
                  //fprintf(stderr, "                a42_U = %ld.\n",a42_U);

                  bb4_pre2 = bb4_pre + 2*a11*a31 + 
                             (a11*a32+a12*a31)*Tr_w + 2*a12*a32*Nm_w;
                  bb5_pre2 = bb5_pre + 2*a21*a31 + 
                             (a21*a32+a22*a31)*Tr_w + 2*a22*a32*Nm_w;
                  bb6_pre2 = bb6_pre + a31sq + a31a32*Tr_w + a32sq*Nm_w;
                  bb8_pre  = 2*a31*a51 + (a31*a52+a32*a51)*Tr_w + 2*a32*a52*Nm_w;

                    // Compute bounds for bb4
                  s[3] = -3*bb3 - Sum3;
                  Sum4 = bb3*s[1] + bb2*s[2] + bb1*s[3];
                  bb4_L = (pari_long)ceil((-t[4] - Sum4)/4.0);
                  bb4_U = (pari_long)floor((t[4] - Sum4)/4.0);

                  for(a42=a42_L;a42<=a42_U;++a42)
                    {
                    //fprintf(stderr, "                  a42 = %ld.\n",a42);
                    s42 = b2c-4*a42;
                    B1 = sqrt(B_s4-t22*t22*s42*s42);
                    a41_L = (pari_long) ceil( (b1c+(-B1+t12*s42)/t11) / 4.0 );
                    a41_U = (pari_long)floor( (b1c+( B1+t12*s42)/t11) / 4.0 );
                    //fprintf(stderr, "                    a41_L = %ld.\n",a41_L);
                    //fprintf(stderr, "                    a41_U = %ld.\n",a41_U);
                    ltop1 = avma;
                    for(a41=a41_L;a41<=a41_U;++a41)
                      {
                      //fprintf(stderr, "                      a41 = %ld.\n",a41);
                      a41sq  = a41*a41;
                      a42sq  = a42*a42;
                      a41a42 = a41*a42;
                      s1a4_mag = sqrt(a41sq + lambda1*a41a42  + lambda2*a42sq);
                      s2a4_mag = sqrt(a41sq + lambda1c*a41a42 + lambda2c*a42sq);

                      if( (s1a4_mag<=B_a4) && (s2a4_mag<=B_a4c) )
                        {
                        bb9 = 2*a41*a51 + (a41*a52+a42*a51)*Tr_w + 2*a42*a52*Nm_w;
                        if(bb9>=bb9_L0 && bb9<=bb9_U0)
                          {
                          bb4 = bb4_pre2 + 2*a41 + a42*Tr_w;
                          if(bb4>=bb4_L && bb4<=bb4_U)
                            {
                            bb5 = bb5_pre2 + 2*a11*a41 + 
                                  (a11*a42+a12*a41)*Tr_w + 2*a12*a42*Nm_w;
                            s[4] = -4*bb4 - Sum4;
                            Sum = bb4*s[1] + bb3*s[2] + bb2*s[3] + bb1*s[4];
                            bb5_L = (pari_long)ceil((-t[5] - Sum)/5.0);
                            bb5_U = (pari_long)floor((t[5] - Sum)/5.0);

                            if(bb5>=bb5_L && bb5<=bb5_U)
                              {
                              bb6 = bb6_pre2 + 2*a21*a41 + 
                                    (a21*a42+a22*a41)*Tr_w + 2*a22*a42*Nm_w;
                              s[5] = -5*bb5 - Sum;
                              Sum = bb5*s[1] + bb4*s[2] + bb3*s[3] + bb2*s[4] + bb1*s[5];
                              bb6_L = (pari_long)ceil((-t[6] - Sum)/6.0);
                              bb6_U = (pari_long)floor((t[6] - Sum)/6.0);
                              if(bb6>=bb6_L && bb6<=bb6_U)
                                {
                                bb7 = bb7_pre + 2*a31*a41 + 
                                      (a31*a42+a32*a41)*Tr_w + 2*a32*a42*Nm_w;
                                s[6] = -6*bb6 - Sum;
                                Sum = bb6*s[1] + bb5*s[2] + bb4*s[3] + bb3*s[4] + 
                                      bb2*s[5] + bb1*s[6];
                                bb7_L = (pari_long)ceil((-t[7] - Sum)/7.0);
                                bb7_U = (pari_long)floor((t[7] - Sum)/7.0);
                                if(bb7>=bb7_L && bb7<=bb7_U)
                                  {
                                  bb8 = bb8_pre + a41sq + a41a42*Tr_w + a42sq*Nm_w;
                                  s[7] = -7*bb7 - Sum;
                                  Sum = bb7*s[1] + bb6*s[2] + bb5*s[3] + bb4*s[4] + 
                                        bb3*s[5] + bb2*s[6] + bb1*s[7];
                                  bb8_L = (pari_long)ceil((-t[8] - Sum)/8.0);
                                  bb8_U = (pari_long)floor((t[8] - Sum)/8.0);
                                  if(bb8>=bb8_L && bb8<=bb8_U)
                                    {
                                    s[8] = -8*bb8 - Sum;
                                    Sum = bb8*s[1] + bb7*s[2] + bb6*s[3] + bb5*s[4] + 
                                          bb4*s[5] + bb3*s[6] + bb2*s[7] + bb1*s[8];
                                    bb9_L = (pari_long)ceil((-t[9] - Sum)/9.0);
                                    bb9_U = (pari_long)floor((t[9] - Sum)/9.0);
                                    if(bb9>=bb9_L && bb9<=bb9_U)
                                      {
                                      tmpdbl = .5*bb9*bb9/bb10;
                                      bb8_L = (pari_long) ceil(tmpdbl - bb8_Upre);
                                      bb8_U = (pari_long)floor(tmpdbl + bb8_Upre);
                                      if(bb8>=bb8_L && bb8<=bb8_U)
                                        {
                                        ++PolyCount;
                                        f_L = mkpoln(11,gen_1,stoi(bb1),stoi(bb2),stoi(bb3),
                                                    stoi(bb4),stoi(bb5),stoi(bb6),stoi(bb7),
                                                    stoi(bb8),stoi(bb9),stoi(bb10));

                                        PolDisc = discsr(f_L);

                                          // check if PolDisc is zero.
                                        if(!gcmp0(PolDisc))  // Then PolDisc is nonzero
                                          {
                                            // check if f_L is irreducible:
                                          if(isirreducible(f_L))
                                            {
                                            ++Test2_Count;

//fprintf(stderr, "f_L = %s\n",GENtostr(f_L));
//fprintf(stderr, "PolDisc = %s\n",GENtostr(PolDisc));
//GEN TestVal1 = factor(PolDisc);
//fprintf(stderr, "Factored PolDisc = %s\n",GENtostr(TestVal1));
//GEN TestVal2 = discf(f_L);
//fprintf(stderr, "Field Disc = %s\n",GENtostr(TestVal2));

                                              // Check if field discriminant is less than or equal to the bound
                                            //if( gcmp(gabs(discf(f_L),MY_PRECISION),Disc_Bound_Pari)<=0 )
                                            if( gcmp(gabs(discf(f_L),BIGDEFAULTPREC),Disc_Bound_Pari)<=0 )
                                              {
                                              ++Test3_Count;
                                              OutStr = GENtostr(f_L);
                                              outfile << OutStr << "\n";
                                              outfile.flush();
                                              free(OutStr);
                                              }
                                            }
                                          }  // Matches:  if(!gcmp0(PolDisc))
                                        }  // Second bb8 test
                                      }  // Second bb9 test
                                    }  // First bb8 test
                                  }  // bb7 test
                                }  // bb6 test
                              }  // bb5 test
                            }  //bb4 test
                          }  // First bb9 test
                        }  // Matches: if( (s1a4_mag<=B_a4) && (s2a4_mag<=B_a4c) )
                      avma = ltop1;
                      }  // End of loop on a41
                    }  // End of loop on a42
                  }  // bb3 test
                }  // Matches: if( (s1a3_mag<=2*tq[3]) && (s2a3_mag<=2*tqc[3]) )

                // Do checkpointing
              if(boinc_time_to_checkpoint())
                {
                // Note: timer() returns elapsed time in milliseconds since the last call to timer
                Time_sec = Time_sec + (pari_long)floor(timer()/1000.0 + .5);
                int retval = do_checkpoint(a5_Idx,a22,a21,a32,a31+1,PolyCount,Test1_Count,Test2_Count,Test3_Count,Time_sec);
                if(retval)
                  {
                  fprintf(stderr, "Checkpoint failed!\n");
                  exit(retval);
                  }
                boinc_checkpoint_completed();
                }

//fprintf(stderr, "Q = %s\n",GENtostr(Q));
//fprintf(stderr, "QHQ = %s\n",GENtostr(QHQ));
//fprintf(stderr, "Disc Bound = %s\n",GENtostr(Disc_Bound_Pari));
//fprintf(stderr, "ChkPntFlag = %d\n",ChkPntFlag);
//fprintf(stderr, "a32 = %ld\n",a32);
//fprintf(stderr, "a32_L = %ld\n",a32_L);
//fprintf(stderr, "a32_U = %ld\n",a32_U);
//fprintf(stderr, "a32_Start = %ld\n",a32_Start);
//fprintf(stderr, "a21_frac_done = %f\n",a21_frac_done);
//fprintf(stderr, "Delta_a21 = %f\n",Delta_a21);
//fprintf(stderr, "a21_L_Orig = %ld\n",a21_L_Orig);
//fprintf(stderr, "a32_L_Orig = %ld\n",a32_L_Orig);
//fprintf(stderr, "NumVals_a21 = %ld\n",NumVals_a21);
//fprintf(stderr, "NumVals_a32 = %ld\n",NumVals_a32);
//fprintf(stderr, "PolyCount = %ld\n",PolyCount);
//fprintf(stderr, "Test1_Count = %ld\n",Test1_Count);
//fprintf(stderr, "Test2_Count = %ld\n",Test2_Count);
//fprintf(stderr, "Test3_Count = %ld\n",Test3_Count);

                // Determine fraction complete for the progress bar
              float a31_frac_done = (a31-a31_L_Orig+1.0)/NumVals_a31;
              float Frac_Done = a5_frac_done + Delta_a5*
                    (a22_frac_done + Delta_a22*
                    (a21_frac_done + Delta_a21*
                    (a32_frac_done + Delta_a32*a31_frac_done)));
              boinc_fraction_done(Frac_Done);

//fprintf(stderr, "a32_frac_done = %f\n",a32_frac_done);
//fprintf(stderr, "fraction complete = %f\n", Frac_Done);


              avma = ltop2;
              }  // End of loop on a31
            }  // End of loop on a32
          }  // Matches: if(bb2>=bb2_L && bb2<=bb2_U)
        }  // Matches: if( (s1a2_mag+s2a2_mag) <= 2.0*Ca1 )
      avma = ltop3;
      }  // End of loop on a21
    }  // End of loop on a22


  // Update the time once more before exiting
  Time_sec = Time_sec + (pari_long)floor(timer()/1000.0 + .5);

  StatVec[0] = PolyCount;
  StatVec[1] = Test1_Count;
  StatVec[2] = Test2_Count;
  StatVec[3] = Test3_Count;
  StatVec[4] = Time_sec;

  avma = ltop;  // Reset pointer to top of pari stack

  }





//******************************************************************************
//* This subroutine does a standard Martinet search, but targets a specific    *
//* value for dL.  It assumes that the following global variables have been    *
//* precomputed: Q, QHQ, Ca1_pre.                                              *
//******************************************************************************

void Mart52Engine_Tgt(GEN K, pari_long dK, GEN dLg, int a11, int a12, pari_long a51, pari_long a52, pari_long a22_L0,
                      pari_long a22_U0, pari_long a21_L0, pari_long a21_U0, pari_long a32_L0, pari_long a32_U0, float Delta_a5, 
                      float Delta_a22, float Delta_a21, float Delta_a32, int ChkPntFlag, int a5_Idx, 
                      pari_long a31_Start, pari_long *StatVec, ofstream& outfile)
  {
  pari_long ltop,ltop1,ltop2,ltop3;
  pari_long PolyCount,Test1_Count,Test2_Count,Test3_Count,Time_sec;
  pari_long a1sq_1,a1sq_2,a1cb_1,a1cb_2,a1_4th_1,a1_4th_2;
  pari_long a2sq_1,a2sq_2,a1a2_1,a1a2_2,a1sq_a2_1,a1sq_a2_2,a1a3_1,a1a3_2;
  pari_long a21,a22,a21sq,a22sq,a21a22;
  pari_long a31,a32,a31sq,a32sq,a31a32;
  pari_long a41,a42,a41sq,a42sq,a41a42;
  pari_long a51sq,a52sq,a51a52;
  pari_long a21_L,a21_U,a22_L,a22_U,a31_L,a31_U,a32_L,a32_U,a41_L,a41_U,a42_L,a42_U;
  pari_long b1,b2,b1b,b2b,b1c,b2c,s22,s32,s42;
  pari_long s[10],Sum,Sum3,Sum4,bb1,bb2,bb3,bb4,bb5,bb6,bb7,bb8,bb9,bb10;
  pari_long bb2_L,bb2_U,bb3_L,bb3_U,bb4_L,bb4_U,bb5_L,bb5_U,bb6_L,bb6_U,bb7_L,bb7_U;
  pari_long bb8_L,bb8_U,bb9_L,bb9_U,bb9_L0,bb9_U0;
  pari_long bb2_pre,bb3_pre,bb4_pre,bb5_pre,bb6_pre,bb7_pre,bb8_pre;
  pari_long bb4_pre2,bb5_pre2,bb6_pre2,bvec_pre_1,bvec_pre_2;
  pari_long wsq_1,wsq_2,Tr_w,Nm_w,r2;
  double lambda1,lambda2,lambda1c,lambda2c;
  double tq[5],tqc[5],t[10],t11,t12,t22,bb8_Upre,tmpdbl;
  double Bnd2,Ca1,B1,B_s2,B_s3,B_s4,B_a4,B_a4c,a32_pre,a42_pre,B_s2_sqrt;
  double s1a2_mag,s2a2_mag,s1a3_mag,s2a3_mag,s1a4_mag,s2a4_mag;
  double s1a5_mag,s2a5_mag,s1a5_mag_sq,s2a5_mag_sq,s1a5_mag_2_5ths,s2a5_mag_2_5ths;
  GEN TmpGEN,w_alg,w_sq,w,wc,f_L,PolDisc;
  char *OutStr;


  // Start the pari timer
  timer();

  ltop = avma;

  PolyCount   = StatVec[0];
  Test1_Count = StatVec[1];
  Test2_Count = StatVec[2];
  Test3_Count = StatVec[3];
  Time_sec    = StatVec[4];


  pari_long NumVals_a5  = (pari_long)floor(1.0/Delta_a5  + .5);
  float a5_frac_done = Delta_a5*a5_Idx;


    // 2nd part of Martinet bound = 2*[dL/(25*dK)]^(1/8)
  TmpGEN = gpow(gdivgs(dLg,25*dK),dbltor(.125),BIGDEFAULTPREC);
  TmpGEN = rtor(TmpGEN,DEFAULTPREC);
  Bnd2 = 2.0*rtodbl(TmpGEN);

  if(NumVals_a5<=MAX_a5_VALUES_TO_DISPLAY)
    {
    fprintf(stderr, "  2nd part of Martinet bound = %lf.\n",Bnd2);
    //fprintf(stderr, "  QHQ = %s\n",GENtostr(QHQ));
    }

  t11 = sqrt(gtodouble(real_i(gmael(QHQ,1,1))));
  t12 = gtodouble(real_i(gmael(QHQ,2,1)))/t11;
  t22 = sqrt(gtodouble(real_i(gmael(QHQ,2,2)))-t12*t12);


    // Get w and the components of w^2.
    // Also compute the trace and norm of w.
  w_alg = basistoalg(K,mkcol2(gen_0,gen_1));
  w_sq  = algtobasis(K,gsqr(w_alg));
  wsq_1 = itos((GEN)w_sq[1]);
  wsq_2 = itos((GEN)w_sq[2]);
  w  = gmael(Q,2,1);  // row 1, col 2   Note: these are complex numbers.
  wc = gmael(Q,2,2);  // row 2, col 2
  Tr_w = (pari_long)floor(gtodouble(real_i(gadd(w,wc)))+.5);
  Nm_w = (pari_long)floor(gtodouble(real_i(gmul(w,wc)))+.5);

    // Compute the parameters lambda1 and lambda2
  r2 = itos(gmael(K,2,2));  // K[2]=[r1,r2]
  if(r2==1)  // Then the subfield is complex. [ie K=Q(sqrt(m)) where m<0]
    {
    lambda1  = (double)Tr_w;
    lambda2  = (double)Nm_w;
    lambda1c = lambda1;
    lambda2c = lambda2;
    }
  else  // w and wc are real (but stored as complex)
    {
    lambda1  = 2.0*gtodouble(real_i(w));
    lambda2  = gtodouble(real_i(gsqr(w)));
    lambda1c = 2.0*gtodouble(real_i(wc));
    lambda2c = gtodouble(real_i(gsqr(wc)));
    }


  a1sq_1 = a11*a11 + a12*a12*wsq_1;
  a1sq_2 = 2*a11*a12 + a12*a12*wsq_2;

  a1cb_1 = a11*a1sq_1 + a12*a1sq_2*wsq_1;
  a1cb_2 = a11*a1sq_2 + a12*a1sq_1 + a12*a1sq_2*wsq_2;

  a1_4th_1 = a11*a1cb_1 + a12*a1cb_2*wsq_1;
  a1_4th_2 = a11*a1cb_2 + a12*a1cb_1 + a12*a1cb_2*wsq_2;

  Ca1 = Ca1_pre + Bnd2;

  if(NumVals_a5<=MAX_a5_VALUES_TO_DISPLAY)
    {
    fprintf(stderr, "  Martinet bound = %f.\n",Ca1);
    }

    // Compute bound on s2
  if(r2==1)  B_s2 = .5*Ca1*Ca1;
  else       B_s2 = Ca1*Ca1;
  B_s2_sqrt = sqrt(B_s2);

  b1 = a1sq_1;
  b2 = a1sq_2;

  bb1  = 2*a11 + a12*Tr_w;
  s[1] = -bb1;
  bb2_L = (pari_long) ceil(.5*(bb1*bb1-Ca1));
  bb2_U = (pari_long)floor(.5*(.8*bb1*bb1 + Ca1));
  bb2_pre = a11*a11 + a11*a12*Tr_w + a12*a12*Nm_w;

  a51sq  = a51*a51;
  a52sq  = a52*a52;
  a51a52 = a51*a52;
  s1a5_mag_sq = a51sq + lambda1*a51a52  + lambda2*a52sq;
  s2a5_mag_sq = a51sq + lambda1c*a51a52 + lambda2c*a52sq;
  s1a5_mag_2_5ths = pow(s1a5_mag_sq,.2);
  s2a5_mag_2_5ths = pow(s2a5_mag_sq,.2);
  s1a5_mag = sqrt(s1a5_mag_sq);
  s2a5_mag = sqrt(s2a5_mag_sq);

  bb5_pre = 2*a51 + a52*Tr_w;  // a5 + a5conj
  bb6_pre = 2*a11*a51 + (a11*a52+a12*a51)*Tr_w + 2*a12*a52*Nm_w;
  bb10 = a51sq + a51a52*Tr_w + a52sq*Nm_w;

    // Compute bound on s3, s4, and s_{-1} for relative quintic
  if(r2==1)
    {
    Get_Pohst_Bounds_n5(.5*Ca1,s1a5_mag,tq);
    tqc[1] = tq[1]; tqc[3] = tq[3]; tqc[4] = tq[4];
    B_s3 = 2.0*tq[3]*tq[3];
    B_s4 = 2.0*tq[4]*tq[4];
    }
  else
    {
    Get_Pohst_Bounds_n5(Ca1 - 5.0*s2a5_mag_2_5ths,s1a5_mag,tq);
    Get_Pohst_Bounds_n5(Ca1 - 5.0*s1a5_mag_2_5ths,s2a5_mag,tqc);
    B_s3 = tq[3]*tq[3] + tqc[3]*tqc[3];
    B_s4 = tq[4]*tq[4] + tqc[4]*tqc[4];
    }

  B_a4 = tq[1]*s1a5_mag;
  if(B_a4>tq[4])  B_a4 = tq[4];
  B_a4c = tqc[1]*s2a5_mag;
  if(B_a4c>tqc[4])  B_a4c = tqc[4];

  a32_pre = sqrt(B_s3)/t22;
  a42_pre = sqrt(B_s4)/t22;

    // Compute bounds on sk for decic (k=3,4,5,6,7,8,9,-1,-2).
  Get_Pohst_Bounds_n10(Ca1,abs(bb10),t);  // t[k]  is bound on sk when k>0.
                                          // t[-k] is bound on sk when k<0.

  bb9_U0 = (pari_long)floor(abs(bb10)*t[1]);
  bb9_L0 = -bb9_U0;
  bb8_Upre = .5*abs(bb10)*t[2];


  //fprintf(stderr, "  t11 = %f.\n",t11);
  //fprintf(stderr, "  t12 = %f.\n",t12);
  //fprintf(stderr, "  t22 = %f.\n",t22);
  //fprintf(stderr, "  B_s2 = %f.\n",B_s2);
  //fprintf(stderr, "  a32_pre = %f.\n",a32_pre);
  //fprintf(stderr, "  a42_pre = %f.\n",a42_pre);


  a22_L = (pari_long) ceil(.5*(b2-B_s2_sqrt/t22));
  a22_U = (pari_long)floor(.5*(b2+B_s2_sqrt/t22));

    // A negative Delta_a22 means it was not computed earlier.
    // Compute it from the pre-checkpoint values.
  if(Delta_a22<0)  Delta_a22 = 1.0 / (a22_U - a22_L + 1.0);


    // Modify a22 limits based on initial inputs
  a22_L = max(a22_L,a22_L0);
  a22_U = min(a22_U,a22_U0);

  pari_long NumVals_a22 = (pari_long)floor(1.0/Delta_a22 + .5);
  pari_long a22_L_Orig  = a22_U - NumVals_a22 + 1;

  if(NumVals_a5<=MAX_a5_VALUES_TO_DISPLAY)
    {
    fprintf(stderr, "  a22_L = %ld.\n",a22_L);
    fprintf(stderr, "  a22_U = %ld.\n",a22_U);
    }


  for(a22=a22_L;a22<=a22_U;++a22)
    {
    float a22_frac_done = Delta_a22*(a22-a22_L_Orig);

    if(NumVals_a5<=MAX_a5_VALUES_TO_DISPLAY)
      {
      fprintf(stderr, "  a22 = %ld.\n",a22);
      }

    s22 = b2-2*a22;
    B1 = sqrt(B_s2-t22*t22*s22*s22);
    a21_L = (pari_long) ceil(.5*(b1+(-B1+t12*s22)/t11));
    a21_U = (pari_long)floor(.5*(b1+( B1+t12*s22)/t11));

      // If there is more than 1 a22, then Delta_a21 will change for each a22.
      // When there is only 1 a22, Delta_a21 is computed externally, so don't change it.
    if(NumVals_a22>1 || Delta_a21<0)  Delta_a21 = 1.0 / (a21_U - a21_L + 1.0);

      // Modify a21 limits based on initial inputs (checkpointed values)
    a21_L = max(a21_L,a21_L0);
    a21_U = min(a21_U,a21_U0);

    pari_long NumVals_a21 = (pari_long)floor(1.0/Delta_a21 + .5);
    pari_long a21_L_Orig  = a21_U - NumVals_a21 + 1;

      // This will reset the a21 starting point after the first pass
    if(ChkPntFlag==0)  a21_L = a21_L_Orig;

    if(NumVals_a5==1)
      {
      fprintf(stderr, "    a21_L = %ld.\n",a21_L);
      fprintf(stderr, "    a21_U = %ld.\n",a21_U);
      }


    ltop3 = avma;
    for(a21=a21_L;a21<=a21_U;++a21)
      {
      float a21_frac_done = Delta_a21*(a21-a21_L_Orig);

      if(NumVals_a5==1 && NumVals_a22==1)  fprintf(stderr, "    a21 = %ld.\n",a21);

      a21sq  = a21*a21;
      a22sq  = a22*a22;
      a21a22 = a21*a22;
      s1a2_mag = sqrt(a21sq + lambda1*a21a22  + lambda2*a22sq);
      s2a2_mag = sqrt(a21sq + lambda1c*a21a22 + lambda2c*a22sq);

      if( (s1a2_mag+s2a2_mag) <= 2.0*Ca1 )
        {

        bb2 = bb2_pre + 2*a21 + a22*Tr_w;

        if(bb2>=bb2_L && bb2<=bb2_U)
          {
          a2sq_1 = a21sq + a22sq*wsq_1;
          a2sq_2 = 2*a21a22 + a22sq*wsq_2;
          a1a2_1 = a11*a21 + a12*a22*wsq_1;
          a1a2_2 = a11*a22 + a12*a21 + a12*a22*wsq_2;
          a1sq_a2_1 = a1sq_1*a21 + a1sq_2*a22*wsq_1;
          a1sq_a2_2 = a1sq_1*a22 + a1sq_2*a21 + a1sq_2*a22*wsq_2;

            // Compute bvec_pre = a1^4 - 4*a1^2*a2 + 2*a2^2
          bvec_pre_1 = a1_4th_1 - 4*a1sq_a2_1 + 2*a2sq_1;
          bvec_pre_2 = a1_4th_2 - 4*a1sq_a2_2 + 2*a2sq_2;

            // Compute [b1b,b2b] = 3*a1*a2-a1^3
          b1b = 3*a1a2_1 - a1cb_1;
          b2b = 3*a1a2_2 - a1cb_2;

          s[2] = bb1*bb1 - 2*bb2;

          bb3_pre = 2*a11*a21 + (a11*a22+a12*a21)*Tr_w + 2*a12*a22*Nm_w;
          bb4_pre = a21sq + a21a22*Tr_w + a22sq*Nm_w;
          bb7_pre = 2*a21*a51 + (a21*a52+a22*a51)*Tr_w + 2*a22*a52*Nm_w;

            // Compute bounds for bb3
          Sum3 = bb2*s[1] + bb1*s[2];
          bb3_L = (pari_long)ceil((-t[3] - Sum3)/3.0);
          bb3_U = (pari_long)floor((t[3] - Sum3)/3.0);


          a32_L = (pari_long) ceil( (b2b-a32_pre) / 3.0 );
          a32_U = (pari_long)floor( (b2b+a32_pre) / 3.0 );

            // If there is more than 1 a21, then Delta_a32 will change for each a21.
            // When there is only 1 a21, Delta_a32 is computed externally, so don't change it.
          if(NumVals_a21>1 || Delta_a32<0)  Delta_a32 = 1.0 / (a32_U - a32_L + 1.0);

            // Modify a32 limits based on initial inputs (checkpointed values)
          a32_L = max(a32_L,a32_L0);
          a32_U = min(a32_U,a32_U0);

          pari_long NumVals_a32 = (pari_long)floor(1.0/Delta_a32 + .5);
          pari_long a32_L_Orig  = a32_U - NumVals_a32 + 1;

            // This will reset the a32 starting value after the first looping pass
          if(ChkPntFlag==0)  a32_L = a32_L_Orig;

          if(NumVals_a5==1 && NumVals_a22==1)
            {
            fprintf(stderr, "      a32_L = %ld.\n",a32_L);
            fprintf(stderr, "      a32_U = %ld.\n",a32_U);
            }


          for(a32=a32_L;a32<=a32_U;++a32)
            {
            float a32_frac_done = Delta_a32*(a32-a32_L_Orig);

            //fprintf(stderr, "        a32 = %ld.\n",a32);

            s32 = b2b-3*a32;
            B1 = sqrt(B_s3-t22*t22*s32*s32);
            a31_L = (pari_long) ceil( (b1b+(-B1+t12*s32)/t11) / 3.0 );
            a31_U = (pari_long)floor( (b1b+( B1+t12*s32)/t11) / 3.0 );

            pari_long NumVals_a31 = a31_U-a31_L+1;
            if(NumVals_a31<1) NumVals_a31 = 1;
            pari_long a31_L_Orig = a31_L;

            // If ChkPntFlag is set then this case has been previously checkpointed,
            // so use the checkpoint value for a31.  But only do this once!
            if(ChkPntFlag)
              {
              a31_L = max(a31_L,a31_Start);
              ChkPntFlag = 0;
              }

            //fprintf(stderr, "            a31_L = %ld.\n",a31_L);
            //fprintf(stderr, "            a31_U = %ld.\n",a31_U);


            ltop2 = avma;
            for(a31=a31_L;a31<=a31_U;++a31)
              {
              //fprintf(stderr, "              a31 = %ld.\n",a31);
              a31sq  = a31*a31;
              a32sq  = a32*a32;
              a31a32 = a31*a32;
              s1a3_mag = sqrt(a31sq + lambda1*a31a32  + lambda2*a32sq);
              s2a3_mag = sqrt(a31sq + lambda1c*a31a32 + lambda2c*a32sq);

              if( (s1a3_mag<=2*tq[3]) && (s2a3_mag<=2*tqc[3]) )
                {

                bb3 = bb3_pre + 2*a31 + a32*Tr_w;

                if(bb3>=bb3_L && bb3<=bb3_U)
                  {
                  a1a3_1 = a11*a31 + a12*a32*wsq_1;
                  a1a3_2 = a11*a32 + a12*a31 + a12*a32*wsq_2;

                    // Set [b1c,b2c] = a1^4 + 4*a1*a3 - 4*a1^2*a2 + 2*a2^2
                  b1c = 4*a1a3_1 + bvec_pre_1;
                  b2c = 4*a1a3_2 + bvec_pre_2;
                  a42_L = (pari_long) ceil( (b2c-a42_pre) / 4.0 );
                  a42_U = (pari_long)floor( (b2c+a42_pre) / 4.0 );

                  //fprintf(stderr, "                a42_L = %ld.\n",a42_L);
                  //fprintf(stderr, "                a42_U = %ld.\n",a42_U);

                  bb4_pre2 = bb4_pre + 2*a11*a31 + 
                             (a11*a32+a12*a31)*Tr_w + 2*a12*a32*Nm_w;
                  bb5_pre2 = bb5_pre + 2*a21*a31 + 
                             (a21*a32+a22*a31)*Tr_w + 2*a22*a32*Nm_w;
                  bb6_pre2 = bb6_pre + a31sq + a31a32*Tr_w + a32sq*Nm_w;
                  bb8_pre  = 2*a31*a51 + (a31*a52+a32*a51)*Tr_w + 2*a32*a52*Nm_w;

                    // Compute bounds for bb4
                  s[3] = -3*bb3 - Sum3;
                  Sum4 = bb3*s[1] + bb2*s[2] + bb1*s[3];
                  bb4_L = (pari_long)ceil((-t[4] - Sum4)/4.0);
                  bb4_U = (pari_long)floor((t[4] - Sum4)/4.0);

                  for(a42=a42_L;a42<=a42_U;++a42)
                    {
                    //fprintf(stderr, "                  a42 = %ld.\n",a42);
                    s42 = b2c-4*a42;
                    B1 = sqrt(B_s4-t22*t22*s42*s42);
                    a41_L = (pari_long) ceil( (b1c+(-B1+t12*s42)/t11) / 4.0 );
                    a41_U = (pari_long)floor( (b1c+( B1+t12*s42)/t11) / 4.0 );
                    //fprintf(stderr, "                    a41_L = %ld.\n",a41_L);
                    //fprintf(stderr, "                    a41_U = %ld.\n",a41_U);
                    ltop1 = avma;
                    for(a41=a41_L;a41<=a41_U;++a41)
                      {
                      //fprintf(stderr, "                      a41 = %ld.\n",a41);
                      a41sq  = a41*a41;
                      a42sq  = a42*a42;
                      a41a42 = a41*a42;
                      s1a4_mag = sqrt(a41sq + lambda1*a41a42  + lambda2*a42sq);
                      s2a4_mag = sqrt(a41sq + lambda1c*a41a42 + lambda2c*a42sq);

                      if( (s1a4_mag<=B_a4) && (s2a4_mag<=B_a4c) )
                        {
                        bb9 = 2*a41*a51 + (a41*a52+a42*a51)*Tr_w + 2*a42*a52*Nm_w;
                        if(bb9>=bb9_L0 && bb9<=bb9_U0)
                          {
                          bb4 = bb4_pre2 + 2*a41 + a42*Tr_w;
                          if(bb4>=bb4_L && bb4<=bb4_U)
                            {
                            bb5 = bb5_pre2 + 2*a11*a41 + 
                                  (a11*a42+a12*a41)*Tr_w + 2*a12*a42*Nm_w;
                            s[4] = -4*bb4 - Sum4;
                            Sum = bb4*s[1] + bb3*s[2] + bb2*s[3] + bb1*s[4];
                            bb5_L = (pari_long)ceil((-t[5] - Sum)/5.0);
                            bb5_U = (pari_long)floor((t[5] - Sum)/5.0);

                            if(bb5>=bb5_L && bb5<=bb5_U)
                              {
                              bb6 = bb6_pre2 + 2*a21*a41 + 
                                    (a21*a42+a22*a41)*Tr_w + 2*a22*a42*Nm_w;
                              s[5] = -5*bb5 - Sum;
                              Sum = bb5*s[1] + bb4*s[2] + bb3*s[3] + bb2*s[4] + bb1*s[5];
                              bb6_L = (pari_long)ceil((-t[6] - Sum)/6.0);
                              bb6_U = (pari_long)floor((t[6] - Sum)/6.0);
                              if(bb6>=bb6_L && bb6<=bb6_U)
                                {
                                bb7 = bb7_pre + 2*a31*a41 + 
                                      (a31*a42+a32*a41)*Tr_w + 2*a32*a42*Nm_w;
                                s[6] = -6*bb6 - Sum;
                                Sum = bb6*s[1] + bb5*s[2] + bb4*s[3] + bb3*s[4] + 
                                      bb2*s[5] + bb1*s[6];
                                bb7_L = (pari_long)ceil((-t[7] - Sum)/7.0);
                                bb7_U = (pari_long)floor((t[7] - Sum)/7.0);
                                if(bb7>=bb7_L && bb7<=bb7_U)
                                  {
                                  bb8 = bb8_pre + a41sq + a41a42*Tr_w + a42sq*Nm_w;
                                  s[7] = -7*bb7 - Sum;
                                  Sum = bb7*s[1] + bb6*s[2] + bb5*s[3] + bb4*s[4] + 
                                        bb3*s[5] + bb2*s[6] + bb1*s[7];
                                  bb8_L = (pari_long)ceil((-t[8] - Sum)/8.0);
                                  bb8_U = (pari_long)floor((t[8] - Sum)/8.0);
                                  if(bb8>=bb8_L && bb8<=bb8_U)
                                    {
                                    s[8] = -8*bb8 - Sum;
                                    Sum = bb8*s[1] + bb7*s[2] + bb6*s[3] + bb5*s[4] + 
                                          bb4*s[5] + bb3*s[6] + bb2*s[7] + bb1*s[8];
                                    bb9_L = (pari_long)ceil((-t[9] - Sum)/9.0);
                                    bb9_U = (pari_long)floor((t[9] - Sum)/9.0);
                                    if(bb9>=bb9_L && bb9<=bb9_U)
                                      {
                                      tmpdbl = .5*bb9*bb9/bb10;
                                      bb8_L = (pari_long) ceil(tmpdbl - bb8_Upre);
                                      bb8_U = (pari_long)floor(tmpdbl + bb8_Upre);
                                      if(bb8>=bb8_L && bb8<=bb8_U)
                                        {
                                        ++PolyCount;
                                        f_L = mkpoln(11,gen_1,stoi(bb1),stoi(bb2),stoi(bb3),
                                                    stoi(bb4),stoi(bb5),stoi(bb6),stoi(bb7),
                                                    stoi(bb8),stoi(bb9),stoi(bb10));

                                        PolDisc = discsr(f_L);
                                          // check if PolDisc is zero.
                                        if(!gcmp0(PolDisc))  // Then PolDisc is nonzero
                                          {
                                            // Get absolute value of PolDisc
                                          if(gcmp(PolDisc,gen_0)<0)  PolDisc = gmul(PolDisc,gen_m1);

                                            // check if PolDisc/dLg is square
                                          if(issquare(gdiv(PolDisc,dLg)))
                                            {
                                            ++Test1_Count;
                                              // check if f_L is irreducible:
                                            if(isirreducible(f_L))
                                              {
                                              ++Test2_Count;
                                                // Check if field discriminant equals dL
                                              if(gequal(dLg,gabs(discf(f_L),BIGDEFAULTPREC)))
                                                {
                                                ++Test3_Count;
                                                OutStr = GENtostr(f_L);
                                                outfile << OutStr << "\n";
                                                outfile.flush();
                                                free(OutStr);
                                                }
                                              }
                                            }
                                          }  // Matches:  if(!gcmp0(PolDisc))
                                        }  // Second bb8 test
                                      }  // Second bb9 test
                                    }  // First bb8 test
                                  }  // bb7 test
                                }  // bb6 test
                              }  // bb5 test
                            }  //bb4 test
                          }  // First bb9 test
                        }  // Matches: if( (s1a4_mag<=B_a4) && (s2a4_mag<=B_a4c) )
                      avma = ltop1;
                      }  // End of loop on a41
                    }  // End of loop on a42
                  }  // bb3 test
                }  // Matches: if( (s1a3_mag<=2*tq[3]) && (s2a3_mag<=2*tqc[3]) )

                // Do checkpointing
              if(boinc_time_to_checkpoint())
                {
                // Note: timer() returns elapsed time in milliseconds since the last call to timer
                Time_sec = Time_sec + (pari_long)floor(timer()/1000.0 + .5);
                int retval = do_checkpoint(a5_Idx,a22,a21,a32,a31+1,PolyCount,Test1_Count,Test2_Count,Test3_Count,Time_sec);
                if(retval)
                  {
                  fprintf(stderr, "Checkpoint failed!\n");
                  exit(retval);
                  }
                boinc_checkpoint_completed();
                }

                // Determine fraction complete for the progress bar
              float a31_frac_done = (a31-a31_L_Orig+1.0)/NumVals_a31;
              float Frac_Done = a5_frac_done + Delta_a5*
                    (a22_frac_done + Delta_a22*
                    (a21_frac_done + Delta_a21*
                    (a32_frac_done + Delta_a32*a31_frac_done)));
              boinc_fraction_done(Frac_Done);


              avma = ltop2;
              }  // End of loop on a31
            }  // End of loop on a32
          }  // Matches: if(bb2>=bb2_L && bb2<=bb2_U)
        }  // Matches: if( (s1a2_mag+s2a2_mag) <= 2.0*Ca1 )
      avma = ltop3;
      }  // End of loop on a21
    }  // End of loop on a22



  // Update the time once more before exiting
  Time_sec = Time_sec + (pari_long)floor(timer()/1000.0 + .5);

  StatVec[0] = PolyCount;
  StatVec[1] = Test1_Count;
  StatVec[2] = Test2_Count;
  StatVec[3] = Test3_Count;
  StatVec[4] = Time_sec;

  avma = ltop;  // Reset pointer to top of pari stack

  }





//******************************************************************************
//* This function uses the method of Pohst to compute bounds on the s_k's. It  *
//* computes the bounds and places them in the input array t.  For k>2, t[k]   *
//* is the bound on s_k.  For k=1,2 we define t[k] to be the bound on s_{-k}.  *
//* This version assumes n=10.                                                 *
//******************************************************************************

void Get_Pohst_Bounds_n10(double t2, double a10mag, double *t)
  {
  const int n = 10;
  int m,k;
  double r,x,x_new,dx,xm,xm1,xn,R,Rp,z[n],tt;


  r = t2/pow(a10mag,2.0/n);

    // First compute z[m] for each value of m.
  for(m=1;m<=n-1;++m)
    {
    x_new = pow( m/r, 1.0/(n-m) );
    do
      {
      x = x_new;
      xm1 = pow(x,m-1);
      xm  = x*xm1;
      xn  = pow(x,n);
      R = xm * (n - m + m/xn);
      Rp = m*(n-m)*xm1*(1-1.0/xn);
      dx = (r-R)/Rp;
      x_new = x + dx;
      }
    while(dx>.0000001);
    z[m] = x_new;
    }

    // Now compute t[k] for each value of k.
  for(k=3;k<=n-1;++k)
    {
    t[k] = pow(z[1],.5*k*(1-n)) + (n-1)*pow(z[1],.5*k);  // corresponds to m=1
    for(m=2;m<=n-1;++m)
      {
      tt = m*pow(z[m],.5*k*(m-n)) + (n-m)*pow(z[m],.5*k*m);
      if(t[k]<tt) t[k]=tt;
      }
    t[k] = t[k]*pow(a10mag,((double)k)/n);
    }

    // Now compute t[1],t[2] which correspond to k=-1,-2.
  for(k=-2;k<=-1;++k)
    {
    t[-k] = pow(z[1],.5*k*(1-n)) + (n-1)*pow(z[1],.5*k);  // corresponds to m=1
    for(m=2;m<=n-1;++m)
      {
      tt = m*pow(z[m],.5*k*(m-n)) + (n-m)*pow(z[m],.5*k*m);
      if(t[-k]<tt) t[-k]=tt;
      }
    t[-k] = t[-k]*pow(a10mag,((double)k)/n);
    }

  }





//******************************************************************************
//* This function is like the last but assumes n=5.  Also, it does not compute *
//* bounds on s_{-2}.                                                          *
//******************************************************************************

void Get_Pohst_Bounds_n5(double t2, double a5mag, double *t)
  {
  const int n = 5;
  int m,k;
  double r,x,x_new,dx,xm,xm1,xn,R,Rp,z[5],tt;


  r = t2/pow(a5mag,2.0/n);

    // First compute z[m] for each value of m.
  for(m=1;m<=n-1;++m)
    {
    x_new = pow( m/r, 1.0/(n-m) );
    do
      {
      x = x_new;
      xm1 = pow(x,m-1);
      xm  = x*xm1;
      xn  = pow(x,n);
      R = xm * (n - m + m/xn);
      Rp = m*(n-m)*xm1*(1-1.0/xn);
      dx = (r-R)/Rp;
      x_new = x + dx;
      }
    while(dx>.0000001);
    z[m] = x_new;
    }

    // Now compute t[k] for each value of k.
  for(k=3;k<=n-1;++k)
    {
    t[k] = pow(z[1],.5*k*(1-n)) + (n-1)*pow(z[1],.5*k);  // corresponds to m=1
    for(m=2;m<=n-1;++m)
      {
      tt = m*pow(z[m],.5*k*(m-n)) + (n-m)*pow(z[m],.5*k*m);
      if(t[k]<tt) t[k]=tt;
      }
    t[k] = t[k]*pow(a5mag,((double)k)/n);
    }

    // Now compute t[1] which correspond to k=-1.
  t[1] = pow(z[1],-.5*(1-n)) + (n-1)*pow(z[1],-.5);  // corresponds to m=1
  for(m=2;m<=n-1;++m)
    {
    tt = m*pow(z[m],-.5*(m-n)) + (n-m)*pow(z[m],-.5*m);
    if(t[1]<tt) t[1]=tt;
    }
  t[1] = t[1]*pow(a5mag,-1.0/n);

  }
