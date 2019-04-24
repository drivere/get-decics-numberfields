//******************************************************************************
//* This function generates all decic fields ramified outside S and having a   *
//* quadratic subfield.  It writes the field data (represented by polynomials) *
//* to an output file whose name is created from the set S. It does not refine *
//* the list of polynomials.                                                   *
//******************************************************************************

#include <string>
#include <iostream>
#include <fstream>
#include <math.h>

#ifdef _WIN32
#include <windows.h>
#endif

#include "boinc_api.h"   // NOTE: Order is important!  Put pari.h before this and all hell breaks loose!
#include "pari.h"
#include "GetDecics.h"
#include "TgtMartinet.h"

#define MAX_PRIME 10000000
#define MAX_CVECS_TO_DISPLAY 5

//using namespace std;
using std::ifstream;
using std::ofstream;

  // Global variables
GEN Sg,Q,QHQ;
double Ca1_pre[9];


int TgtMartinet(char *FilenameIn, char *FilenameOut, int ChkPntFlag, long CvecIdx, 
                long N1_Start, long N2_Start, long long *StatVec)
  {
  int  i,a11,a12,r1,r2;
  long ltop,dK,VarNum_y;
  GEN  K,Kpol,ConVecs,sig1w,sig2w,sig1a1,sig2a1;
  string DataStr;


  pari_init(300000000,MAX_PRIME);  // Reserve 150 MB for the pari stack

    // Open the input file
  fprintf(stderr, "Reading file %s\n",FilenameIn);
  ifstream infile(FilenameIn);
  if(!infile)
    {
    fprintf(stderr, "Could not read file.  Aborting.\n");
    exit(1);
    }

    // Now read from the input file.
    // The 1st line is the polynomial representing the base field K.
  getline(infile,DataStr);
  fprintf(stderr, "    K = %s\n",DataStr.c_str());
  Kpol = gp_read_str((char*)(DataStr.c_str()));
  VarNum_y = fetch_user_var((char*)"y");   // Define a new variable y
  setvarn(Kpol,VarNum_y);           // Set variable number to "y".
  K = nfinit0(Kpol,0,MEDDEFAULTPREC);


    // The 2nd line is the set S (as a GEN).
  getline(infile,DataStr);
  Sg = gp_read_str((char*)(DataStr.c_str()));
  fprintf(stderr, "    S = %s\n",DataStr.c_str());


    // The 3rd line is the vector of congruences (as a GEN).
  getline(infile,DataStr);
  ConVecs = gp_read_str((char*)(DataStr.c_str()));
  Write_Cvec_Stats(ConVecs);


    // That is all the inputs, so close the input file.
  infile.close();


    // Save the current top of the pari stack.
  ltop = avma;


  r1 = itos(gmael(K,2,1));  // K[2]=[r1,r2]
  r2 = itos(gmael(K,2,2));

    // Get absolute value of discriminant of K
  dK = abs(itos((GEN)K[3]));

  fprintf(stderr, "    |dK| = %ld\n",dK);
  fprintf(stderr, "    Signature = [%d,%d]\n",r1,r2);


    // Get the embeddings applied to the integral basis (as complex numbers).
    // Here sig1w[i] = sig1 applied to w_i.  The others are similarly defined.
  sig1w = cgetg(3,t_VEC);
  sig2w = cgetg(3,t_VEC);
  for(i=1;i<=2;++i)
    {       // Note: K[5][1]=[[sig_i(w_j)]]
    sig1w[i] = (long)gmael4(K,5,1,i,1);  // This is sig1(w_i)
    if(r1==2)  sig2w[i] = (long)gmael4(K,5,1,i,2);  // This is sig2(w_i)
    else  sig2w[i] = (long)gconj((GEN)sig1w[i]);
    }

    // Precompute the different values for 1st part of Ca1 bound.
  for(a11=0;a11<=2;++a11)
    {
    for(a12=0;a12<=2;++a12)
      {
      if(a11==2 && a12==2 && (dK%4)!=0)  // a1=2+2w and 4 does not divide dK
        {
        sig1a1 = gadd( gmulsg(-1,(GEN)sig1w[1]),gmulsg(a12,(GEN)sig1w[2]) );
        sig2a1 = gadd( gmulsg(-1,(GEN)sig2w[1]),gmulsg(a12,(GEN)sig2w[2]) );
        }
      else
        {
        sig1a1 = gadd( gmulsg(a11,(GEN)sig1w[1]),gmulsg(a12,(GEN)sig1w[2]) );
        sig2a1 = gadd( gmulsg(a11,(GEN)sig2w[1]),gmulsg(a12,(GEN)sig2w[2]) );
        }
      Ca1_pre[3*a11+a12] = ( gtodouble(gsqr(gabs(sig1a1,DEFAULTPREC))) + 
                             gtodouble(gsqr(gabs(sig2a1,DEFAULTPREC))) )/5.0;
      }
    }


    // Create the Q matrix.
  Q = cgetg(3,t_MAT);
  Q[1] = (long)mkcol2((GEN)sig1w[1],(GEN)sig2w[1]);
  Q[2] = (long)mkcol2((GEN)sig1w[2],(GEN)sig2w[2]);
  Q = gerepilecopy(ltop,Q);

    // Compute QHQ
  ltop = avma;
  QHQ = gmul(gconj(gtrans(Q)),Q);
  QHQ = gerepilecopy(ltop,QHQ);


    // Open the output file for appending.
  fprintf(stderr, "Opening output file %s\n",FilenameOut);
  ofstream outfile;
  outfile.open(FilenameOut,ios::app);
  if(!outfile)
    {
    fprintf(stderr, "Could not open output file.  Aborting.\n");
    exit(1);
    }


    // Finally start the search:
  fprintf(stderr, "Now starting the targeted Martinet search:\n");
  Mart52Engine_Tgt(K,ConVecs,dK,1,ChkPntFlag,CvecIdx,N1_Start,N2_Start,StatVec,outfile);
  fprintf(stderr, "The search has finished.\n");

  outfile.close();

  pari_close();

  return 0;

  }  // End of main





//******************************************************************************
//* This subroutine does a targetted Martinet search.  It assumes that these   *
//* global variables have been precomputed: Sg, Q, QHQ, and Ca1_pre.           *
//* The input CVecVec is a vector of Cvec information in the same format as    *
//* that output by GetConVec()- the first element is the Modulus ideal M, the  *
//* second element is the contribution of P to dL (not including the factor of *
//* dK^5), and the rest of the elements are the actual congruence vectors (as  *
//* 5-dim vectors of t_COLs).  The other inputs are the field K, the field     *
//* discriminant dK, and a pointer to the output file where the field data is  *
//* to be written.  Note: If the modulus ideal is M = P1^r1*...*Pn^rn then M   *
//* is represented by the n-by-2 matrix [P1  r1;  P2  r2; .... Pn  rn].        *
//******************************************************************************

void Mart52Engine_Tgt(GEN K, GEN CVecVec, long dK, long dL_Factor, int ChkPntFlag, 
                      long CvecIdx, long N1_Start, long N2_Start, long long *StatVec,
                      ofstream& outfile)
  {
  int  a1_is_0,j,Idx;
  long ltop,ltop1,ltop2,ltop3,ltop4,ltop5;
  long i,n,NumPrimes,NumCvecs;
  long long PolyCount,Test1_Count,Test2_Count,Test3_Count,Time_sec;
  long k1,k2,k1_L,k1_U,k2_L,k2_U,L1,L2,L1_L,L1_U,L2_L,L2_U;
  long m1,m2,m1_L,m1_U,m2_L,m2_U,N1,N2,N1_L,N1_U,N2_L,N2_U;
  long long s[10],Sum,Sum3,Sum4,bb1,bb2,bb3,bb4,bb5,bb6,bb7,bb8,bb9,bb10;
  long long bb2_L,bb2_U,bb3_L,bb3_U,bb4_L,bb4_U,bb5_L,bb5_U,bb6_L,bb6_U,bb7_L,bb7_U;
  long long bb8_L,bb8_U,bb9_L,bb9_U,bb9_L0,bb9_U0;
  long long bb2_pre,bb3_pre,bb4_pre,bb5_pre,bb6_pre,bb7_pre,bb8_pre;
  long long bb4_pre2,bb5_pre2,bb6_pre2,bvec_pre_1,bvec_pre_2;
  long wsq_1,wsq_2,Tr_w,Nm_w,r2;
  long a11,a12,a1sq_1,a1sq_2,a1cb_1,a1cb_2,a1_4th_1,a1_4th_2;
  long a2sq_1,a2sq_2,a1a2_1,a1a2_2,a1sq_a2_1,a1sq_a2_2,a1a3_1,a1a3_2;
  long a21,a22,a21sq,a22sq,a21a22;
  long a31,a32,a31sq,a32sq,a31a32;
  long a41,a42,a41sq,a42sq,a41a42;
  long a51,a52,a51sq,a52sq,a51a52;
  double lambda1,lambda2,lambda1c,lambda2c;
  double tq[5],tqc[5],t[10],t11,t12,t22,bb8_Upre,tmpdbl;
  double Bnd2,Ca1,B1,B_s2,B_s3,B_s4,B_a4,B_a4c,B_a5,B_a5_sqrt,B_s2_sqrt;
  double s1a2_mag,s2a2_mag,s1a3_mag,s2a3_mag,s1a4_mag,s2a4_mag;
  double s1a5_mag,s2a5_mag,s1a5_mag_sq,s2a5_mag_sq,s1a5_mag_2_5ths,s2a5_mag_2_5ths;
  double c1p,c2p,d1p,d2p,e1p,e2p,f1p,f2p,k2p,L2p,m2p,N2p,L2_pre,m2_pre;
  GEN dKg,TmpGEN,w_alg,w_sq,w,wc,Mat,P,M,Minv,B,dLg,Cvec,b,c,a1,a2,a3,a4,a5;
  GEN Cvec_prime,kvec,Lvec,mvec,Nvec,f_L,PolDisc;
  char *OutStr;


  // Start the pari timer.
  timer();

  ltop = avma;

  PolyCount   = StatVec[0];
  Test1_Count = StatVec[1];
  Test2_Count = StatVec[2];
  Test3_Count = StatVec[3];

  Time_sec = 0;
  if(ChkPntFlag)  // Use elapsed time from checkpoint file.
    {
    Time_sec = StatVec[4];
    }

  n = lg(Sg)-1;  // Number of primes in the set S

    // Get w and the components of w^2.
    // Also compute the trace and norm of w.
  w_alg = basistoalg(K,mkcol2(gen_0,gen_1));
  w_sq  = algtobasis(K,gsqr(w_alg));
  wsq_1 = itos((GEN)w_sq[1]);
  wsq_2 = itos((GEN)w_sq[2]);
  w  = gmael(Q,2,1);  // row 1, col 2   Note: these are complex numbers.
  wc = gmael(Q,2,2);  // row 2, col 2
  Tr_w = (long)floor(gtodouble(real_i(gadd(w,wc)))+.5);
  Nm_w = (long)floor(gtodouble(real_i(gmul(w,wc)))+.5);

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


  Mat = (GEN)CVecVec[1];     // Matrix representing the modulus ideal
  NumPrimes = lg((GEN)Mat[1])-1;      // Number of rows in Mat
  P = idealhermite(K,gmael(Mat,1,1)); // 1st prime from Mat
  M = idealpow(K,P,gmael(Mat,2,1));   // Initialize M to P1^r1
  for(i=2;i<=NumPrimes;++i)
    {
    P = idealhermite(K,gmael(Mat,1,i));  // P = ith prime from Mat
    M = idealmul(K,M,idealpow(K,P,gmael(Mat,2,i)));
    }
  Minv = ginv(M);

  dKg = stoi(dK);
  dLg = gmulsg( dL_Factor, gmul((GEN)CVecVec[2],gpowgs(dKg,5)) );

    // 2nd part of Martinet bound = 2*[dL/(25*dK)]^(1/8)
  TmpGEN = gpow(gdivgs(dLg,25*dK),dbltor(.125),BIGDEFAULTPREC);
  TmpGEN = rtor(TmpGEN,DEFAULTPREC);
  Bnd2 = 2.0*rtodbl(TmpGEN);


  NumCvecs = lg(CVecVec)-3;

    // Compute B and the t_ij's
  B = gmul(gmul(gtrans(M),QHQ),M);
  t11 = sqrt(gtodouble(real_i(gmael(B,1,1))));
  t12 = gtodouble(real_i(gmael(B,2,1)))/t11;
  t22 = sqrt(gtodouble(real_i(gmael(B,2,2)))-t12*t12);

    // Allocate column vectors for the coefficients
  kvec = cgetg(3,t_COL);
  Lvec = cgetg(3,t_COL);
  mvec = cgetg(3,t_COL);
  Nvec = cgetg(3,t_COL);

  ltop5 = avma;    // Save pointer to top of pari stack.

  float Delta_Cvec = 1.0 / NumCvecs;

  for(i=CvecIdx;i<NumCvecs;++i)
    {
    float Cvec_frac_done = i*Delta_Cvec;

    Cvec = (GEN)CVecVec[i+3];
      // By the way the congruence vectors were generated, the 
      // first component gives the value for a1.
    a1 = (GEN)Cvec[1];

    a11 = itos((GEN)a1[1]);
    a12 = itos((GEN)a1[2]);
    Idx = 3*a11 + a12;
    if(Idx<0) Idx=8;  // When 4 doesn't divide dK, the last element of A1Set is -1+2w, 
                      // which would give Idx=-1; so for this case we set Idx=8.

    if(Idx==0) a1_is_0 = 1;
    else       a1_is_0 = 0;

    a1sq_1 = a11*a11 + a12*a12*wsq_1;
    a1sq_2 = 2*a11*a12 + a12*a12*wsq_2;

    a1cb_1 = a11*a1sq_1 + a12*a1sq_2*wsq_1;
    a1cb_2 = a11*a1sq_2 + a12*a1sq_1 + a12*a1sq_2*wsq_2;

    a1_4th_1 = a11*a1cb_1 + a12*a1cb_2*wsq_1;
    a1_4th_2 = a11*a1cb_2 + a12*a1cb_1 + a12*a1cb_2*wsq_2;

    Ca1 = Ca1_pre[Idx] + Bnd2;

      // Compute bound on s2
    if(r2==1)  B_s2 = .5*Ca1*Ca1;
    else       B_s2 = Ca1*Ca1;
    B_s2_sqrt = sqrt(B_s2);

      // Compute ellipsoidal bound on a5
    B_a5 = pow(.2*Ca1,5.0);
    if(r2==1) B_a5 = B_a5/16.0;  // Totally complex case
    B_a5_sqrt = sqrt(B_a5);

    b = mkcol2(stoi(a1sq_1),stoi(a1sq_2));   // b = a1^2

    c = (GEN)Cvec[2];  // Congruence on x^3 coeff
    Cvec_prime = gmul(Minv, gsub(b,gmulsg(2,c)));  // = Minv*(b-2c)
    c1p = .5*gtodouble((GEN)Cvec_prime[1]);
    c2p = .5*gtodouble((GEN)Cvec_prime[2]);
    k2_L = (long) ceil(c2p - B_s2_sqrt/(2*t22) );
    k2_U = (long)floor(c2p + B_s2_sqrt/(2*t22) );

    Cvec_prime = gmul(Minv,(GEN)Cvec[5]);  // Congruence on x^0 coeff
    f1p = gtodouble((GEN)Cvec_prime[1]);
    f2p = gtodouble((GEN)Cvec_prime[2]);
    N2_L = (long)ceil(-B_a5_sqrt/t22 - f2p);
    N2_U = (long)floor(B_a5_sqrt/t22 - f2p);

    long NumVals_N2 = N2_U - N2_L + 1;
    if(NumVals_N2<1) NumVals_N2 = 1;
    float Delta_N2 = 1.0 / NumVals_N2;
    long N2_L_Orig = N2_L;

    if(ChkPntFlag)
      {
      N2_L = max(N2_L,N2_Start);
      }

    if(NumCvecs<MAX_CVECS_TO_DISPLAY)
      {
      fprintf(stderr, "    N2_L = %ld.\n",N2_L);
      fprintf(stderr, "    N2_U = %ld.\n",N2_U);
      }

    bb1  = 2*a11 + a12*Tr_w;
    s[1] = -bb1;
    bb2_L = (long long) ceil(.5*(bb1*bb1-Ca1));
    bb2_U = (long long)floor(.5*(.8*bb1*bb1 + Ca1));
    bb2_pre = a11*a11 + a11*a12*Tr_w + a12*a12*Nm_w;

      // Loop over x^0 coefficient
    for(N2=N2_L;N2<=N2_U;++N2)
      {
      float N2_frac_done = Delta_N2*(N2-N2_L_Orig);

      if(NumCvecs==1)  fprintf(stderr, "      N2 = %ld.\n",N2);

      Nvec[2] = (long)stoi(N2);
      N2p = f2p + N2;
      B1 = sqrt(fabs(B_a5-t22*t22*N2p*N2p));  // The abs value is to fix issues with round off error 
                                              // where the radical was a very small negative value 
                                              // when it should have been 0.

      N1_L = (long) ceil(-f1p + (-B1-t12*N2p)/t11);
      N1_U = (long)floor(-f1p + ( B1-t12*N2p)/t11);

      long NumVals_N1 = N1_U - N1_L + 1;
      if(NumVals_N1<1) NumVals_N1 = 1;
      long N1_L_Orig = N1_L;

        // If ChkPntFlag is set then this case has been previously checkpointed,
        // so use the checkpoint value for N1.  But only do this once!
      if(ChkPntFlag)
        {
        N1_L = max(N1_L,N1_Start);
        ChkPntFlag = 0;
        }

      if(NumCvecs<MAX_CVECS_TO_DISPLAY && NumVals_N2<10)
        {
        fprintf(stderr, "        N1_L = %ld.\n",N1_L);
        fprintf(stderr, "        N1_U = %ld.\n",N1_U);
        }

      ltop4 = avma;

      for(N1=N1_L;N1<=N1_U;++N1)
        {
        //fprintf(stderr, "          N1 = %ld.\n",N1);

        Nvec[1] = (long)stoi(N1);

        a5 = gadd(gmul(M,Nvec),(GEN)Cvec[5]);
        a51 = itos((GEN)a5[1]);
        a52 = itos((GEN)a5[2]);

          // When a1=0, we may assume a52>=0.
        if( !(a1_is_0) || a52>=0 )
          {
            // Check that a5 is nonzero.  Otherwise, the method of Pohst fails 
            // because bb10=a5*s2a5=0, which results in division by zero.
          if(a51!=0 || a52!=0)
            {

            a51sq  = a51*a51;
            a52sq  = a52*a52;
            a51a52 = a51*a52;
            s1a5_mag_sq = a51sq + lambda1*a51a52  + lambda2*a52sq;
            s2a5_mag_sq = a51sq + lambda1c*a51a52 + lambda2c*a52sq;
            s1a5_mag_2_5ths = pow(s1a5_mag_sq,.2);
            s2a5_mag_2_5ths = pow(s2a5_mag_sq,.2);

            if( (s1a5_mag_2_5ths+s2a5_mag_2_5ths) <= Ca1/5.0 )
              {
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

              L2_pre = sqrt(B_s3)/(3.0*t22);
              m2_pre = sqrt(B_s4)/(4.0*t22);

                // Compute bounds on sk for decic (k=3,4,5,6,7,8,9,-1,-2).
              Get_Pohst_Bounds_n10(Ca1,abs(bb10),t);  // t[k]  is bound on sk when k>0.
                                                      // t[-k] is bound on sk when k<0.

              bb9_U0 = (long long)floor(abs(bb10)*t[1]);
              bb9_L0 = -bb9_U0;
              bb8_Upre = .5*abs(bb10)*t[2];

                // Loop over x^3 coefficient
              for(k2=k2_L;k2<=k2_U;++k2)
                {
                //fprintf(stderr, "            k2 = %ld.\n",k2);

                kvec[2] = (long)stoi(k2);
                k2p = c2p - k2;
                B1 = sqrt(fabs(.25*B_s2-t22*t22*k2p*k2p));
                k1_L = (long) ceil(c1p + (-B1+t12*k2p)/t11);
                k1_U = (long)floor(c1p + ( B1+t12*k2p)/t11);
                ltop3 = avma;

                for(k1=k1_L;k1<=k1_U;++k1)
                  {
                  //fprintf(stderr, "              k1 = %ld.\n",k1);

                  kvec[1] = (long)stoi(k1);
                  a2 = gadd(gmul(M,kvec),(GEN)Cvec[2]);
                  a21 = itos((GEN)a2[1]);
                  a22 = itos((GEN)a2[2]);

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

                      b = mkcol2( stoi(3*a1a2_1 - a1cb_1), stoi(3*a1a2_2 - a1cb_2) );
                      c = (GEN)Cvec[3];  // Congruence on x^2 coeff
                      Cvec_prime = gmul(Minv,gsub(b,gmulsg(3,c)));  // = Minv*(b-3c)
                      d1p = gtodouble((GEN)Cvec_prime[1])/3.0;
                      d2p = gtodouble((GEN)Cvec_prime[2])/3.0;
                      L2_L = (long) ceil(d2p - L2_pre);
                      L2_U = (long)floor(d2p + L2_pre);

                      s[2] = bb1*bb1 - 2*bb2;

                      bb3_pre = 2*a11*a21 + (a11*a22+a12*a21)*Tr_w + 2*a12*a22*Nm_w;
                      bb4_pre = a21sq + a21a22*Tr_w + a22sq*Nm_w;
                      bb7_pre = 2*a21*a51 + (a21*a52+a22*a51)*Tr_w + 2*a22*a52*Nm_w;

                        // Compute bounds for bb3
                      Sum3 = bb2*s[1] + bb1*s[2];
                      bb3_L = (long long)ceil((-t[3] - Sum3)/3.0);
                      bb3_U = (long long)floor((t[3] - Sum3)/3.0);

                        // Now loop over x^2 coefficient
                      for(L2=L2_L;L2<=L2_U;++L2)
                        {
                        //fprintf(stderr, "                L2 = %ld.\n",L2);

                        Lvec[2] = (long)stoi(L2);
                        L2p = d2p - L2;
                        B1 = sqrt(fabs(B_s3/9.0-t22*t22*L2p*L2p));
                        L1_L = (long) ceil(d1p + (-B1+t12*L2p)/t11);
                        L1_U = (long)floor(d1p + ( B1+t12*L2p)/t11);
                        ltop2 = avma;

                        for(L1=L1_L;L1<=L1_U;++L1)
                          {
                          //fprintf(stderr, "                  L1 = %ld.\n",L1);

                          Lvec[1] = (long)stoi(L1);
                          a3 = gadd(gmul(M,Lvec),(GEN)Cvec[3]);
                          a31 = itos((GEN)a3[1]);
                          a32 = itos((GEN)a3[2]);

                          a31sq  = a31*a31;
                          a32sq  = a32*a32;
                          a31a32 = a31*a32;
                          s1a3_mag = sqrt(a31sq + lambda1*a31a32  + lambda2*a32sq);
                          s2a3_mag = sqrt(a31sq + lambda1c*a31a32 + lambda2c*a32sq);

                          if( (s1a3_mag<=2*tq[3]) && (s2a3_mag<=2*tqc[3]) )
                            {
                              // Compute bb3.
                            bb3 = bb3_pre + 2*a31 + a32*Tr_w;

                            if(bb3>=bb3_L && bb3<=bb3_U)
                              {

                              a1a3_1 = a11*a31 + a12*a32*wsq_1;
                              a1a3_2 = a11*a32 + a12*a31 + a12*a32*wsq_2;

                                // Set b = a1^4 + 4*a1*a3 - 4*a1^2*a2 + 2*a2^2
                              b = mkcol2( stoi(4*a1a3_1 + bvec_pre_1), 
                                          stoi(4*a1a3_2 + bvec_pre_2) );
                              c = (GEN)Cvec[4];  // Congruence on x coeff
                              Cvec_prime = gmul(Minv,gsub(b,gmulsg(4,c)));  // = Minv*(b-4c)
                              e1p = gtodouble((GEN)Cvec_prime[1])/4.0;
                              e2p = gtodouble((GEN)Cvec_prime[2])/4.0;
                              m2_L = (long) ceil(e2p - m2_pre);
                              m2_U = (long)floor(e2p + m2_pre);

                              bb4_pre2 = bb4_pre + 2*a11*a31 + 
                                         (a11*a32+a12*a31)*Tr_w + 2*a12*a32*Nm_w;
                              bb5_pre2 = bb5_pre + 2*a21*a31 + 
                                         (a21*a32+a22*a31)*Tr_w + 2*a22*a32*Nm_w;
                              bb6_pre2 = bb6_pre + a31sq + a31a32*Tr_w + a32sq*Nm_w;
                              bb8_pre  = 2*a31*a51 + (a31*a52+a32*a51)*Tr_w + 2*a32*a52*Nm_w;

                                // Compute bounds for bb4
                              s[3] = -3*bb3 - Sum3;
                              Sum4 = bb3*s[1] + bb2*s[2] + bb1*s[3];
                              bb4_L = (long long)ceil((-t[4] - Sum4)/4.0);
                              bb4_U = (long long)floor((t[4] - Sum4)/4.0);

                                // Now loop over x^1 coefficient
                              for(m2=m2_L;m2<=m2_U;++m2)
                                {
                                //fprintf(stderr, "                    m2 = %ld.\n",m2);

                                mvec[2] = (long)stoi(m2);
                                m2p = e2p - m2;
                                B1 = sqrt(B_s4/16.0-t22*t22*m2p*m2p);
                                m1_L = (long) ceil(e1p + (-B1+t12*m2p)/t11);
                                m1_U = (long)floor(e1p + ( B1+t12*m2p)/t11);
                                ltop1 = avma;

                                for(m1=m1_L;m1<=m1_U;++m1)
                                  {
                                  //fprintf(stderr, "                      m1 = %ld.\n",m1);

                                  mvec[1] = (long)stoi(m1);
                                  a4 = gadd(gmul(M,mvec),(GEN)Cvec[4]);
                                  a41 = itos((GEN)a4[1]);
                                  a42 = itos((GEN)a4[2]);

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
                                        bb5_L = (long long)ceil((-t[5] - Sum)/5.0);
                                        bb5_U = (long long)floor((t[5] - Sum)/5.0);
                                        if(bb5>=bb5_L && bb5<=bb5_U)
                                          {
                                          bb6 = bb6_pre2 + 2*a21*a41 + 
                                                (a21*a42+a22*a41)*Tr_w + 2*a22*a42*Nm_w;
                                          s[5] = -5*bb5 - Sum;
                                          Sum = bb5*s[1] + bb4*s[2] + bb3*s[3] + bb2*s[4] + bb1*s[5];
                                          bb6_L = (long long)ceil((-t[6] - Sum)/6.0);
                                          bb6_U = (long long)floor((t[6] - Sum)/6.0);
                                          if(bb6>=bb6_L && bb6<=bb6_U)
                                            {
                                            bb7 = bb7_pre + 2*a31*a41 + 
                                                  (a31*a42+a32*a41)*Tr_w + 2*a32*a42*Nm_w;
                                            s[6] = -6*bb6 - Sum;
                                            Sum = bb6*s[1] + bb5*s[2] + bb4*s[3] + bb3*s[4] + 
                                                  bb2*s[5] + bb1*s[6];
                                            bb7_L = (long long)ceil((-t[7] - Sum)/7.0);
                                            bb7_U = (long long)floor((t[7] - Sum)/7.0);
                                            if(bb7>=bb7_L && bb7<=bb7_U)
                                              {
                                              bb8 = bb8_pre + a41sq + a41a42*Tr_w + a42sq*Nm_w;
                                              s[7] = -7*bb7 - Sum;
                                              Sum = bb7*s[1] + bb6*s[2] + bb5*s[3] + bb4*s[4] + 
                                                    bb3*s[5] + bb2*s[6] + bb1*s[7];
                                              bb8_L = (long long)ceil((-t[8] - Sum)/8.0);
                                              bb8_U = (long long)floor((t[8] - Sum)/8.0);
                                              if(bb8>=bb8_L && bb8<=bb8_U)
                                                {
                                                s[8] = -8*bb8 - Sum;
                                                Sum = bb8*s[1] + bb7*s[2] + bb6*s[3] + bb5*s[4] + 
                                                      bb4*s[5] + bb3*s[6] + bb2*s[7] + bb1*s[8];
                                                bb9_L = (long long)ceil((-t[9] - Sum)/9.0);
                                                bb9_U = (long long)floor((t[9] - Sum)/9.0);
                                                if(bb9>=bb9_L && bb9<=bb9_U)
                                                  {
                                                  tmpdbl = .5*bb9*bb9/bb10;
                                                  bb8_L = (long long) ceil(tmpdbl - bb8_Upre);
                                                  bb8_U = (long long)floor(tmpdbl + bb8_Upre);
                                                  if(bb8>=bb8_L && bb8<=bb8_U)
                                                    {
                                                    ++PolyCount;
                                                    f_L = mkpoln(11,gen_1,stoi(bb1),stoi(bb2),stoi(bb3),
                                                                stoi(bb4),stoi(bb5),stoi(bb6),stoi(bb7),
                                                                stoi(bb8),stoi(bb9),stoi(bb10));
                                                    PolDisc = discsr(f_L);

//fprintf(stderr, "f_L = %s.\n",GENtostr(f_L));
//fprintf(stderr, "PolDisc = %s.\n",GENtostr(PolDisc));

                                                    if(!gcmp0(PolDisc))  // PolDisc must be non-zero.
                                                      {
                                                        // Get absolute value of PolDisc
                                                      if(gcmp(PolDisc,gen_0)<0)  PolDisc = gmul(PolDisc,gen_m1);
                                                      for(j=1;j<=n;++j)
                                                        {  // Divide out all factors of p where p is in S
                                                        PolDisc = gdiv(PolDisc,
                                                                  gpowgs((GEN)Sg[j],ggval(PolDisc,(GEN)Sg[j])));
                                                        }
                                                        // Whats left must be a square:
                                                      if(issquare(PolDisc))
                                                        {
                                                        ++Test1_Count;
                                                          // check if f_L is irreducible:
                                                        if(isirreducible(f_L))
                                                          {
                                                          ++Test2_Count;
                                                          //fprintf(stderr, "f is irreducible.\n");
                                                            // Check if field discriminant divides dL:
                                                          if(gdvd(dLg,discf(f_L)))
                                                          //if(gdvd(dLg,nfdisc0(f_L,2,NULL)))  // Use round 2 algorithm
                                                            {
                                                            ++Test3_Count;
                                                            OutStr = GENtostr(f_L);
                                                            //fprintf(stderr, "Poly = %s\n",OutStr);
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
                                  }  // End of loop on m1
                                }  // End of loop on m2
                              }  // bb3 test
                            }  // Matches: if( (s1a3_mag<=2*tq[3]) && (s2a3_mag<=2*tqc[3]) )
                          avma = ltop2;
                          }  // End of loop on L1
                        }  // End of loop on L2
                      }  // bb2 test
                    }  // Matches: if( (s1a2_mag+s2a2_mag) <= 2.0*Ca1 )
                  avma = ltop3;
                  }  // End of loop on k1
                }  // End of loop on k2
              }  // Matches: if( (s1a5_mag_2_5ths+s2a5_mag_2_5ths) <= Ca1/5.0 )
            }  // Matches: if(a51!=0 || a52!=0)
          }  // Matches: if( !(a1_is_0) || a52>=0 )
        avma = ltop4;

          // Do checkpointing
        if(boinc_time_to_checkpoint())
          {
          // Note: timer() returns elapsed time in milliseconds since the last call to timer
          Time_sec = Time_sec + (long)floor(timer()/1000.0 + .5);
	  int retval = do_checkpoint(i,N2,N1+1,PolyCount,Test1_Count,Test2_Count,Test3_Count,Time_sec);
          if(retval)
            {
            fprintf(stderr, "Checkpoint failed!\n");
            exit(retval);
            }
          boinc_checkpoint_completed();
          }

        float N1_frac_done = (N1-N1_L_Orig+1.0)/NumVals_N1;
        float Frac_Done = Cvec_frac_done + Delta_Cvec*(N2_frac_done + Delta_N2*N1_frac_done);
        boinc_fraction_done(Frac_Done);

        //fprintf(stderr, "        Frac_Done = %f.\n",Frac_Done);

        }  // End of loop on N1
      }  // End of loop on N2
    avma = ltop5;

    }  // End loop on i (loop over Cvecs)


  float Percent1 = 0;
  float Percent2 = 0;
  float Percent3 = 0;

  if(PolyCount!=0)    Percent1 = 100.0*Test1_Count/PolyCount;
  if(Test1_Count!=0)  Percent2 = 100.0*Test2_Count/Test1_Count;
  if(Test2_Count!=0)  Percent3 = 100.0*Test3_Count/Test2_Count;

  Time_sec = Time_sec + (long)floor(timer()/1000.0 + .5);

  outfile << "#   The search is complete. Stats:\n";
  outfile << "#   Inspected " << PolyCount << " polynomials.\n";
  outfile << "#   Num Polys passing PolDisc test = " << Test1_Count << " (" << Percent1 << "%).\n";
  outfile << "#   Num Polys passing irreducibility test = " << Test2_Count << " (" << Percent2 << "%).\n";
  outfile << "#   Num Polys passing field disc test = " << Test3_Count << " (" << Percent3 << "%).\n";
  outfile << "#   Elapsed Time = " << Time_sec << " (sec)\n";
  outfile.flush();

  avma = ltop;  // Restore pointer to top of pari stack

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





//******************************************************************************
//* This function writes out discriminant bound, the skip, and the number of
//* congruence vectors for a vector of congruence data.
//******************************************************************************

void Write_Cvec_Stats(GEN Vec)
  {
  long N,NumFactors;
  GEN M,dLg;

  dLg = (GEN)Vec[2];
  N  = lg(Vec)-3;

  M = (GEN)Vec[1];  // modulus ideal
  NumFactors = lg((GEN)M[1])-1;   // Number of rows in M

  //fprintf(stderr, "    NumFactors = %d\n",NumFactors);

  char TmpStr[32];
  string SkipStr = "Skip = ";
  if(NumFactors==1)
    {
    long k = itos((GEN)((GEN)M[2])[1]);  //  col 2, row 1
    sprintf(TmpStr,"P^%ld",k);
    SkipStr += TmpStr;
    }
  else if(NumFactors==2)
    {
    long k1 = itos((GEN)((GEN)M[2])[1]);  //  col 2, row 1
    long k2 = itos((GEN)((GEN)M[2])[2]);  //  col 2, row 2
    sprintf(TmpStr,"(P^%ld)*(Q^%ld)",k1,k2);
    SkipStr += TmpStr;
    }
  else if(NumFactors==3)
    {
    long k1 = itos((GEN)((GEN)M[2])[1]);  //  col 2, row 1
    long k2 = itos((GEN)((GEN)M[2])[2]);  //  col 2, row 2
    long k3 = itos((GEN)((GEN)M[2])[3]);  //  col 2, row 3
    sprintf(TmpStr,"(P1^%ld)*(P2^%ld)*(P3^%ld)",k1,k2,k3);
    SkipStr += TmpStr;
    }
  else
    {
    SkipStr = "";
    }

  char *charStr = GENtostr(dLg);
  fprintf(stderr, "    Disc Bound = %s\n",charStr);
  fprintf(stderr, "    %s\n",SkipStr.c_str());
  fprintf(stderr, "    Num Congruences = %ld\n",N);
  free(charStr);

  return;
  }
