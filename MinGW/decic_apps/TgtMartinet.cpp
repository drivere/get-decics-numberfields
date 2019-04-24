//******************************************************************************
//* This file contains all the necessary functions for doing the imprimitive   *
//* decic (degree 10) searches.                                                *
//******************************************************************************

//typedef long long pari_long;

#include <string>
#include <iostream>
#include <fstream>
#include <math.h>

#ifdef _WIN32
#  include <windows.h>
#endif

#include "boinc_api.h"
#include "GetDecics.h"
#include "TgtMartinet.h"


// Uncomment this to turn on DEBUG
//#define DEBUG_TEST

// Uncomment this to turn on profiling
//#define PROFILER_ON


#define MAX_PRIME 10000
#define MAX_CVECS_TO_DISPLAY 5


using std::ifstream;
using std::ofstream;


// Global variables
GEN Sg,Q,QHQ;
pari_long N2_MIN, N2_MAX, N1_MIN, N1_MAX, K2_MIN, K2_MAX, K1_MIN, K1_MAX;
double Ca1_pre[9], SCALE;
char *polGoodFlag;

// Timer using wall time
struct timespec wallTime;
inline pari_long myTimer() { 
  pari_long sec, msec;
  struct timespec newTime;
  clock_gettime(CLOCK_MONOTONIC, &newTime);
  sec  = newTime.tv_sec - wallTime.tv_sec;
  msec = (newTime.tv_nsec - wallTime.tv_nsec + 500000)/1000000;
  msec = msec + sec*1000;
  wallTime = newTime;
  return msec;
  }



// This function loads data from the WU file; and computes the globals Ca1_pre, Q and QHQ.
// Inputs:
//    FilenameIn  - Filename for the WU data.
//    FilenameOut - Output filename for the list of polynomials found.
//    ChkPntFlag  - Flag telling us if there was a previous check point.
//    CvecIdx     - The starting index for the congruence vectors, only used if ChkPntFlag=1.
//    N1_ChkPnt   - The starting value for the N1 loop, only used if ChkPntFlag=1.
//    N2_ChkPnt   - The starting value for the N2 loop, only used if ChkPntFlag=1.
//    k1_ChkPnt   - The starting value for the k1 loop, only used if ChkPntFlag=1.
//    k2_ChkPnt   - The starting value for the k2 loop, only used if ChkPntFlag=1.
//    L1_ChkPnt   - The starting value for the L1 loop, only used if ChkPntFlag=1.
//    L2_ChkPnt   - The starting value for the L2 loop, only used if ChkPntFlag=1.
//    m1_ChkPnt   - The starting value for the m1 loop, only used if ChkPntFlag=1.
//    m2_ChkPnt   - The starting value for the m2 loop, only used if ChkPntFlag=1.
//    StatVec     - The current statistics count:
//                     StatVec[0] = # polynomials inspected so far.
//                     StatVec[1] = # polynomials passing polynomial discriminant test.
//                     StatVec[2] = # polynomials passing irreduciblity test.
//                     StatVec[3] = # polynomials passing field discriminant test.
//                     StatVec[4] = Elapsed Time counter.

int TgtMartinet(char *FilenameIn, char *FilenameOut, int ChkPntFlag, pari_long CvecIdx, 
                pari_long N1_ChkPnt, pari_long N2_ChkPnt, pari_long k1_ChkPnt, pari_long k2_ChkPnt, 
                pari_long L1_ChkPnt, pari_long L2_ChkPnt, pari_long m1_ChkPnt, pari_long m2_ChkPnt, 
                pari_long *StatVec)
  {
  int  i,a11,a12,r1,r2;
  pari_long ltop,dK,VarNum_y,NumCvecs;
  GEN  K,Kpol,ConVecs,sig1w,sig2w,sig1a1,sig2a1;
  string DataStr;


  pari_init(300000000,MAX_PRIME);  // Reserve 300 MB for the pari stack


  // Initialize the N1,N2,k1,k2 limits in case they are not in the WU file.
  // Set to extreme values (these will get set correctly later)
  N1_MIN = -1E9;
  N2_MIN = -1E9;
  K1_MIN = -1E9;
  K2_MIN = -1E9;
  N1_MAX =  1E9;
  N2_MAX =  1E9;
  K1_MAX =  1E9;
  K2_MAX =  1E9;


  // Open the work unit input file
  fprintf(stderr, "Reading file %s\n",FilenameIn);
  ifstream infile(FilenameIn);
  if(!infile)
    {
    fprintf(stderr, "Could not read file.  Aborting.\n");
    exit(1);
    }

  // Read the WU data from the input file.
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
  NumCvecs = lg(ConVecs)-3;

  // The 4th line, if it exists, is a scale factor to apply to the Martinet bound
  infile >> SCALE;
  if(infile.eof())  SCALE = 1.0;  // This is to handle the case when SCALE is not present.
  if(SCALE<.5 || SCALE>1.0) SCALE = 1.0;  // Just a Safeguard
  fprintf(stderr, "    SCALE = %f\n",SCALE);

  // The 5th and 6th lines, if they exist and NumCvecs=1, are the limits on N2.
  if(!infile.eof() && NumCvecs==1)
    {
    infile >> N2_MIN;
    if(!infile.eof())  infile >> N2_MAX;
    fprintf(stderr, "    N2_MIN = %lld\n",N2_MIN);
    fprintf(stderr, "    N2_MAX = %lld\n",N2_MAX);
    }
  pari_long NumValsN2 = N2_MAX - N2_MIN + 1;

  // The 7th and 8th lines, if they exist and NumValsN2=1, are the limits on N1.
  if(!infile.eof() && NumValsN2==1)
    {
    infile >> N1_MIN;
    if(!infile.eof())  infile >> N1_MAX;
    fprintf(stderr, "    N1_MIN = %lld\n",N1_MIN);
    fprintf(stderr, "    N1_MAX = %lld\n",N1_MAX);
    }
  pari_long NumValsN1 = N1_MAX - N1_MIN + 1;

  // The 9th and 10th lines, if they exist and NumValsN1=1, are the limits on k2.
  if(!infile.eof() && NumValsN1==1)
    {
    infile >> K2_MIN;
    if(!infile.eof())  infile >> K2_MAX;
    fprintf(stderr, "    K2_MIN = %lld\n",K2_MIN);
    fprintf(stderr, "    K2_MAX = %lld\n",K2_MAX);
    }
  pari_long NumValsK2 = K2_MAX - K2_MIN + 1;

  // The 11th and 12th lines, if they exist and NumValsK2=1, are the limits on k1.
  if(!infile.eof() && NumValsK2==1)
    {
    infile >> K1_MIN;
    if(!infile.eof())  infile >> K1_MAX;
    fprintf(stderr, "    K1_MIN = %lld\n",K1_MIN);
    fprintf(stderr, "    K1_MAX = %lld\n",K1_MAX);
    }

  // That is all the inputs, so close the input file.
  infile.close();


  // Save the current top of the pari stack.
  ltop = avma;

  // Extract the signature from the field K
  r1 = itos(gmael(K,2,1));  // K[2]=[r1,r2]
  r2 = itos(gmael(K,2,2));

  // Get absolute value of discriminant of K
  dK = llabs(itos((GEN)K[3]));

  fprintf(stderr, "    |dK| = %lld\n",dK);
  fprintf(stderr, "    Signature = [%d,%d]\n",r1,r2);


  // Get the embeddings applied to the integral basis (as complex numbers).
  // Here sig1w[i] = sig1 applied to w_i.  The others are similarly defined.
  // NOTE: The base field is quadratic, so the integral basis is denoted {1,w}.
  //       The quadratic will take 1 of 2 signatures, [2,0] or [0,1].
  //       [2,0] corresponds to totally real quadratics, and [0,1] corresponds to 
  //       a complex quadratic.  When K is complex, the embedding sig2 is complex
  //       conjugation.
  sig1w = cgetg(3,t_VEC);
  sig2w = cgetg(3,t_VEC);
  for(i=1;i<=2;++i)
    {       // Note: K[5][1]=[[sig_i(w_j)]]
    sig1w[i] = (pari_long)gmael4(K,5,1,i,1);  // This is sig1(w_i)
    if(r1==2)  sig2w[i] = (pari_long)gmael4(K,5,1,i,2);  // This is sig2(w_i)
    else  sig2w[i] = (pari_long)gconj((GEN)sig1w[i]);    // This is the complex case, sig2 is complex conjugation.
    }
  //printf("sig1w = %s\n", GENtostr(sig1w));
  //printf("sig2w = %s\n", GENtostr(sig2w));


  // Precompute the different values for 1st part of Ca1 bound.
  // The first part of the bound is: ( |sig1(a1)|^2 + |sig2(a1)|^2 ) / 5
  // There are 9 possible values for the a1 coefficient.  They are:
  //    if 4 divides dK: {0,1,2,w,1+w,2+w,2w,1+2w,2+2w}
  //    if 4 does not divide dK: {0,1,2,w,1+w,2+w,2w,1+2w,-1+2w}
  //    NOTE: the 2 sets are the same except for the last element.
  // If we write a1 = a11 + a12*w then by linearity of the embeddings:
  //    sig1(a1) = a11 + a12 * sig1(w)
  //    sig2(a1) = a11 + a12 * sig2(w)
  // NOTE: If we wrote the integral basis as {w1,w2}, then below 
  //       sig1w[1] = sig1(w1) and sig1w[2] = sig1(w2)
  //       Since K is quadratic, w1=1, so sig1w[1]=1 (the code below is left over from a more general version)
  //       The same remarks also apply to sig2w[:].
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
  // This is the same Q in Eqn 5.4, p.53 in my dissertation.
  Q = cgetg(3,t_MAT);
  Q[1] = (pari_long)mkcol2((GEN)sig1w[1],(GEN)sig2w[1]);
  Q[2] = (pari_long)mkcol2((GEN)sig1w[2],(GEN)sig2w[2]);
  Q = gerepilecopy(ltop,Q);

  // Compute QHQ (Q-Hermitian * Q). NOTE: Hermitian means conjugate-transpose.
  ltop = avma;
  QHQ = gmul(gconj(gtrans(Q)),Q);
  QHQ = gerepilecopy(ltop,QHQ);
  //printf("Q   = %s\n", GENtostr(Q));
  //printf("QHQ = %s\n", GENtostr(QHQ));


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
  Mart52Engine_Tgt(K, ConVecs, dK, 1, ChkPntFlag, CvecIdx, N1_ChkPnt, N2_ChkPnt, 
     k1_ChkPnt, k2_ChkPnt, L1_ChkPnt, L2_ChkPnt, m1_ChkPnt, m2_ChkPnt, StatVec,outfile);
  fprintf(stderr, "The search has finished.\n");

  outfile.close();

  pari_close();

  return 0;

  }  // End of function TgtMartinet()





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

void Mart52Engine_Tgt(GEN K, GEN CVecVec, pari_long dK, pari_long dL_Factor, int ChkPntFlag, pari_long CvecIdx, 
                      pari_long N1_ChkPnt, pari_long N2_ChkPnt, pari_long k1_ChkPnt, pari_long k2_ChkPnt, 
                      pari_long L1_ChkPnt, pari_long L2_ChkPnt, pari_long m1_ChkPnt, pari_long m2_ChkPnt, 
                      pari_long *StatVec, ofstream& outfile)
  {
  int  a1_is_0,j,Idx;
  pari_long ltop;
  pari_long i,NumPrimes,NumCvecs;
  pari_long k1,k2,k1_L,k1_U,k2_L,k2_U,L1,L2,L1_L,L1_U,L2_L,L2_U;
  pari_long m1,m2,m1_L,m1_U,m2_L,m2_U,N1,N2,N1_L,N1_U,N2_L,N2_U;
  pari_long bb[11],s[10],Sum,Sum3,Sum4;
  pari_long bb2_L,bb2_U,bb3_L,bb3_U,bb4_L,bb4_U,bb5_L,bb5_U,bb6_L,bb6_U,bb7_L,bb7_U;
  pari_long bb8_L,bb8_U,bb9_L,bb9_U,bb9_L0,bb9_U0;
  pari_long bb2_pre,bb3_pre,bb4_pre,bb5_pre,bb6_pre,bb7_pre,bb8_pre;
  pari_long bb4_pre2,bb5_pre2,bb6_pre2,bvec_pre_1,bvec_pre_2;
  pari_long wsq_1,wsq_2,Tr_w,Nm_w,r2;
  pari_long a11,a12,a1sq_1,a1sq_2,a1cb_1,a1cb_2,a1_4th_1,a1_4th_2;
  pari_long a2sq_1,a2sq_2,a1a2_1,a1a2_2,a1sq_a2_1,a1sq_a2_2,a1a3_1,a1a3_2;
  pari_long a21,a22,a21sq,a22sq,a21a22;
  pari_long a31,a32,a31sq,a32sq,a31a32;
  pari_long a41,a42,a41sq,a42sq,a41a42;
  pari_long a51,a52,a51sq,a52sq,a51a52;
  pari_long cv21,cv22,cv31,cv32,cv41,cv42,cv51,cv52;
  pari_long M11,M12,M21,M22,b1,b2;
  double lambda1,lambda2,lambda1c,lambda2c;
  double tq[5],tqc[5],t[10],t11,t12,t22,bb8_Upre,tmpdbl;
  double Bnd2,Ca1,B1,B_s2,B_s3,B_s4,B_a4,B_a4c,B_a5,B_a5_sqrt,B_s2_sqrt;
  double s1a2_mag,s2a2_mag,s1a3_mag,s2a3_mag,s1a4_mag,s2a4_mag;
  double s1a5_mag,s2a5_mag,s1a5_mag_sq,s2a5_mag_sq,s1a5_mag_2_5ths,s2a5_mag_2_5ths;
  double c1p,c2p,d1p,d2p,e1p,e2p,f1p,f2p,k2p,L2p,m2p,N2p,L2_pre,m2_pre;
  double Minv11,Minv12,Minv21,Minv22;


/************************************************************************************
                               GENERAL NOTES:
We are looking for degree 10 fields that are degree 5 extensions of a quadratic 
base field.  The quadratic field is denoted K, and the degree 10 field is denoted L.
Since these fields are extensions of the rationals, they are represented by 
polynomials with integer coefficients.  The algorithm basically computes bounds 
for the polynomial coefficients and then loops over these bounds.

The polynomial under test can be viewed from two perspectives.  The first is as 
a degree 10 polynomial with integer coefficients:
f(x) = x^10 + b1*x^9 + b2*x^8 + b3*x^7 + b4*x^6 + b5*x^5 + b6*x^4 + b7*x^3 + b8*x^2 + b9*x^1 + b10
Note these b coefficients are denoted bb in the variable declarations above.
Also, the bbx_L and bbx_U variables represent Lower and Upper bounds for 
these coefficients.  These coefficients are not explicitly looped over, but 
they are computed along the way and compared with their respective bounds in 
order to more quickly rule out the current polynomial under test.

The second way of representing the polynomial is as a degree 5 polynomial over 
the base field K.  In this representation we write:
f(x) = x^5 + a1*x^4 + a2*x^3 + a3*x^2 + a4*x + a5
where each of the coefficients is an "integer" from the ring of integers of K.
The ring of integers of K has an integral basis which we denote {1,w}.
[An integral basis can be thought of as a "vector space" over the integers, so 
that any element z in the ring of integers of K can be written as z = z1 + z2*w. 
I put vector space in quotes, because the integers are not a field. Technically 
speaking, the integral basis is a "Z-module", but most non-mathematicians have 
no idea what that means.]
Therefore, the coefficients can be written:
   a1 = a11 + a12*w
   a2 = a21 + a22*w
   a3 = a31 + a32*w
   a4 = a41 + a42*w
   a5 = a51 + a52*w
where each aij is an integer.
We have the following associations in the loops below:
  a2:  k = k1 + k2*w
  a3:  L = L1 + L2*w
  a4:  m = m1 + m2*w
  a5:  N = N1 + N2*w
The algorithm loops over the coefficients in the following order:
a5,a2,a3,a4; or more explicitly: (N2,N1,k2,k1,L2,L1,m2,m1).
The reason for using two sets of looping variables is that the (k,L,m,N) values are 
sequential, whereas the (a2,a3,a4,a5) values must obey certain congruence relations.
NOTE: It may be possible to rewrite the code so that we loop directly over a21,a22,...
      But if this were done, the for loops would look something like this:
         for(a21=a21_L; a21<=a21_U; a21=a21+skip)
      where the skip would need to be computed from the current values of the outer
      loops.  Maybe that's more efficient or the same as what I am currently
      doing, it's hard to say.
Also note there is no explicit loop over the a1 coefficient.  That is because
the outermost loop is over the congruence vectors, and each congruence vector 
is associated with a fixed value of a1.
************************************************************************************/


  // Start the timer.
  myTimer();


  ltop = avma;

  // Again, the integral basis is denoted {1,w}.
  // Get w and the components of w^2.
  // Also compute the trace and norm of w.
  GEN w_alg = basistoalg(K,mkcol2(gen_0,gen_1));  // Convert w into algebraic number (represented as a pari t_POLMOD)
  GEN w_sq  = algtobasis(K,gsqr(w_alg));          // Square w and convert back to integral basis format.
  wsq_1 = itos((GEN)w_sq[1]);  // w^2 = wsq_1 + wsq_2 * w
  wsq_2 = itos((GEN)w_sq[2]);
  // This is w and its Galois conjugate as complex numbers:
  GEN w  = gmael(Q,2,1);  // row 1, col 2
  GEN wc = gmael(Q,2,2);  // row 2, col 2  (the Galois conjugate of w)
  // This is the trace and norm of w (which are always integers):
  Tr_w = (pari_long)floor(gtodouble(real_i(gadd(w,wc)))+.5);
  Nm_w = (pari_long)floor(gtodouble(real_i(gmul(w,wc)))+.5);

  // Compute the parameters lambda1 and lambda2 (and their galois conjugates).
  // These quantities appear in several of the equations that bound the polynomial
  // coefficients, so it is best to compute them here, rather than inside the loops below. 
  r2 = itos(gmael(K,2,2));  // K[2]=[r1,r2] is the signature of the field K (r2 is the number of complex embeddings)
  if(r2==1)  // Then the subfield is complex. [ie K=Q(sqrt(m)) where m<0]
    {
    lambda1  = (double)Tr_w;
    lambda2  = (double)Nm_w;
    lambda1c = lambda1;
    lambda2c = lambda2;
    }
  else  // K is real.  w and wc are real (but stored as complex)
    {
    lambda1  = 2.0*gtodouble(real_i(w));
    lambda2  = gtodouble(real_i(gsqr(w)));
    lambda1c = 2.0*gtodouble(real_i(wc));
    lambda2c = gtodouble(real_i(gsqr(wc)));
    }


  // This computes the matrix M and it's inverse.
  // NOTE: M is defined about half way down on p.56 of my dissertation.
  GEN Mat = (GEN)CVecVec[1];     // Matrix representing the modulus ideal
  NumPrimes = lg((GEN)Mat[1])-1;      // Number of rows in Mat
  GEN P = idealhermite(K,gmael(Mat,1,1)); // 1st prime from Mat (in Hermite normal form)
  GEN M = idealpow(K,P,gmael(Mat,2,1));   // Initialize M to P1^r1
  for(i=2;i<=NumPrimes;++i)
    {
    P = idealhermite(K,gmael(Mat,1,i));  // P = ith prime from Mat
    M = idealmul(K,M,idealpow(K,P,gmael(Mat,2,i))); // M=M*Pi^ri  for ith prime
    }
  GEN Minv = ginv(M);  // The inverse of the matrix M
  //printf("M    = %s\n", GENtostr(M));
  //printf("Minv = %s\n", GENtostr(Minv));

  // Extract elements of M and Minv and store in native data types.
  M11 = itos(gmael(M,1,1));
  M12 = itos(gmael(M,2,1));
  M21 = itos(gmael(M,1,2));
  M22 = itos(gmael(M,2,2));
  Minv11 = gtodouble(real_i(gmael(Minv,1,1)));
  Minv12 = gtodouble(real_i(gmael(Minv,2,1)));
  Minv21 = gtodouble(real_i(gmael(Minv,1,2)));
  Minv22 = gtodouble(real_i(gmael(Minv,2,2)));
  //printf("converted M    = [%ld, %ld; %ld, %ld]\n", M11,M12,M21,M22);
  //printf("converted Minv = [%g, %g; %g, %g]\n", Minv11,Minv12,Minv21,Minv22);



  // Recall: K is the quadratic base field and L is the degree 5 extension of K
  //         (taken together they give a degree 10 extension of the rationals).
  // dKg is the discriminant K (as a pari GEN).
  // dLg is the targeted disriminant of L (as a pari GEN).
  GEN dKg  = stoi(dK);
  GEN dLg  = gmulsg( dL_Factor, gmul((GEN)CVecVec[2],gpowgs(dKg,5)) );

  // Compute 2nd part of Martinet bound = 2*[dL/(25*dK)]^(1/8)
  GEN TmpGEN = gpow(gdivgs(dLg,25*dK),dbltor(.125),BIGDEFAULTPREC);
  TmpGEN = rtor(TmpGEN,DEFAULTPREC);
  Bnd2 = 2.0*rtodbl(TmpGEN);

  // This is the number of congruence vectors to loop over.
  NumCvecs = lg(CVecVec)-3;

  // Compute B and the corresponding t_ij's
  // The t_ij's are defined in Eqn 5.13 on p.55 in my dissertation.
  GEN B = gmul(gmul(gtrans(M),QHQ),M);  // This is (Q*M)^H * (Q*M)
  t11 = sqrt(gtodouble(real_i(gmael(B,1,1))));
  t12 = gtodouble(real_i(gmael(B,2,1)))/t11;
  t22 = sqrt(gtodouble(real_i(gmael(B,2,2)))-t12*t12);
  //printf("B = %s\n", GENtostr(B));

  float Delta_Cvec = 1.0 / NumCvecs;

  bb[0]=1;  // The decic polynomial is monic


#ifdef DEBUG_TEST
  polyBufferSize = 1;  // Test a single polynomial when debugging.
#endif


  // Allocate memory for the polynomial buffers and the polGoodFlag.
  // We use a double buffering system so the cpu can buffer the next batch while 
  // the gpu is processing the previous batch (i.e. parallelize cpu and gpu).
  pari_long *polyBuffer1 = (pari_long*)malloc(polyBufferSize * 11 * sizeof(pari_long));
  if (!polyBuffer1) {
    fprintf(stderr, "Failed to allocate polynomial buffer 1.\n");
    exit(1);
  }
  pari_long *polyBuffer2 = (pari_long*)malloc(polyBufferSize * 11 * sizeof(pari_long));
  if (!polyBuffer2) {
    fprintf(stderr, "Failed to allocate polynomial buffer 2.\n");
    exit(1);
  }
  polGoodFlag = (char*)malloc(polyBufferSize * sizeof(char));
  if (!polGoodFlag) {
    fprintf(stderr, "Failed to allocate polGoodFlag array.\n");
    exit(1);
  }
  int buffCnt = 0; // A count of how many polynomials are currently in the buffer.

  // Loop indices corresponding to the two polynomial buffers.
  // These are used when checkpointing.
  pari_long loopIdxs1[9], loopIdxs2[9];

  // Set the current polynomial buffer to the first buffer.
  // Similarly, point to the first loopIdxs vector.
  pari_long *polyBuffer = polyBuffer1;
  pari_long *loopIdxs = loopIdxs1;
  int bufferPtr = 0;  // This is a toggle switch that points to the current buffer.


  for(i=CvecIdx;i<NumCvecs;++i)
    {
    float Cvec_frac_done = i*Delta_Cvec;

    // Extract the congruence vector for the current index.
    GEN Cvec = (GEN)CVecVec[i+3];

    // By the way the congruence vectors were generated, the 
    // first component gives the value for a1.
    GEN a1 = (GEN)Cvec[1];

    // Extract the congruences and store in 64bit longs
    GEN cv;
    cv = (GEN)Cvec[2];  cv21 = itos((GEN)cv[1]);  cv22 = itos((GEN)cv[2]);
    cv = (GEN)Cvec[3];  cv31 = itos((GEN)cv[1]);  cv32 = itos((GEN)cv[2]);
    cv = (GEN)Cvec[4];  cv41 = itos((GEN)cv[1]);  cv42 = itos((GEN)cv[2]);
    cv = (GEN)Cvec[5];  cv51 = itos((GEN)cv[1]);  cv52 = itos((GEN)cv[2]);


    // Recall each coefficient is an element in the quadratic field K, so has two 
    // components when written in terms of the integral basis.
    // a1 = a11 + a12 * w  where {1,w} is the integral basis.
    a11 = itos((GEN)a1[1]);
    a12 = itos((GEN)a1[2]);
    Idx = 3*a11 + a12;
    if(Idx<0) Idx=8;  // When 4 doesn't divide dK, the last element of A1Set is -1+2w,
                      // which would give Idx=-1; so for this case we set Idx=8.

    if(Idx==0) a1_is_0 = 1;
    else       a1_is_0 = 0;

    // These are the two components of a1^2
    a1sq_1 = a11*a11 + a12*a12*wsq_1;
    a1sq_2 = 2*a11*a12 + a12*a12*wsq_2;

    // These are the two components of a1^3
    a1cb_1 = a11*a1sq_1 + a12*a1sq_2*wsq_1;
    a1cb_2 = a11*a1sq_2 + a12*a1sq_1 + a12*a1sq_2*wsq_2;

    // These are the two components of a1^4
    a1_4th_1 = a11*a1cb_1 + a12*a1cb_2*wsq_1;
    a1_4th_2 = a11*a1cb_2 + a12*a1cb_1 + a12*a1cb_2*wsq_2;

    // This is the Martinet bound corresponding to the current value of a1.
    Ca1 = Ca1_pre[Idx] + Bnd2;

    // Apply the scale factor to the Martinet Bound
    // The SCALE factor allows us to artificially decrease the bound in order to
    // speed up the loops below.  This means the search is not guaranteed to find
    // all fields, but allows the testing of more congruence vectors.  This SCALE
    // factor is rarely used and can be removed for the GPU app.
    Ca1 = Ca1 * SCALE;

    // Compute bound on s2
    // NOTE: s[2] is the 2nd power sum (i.e. the sum of the squares of the polynomial roots).
    //       In general, s[n] is the nth power sum (sum of nth powers of the roots).
    //       The power sums and their bounds is discussed on p.11 of my dissertation.
    if(r2==1)  B_s2 = .5*Ca1*Ca1;
    else       B_s2 = Ca1*Ca1;
    B_s2_sqrt = sqrt(B_s2);

    // Compute ellipsoidal bound on a5
    B_a5 = pow(.2*Ca1,5.0);
    if(r2==1) B_a5 = B_a5/16.0;  // Totally complex case
    B_a5_sqrt = sqrt(B_a5);


    // This calculation is described in section 5.4 (starting p.56) in my dissertation.
    // This is .5 * Minv*(a1^2-2c) where c = Cvec[2] = congruence on x^3 coeff
    c1p = .5 * (Minv11*(a1sq_1-2*cv21) + Minv12*(a1sq_2-2*cv22) );
    c2p = .5 * (Minv21*(a1sq_1-2*cv21) + Minv22*(a1sq_2-2*cv22) );

    k2_L = (pari_long) ceil(c2p - B_s2_sqrt/(2*t22) );
    k2_U = (pari_long)floor(c2p + B_s2_sqrt/(2*t22) );

    k2_L = max(k2_L,K2_MIN);
    k2_U = min(k2_U,K2_MAX);

    pari_long NumVals_k2 = k2_U - k2_L + 1;
    if(NumVals_k2<1) NumVals_k2 = 1;
    float Delta_k2 = 1.0 / NumVals_k2;
    pari_long k2_L_Orig = k2_L;

    // This is Minv * Cvec[5]
    f1p = Minv11*cv51 + Minv12*cv52;
    f2p = Minv21*cv51 + Minv22*cv52;

    N2_L = (pari_long)ceil(-B_a5_sqrt/t22 - f2p);
    N2_U = (pari_long)floor(B_a5_sqrt/t22 - f2p);

    N2_L = max(N2_L,N2_MIN);
    N2_U = min(N2_U,N2_MAX);

    pari_long NumVals_N2 = N2_U - N2_L + 1;
    if(NumVals_N2<1) NumVals_N2 = 1;
    float Delta_N2 = 1.0 / NumVals_N2;
    pari_long N2_L_Orig = N2_L;

    // If ChkPntFlag is set then this case has been previously checkpointed,
    // so use the checkpoint value for N2 and k2.
    if(ChkPntFlag)
      {
      N2_L = max(N2_L,N2_ChkPnt);
      k2_L = max(k2_L,k2_ChkPnt);
      }

    if(NumCvecs<MAX_CVECS_TO_DISPLAY)
      {
      fprintf(stderr, "    N2_L = %lld.\n",N2_L);
      fprintf(stderr, "    N2_U = %lld.\n",N2_U);
      }

    bb[1] = 2*a11 + a12*Tr_w;
    s[1]  = -bb[1];
    bb2_L = (pari_long) ceil(.5*(bb[1]*bb[1]-Ca1));
    bb2_U = (pari_long)floor(.5*(.8*bb[1]*bb[1] + Ca1));
    bb2_pre = a11*a11 + a11*a12*Tr_w + a12*a12*Nm_w;

    // Loop over x^0 coefficient
    // This coefficient is N = N1 + N2*w, so it consists of a double loop; first we 
    // loop on N2 and then the current value of N2 is used to get the loop range for N1.
    for(N2=N2_L;N2<=N2_U;++N2)
      {
      float N2_frac_done = Delta_N2*(N2-N2_L_Orig);

      if(NumCvecs==1)  fprintf(stderr, "      N2 = %lld.\n",N2);

      N2p = f2p + N2;
      B1 = sqrt(fabs(B_a5-t22*t22*N2p*N2p));  // The abs value is to fix issues with round off error 
                                              // where the radical was a very small negative value 
                                              // when it should have been 0.

      N1_L = (pari_long) ceil(-f1p + (-B1-t12*N2p)/t11);
      N1_U = (pari_long)floor(-f1p + ( B1-t12*N2p)/t11);

      N1_L = max(N1_L,N1_MIN);
      N1_U = min(N1_U,N1_MAX);

      pari_long NumVals_N1 = N1_U - N1_L + 1;
      if(NumVals_N1<1) NumVals_N1 = 1;
      float Delta_N1 = 1.0 / NumVals_N1;
      pari_long N1_L_Orig = N1_L;

      // If ChkPntFlag is set then this case has been previously checkpointed,
      // so use the checkpoint value for N1.
      if(ChkPntFlag)
        {
        N1_L = max(N1_L,N1_ChkPnt);
        }

      if(NumCvecs<MAX_CVECS_TO_DISPLAY && NumVals_N2<10)
        {
        fprintf(stderr, "        N1_L = %lld.\n",N1_L);
        fprintf(stderr, "        N1_U = %lld.\n",N1_U);
        }

      for(N1=N1_L;N1<=N1_U;++N1)
        {
        float N1_frac_done = Delta_N1*(N1-N1_L_Orig);

        if(NumCvecs==1 && NumVals_N2==1)  fprintf(stderr, "          N1 = %lld.\n",N1);

        a51 = M11*N1 + M12*N2 + cv51;
        a52 = M21*N1 + M22*N2 + cv52;

        // When a1=0, we may assume a52>=0.
        if( !(a1_is_0) || a52>=0 )
          {
          // Check that a5 is nonzero.  Otherwise, the method of Pohst fails 
          // because bb10=a5*s2a5=0, which results in division by zero.
          // NOTE: When a5=0, the polynomial is reducible, so it cant possibly represent our field anyways.
          if(a51!=0 || a52!=0)
            {
            a51sq  = a51*a51;
            a52sq  = a52*a52;
            a51a52 = a51*a52;
            s1a5_mag_sq = a51sq + lambda1*a51a52  + lambda2*a52sq;
            s2a5_mag_sq = a51sq + lambda1c*a51a52 + lambda2c*a52sq;
            s1a5_mag_2_5ths = pow(s1a5_mag_sq,.2);
            s2a5_mag_2_5ths = pow(s2a5_mag_sq,.2);

            // This check is Thm 2.15 in my dissertation.
            //   s1a5_mag_2_5ths = |sig1(a5)|^(2/5)
            //   s2a5_mag_2_5ths = |sig2(a5)|^(2/5)
            if( (s1a5_mag_2_5ths+s2a5_mag_2_5ths) <= Ca1/5.0 )
              {
              s1a5_mag = sqrt(s1a5_mag_sq);
              s2a5_mag = sqrt(s2a5_mag_sq);

              bb5_pre = 2*a51 + a52*Tr_w;  // a5 + a5conj
              bb6_pre = 2*a11*a51 + (a11*a52+a12*a51)*Tr_w + 2*a12*a52*Nm_w;
              bb[10] = a51sq + a51a52*Tr_w + a52sq*Nm_w;

              // Compute bound on s3, s4, and s_{-1} for relative quintic
              // The method of Pohst gives very good bounds.
              if(r2==1)  // Then K is complex
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
              Get_Pohst_Bounds_n10(Ca1,llabs(bb[10]),t);  // t[k]  is bound on sk when k>0.
                                                        // t[-k] is bound on sk when k<0.

              bb9_U0 = (pari_long)floor(llabs(bb[10])*t[1]);
              bb9_L0 = -bb9_U0;
              bb8_Upre = .5*llabs(bb[10])*t[2];

              if(NumCvecs==1 && NumVals_N2==1 && NumVals_N1==1) {
                fprintf(stderr, "            k2 range: %lld => %lld.\n",k2_L,k2_U); }

              // Loop over x^3 coefficient
              // This coefficient is k = k1 + k2*w, so it consists of a double loop; first we 
              // loop on k2 and then the current value of k2 is used to get the loop range for k1.
              for(k2=k2_L;k2<=k2_U;++k2)
                {
                float k2_frac_done = Delta_k2*(k2-k2_L_Orig);

                if(NumCvecs==1 && NumVals_N2==1 && NumVals_N1==1) {
                  fprintf(stderr, "            k2 = %lld.\n",k2); }

                k2p = c2p - k2;
                B1 = sqrt(fabs(.25*B_s2-t22*t22*k2p*k2p));
                k1_L = (pari_long) ceil(c1p + (-B1+t12*k2p)/t11);
                k1_U = (pari_long)floor(c1p + ( B1+t12*k2p)/t11);

                k1_L = max(k1_L,K1_MIN);
                k1_U = min(k1_U,K1_MAX);

                pari_long NumVals_k1 = k1_U - k1_L + 1;
                if(NumVals_k1<1) NumVals_k1 = 1;
                pari_long k1_L_Orig = k1_L;

                if(NumCvecs==1 && NumVals_N2==1 && NumVals_N1==1 && NumVals_k2==1) {
                  fprintf(stderr, "            k1 range: %lld => %lld.\n",k1_L,k1_U); }

                // If ChkPntFlag is set then this case has been previously checkpointed,
                // so use the checkpoint value for k1.
                if(ChkPntFlag)
                  {
                  k1_L = max(k1_L,k1_ChkPnt);
                  }

                for(k1=k1_L;k1<=k1_U;++k1)
                  {

                  if(NumCvecs==1 && NumVals_N2==1 && NumVals_N1==1 && NumVals_k2==1) {
                    fprintf(stderr, "            k1 = %lld.\n",k1); }

                  a21 = M11*k1 + M12*k2 + cv21;
                  a22 = M21*k1 + M22*k2 + cv22;

                  a21sq  = a21*a21;
                  a22sq  = a22*a22;
                  a21a22 = a21*a22;
                  s1a2_mag = sqrt(a21sq + lambda1*a21a22  + lambda2*a22sq);
                  s2a2_mag = sqrt(a21sq + lambda1c*a21a22 + lambda2c*a22sq);

                  // This check is Thm 2.17 in my dissertation.
                  if( (s1a2_mag+s2a2_mag) <= 2.0*Ca1 )
                    {

                    bb[2] = bb2_pre + 2*a21 + a22*Tr_w;

                    if(bb[2]>=bb2_L && bb[2]<=bb2_U)
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

                      // This is Minv*(b-3c)/3 where b = 3*a1*a2 - a1^3
                      // and c = Cvec[3] = congruence on x^2 coeff
                      b1 = 3*a1a2_1 - a1cb_1;
                      b2 = 3*a1a2_2 - a1cb_2;
                      d1p = ( Minv11*(b1-3*cv31) + Minv12*(b2-3*cv32) ) / 3.0;
                      d2p = ( Minv21*(b1-3*cv31) + Minv22*(b2-3*cv32) ) / 3.0;

                      L2_L = (pari_long) ceil(d2p - L2_pre);
                      L2_U = (pari_long)floor(d2p + L2_pre);

                      s[2] = bb[1]*bb[1] - 2*bb[2];

                      bb3_pre = 2*a11*a21 + (a11*a22+a12*a21)*Tr_w + 2*a12*a22*Nm_w;
                      bb4_pre = a21sq + a21a22*Tr_w + a22sq*Nm_w;
                      bb7_pre = 2*a21*a51 + (a21*a52+a22*a51)*Tr_w + 2*a22*a52*Nm_w;

                      // Compute bounds for bb3
                      Sum3 = bb[2]*s[1] + bb[1]*s[2];
                      bb3_L = (pari_long)ceil((-t[3] - Sum3)/3.0);
                      bb3_U = (pari_long)floor((t[3] - Sum3)/3.0);

                      // If ChkPntFlag is set then this case has been previously checkpointed,
                      // so use the checkpoint value for L2.
                      if(ChkPntFlag)
                        {
                        L2_L = max(L2_L,L2_ChkPnt);
                        }

                      // Now loop over x^2 coefficient
                      // This coefficient is L = L1 + L2*w, so it consists of a double loop; first we 
                      // loop on L2 and then the current value of L2 is used to get the loop range for L1.
                      for(L2=L2_L;L2<=L2_U;++L2)
                        {
                        //fprintf(stderr, "                L2 = %lld.\n",L2);

                        L2p = d2p - L2;
                        B1 = sqrt(fabs(B_s3/9.0-t22*t22*L2p*L2p));
                        L1_L = (pari_long) ceil(d1p + (-B1+t12*L2p)/t11);
                        L1_U = (pari_long)floor(d1p + ( B1+t12*L2p)/t11);

                        // If ChkPntFlag is set then this case has been previously checkpointed,
                        // so use the checkpoint value for L1.
                        if(ChkPntFlag)
                          {
                          L1_L = max(L1_L,L1_ChkPnt);
                          }

                        for(L1=L1_L;L1<=L1_U;++L1)
                          {
                          //fprintf(stderr, "                  L1 = %lld.\n",L1);

                          a31 = M11*L1 + M12*L2 + cv31;
                          a32 = M21*L1 + M22*L2 + cv32;

                          a31sq  = a31*a31;
                          a32sq  = a32*a32;
                          a31a32 = a31*a32;
                          s1a3_mag = sqrt(a31sq + lambda1*a31a32  + lambda2*a32sq);
                          s2a3_mag = sqrt(a31sq + lambda1c*a31a32 + lambda2c*a32sq);

                          if( (s1a3_mag<=2*tq[3]) && (s2a3_mag<=2*tqc[3]) )
                            {
                            // Compute bb3.
                            bb[3] = bb3_pre + 2*a31 + a32*Tr_w;

                            if(bb[3]>=bb3_L && bb[3]<=bb3_U)
                              {

                              a1a3_1 = a11*a31 + a12*a32*wsq_1;
                              a1a3_2 = a11*a32 + a12*a31 + a12*a32*wsq_2;

                              // Set b = a1^4 + 4*a1*a3 - 4*a1^2*a2 + 2*a2^2
                              // Compute e = Minv*(b-4c)/4
                              b1 = 4*a1a3_1 + bvec_pre_1;
                              b2 = 4*a1a3_2 + bvec_pre_2;
                              e1p = ( Minv11*(b1-4*cv41) + Minv12*(b2-4*cv42) ) / 4.0;
                              e2p = ( Minv21*(b1-4*cv41) + Minv22*(b2-4*cv42) ) / 4.0;

                              m2_L = (pari_long) ceil(e2p - m2_pre);
                              m2_U = (pari_long)floor(e2p + m2_pre);

                              bb4_pre2 = bb4_pre + 2*a11*a31 + 
                                         (a11*a32+a12*a31)*Tr_w + 2*a12*a32*Nm_w;
                              bb5_pre2 = bb5_pre + 2*a21*a31 + 
                                         (a21*a32+a22*a31)*Tr_w + 2*a22*a32*Nm_w;
                              bb6_pre2 = bb6_pre + a31sq + a31a32*Tr_w + a32sq*Nm_w;
                              bb8_pre  = 2*a31*a51 + (a31*a52+a32*a51)*Tr_w + 2*a32*a52*Nm_w;

                                // Compute bounds for bb4
                              s[3] = -3*bb[3] - Sum3;
                              Sum4 = bb[3]*s[1] + bb[2]*s[2] + bb[1]*s[3];
                              bb4_L = (pari_long)ceil((-t[4] - Sum4)/4.0);
                              bb4_U = (pari_long)floor((t[4] - Sum4)/4.0);

                              // If ChkPntFlag is set then this case has been previously checkpointed,
                              // so use the checkpoint value for m2.
                              if(ChkPntFlag)
                                {
                                m2_L = max(m2_L,m2_ChkPnt);
                                }

                              // Now loop over x^1 coefficient
                              // This coefficient is m = m1 + m2*w, so it consists of a double loop; first we 
                              // loop on m2 and then the current value of m2 is used to get the loop range for m1.
                              for(m2=m2_L;m2<=m2_U;++m2)
                                {
                                //fprintf(stderr, "                    m2 = %lld.\n",m2);

                                m2p = e2p - m2;
                                B1 = sqrt(B_s4/16.0-t22*t22*m2p*m2p);
                                m1_L = (pari_long) ceil(e1p + (-B1+t12*m2p)/t11);
                                m1_U = (pari_long)floor(e1p + ( B1+t12*m2p)/t11);

                                // If ChkPntFlag is set then this case has been previously checkpointed,
                                // so use the checkpoint value for m1.
                                // We only want to do this once, so reset the ChkPntFlag.
                                // NOTE: k2 is not like the other loop indices in that his limits are
                                //       computed several layers before his actual loop.  So we need 
                                //       to reset his lower limit to the pre-checkpoint value.
                                if(ChkPntFlag)
                                  {
                                  m1_L = max(m1_L,m1_ChkPnt);
                                  k2_L = k2_L_Orig;  // Restore k2_L to its original value.
                                  ChkPntFlag = 0;
                                  }

                                for(m1=m1_L;m1<=m1_U;++m1)
                                  {
                                  //fprintf(stderr, "                      m1 = %lld.\n",m1);

                                  a41 = M11*m1 + M12*m2 + cv41;
                                  a42 = M21*m1 + M22*m2 + cv42;

                                  a41sq  = a41*a41;
                                  a42sq  = a42*a42;
                                  a41a42 = a41*a42;
                                  s1a4_mag = sqrt(a41sq + lambda1*a41a42  + lambda2*a42sq);
                                  s2a4_mag = sqrt(a41sq + lambda1c*a41a42 + lambda2c*a42sq);

                                  if( (s1a4_mag<=B_a4) && (s2a4_mag<=B_a4c) )
                                    {
                                    bb[9] = 2*a41*a51 + (a41*a52+a42*a51)*Tr_w + 2*a42*a52*Nm_w;
                                    if(bb[9]>=bb9_L0 && bb[9]<=bb9_U0)
                                      {
                                      bb[4] = bb4_pre2 + 2*a41 + a42*Tr_w;
                                      if(bb[4]>=bb4_L && bb[4]<=bb4_U)
                                        {
                                        bb[5] = bb5_pre2 + 2*a11*a41 + 
                                              (a11*a42+a12*a41)*Tr_w + 2*a12*a42*Nm_w;
                                        s[4] = -4*bb[4] - Sum4;
                                        Sum = bb[4]*s[1] + bb[3]*s[2] + bb[2]*s[3] + bb[1]*s[4];
                                        bb5_L = (pari_long)ceil((-t[5] - Sum)/5.0);
                                        bb5_U = (pari_long)floor((t[5] - Sum)/5.0);
                                        if(bb[5]>=bb5_L && bb[5]<=bb5_U)
                                          {
                                          bb[6] = bb6_pre2 + 2*a21*a41 + 
                                                (a21*a42+a22*a41)*Tr_w + 2*a22*a42*Nm_w;
                                          s[5] = -5*bb[5] - Sum;
                                          Sum = bb[5]*s[1] + bb[4]*s[2] + bb[3]*s[3] + bb[2]*s[4] + bb[1]*s[5];
                                          bb6_L = (pari_long)ceil((-t[6] - Sum)/6.0);
                                          bb6_U = (pari_long)floor((t[6] - Sum)/6.0);
                                          if(bb[6]>=bb6_L && bb[6]<=bb6_U)
                                            {
                                            bb[7] = bb7_pre + 2*a31*a41 + 
                                                  (a31*a42+a32*a41)*Tr_w + 2*a32*a42*Nm_w;
                                            s[6] = -6*bb[6] - Sum;
                                            Sum = bb[6]*s[1] + bb[5]*s[2] + bb[4]*s[3] + bb[3]*s[4] + 
                                                  bb[2]*s[5] + bb[1]*s[6];
                                            bb7_L = (pari_long)ceil((-t[7] - Sum)/7.0);
                                            bb7_U = (pari_long)floor((t[7] - Sum)/7.0);
                                            if(bb[7]>=bb7_L && bb[7]<=bb7_U)
                                              {
                                              bb[8] = bb8_pre + a41sq + a41a42*Tr_w + a42sq*Nm_w;
                                              s[7] = -7*bb[7] - Sum;
                                              Sum = bb[7]*s[1] + bb[6]*s[2] + bb[5]*s[3] + bb[4]*s[4] + 
                                                    bb[3]*s[5] + bb[2]*s[6] + bb[1]*s[7];
                                              bb8_L = (pari_long)ceil((-t[8] - Sum)/8.0);
                                              bb8_U = (pari_long)floor((t[8] - Sum)/8.0);
                                              if(bb[8]>=bb8_L && bb[8]<=bb8_U)
                                                {
                                                s[8] = -8*bb[8] - Sum;
                                                Sum = bb[8]*s[1] + bb[7]*s[2] + bb[6]*s[3] + bb[5]*s[4] + 
                                                      bb[4]*s[5] + bb[3]*s[6] + bb[2]*s[7] + bb[1]*s[8];
                                                bb9_L = (pari_long)ceil((-t[9] - Sum)/9.0);
                                                bb9_U = (pari_long)floor((t[9] - Sum)/9.0);
                                                if(bb[9]>=bb9_L && bb[9]<=bb9_U)
                                                  {
                                                  tmpdbl = .5*bb[9]*bb[9]/bb[10];
                                                  bb8_L = (pari_long) ceil(tmpdbl - bb8_Upre);
                                                  bb8_U = (pari_long)floor(tmpdbl + bb8_Upre);
                                                  if(bb[8]>=bb8_L && bb[8]<=bb8_U)
                                                    {

                                                    // Add the polynomial to the buffer.
                                                    for(j=0;j<=10;++j)  polyBuffer[buffCnt*11+j] = bb[j];
                                                    ++buffCnt;

                                                    // If buffer is full then process the polynomials
                                                    if(buffCnt==polyBufferSize)
                                                      {
                                                      //loopIdxs = {i,N1,N2,k1,k2,L1,L2,m1+1,m2};
                                                      loopIdxs[0] = i;
                                                      loopIdxs[1] = N1;   loopIdxs[2] = N2;
                                                      loopIdxs[3] = k1;   loopIdxs[4] = k2;
                                                      loopIdxs[5] = L1;   loopIdxs[6] = L2;
                                                      loopIdxs[7] = m1+1; loopIdxs[8] = m2;

                                                      testPolys(polyBuffer, buffCnt, StatVec, loopIdxs, outfile);

                                                      // Toggle the buffer pointer, and set the new polyBuffer.
                                                      bufferPtr = (bufferPtr+1)%2;
                                                      if (bufferPtr==0)  {
                                                        polyBuffer = polyBuffer1;
                                                        loopIdxs   = loopIdxs1;
                                                        }
                                                      else  {
                                                        polyBuffer = polyBuffer2;
                                                        loopIdxs   = loopIdxs2;
                                                        }

                                                      // Reset the buffer count in preparation for the next batch of polynomials
                                                      buffCnt = 0;
                                                      }

                                                    }  // Second bb8 test
                                                  }  // Second bb9 test
                                                }  // First bb8 test
                                              }  // bb7 test
                                            }  // bb6 test
                                          }  // bb5 test
                                        }  //bb4 test
                                      }  // First bb9 test
                                    }  // Matches: if( (s1a4_mag<=B_a4) && (s2a4_mag<=B_a4c) )
                                  }  // End of loop on m1
                                }  // End of loop on m2
                              }  // bb3 test
                            }  // Matches: if( (s1a3_mag<=2*tq[3]) && (s2a3_mag<=2*tqc[3]) )
                          }  // End of loop on L1
                        }  // End of loop on L2
                      }  // bb2 test
                    }  // Matches: if( (s1a2_mag+s2a2_mag) <= 2.0*Ca1 )

                  // Determine fraction complete for the progress bar
                  float k1_frac_done = (float)(k1-k1_L_Orig+1) / (float)NumVals_k1;
                  float Frac_Done = Cvec_frac_done + Delta_Cvec*
                        (N2_frac_done + Delta_N2*
                        (N1_frac_done + Delta_N1*
                        (k2_frac_done + Delta_k2*k1_frac_done)));
                  boinc_fraction_done(Frac_Done);

                  }  // End of loop on k1
                }  // End of loop on k2
              }  // Matches: if( (s1a5_mag_2_5ths+s2a5_mag_2_5ths) <= Ca1/5.0 )
            }  // Matches: if(a51!=0 || a52!=0)
          }  // Matches: if( !(a1_is_0) || a52>=0 )
        }  // End of loop on N1
      }  // End of loop on N2
    }  // End loop on i (loop over Cvecs)


  // Test the final batch of polynomials.
  if(buffCnt>0) {
    //fprintf(stderr,"Starting last call to testPolys.  numPolys = %d\n", buffCnt);
    //loopIdxs = {i,N1,N2,k1,k2,L1,L2,m1,m2};
    loopIdxs[0] = i;  loopIdxs[1] = N1;  loopIdxs[2] = N2;   loopIdxs[3] = k1;  loopIdxs[4] = k2;
    loopIdxs[5] = L1; loopIdxs[6] = L2;  loopIdxs[7] = m1+1; loopIdxs[8] = m2;
    testPolys(polyBuffer, buffCnt, StatVec, loopIdxs, outfile);
    }

  // GPU apps need to call testPolys once more to flush the last batch from the GPU
#if defined(APP_VERSION_GPU_OPENCL) || defined(APP_VERSION_GPU_CUDA)
  testPolys(polyBuffer, 0, StatVec, loopIdxs, outfile);
#endif


  float Percent1 = 0;
  float Percent2 = 0;
  float Percent3 = 0;

  if(StatVec[0]!=0)  Percent1 = 100.0 * StatVec[1] / StatVec[0];
  if(StatVec[1]!=0)  Percent2 = 100.0 * StatVec[2] / StatVec[1];
  if(StatVec[2]!=0)  Percent3 = 100.0 * StatVec[3] / StatVec[2];

  // Update the elapsed time once more before writing stats to the file.
  pari_long Time_sec = StatVec[4];
  Time_sec = Time_sec + (pari_long)floor(myTimer()/1000.0 + .5);

  // Now that the search is complete, write the final stats to the output file.
  outfile << "#   The search is complete. Stats:\n";
  outfile << "#   Inspected " << StatVec[0] << " polynomials.\n";
  outfile << "#   Num Polys passing PolDisc test = " << StatVec[1] << " (" << Percent1 << "%).\n";
  outfile << "#   Num Polys passing irreducibility test = " << StatVec[2] << " (" << Percent2 << "%).\n";
  outfile << "#   Num Polys passing field disc test = " << StatVec[3] << " (" << Percent3 << "%).\n";
  outfile << "#   Elapsed Time = " << Time_sec << " (sec)\n";
  outfile.flush();

  // Free up memory
  free(polyBuffer1);
  free(polyBuffer2);
  free(polGoodFlag);

  avma = ltop;  // Restore pointer to top of pari stack

  }





void testPolys(pari_long *polBufNow, int numPolysNow, pari_long *StatVec, pari_long *loopIdxsNow, ofstream& outfile)
  {
  static int firstPass = 1;

  // To implement double buffering, it is necessary to store the previous state.
  static pari_long *polBufPrev = NULL;
  static pari_long *loopIdxsPrev = NULL;
  static int numPolysPrev = 0;


  // Setup more descriptive names for elements of the stats vector.
  pari_long *polCount, *pdCount, *irrCount, *fdCount;
  polCount = &(StatVec[0]);
  pdCount  = &(StatVec[1]);
  irrCount = &(StatVec[2]);
  fdCount  = &(StatVec[3]);


  int numPrimes = (int)(lg(Sg)-1);  // Number of primes in the set S
  int pSet[3];  // This allows for a maximum of 3 primes.
  for(int k=0; k<numPrimes; k++)  pSet[k] = (int)itos((GEN)Sg[k+1]);


#ifdef DEBUG_TEST
    // This is the poly: x^10 + 850*x^6 - 1760*x^5 + 4100625*x^2 + 26244000*x + 47239200
    polBuf[0]  = 1;
    polBuf[1]  = 0;
    polBuf[2]  = 0;
    polBuf[3]  = 0;
    polBuf[4]  = 850;
    polBuf[5]  = -1760;
    polBuf[6]  = 0;
    polBuf[7]  = 0;
    polBuf[8]  = 4100625;
    polBuf[9]  = 26244000;
    polBuf[10] = 47239200;
#endif


  //////////////////////////////////////////////////////////////////////////////
  // 
  // POLYNOMIAL DISCRIMINANT TEST
  //
  // For every polynomial in the buffer, compute the polynomial discriminant, 
  // divide out all factors of primes in S, and then set the polGoodFlag if
  // what's left is a perfect square.
  //
  // The method used depends on which pre-processor directive is in force.
  // There is the standard CPU method, and then the various GPU methods.

  // This performs the polDisc test using the CPU version:
#ifdef APP_VERSION_CPU_STD
  int status = polDiscTest_cpu(polBufNow, numPolysNow, polGoodFlag, numPrimes, pSet);
  // The cpu version has to trick the code below into processing the current buffer.
  // This is easily done by turning off the "first pass" flag and setting the "previous"
  // state to the current state.
  firstPass = 0;
  polBufPrev = polBufNow;
  loopIdxsPrev = loopIdxsNow;
  numPolysPrev = numPolysNow;
#endif

  // This performs the polDisc test using the CUDA-GPU version:
#ifdef APP_VERSION_GPU_CUDA
  boinc_begin_critical_section();
  int status = polDiscTest_gpuCuda(polBufNow, numPolysNow, polGoodFlag, numPrimes, pSet);
  boinc_end_critical_section();
#endif

  // This performs the polDisc test using the OPENCL-GPU version:
#ifdef APP_VERSION_GPU_OPENCL
  boinc_begin_critical_section();
  int status = polDiscTest_gpuOpenCL(polBufNow, numPolysNow, polGoodFlag, numPrimes, pSet);
  boinc_end_critical_section();
#endif


  // Check the return status for success:
  if(status!=0) {
    fprintf(stderr, "polDisc Test had an error. Aborting.\n");
    exit(1);
    }

  //
  // End of polynomial discriminant test.
  //
  //////////////////////////////////////////////////////////////////////////////


  // On the first pass we skip the rest of the tests (unless cpu).
  // This is because the first pass is still being processed on the GPU.
  if (firstPass) {
    // Save the state of the first pass (needed in the next iteration)
    polBufPrev = polBufNow;
    loopIdxsPrev = loopIdxsNow;
    numPolysPrev = numPolysNow;

    firstPass = 0;
    return;
  }


  *polCount += numPolysPrev;  // Update the polynomial counter.

  // Print out the count every 1 million
  //if(*polCount%1000000==1) fprintf(stderr, "Polynomial Count = %lld.\n", *polCount);


#ifdef DEBUG_TEST
    for(int k=0; k<numPolysPrev; k++) {
      cout << "polGoodFlag[" << k << "] = " << (int)polGoodFlag[k] << "\n";
      }
    exit(1);
#endif


  // The GPU is now processing the current buffer.
  // PolGoodFlag has the flags from the previous call to the GPU, so we now 
  // finish the polDiscTest for the previous iteration.

  // Save the current top of the PARI stack
  pari_long ltop = avma;

  // Continue testing only those polynomials that were flagged as good
  for(int j=0;j<numPolysPrev;++j)
    {
    if(polGoodFlag[j])
      {

      // Increment the polDisc counter.
      (*pdCount)++;

      //fprintf(stderr, "polDisc Counter = %lld.\n", *pdCount);

      // Create the PARI degree 10 minimal polynomial for this field:
      GEN f_L = mkpoln( 11, gen_1, stoi(polBufPrev[j*11+1]), stoi(polBufPrev[j*11+2]),
                                   stoi(polBufPrev[j*11+3]), stoi(polBufPrev[j*11+4]),
                                   stoi(polBufPrev[j*11+5]), stoi(polBufPrev[j*11+6]),
                                   stoi(polBufPrev[j*11+7]), stoi(polBufPrev[j*11+8]),
                                   stoi(polBufPrev[j*11+9]), stoi(polBufPrev[j*11+10]) );

      //fprintf(stderr, "%s\n",GENtostr(f_L));


      // Check if f_L is irreducible:
      if(isirreducible(f_L))
        {
        // Increment the irreducibilty counter.
        (*irrCount)++;

        // Compute the field discriminant of L:
        // NOTE: this is a computationally expensive task.
        GEN fldDisc = discf(f_L);

        // Divide out all factors of p where p is in S
        for(int k=1;k<=numPrimes;++k)
          {
          fldDisc = gdiv(fldDisc,gpowgs((GEN)Sg[k],ggval(fldDisc,(GEN)Sg[k])));
          }

        // Whats left must be +/- 1
        if(gcmp1(gabs(fldDisc,DEFAULTPREC)))
          {
          // Increment the final test counter.
          (*fdCount)++;

          // Convert the polynomial into a string.
          char *OutStr = GENtostr(f_L);
          //fprintf(stderr, "Poly = %s\n",OutStr);

          // Write the polynomial to the output file.
          outfile << OutStr << "\n";
          outfile.flush();  // Make sure we flush the buffer before continuing.
          free(OutStr);
          }

        } // Matches: if(isirreducible(f_L))

      // Restore pointer to top of pari stack
      avma = ltop;

      } // Matches: if(polGoodFlag[j])
    }  // End loop over buffer


  // Do checkpointing
  if(boinc_time_to_checkpoint())
    {
    /* StatVec[4] is the elapsed time in seconds */
    /* Note: myTimer() returns elapsed time in milliseconds since the last call to myTimer */
    StatVec[4] = StatVec[4] + (pari_long)floor(myTimer()/1000.0 + .5);

    int retval = do_checkpoint(loopIdxsPrev, StatVec);
    if(retval)
      {
      fprintf(stderr, "Checkpoint failed!\n");
      exit(retval);
      }
    boinc_checkpoint_completed();
    }

  // Store the current state for the next iteration.
  polBufPrev = polBufNow;
  loopIdxsPrev = loopIdxsNow;
  numPolysPrev = numPolysNow;


// If profiling, only do a few passes
#ifdef PROFILER_ON
  static int numPasses = 0;
  ++numPasses;
  if (numPasses==100) {
    #ifdef APP_VERSION_GPU_CUDA
      cleanupCuda();
    #endif
    boinc_finish(0);
    }
#endif

}  // End of function testPolys





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
