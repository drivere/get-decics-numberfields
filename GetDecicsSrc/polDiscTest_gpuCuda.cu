// System includes
#include <stdlib.h>
#include <stdio.h>
#include <math.h>

// CUDA runtime
#include <cuda_runtime.h>
#include <helper_cuda.h>
#include <helper_functions.h>
#include <cuda.h>


//#define CUDA_PROFILER

#ifdef CUDA_PROFILER
  #include <cuda_profiler_api.h>
#endif


// Use this to turn on DEBUG mode
//#define DEBUG
#define DBG_THREAD -1


// The PRINTF_ENABLED is used in gpuMultiPrec to turn on the printing functions.
#ifdef DEBUG
  #define PRINTF_ENABLED
#endif


#define CUDA
#include "gpuMultiPrec128.h"
//#include "gpuMultiPrec256.h"
#include "cuda_GetDecics.h"


// Possible states for the validFlag;
#define TRUE    1
#define FALSE   0
#define MEM_ERR 2


extern int  numBlocks, threadsPerBlock, polyBufferSize;



// CUDA kernel function to do the pol disc test (stage 1)
__global__
void pdtKernel_stage1(int numPolys, int64_t *polys, char *validFlag, mp_int* polDiscArray)
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;


  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;


  // We error on the side of caution and initialize validFlag to true.
  // This setting keeps the polynomial on the list for further testing.
  // We do this in case the kernel aborts early before properly setting the flag.
  validFlag[index] = TRUE;


#ifdef CUDA_PROFILER
  unsigned int time1 = clock();
#endif


  // Extract the polynomial for this thread.
  // It is assummed the input coefficients are in decreasing order of degree.
  // (i.e. A[0]*x^10 + A[1]*x^9 + ... + A[9]*x + A[10])
  // BUT FOR IMPLEMENTATION REASONS, WE REVERSE THE ORDER.
  int64_t A[11];
//#pragma unroll
  for(int col = 0; col < 11; col++)  A[10-col] = polys[index*11+col];

  // Compute the derivative of A.  Call it B.
  // NOTE: B = 10*x^9 + 9*A[9]*x^8 + 8*A[8]*x^7 + ... + 2*A[2]*x + A[1]
  int64_t B[10];
//#pragma unroll
  for(int k = 1; k <= 10; k++)  B[k-1] = k*A[k];

  // The discriminant of a monic decic is -1*Resultant(A,B).
  // We use Algorithm 3.3.7 in Cohen's Book (p.122).

  //////////////////////////////////////////////////////////////////////////////
  // Step 1: Initialization.
  //////////////////////////////////////////////////////////////////////////////

  // Get content of B (gcd of all its coeffs).  Since the leading coeff of B is 10,
  // its content is one of {1,2,5,10}. So it suffices to determine whether or not
  // 2 and 5 divide its coeffs.

  int cont2 = 2;  // The "2" portion of the content.  Default to 2.
  for(int k = 0; k < 10; k+=2) {  // We only need to check the even coeffs
    if( (B[k]&1) == 1) { cont2=1; break;}  // Set content to 1 and break if any coeff is odd.
    }

  int cont5 = 5; // The "5" portion of the content.  Default to 5.
  for(int k = 0; k < 9; k++) {  // We can skip the leading term, which we know to be 10.
    if( (B[k]%5) != 0 ) { cont5=1; break;}  // Set content to 1 and break if any coeff is NOT divisible by 5.
    }

    __syncwarp();

  // Finally, we get the full content of B:
  int contB = cont2 * cont5;

  // Scale B by its content.
  for(int k = 0; k < 10; k++)  B[k] = B[k] / contB;


#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("Original polynomials:\n");
    printf("  A = %ld ", A[0]);
    for(int k=1; k<11; k++) printf("+ %ld x^%d ", A[k], k);
    printf("\n");
    printf("  B = %ld ", B[0]);
    for(int k=1; k<10; k++) printf("+ %ld x^%d ", B[k], k);
    printf("\n");
    }
#endif


  ////////////////////////////////////////////////////////////////
  /*  Do the first iteration of the sub-resultant algorithm.    */
  /*  This allows us to stay with longs a little longer before  */
  /*  transitioning to multi-precision.                         */

  // This computes: R = d*A-S*B in Algorithm 3.1.2
  long R[10];
  R[0] = B[9]*A[0];
  for(int k=1;k<=9;++k)  R[k] = B[9]*A[k] - B[k-1];

  // The last line was the 1st iteration of Pseudo Division.
  // If A[9]==0, only 1 iteration is needed and R[k] = B[9]*R[k] (since q=B[9]).
  // Otherwise, a 2nd iteration is needed which gives R[k] = B[9]*R[k] - R[9]*B[k].
  // The next line handles both cases together (note that R[9]=0 in case 1):
  for(int k=0;k<=8;++k)  R[k] = B[9]*R[k] - R[9]*B[k];

  // Determine the degree of R (it must be less than or equal to 8)
  int degR = 0;
  for(int k=8; k>0; k--)  {
    if( R[k]!=0 ) { degR=k; break; }
    }

  // Multi-precision declarations
  mp_int g, h, mpA[10], mpB[9], mpR[10], BR, SB[9];
  mp_int q, gPow, hPow, scale;

  // Setup next iteration: A=B, B=R, g=A[9](= original B[9]), h=g.
  int degA = 9;
  int degB = degR;
  mp_set_vec_int64(mpA, B, degA+1);  // initialize mpA to B.
  mp_set_vec_int64(mpB, R, degR+1);  // initialize mpB to R.
  mp_set_int64(&g, B[9]);
  mp_set_int64(&h, B[9]);

  /*  The first iteration of sub-resultant is now complete. */
  ////////////////////////////////////////////////////////////


  // The remaining multi-precision initializations.
  // Note: These need to either be set or zeroed out one time.
  for(int k=0; k<10; k++)  mp_zero(&(mpR[k]));
  mp_zero(&BR);
  for(int k=0; k<9; k++)  mp_zero(&(SB[k]));
  //mp_zero(&q);  // This one is not needed at this point.
  mp_zero(&gPow);
  mp_zero(&hPow);
  mp_zero(&scale);


#ifdef DEBUG
  int iter = 0;
  if(index==DBG_THREAD) {
    printf("AFTER FIRST SUB-RESULTANT ITERATION:\n");
    printf("long versions:\n");
    printf("  A = %ld ", B[0]); // Note: The new A is really B
    for(int k=1; k<=degA; k++) printf("+ %ld x^%d ", B[k], k);
    printf("\n");
    printf("  B = %ld ", R[0]); // Note: The new B is really R
    for(int k=1; k<=degB; k++) printf("+ %ld x^%d ", R[k], k);
    printf("\n");
    printf("Multi-precision versions:\n");
    printf("mpA = ");  mp_print_poly(mpA, degA); printf("\n");
    printf("mpB = ");  mp_print_poly(mpB, degB); printf("\n");

    // This tests multiplication:
    if(0) {
      mp_set(&hPow, 1);
      for(int k=1; k<=12; k++)  {
        mp_mul( &hPow, &mpA[0], &hPow );
        printf("A[0]^%d = ",k); mp_printf(hPow); printf("\n");
        }
      }

    }
#endif


#ifdef CUDA_PROFILER
  unsigned int time2 = clock();
  if(index==DBG_THREAD) {
    printf("Kernel 1 Initialization Time = %d\n", time2 - time1); }
#endif

    __syncwarp();


  //////////////////////////////////////////////////////////////////////////////
  // Steps 2/3: Pseudo Division and Reduction.
  //////////////////////////////////////////////////////////////////////////////

  // This is really a loop over the degree of B.
  // degB starts <= 8 and drops by at least 1 every iteration, so we loop the max of 8 times.
  // This gives a fixed size for the for loop and we break early once degB=0.
  for(int degIter=8; degIter>0; --degIter) {

    // We are done once degB=0, so exit the loop
    if(degB==0) break;

    int delta = degA - degB;

    ////////////////////////////////////////////////////////////////////////////
    // Pseudo Division.  This is Algorithm 3.1.2 on p.112 of Cohen's book.
    // This computes R such that B[degB]^(delta+1)*A = B*Q + R where degR < degB
    // Note, since we don't need Q, we don't compute it.

    // Initialize R to A.
    degR = degA;
    mp_copy_vec(mpA, mpR, degA+1);

    int e = delta + 1;

    // degR starts at degB+delta and must drop by at least 1 each pass through the loop.
    // So we loop the maximum number of times which is delta+1.
    // We do this to get a fixed size for loop, and break early once degR<degB
    for(int delIter=delta; delIter>=0; --delIter) {

      // We are done once the degree of R is less than the degree of B
      if(degR<degB) break;

      // We dont actually need the polynomial S, just it's degree.
      int degS = degR - degB;

      // Compute S*B.
      // Note: SB = R[degR] * (B[0]*x^(degS) + B[1]*x^(degS+1) + ... + B[degB]*x^(degR))
      //       Also, since B[degB]*R-SB has degree degR-1 or smaller, we can skip the last coeff.
      // What follows is the mp equivalent of this:
      //      for(int k=0; k<=degS-1; k++)  SB[k] = 0;
      //      for(int k=degS; k<degR; k++)  SB[k] = R[degR]*B[k-degS];
      for(int k=0; k<=degS-1; k++)  mp_zero(&(SB[k]));
      for(int k=degS; k<degR; k++)  {
        int retVal = mp_mul( &(mpR[degR]), &(mpB[k-degS]), &(SB[k]) );
        if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
        }
      // Compute R = B[degB]*R - S*B
      // What follows is the mp equivalent of this:
      //      for(int k=0; k<degR; k++)  R[k] = B[degB]*R[k]-SB[k];
      for(int k=0; k<degR; k++) {
        int retVal = mp_mul( &(mpB[degB]), &(mpR[k]), &BR );
        if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
        mp_sub( &BR, &(SB[k]), &(mpR[k]) );
        }

      // Determine the degree of the new R.
      int degRnew = 0;
      for(int k=degR-1; k>0; k--)  {
        //if( !IS_ZERO(&(mpR[k])) ) { degRnew=k; break; }
        if( mpR[k].used>0 ) { degRnew=k; break; }
        }
      degR = degRnew;

      --e;
      }  // End of inner for loop


    // Compute q = B[degB]^e
    mp_set(&q, 1);
    for(int k=1; k<=e; k++)  {
      int retVal = mp_mul( &q, &(mpB[degB]), &q );   // Set q = q * B[degB]
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
      }

    // Compute R = q*R.
    for(int k=0; k<=degR; k++)  {
      int retVal = mp_mul( &(mpR[k]), &q, &(mpR[k]) );  // R[k] = R[k] * q;
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
      }

    // End of Pseudo Division
    ////////////////////////////////////////////////////////////////////////////


    // Set A = B
    degA = degB;
    mp_copy_vec(mpB, mpA, degB+1);  // for(int k=0; k<=degB; k++)  A[k] = B[k];

    // Set B = R/(g*h^delta)
    mp_copy(&h, &hPow);  // Init hPow = h
    for(int k=1; k<=delta-1; k++)  {
      int retVal = mp_mul( &hPow, &h, &hPow );  // Set hPow = hPow*h
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
      }

    int retVal = mp_mul( &g, &hPow, &scale );  // scale = g*hPow
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }

    degB = degR;
    for(int k=0; k<=degR; k++)  {
      int retVal = mp_div( &(mpR[k]), &scale, &(mpB[k]), NULL ); // Set B[k] = R[k] / scale;
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
      }


    // Get new g for next iteration.  g = leading coeff of A
    mp_copy( &(mpA[degA]), &g);

    // Compute the new h = g^delta * h^(1-delta)
    // Note: degA > degB so delta is always > 0.
    if(delta==1) {
      // Then set h=g
      mp_copy( &g, &h );
      }
    else {
      // The power on h will be negative, so compute h = g^delta / h^(delta-1)

      // First compute g^delta:
      mp_copy(&g, &gPow);  // Init gPow = g
      for(int k=1; k<=delta-1; k++)  {
        int retVal = mp_mul( &gPow, &g, &gPow );  // Set gPow = gPow*g
        if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
        }

      // Then compute h^(delta-1):
      mp_copy(&h, &hPow);  // Init hPow = h
      for(int k=1; k<=delta-2; k++)  {
        int retVal = mp_mul( &hPow, &h, &hPow );  // Set hPow = hPow*h
        if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
        }

      // Finally, divide them:
      int retVal = mp_div( &gPow, &hPow, &h, NULL );  // Set h = gPow / hPow;
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
      }

    #ifdef DEBUG
      ++iter;
      if(index==DBG_THREAD) {
        printf("\n");
        printf("Iteration %d:\n", iter);
        printf("  degA = %d\n", degA);
        printf("  A = "); mp_print_poly(mpA,degA); printf("\n");
        printf("  degB = %d\n", degB);
        printf("  B = "); mp_print_poly(mpB,degB); printf("\n");
        printf("  g = "); mp_printf(g); printf("\n");
        printf("  h = "); mp_printf(h); printf("\n");
        printf("\n");
        }
    #endif

    }  // End of outer for loop


#ifdef CUDA_PROFILER
  unsigned int time3 = clock();
  if(index==DBG_THREAD) {
    printf("Kernel 1 Intermediate Steps = %d\n", time3 - time2); }
#endif


#ifdef DEBUG
  if(index==DBG_THREAD) { printf("g = ");  mp_printf(g); printf("\n"); }
  if(index==DBG_THREAD) { printf("h = ");  mp_printf(h); printf("\n"); }
  if(index==DBG_THREAD) { printf("B[0] = ");  mp_printf(mpB[0]); printf("\n"); }
#endif


  //////////////////////////////////////////////////////////////////////////////
  // Step 4: Complete the resultant (and discriminant) calculation.
  //////////////////////////////////////////////////////////////////////////////

  // We actually don't compute the complete discriminant, since we don't need it.
  // We don't care about the sign or any square factors.  So we make a slight 
  // modification to step 4 in Algorithm 3.3.7 of Cohen's book.
  // If the degree of A is even (say 2k) then the final computation of h gives:
  //    h <- h * (B[0]/h)^(2k), so it suffices to just consider h.
  // On the other hand, if A is odd (say 2k+1), then the final value for h is
  //    h <- B[0] * (B[0]/h)^(2k), so it suffices to just consider B[0].
  // There is one exception to this - when B[0] = 0, in which case polDisc = 0.
  // Furthermore, we ignore the sign term and the t term (since it is square).


  // If the discriminant is zero, then the polynomial is reducible.
  // In this case, the polynomial is invalid.  Set the flag.
  mp_int *polDisc;

  if( IS_ZERO(mpB) ) {  // mpB is the address of mpB[0]
    validFlag[index] = FALSE;
    polDisc = &(mpB[0]);
    }
  else {
    if(degA%2==0)  polDisc = &h;         // Set polDisc = h
    else           polDisc = &(mpB[0]);  // Set polDisc = B[0]
    }


#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("polDisc = ");  mp_printf(*polDisc); printf("\n");
    }
#endif


  // Make sure the discriminant is positive
  polDisc->sign = MP_ZPOS;


  // Store discriminant in device memory
  mp_copy(polDisc, &(polDiscArray[index]));


#ifdef CUDA_PROFILER
  unsigned int time4 = clock();
  if(index==DBG_THREAD) {
    printf("Kernel 1 Final Step = %d\n", time4 - time3); }
#endif

}






// CUDA kernel function to do the pol disc test (stage 2)
__global__
void pdtKernel_stage2(int numPolys, char *validFlag, mp_int* polDiscArray, int p1, int p2)
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;


  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;


  int numP, pSet[2] = {p1, p2};
  numP = (p1==p2) ? 1 : 2;


  // Extract polynomial discriminant for this thread
  mp_int polDisc;
  for (int n = 0; n < MP_PREC; n++)  polDisc.dp[n] = polDiscArray[index].dp[n];
  polDisc.used = polDiscArray[index].used;
  polDisc.sign = polDiscArray[index].sign;


  // Initialize local variables
  mp_int q, Mod;
  mp_zero(&q);
  mp_zero(&Mod);


  // Divide out all factors of p for each prime in pSet
#pragma unroll
  for(int k=0; k<numP; k++)  {
    int thisP = pSet[k];
    if(thisP==2) {
      // We treat the p=2 case special.  For two reasons, one it can be handled 
      // much more efficiently, and two there are usually many factors of 2.
#pragma unroll
      for(;;) {  // We remove 10 powers of 2 at a time
        mp_mod_2d( &polDisc, 10, &Mod );  // Set Mod = polDisc%1024
        if( !IS_ZERO(&Mod) ) break;  // Exit once there are no more factors of 1024
        mp_div_2d( &polDisc, 10, &polDisc, NULL ); // Set polDisc = polDisc/1024
        }
      // What remains has at most 9 powers of 2.
      // We remove the rest 1 at a time
#pragma unroll
      for(;;) {
        mp_mod_2d( &polDisc, 1, &Mod );  // Set Mod = polDisc%2
        if( !IS_ZERO(&Mod) ) break;  // Exit once there are no more factors of 2
        mp_div_2d( &polDisc, 1, &polDisc, NULL ); // Set polDisc = polDisc/2
        }
      }
    else if(thisP==5) {
      // We handle 5 separately since polDisc can have many factors of 5.
      mp_digit rem;
#pragma unroll
      for(;;) {  // We remove 8 powers of 5 at a time
        mp_div_d( &polDisc, 390625, &q, &rem );  // polDisc = q*5^8 + rem
        if( rem!=0 ) break;  // Exit once there are no more factors of 5^8
        mp_copy( &q, &polDisc );  // Otherwise, since the remainder is zero, set polDisc = q
        }
      // What remains has at most 7 powers of 5.
      // We remove them 1 at a time
#pragma unroll
      for(;;) {
        mp_div_d( &polDisc, 5, &q, &rem );  // polDisc = q*5 + rem
        if( rem!=0 ) break;  // Exit once there are no more factors of 5
        mp_copy( &q, &polDisc );  // Otherwise, since the remainder is zero, set polDisc = q
        }
      }
    else {
      // Remove the other primes, 1 power at a time.
      mp_digit rem;
#pragma unroll
      for(;;) {
        mp_div_d( &polDisc, thisP, &q, &rem );  // polDisc = q*p + rem
        if( rem!=0 ) break;  // Exit once there are no more factors of thisP
        mp_copy( &q, &polDisc );  // Otherwise, since the remainder is zero, set polDisc = q
        }
      }

    } // End of loop on k


  // Put modified discriminant back into device memory
  mp_copy(&polDisc, &(polDiscArray[index]));

}





// CUDA kernel function to do the pol disc test (stage 3)
// The validFlag was originally initialized to 1.
// In this kernel, we set the flag to zero if the polDisc is NOT a perfect square.
// Recall the theorem:
//      N is a perfect square => N is a square mod n for all n.
// So the contrapositive gives: 
//      N is not a square mod n for some n => N is not a perfect square
// This gives a very fast method of finding non-squares: just check the number mod n
// for a large enough set of n's.  This will quickly filter out over 99% of the 
// non-squares.  Any number passing all the modulus tests would have a small chance 
// of being a perfect square.  One would normally check these few remaining cases
// by actually computing the sqrt.  In our case, we just throw it back to the cpu
// to deal with.
__global__
void pdtKernel_stage3(int numPolys, char *validFlag, mp_int* polDiscArray)
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  // Also return early if validFlag is already false, which can be set in stage 1.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;


  // Extract polynomial discriminant for this thread
  mp_int polDisc;
  for (int n = 0; n < MP_PREC; n++)  polDisc.dp[n] = polDiscArray[index].dp[n];
  polDisc.used = polDiscArray[index].used;
  polDisc.sign = polDiscArray[index].sign;


  //mp_printf_thread(index, "polDisc = ", polDisc);


  // These are the residues Mod 64,63,65,11
  const char resMod64[]={
    1,1,0,0,1,0,0,0,0,1, 0,0,0,0,0,0,1,1,0,0, 0,0,0,0,0,1,0,0,0,0,
    0,0,0,1,0,0,1,0,0,0, 0,1,0,0,0,0,0,0,0,1, 0,0,0,0,0,0,0,1,0,0, 0,0,0,0};
  const char resMod63[]={
    1,1,0,0,1,0,0,1,0,1, 0,0,0,0,0,0,1,0,1,0, 0,0,1,0,0,1,0,0,1,0,
    0,0,0,0,0,0,1,1,0,0, 0,0,0,1,0,0,1,0,0,1, 0,0,0,0,0,0,0,0,1,0, 0,0,0};
  const char resMod65[]={
    1,1,0,0,1,0,0,0,0,1, 1,0,0,0,1,0,1,0,0,0, 0,0,0,0,0,1,1,0,0,1,
    1,0,0,0,0,1,1,0,0,1, 1,0,0,0,0,0,0,0,0,1, 0,1,0,0,0,1,1,0,0,0, 0,1,0,0,1};
  const char resMod11[]={1,1,0,1,1,1,0,0,0,1, 0};


  // First compute polDisc modulo (64*63*65*11)
  mp_digit rem;
  mp_div_d( &polDisc, 2882880, NULL, &rem );


  // Check if rem is a quadratic residue modulo 64.
  // If it's not a residue mod 64, then polDisc is not a perfect square.
  if ( !resMod64[rem & 0x3F] )  {
    validFlag[index]=FALSE;
    return;
    }

  // Check if rem is a quadratic residue modulo 63.
  if ( !resMod63[rem % 63] )  {
    validFlag[index]=FALSE;
    return;
    }

  // Check if rem is a quadratic residue modulo 65.
  if ( !resMod65[rem % 65] )  {
    validFlag[index]=FALSE;
    return;
    }

  // Check if rem is a quadratic residue modulo 11.
  if ( !resMod11[rem % 11] )  {
    validFlag[index]=FALSE;
    return;
    }


  // Do a 2nd pass with other moduli.
  // Compute polDisc modulo (17*19*23*29*31)
  mp_div_d( &polDisc, 6678671, NULL, &rem );

  // Check if rem is a quadratic residue modulo 17.
  const char resMod17[] = {1,1,1,0,1, 0,0,0,1,1, 0,0,0,1,0, 1,1};
  if ( !resMod17[rem % 17] )  {
    validFlag[index]=FALSE;
    return;
    }

  // Check if rem is a quadratic residue modulo 19.
  const char resMod19[] = {1,1,0,0,1, 1,1,1,0,1, 0,1,0,0,0, 0,1,1,0};
  if ( !resMod19[rem % 19] )  {
    validFlag[index]=FALSE;
    return;
    }

  // Check if rem is a quadratic residue modulo 23.
  const char resMod23[] = {1,1,1,1,1, 0,1,0,1,1, 0,0,1,1,0, 0,1,0,1,0, 0,0,0};
  if ( !resMod23[rem % 23] )  {
    validFlag[index]=FALSE;
    return;
    }

  // Check if rem is a quadratic residue modulo 29.
  const char resMod29[] = {1,1,0,0,1, 1,1,1,0,1, 0,0,0,1,0, 0,1,0,0,0, 1,0,1,1,1, 1,0,0,1};
  if ( !resMod29[rem % 29] )  {
    validFlag[index]=FALSE;
    return;
    }

  // Check if rem is a quadratic residue modulo 31.
  const char resMod31[] = {1,1,1,0,1, 1,0,1,1,1, 1,0,0,0,1, 0,1,0,1,1, 1,0,0,0,0, 1,0,0,1,0, 0};
  if ( !resMod31[rem % 31] )  {
    validFlag[index]=FALSE;
    return;
    }

}






//////////////////////////////////////////////////////////////////////////////////////////
//! Entry point for Cuda functionality on host side
//! 
//! This function performs the polynomial discriminant test for the GetDecics program.
//! For every polynomial in the input buffer, it computes the polynomial discriminant, 
//! divides out all factors of primes from S, and then sets the polGoodFlag if
//! what's left is a perfect square.
//! 
//////////////////////////////////////////////////////////////////////////////////////////

extern "C" int
polDiscTest_gpuCuda(long long polBuf[][11], int numPolys, char *polGoodFlag, int numP, int *pSet)
  {
  static int numPolysPrev = 0;
  static int firstPass = 1;

  //printf("Entering polDiscTest\n");
  //printf("  numPolysPrev = %d\n", numPolysPrev);
  //printf("  numPolys = %d\n", numPolys);
  //printf("  firstPass = %d\n", firstPass);


  // If this is not the first pass then transfer the polGoodFlag from the GPU (from previous pass).
  if (!firstPass) {

    // First make sure the previous pass has finished:
    cudaStreamSynchronize(pdtStream);
    CUDACHECK;

    // Get the flag data off the GPU:
    for (int k=0;k<numPolysPrev;k++)  polGoodFlag[k] = kernelFlagBuffer[k];

  }


  // Only invoke the GPU if there are polynomials to process.
  // If there are no polynomials, then this signifies the "last" pass.
  // We already pulled the previous results off the GPU above, so just return.
  if ( numPolys==0 )  return 0;


  // Save state parameters for next iteration
  firstPass = 0;
  numPolysPrev = numPolys;


#ifdef CUDA_PROFILER
  cudaProfilerStart();
#endif

  // Setup primes for the kernel
  int p1, p2;
  if(numP==1)       { p1=pSet[0]; p2=pSet[0]; }
  else if(numP==2)  { p1=pSet[0]; p2=pSet[1]; }
  else { printf("Error: This function only supports 2 primes max."); return FAIL; }

  // Copy polynomials to the device memory
  for (int row = 0; row < numPolys; row++) {
    for (int col = 0; col < 11; col++) {
      kernelPolyBuffer[row*11+col] = polBuf[row][col];
    }
  }


  // THIS METHOD DOES NOT WORK WELL!
  // Launch the executable graph
  //cudaGraphLaunch(pdtExecGraph, pdtStream);
  //CUDACHECK;


  // Launch stage 1 threads on the GPU
  int numBlocksNew = (numPolys + threadsPerBlock - 1) / threadsPerBlock;
  //printf("Launching Stage 1.\n");
  pdtKernel_stage1<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, kernelPolyBuffer, kernelFlagBuffer, kernelDiscBuffer);
  //cudaDeviceSynchronize();
  CUDACHECK;

  // Launch stage 2 threads
  //printf("Launching Stage 2.\n");
  pdtKernel_stage2<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, kernelFlagBuffer, kernelDiscBuffer, p1, p2);
  //cudaDeviceSynchronize();
  CUDACHECK;

  // Launch stage 3 threads
  //printf("Launching Stage 3.\n\n");
  pdtKernel_stage3<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, kernelFlagBuffer, kernelDiscBuffer);
  //cudaDeviceSynchronize();
  CUDACHECK;


#ifdef CUDA_PROFILER
  cudaProfilerStop();
#endif


  // If we make it this far, we assume success.  So return 0.
  return 0;

  }




// This function creates the Cuda Execution Graph.
// This method turned out to be unusable, since the graph hard codes the kernel arguments.
extern "C" int
generateCudaGraph(void)
  {
  cudaGraph_t  pdtGraph;
  cudaGraphNode_t  stg1, stg2, stg3;
  cudaKernelNodeParams paramsStg1 = {0};
  cudaKernelNodeParams paramsStg2 = {0};
  cudaKernelNodeParams paramsStg3 = {0};


  // These need to be set before the kernel args are created
  // They get hard coded into the graph.
  int NUM_POLYS = polyBufferSize;
  int P1=2, P2=5;


  // Setup array of pointers for kernel arguments
  void *kerArgs1[4] = {(void*)&NUM_POLYS, (void*)&kernelPolyBuffer, (void*)&kernelFlagBuffer, (void*)&kernelDiscBuffer};
  void *kerArgs2[5] = {&NUM_POLYS, &kernelFlagBuffer, &kernelDiscBuffer, &P1, &P2};
  void *kerArgs3[3] = {&NUM_POLYS, &kernelFlagBuffer, &kernelDiscBuffer};


  // Setup the kernel node parameters:
       /* 1st kernel */
  paramsStg1.gridDim  = dim3(numBlocks, 1, 1);
  paramsStg1.blockDim = dim3(threadsPerBlock, 1, 1);
  paramsStg1.func     = (void*)pdtKernel_stage1;
  paramsStg1.extra    = NULL;
  paramsStg1.kernelParams   = (void **)kerArgs1;
  paramsStg1.sharedMemBytes = 0;
       /* 2nd kernel */
  paramsStg2.gridDim  = dim3(numBlocks, 1, 1);
  paramsStg2.blockDim = dim3(threadsPerBlock, 1, 1);
  paramsStg2.func     = (void*)pdtKernel_stage2;
  paramsStg2.extra    = NULL;
  paramsStg2.kernelParams   = (void **)kerArgs2;
  paramsStg2.sharedMemBytes = 0;
       /* 3rd kernel */
  paramsStg3.gridDim  = dim3(numBlocks, 1, 1);
  paramsStg3.blockDim = dim3(threadsPerBlock, 1, 1);
  paramsStg3.func     = (void*)pdtKernel_stage3;
  paramsStg3.extra    = NULL;
  paramsStg3.kernelParams   = (void **)kerArgs3;
  paramsStg3.sharedMemBytes = 0;


  // Create the graph object
  cudaGraphCreate(&pdtGraph, 0);
  CUDACHECK;

  // Add the kernel nodes
  cudaGraphAddKernelNode(&stg1, pdtGraph, NULL, 0, &paramsStg1);
  CUDACHECK;
  cudaGraphAddKernelNode(&stg2, pdtGraph, NULL, 0, &paramsStg2);
  CUDACHECK;
  cudaGraphAddKernelNode(&stg3, pdtGraph, NULL, 0, &paramsStg3);
  CUDACHECK;

  // Add the node dependencies
  cudaGraphAddDependencies(pdtGraph, &stg1, &stg2, 1);
  CUDACHECK;
  cudaGraphAddDependencies(pdtGraph, &stg2, &stg3, 1);
  CUDACHECK;


  // Instantiate graph and apply optimizations
  cudaGraphInstantiate(&pdtExecGraph, pdtGraph, NULL, NULL, 0);


  return 0;

  }
