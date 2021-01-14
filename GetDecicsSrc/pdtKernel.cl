
/* This is supposed to give printf functionality on AMD */
//#pragma OPENCL EXTENSION cl_amd_printf : enable

#define TRUE  1
#define FALSE 0
#define MEM_ERR 2


// Use this to turn on DEBUG mode
//#define DEBUG
#define DBG_THREAD 0


// WARNING: printf can have problems with some OpenCL implementations
// We only enable it for debug purposes.
// The PRINTF_ENABLED is used in gpuMultiPrec to turn on the printing functions.
#ifdef DEBUG
  #define PRINTF_ENABLED
#endif


#include "gpuMultiPrec.h"



/*
// NOTE: This is the original code which has now been deprecated.
// OpenCL kernel function to do the pol disc test (stage 1)
__kernel
void pdtKernelStg1(int numPolys, __global int64_t *polys, __global char *validFlag, __global mp_int *polDiscArray )
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;


  // We error on the side of caution and initialize validFlag to true.
  // This setting keeps the polynomial on the list for further testing.
  // We do this in case the kernel aborts early before properly setting the flag.
  validFlag[index] = TRUE;


  // Extract the polynomial for this thread.
  // It is assummed the input coefficients are in decreasing order of degree.
  // (i.e. A[0]*x^10 + A[1]*x^9 + ... + A[9]*x + A[10])
  // BUT FOR IMPLEMENTATION REASONS, WE REVERSE THE ORDER.
  int64_t A[11];
  for(int col = 0; col < 11; col++)  A[10-col] = polys[index*11+col];


  // Compute the derivative of A.  Call it B.
  // NOTE: B = 10*x^9 + 9*A[9]*x^8 + 8*A[8]*x^7 + ... + 2*A[2]*x + A[1]
  int64_t B[10];
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
    printf("\n\n");
    }
#endif


  ////////////////////////////////////////////////////////////////
  //  Do the first iteration of the sub-resultant algorithm.    //
  //  This allows us to stay with longs a little longer before  //
  //  transitioning to multi-precision.                         //

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

  //  The first iteration of sub-resultant is now complete. //
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
  //mp_copy(polDisc, &(polDiscArray[index]));
  for (int n = 0; n < MP_PREC; n++)  polDiscArray[index].dp[n] = polDisc->dp[n];
  polDiscArray[index].used = polDisc->used;
  polDiscArray[index].sign = polDisc->sign;

}
*/








// OpenCL kernel function to do the sub-resultant initialization and first iteration.
__kernel
void pdtKernelSubResultantInit(int numPolys, __global int64_t *polys, __global int64_t *polyA, __global int64_t *polyB, 
     __global int *DegA, __global int *DegB, __global int64_t *G, __global int64_t *H )
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;


  // Extract the polynomial for this thread.
  // It is assummed the input coefficients are in decreasing order of degree.
  // (i.e. A[0]*x^10 + A[1]*x^9 + ... + A[9]*x + A[10])
  // BUT FOR IMPLEMENTATION REASONS, WE REVERSE THE ORDER.
  int64_t A[11];
  for(int col = 0; col < 11; col++)  A[10-col] = polys[index*11+col];

  // Compute the derivative of A.  Call it B.
  // NOTE: B = 10*x^9 + 9*A[9]*x^8 + 8*A[8]*x^7 + ... + 2*A[2]*x + A[1]
  int64_t B[10];
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
    printf("\n\n");
    }
#endif


  ////////////////////////////////////////////////////////////////
  //  Do the first iteration of the sub-resultant algorithm.    //
  //  This allows us to stay with longs a little longer before  //
  //  transitioning to multi-precision.                         //

  // This computes: R = d*A-S*B in Algorithm 3.1.2
  int64_t R[10];
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

  //  The first iteration of sub-resultant is now complete.     //
  ////////////////////////////////////////////////////////////////


  // Setup next iteration: A=B, B=R, g=A[9](= original B[9]), h=g.
  DegA[index] = 9;
  DegB[index] = degR;
  for(int col=0; col<=9; col++)    polyA[index*10+col] = B[col];
  for(int col=0; col<=degR; col++) polyB[index*9 +col] = R[col];
  G[index] = B[9];
  H[index] = B[9];

#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration 1:\n");
    printf("  A = %ld ", polyA[index*10]);
    for(int k=1; k<=DegA[index]; k++) printf("+ %ld x^%d ", polyA[index*10+k], k);
    printf("\n");
    printf("  B = %ld ", polyB[index*9]);
    for(int k=1; k<=DegB[index]; k++) printf("+ %ld x^%d ", polyB[index*9+k], k);
    printf("\n  g = %ld\n", G[index]);
    printf("  h = %ld\n\n", H[index]);
    }
#endif

}  // End of pdtKernelSubResultantInit





// OpenCL kernel function to run the iteration of the sub-resultant for the case when degB = 8.
__kernel
void pdtKernelSubResultantDegB8(int numPolys, __global int64_t *polyA, __global int64_t *polyB, 
     __global int *DegA, __global int *DegB, __global int64_t *G, __global int64_t *H )
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;

  // Skip any polynomial for which degB is not 8.
  if(DegB[index]<8) return;


  // Extract A and B polynomials from previous stage
  int64_t A[10], B[9];
  for(int col=0; col<=9; col++)  A[col] = polyA[index*10+col];
  for(int col=0; col<=8; col++)  B[col] = polyB[index*9 +col];

  // Compute R
  int64_t R[9];
  R[0] = B[8]*A[0];
  for(int k=1;k<=8;++k)  R[k] = B[8]*A[k] - A[9]*B[k-1];
  for(int k=0;k<=7;++k)  R[k] = B[8]*R[k] - R[8]*B[k];

  // Determine the degree of R (it must be less than or equal to 7)
  int degR = 0;
  for(int k=7; k>0; k--)  {
    if( R[k]!=0 ) { degR=k; break; }
    }

  // Scale R by g*h.  g=h=A[9]
  int64_t Rscale = A[9]*A[9];
  for(int k=0;k<=degR;++k)  R[k] = R[k]/Rscale;

  // Setup the next iteration: A=B, B=R, g=l(A), h=g.
  DegA[index] = 8;
  DegB[index] = degR;
  for(int col=0; col<=8; col++)    polyA[index*10+col] = B[col];
  for(int col=0; col<=degR; col++) polyB[index*9 +col] = R[col];
  G[index] = B[8];  // g = leading coeff of A = B[8]
  H[index] = B[8];  // h = g

#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB8:\n");
    printf("  A = %ld ", polyA[index*10]);
    for(int k=1; k<=DegA[index]; k++) printf("+ %ld x^%d ", polyA[index*10+k], k);
    printf("\n");
    printf("  B = %ld ", polyB[index*9]);
    for(int k=1; k<=DegB[index]; k++) printf("+ %ld x^%d ", polyB[index*9+k], k);
    printf("\n  g = %ld\n", G[index]);
    printf("  h = %ld\n\n", H[index]);
    }
#endif

}  // End of pdtKernelSubResultantDegB8





// OpenCL kernel function for initializing the multi-precision variables needed by sub-resultant.
__kernel
void pdtKernelSubResultantMpInit(int numPolys, __global char *validFlag, __global int64_t *polyA, __global int64_t *polyB, 
     __global int *DegA, __global int *DegB, __global mp_int *mpA, __global mp_int *mpB )
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;

  // We error on the side of caution and initialize validFlag to true.
  // This setting keeps the polynomial on the list for further testing.
  // We do this in case the kernel aborts early before properly setting the flag.
  validFlag[index] = TRUE;

  // Transfer the int64_t data into the multi-precision variables
  // We only do the polynomials A and B for now, G/H can stay 64 bits for a couple more iterations.
  //for(int col=0; col<=DegA[index]; col++)  mp_set_int64(&(mpA[index*10+col]), polyA[index*10+col]);
  //for(int col=0; col<=DegB[index]; col++)  mp_set_int64(&(mpB[index*9 +col]), polyB[index*9 +col]);

  // OpenCL doesn't allow mpA/mpB to be passed by reference into the mp_set_int64 function as above.
  // So we use an intermediate temp variable.
  mp_int tmp;
  for(int col=0; col<=DegA[index]; col++) {
    mp_set_int64( &tmp, polyA[index*10+col]  );
    mp_copy_p2g(  &tmp, &(mpA[index*10+col]) );  // Set mpA[..] = tmp
    }
  for(int col=0; col<=DegB[index]; col++) {
    mp_set_int64( &tmp, polyB[index*9+col]  );
    mp_copy_p2g(  &tmp, &(mpB[index*9+col]) );  // Set mpB[..] = tmp
    }

#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After multi-precision initialization:\n");
    printf("  A = "); mp_print_poly_g(&(mpA[index*10]),DegA[index]); printf("\n");
    printf("  B = "); mp_print_poly_g(&(mpB[index*9]), DegB[index]); printf("\n\n");
    }
#endif

}





// OpenCL kernel function to run the iteration of the sub-resultant for the case when degB=7 and degA=9.
__kernel
void pdtKernelSubResultantDegB7DegA9(int numPolys, __global int *DegA, __global int *DegB, __global mp_int *MPA, 
     __global mp_int *MPB, __global int64_t *G, __global int64_t *H )
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;

  // Skip any polynomial for which degB is not 7 or degA is not 9.
  if(DegB[index]!=7 || DegA[index]!=9) return;


  // Multi-precision declarations
  mp_int mpA[10], mpB[8], mpR[9], mpT1, mpT2;

  // Copy data from gpu memory into local memory for this thread
  for(int col=0; col<=9; col++)  mp_copy_g2p(&(MPA[index*10+col]), &(mpA[col]));
  for(int col=0; col<=7; col++)  mp_copy_g2p(&(MPB[index*9 +col]), &(mpB[col]));


  // The remaining multi-precision initializations.
  // Note: These need to either be set or zeroed out one time.
  for(int k=0; k<=8; k++)  mp_zero(&(mpR[k]));
  mp_zero(&mpT1);
  mp_zero(&mpT2);


  //////////////////////////////////////////////////////////////////////////////
  // Compute R.
  // What follows is the mp equivalent of this:
  //    R[0] = B[7]*A[0];  R[1] = B[7]*A[1];
  //    for(int k=2;k<=8;++k)  R[k] = B[7]*A[k] - A[9]*B[k-2];
  //    R[0] = B[7]*R[0];
  //    for(int k=1;k<=7;++k)  R[k] = B[7]*R[k] - R[8]*B[k-1];
  //    for(int k=0;k<=6;++k)  R[k] = B[7]*R[k] - R[7]*B[k];
  mp_mul( &(mpB[7]), &(mpA[0]), &(mpR[0]) );
  mp_mul( &(mpB[7]), &(mpA[1]), &(mpR[1]) );
  for(int k=2;k<=8;++k) {
    mp_mul( &(mpB[7]), &(mpA[k]),   &mpT1 );  // 1st term
    mp_mul( &(mpA[9]), &(mpB[k-2]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  mp_mul( &(mpB[7]), &(mpR[0]), &(mpR[0]) );
  for(int k=1;k<=7;++k) {
    mp_mul( &(mpB[7]), &(mpR[k]),   &mpT1 );  // 1st term
    mp_mul( &(mpR[8]), &(mpB[k-1]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  for(int k=0;k<=6;++k) {
    mp_mul( &(mpB[7]), &(mpR[k]), &mpT1 );  // 1st term
    mp_mul( &(mpR[7]), &(mpB[k]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  //////////////////////////////////////////////////////////////////////////////


  // Determine the degree of R (it must be less than or equal to 6)
  int degR = 0;
  for(int k=6; k>0; k--)  {
    if( mpR[k].used>0 ) { degR=k; break; }
    }


  // Scale R by g*h^2 where g=h=A[9].
  // We know that A[9]^3<1000 easily fits in 31 bits (size of a digit).
  mp_digit Rscale = mpA[9].dp[0] * mpA[9].dp[0] * mpA[9].dp[0];
  for(int k=0;k<=degR;++k) {
    mp_div_d( &(mpR[k]), Rscale, &(mpR[k]), NULL );  // R[k] = R[k]/Rscale;
    mpR[k].sign = mpR[k].sign * mpA[9].sign;  // Correct the sign
    }


  // Set A=B
  DegA[index] = 7;
  for(int col=0; col<=7; col++)  mp_copy_p2g( &(mpB[col]), &(MPA[index*10+col]) );

  // Set B = R
  DegB[index] = degR;
  for(int col=0; col<=degR; col++)  mp_copy_p2g( &(mpR[col]), &(MPB[index*9+col]) );

  // Set g = B[7].
  // Since there are only 31 bits in a digit, we need to do some work to get int64_t.
  int64_t g = (((uint64_t)mpB[7].dp[1])<<DIGIT_BIT) + (uint64_t)mpB[7].dp[0];
  g = g * mpB[7].sign;

  // Set G and H.
  G[index] = g;  // g = leading coeff of A = B[7]
  H[index] = (g*g)/H[index];  // h = g^2/h = B[7]^2/A[9]

#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB7, degA9:\n");
    printf("  A = "); mp_print_poly_g(&(MPA[index*10]),DegA[index]); printf("\n");
    printf("  B = "); mp_print_poly_g(&(MPB[index*9]), DegB[index]); printf("\n");
    printf("  g = %ld\n", G[index]);
    printf("  h = %ld\n\n", H[index]);
    }
#endif

}  // End of pdtKernelSubResultantDegB7DegA9





// OpenCL kernel function to run the iteration of the sub-resultant for the case when degB=7 and degA=8.
__kernel
void pdtKernelSubResultantDegB7DegA8(int numPolys, __global int *DegA, __global int *DegB, __global mp_int *MPA, 
     __global mp_int *MPB, __global int64_t *G, __global int64_t *H )
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;

  // Skip any polynomial for which degB is not 7 or degA is not 8.
  if(DegB[index]!=7 || DegA[index]!=8) return;


  // Multi-precision declarations
  mp_int mpA[9], mpB[8], mpR[8], mpT1, mpT2;

  // Copy data from gpu memory into local memory for this thread
  for(int col=0; col<=8; col++)  mp_copy_g2p(&(MPA[index*10+col]), &(mpA[col]));
  for(int col=0; col<=7; col++)  mp_copy_g2p(&(MPB[index*9 +col]), &(mpB[col]));

  // The remaining multi-precision initializations.
  // Note: These need to either be set or zeroed out one time.
  for(int k=0; k<=7; k++)  mp_zero(&(mpR[k]));
  mp_zero(&mpT1);
  mp_zero(&mpT2);


  //////////////////////////////////////////////////////////////////////////////
  // Compute R.
  // What follows is the mp equivalent of this:
  //    R[0] = B[7]*A[0];
  //    for(int k=1;k<=7;++k)  R[k] = B[7]*A[k] - A[8]*B[k-1];
  //    for(int k=0;k<=6;++k)  R[k] = B[7]*R[k] - R[7]*B[k];
  mp_mul( &(mpB[7]), &(mpA[0]), &(mpR[0]) );
  for(int k=1;k<=7;++k) {
    mp_mul( &(mpB[7]), &(mpA[k]),   &mpT1 );  // 1st term
    mp_mul( &(mpA[8]), &(mpB[k-1]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  for(int k=0;k<=6;++k) {
    mp_mul( &(mpB[7]), &(mpR[k]), &mpT1 );  // 1st term
    mp_mul( &(mpR[7]), &(mpB[k]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  //////////////////////////////////////////////////////////////////////////////


  // Determine the degree of R (it must be less than or equal to 6)
  int degR = 0;
  for(int k=6; k>0; k--)  {
    if( mpR[k].used>0 ) { degR=k; break; }
    }

  // Scale R by g*h where g=h=A[8].
  mp_digit Rscale = mpA[8].dp[0] * mpA[8].dp[0];
  for(int k=0;k<=degR;++k) {
    mp_div_d( &(mpR[k]), Rscale, &(mpR[k]), NULL );  // R[k] = R[k]/Rscale;
    }

  // Set A=B
  DegA[index] = 7;
  for(int col=0; col<=7; col++)  mp_copy_p2g( &(mpB[col]), &(MPA[index*10+col]) );

  // Set B = R
  DegB[index] = degR;
  for(int col=0; col<=degR; col++)  mp_copy_p2g( &(mpR[col]), &(MPB[index*9+col]) );

  // Set g = B[7].
  // Since there are only 31 bits in a digit, we need to do some work to get int64_t.
  int64_t g = (((uint64_t)mpB[7].dp[1])<<DIGIT_BIT) + (uint64_t)mpB[7].dp[0];
  g = g * mpB[7].sign;

  // Set G and H.
  G[index] = g;  // g = leading coeff of A = B[7]
  H[index] = g;  // h = g (since delta=1)

#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB7, degA8:\n");
    printf("  A = "); mp_print_poly_g(&(MPA[index*10]),DegA[index]); printf("\n");
    printf("  B = "); mp_print_poly_g(&(MPB[index*9]), DegB[index]); printf("\n");
    printf("  g = %ld\n", G[index]);
    printf("  h = %ld\n\n", H[index]);
    }
#endif

}  // End of pdtKernelSubResultantDegB7DegA8





// OpenCL kernel function to run the iteration of the sub-resultant for the case when degB=6 and degA=9.
__kernel
void pdtKernelSubResultantDegB6DegA9(int numPolys, __global int *DegA, __global int *DegB, __global mp_int *MPA, 
     __global mp_int *MPB, __global int64_t *G, __global int64_t *H )
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;

  // Skip any polynomial for which degB is not 6 or degA is not 9.
  if(DegB[index]!=6 || DegA[index]!=9) return;


  // Multi-precision declarations
  mp_int mpA[10], mpB[7], mpR[9], mpT1, mpT2;

  // Copy data from global memory into local memory for this thread
  for(int col=0; col<=9; col++)  mp_copy_g2p(&(MPA[index*10+col]), &(mpA[col]));
  for(int col=0; col<=6; col++)  mp_copy_g2p(&(MPB[index*9 +col]), &(mpB[col]));


  // The remaining multi-precision initializations.
  // Note: These need to either be set or zeroed out one time.
  for(int k=0; k<=8; k++)  mp_zero(&(mpR[k]));
  mp_zero(&mpT1);
  mp_zero(&mpT2);


  //////////////////////////////////////////////////////////////////////////////
  // Compute R.
  // What follows is the mp equivalent of this:
  //    R[0] = B[6]*A[0];  R[1] = B[6]*A[1];  R[2] = B[6]*A[2];
  //    for(int k=3;k<=8;++k)  R[k] = B[6]*A[k] - A[9]*B[k-3];
  //    R[0] = B[6]*R[0];  R[1] = B[6]*R[1];
  //    for(int k=2;k<=7;++k)  R[k] = B[6]*R[k] - R[8]*B[k-2];
  //    R[0] = B[6]*R[0];
  //    for(int k=1;k<=6;++k)  R[k] = B[6]*R[k] - R[7]*B[k-1];
  //    for(int k=0;k<=5;++k)  R[k] = B[6]*R[k] - R[6]*B[k];

  mp_mul( &(mpB[6]), &(mpA[0]), &(mpR[0]) );
  mp_mul( &(mpB[6]), &(mpA[1]), &(mpR[1]) );
  mp_mul( &(mpB[6]), &(mpA[2]), &(mpR[2]) );
  for(int k=3;k<=8;++k) {
    mp_mul( &(mpB[6]), &(mpA[k]),   &mpT1 );  // 1st term
    mp_mul( &(mpA[9]), &(mpB[k-3]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  mp_mul( &(mpB[6]), &(mpR[0]), &(mpR[0]) );
  mp_mul( &(mpB[6]), &(mpR[1]), &(mpR[1]) );
  for(int k=2;k<=7;++k) {
    mp_mul( &(mpB[6]), &(mpR[k]),   &mpT1 );  // 1st term
    mp_mul( &(mpR[8]), &(mpB[k-2]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  mp_mul( &(mpB[6]), &(mpR[0]), &(mpR[0]) );
  for(int k=1;k<=6;++k) {
    mp_mul( &(mpB[6]), &(mpR[k]),   &mpT1 );  // 1st term
    mp_mul( &(mpR[7]), &(mpB[k-1]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  for(int k=0;k<=5;++k) {
    mp_mul( &(mpB[6]), &(mpR[k]), &mpT1 );  // 1st term
    mp_mul( &(mpR[6]), &(mpB[k]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  //////////////////////////////////////////////////////////////////////////////


  // Determine the degree of R (it must be less than or equal to 5)
  int degR = 0;
  for(int k=5; k>0; k--)  {
    if( mpR[k].used>0 ) { degR=k; break; }
    }


  // Scale R by g*h^3 where g=h=A[9].
  // We know that A[9]^4<10000 easily fits in 31 bits (size of a digit).
  mp_digit Rscale = mpA[9].dp[0] * mpA[9].dp[0];
  Rscale = Rscale * Rscale;
  for(int k=0;k<=degR;++k) {
    mp_div_d( &(mpR[k]), Rscale, &(mpR[k]), NULL );  // R[k] = R[k]/Rscale;
    }


  // Set A=B
  DegA[index] = 6;
  for(int col=0; col<=6; col++)  mp_copy_p2g( &(mpB[col]), &(MPA[index*10+col]) );

  // Set B = R
  DegB[index] = degR;
  for(int col=0; col<=degR; col++)  mp_copy_p2g( &(mpR[col]), &(MPB[index*9+col]) );

  // Set g = B[6].
  // Since there are only 31 bits in a digit, we need to do some work to get int64_t.
  int64_t g = (((uint64_t)mpB[6].dp[1])<<DIGIT_BIT) + (uint64_t)mpB[6].dp[0];
  g = g * mpB[6].sign;

  // Set G and H.
  G[index] = g;  // g = leading coeff of A = B[6]
  H[index] = (g*g*g)/(H[index]*H[index]);  // h = g^3/h^2

#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB6, degA9:\n");
    printf("  A = "); mp_print_poly_g(&(MPA[index*10]),DegA[index]); printf("\n");
    printf("  B = "); mp_print_poly_g(&(MPB[index*9]), DegB[index]); printf("\n");
    printf("  g = %ld\n", G[index]);
    printf("  h = %ld\n\n", H[index]);
    }
#endif

}  // End of pdtKernelSubResultantDegB6DegA9





// OpenCL kernel function to run the iteration of the sub-resultant for the case when degB=6 and degA=8.
__kernel
void pdtKernelSubResultantDegB6DegA8(int numPolys, __global int *DegA, __global int *DegB, __global mp_int *MPA, 
     __global mp_int *MPB, __global int64_t *G, __global int64_t *H )
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;

  // Skip any polynomial for which degB is not 6 or degA is not 8.
  if(DegB[index]!=6 || DegA[index]!=8) return;


  // Multi-precision declarations
  mp_int mpA[9], mpB[7], mpR[8], mpT1, mpT2;

  // Copy data from global memory into local memory for this thread
  for(int col=0; col<=8; col++)  mp_copy_g2p(&(MPA[index*10+col]), &(mpA[col]));
  for(int col=0; col<=6; col++)  mp_copy_g2p(&(MPB[index*9 +col]), &(mpB[col]));


  // The remaining multi-precision initializations.
  // Note: These need to either be set or zeroed out one time.
  for(int k=0; k<=7; k++)  mp_zero(&(mpR[k]));
  mp_zero(&mpT1);
  mp_zero(&mpT2);


  //////////////////////////////////////////////////////////////////////////////
  // Compute R.
  // What follows is the mp equivalent of this:
  //    R[0] = B[6]*A[0];  R[1] = B[6]*A[1];
  //    for(int k=2;k<=7;++k)  R[k] = B[6]*A[k] - A[8]*B[k-2];
  //    R[0] = B[6]*R[0];
  //    for(int k=1;k<=6;++k)  R[k] = B[6]*R[k] - R[7]*B[k-1];
  //    for(int k=0;k<=5;++k)  R[k] = B[6]*R[k] - R[6]*B[k];

  mp_mul( &(mpB[6]), &(mpA[0]), &(mpR[0]) );
  mp_mul( &(mpB[6]), &(mpA[1]), &(mpR[1]) );
  for(int k=2;k<=7;++k) {
    mp_mul( &(mpB[6]), &(mpA[k]),   &mpT1 );  // 1st term
    mp_mul( &(mpA[8]), &(mpB[k-2]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  mp_mul( &(mpB[6]), &(mpR[0]), &(mpR[0]) );
  for(int k=1;k<=6;++k) {
    mp_mul( &(mpB[6]), &(mpR[k]),   &mpT1 );  // 1st term
    mp_mul( &(mpR[7]), &(mpB[k-1]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  for(int k=0;k<=5;++k) {
    mp_mul( &(mpB[6]), &(mpR[k]), &mpT1 );  // 1st term
    mp_mul( &(mpR[6]), &(mpB[k]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  //////////////////////////////////////////////////////////////////////////////


  // Determine the degree of R (it must be less than or equal to 5)
  int degR = 0;
  for(int k=5; k>0; k--)  {
    if( mpR[k].used>0 ) { degR=k; break; }
    }


  // Scale R by g*h^2 where g=h=A[8].
  // Analysis shows A[8]^3 should fit within 31 bits, but just to be safe
  // we do the division in 2 steps.
  mp_digit Rscale = mpA[8].dp[0] * mpA[8].dp[0];
  for(int k=0;k<=degR;++k) {
    mp_div_d( &(mpR[k]), Rscale, &(mpR[k]), NULL );  // R[k] = R[k]/A[8]^2;
    mp_div_d( &(mpR[k]), mpA[8].dp[0], &(mpR[k]), NULL );  // R[k] = R[k]/A[8];
    mpR[k].sign = mpR[k].sign * mpA[8].sign;  // Correct the sign
    }


  // Set A=B
  DegA[index] = 6;
  for(int col=0; col<=6; col++)  mp_copy_p2g( &(mpB[col]), &(MPA[index*10+col]) );

  // Set B = R
  DegB[index] = degR;
  for(int col=0; col<=degR; col++)  mp_copy_p2g( &(mpR[col]), &(MPB[index*9+col]) );

  // Set g = B[6].
  // Since there are only 31 bits in a digit, we need to do some work to get int64_t.
  int64_t g = (((uint64_t)mpB[6].dp[1])<<DIGIT_BIT) + (uint64_t)mpB[6].dp[0];
  g = g * mpB[6].sign;

  // Set G and H.
  G[index] = g;  // g = leading coeff of A = B[6]
  H[index] = mpA[8].sign * (g*g) / ((int64_t)mpA[8].dp[0]); // h = (g^2)/A[8]


#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB6, degA8:\n");
    printf("  A = "); mp_print_poly_g(&(MPA[index*10]),DegA[index]); printf("\n");
    printf("  B = "); mp_print_poly_g(&(MPB[index*9]), DegB[index]); printf("\n");
    printf("  g = %ld\n", G[index]);
    printf("  h = %ld\n\n", H[index]);
    }
#endif

}  // End of pdtKernelSubResultantDegB6DegA8








// OpenCL kernel function to run the iteration of the sub-resultant for the case when degB=6 and degA=7.
__kernel
void pdtKernelSubResultantDegB6DegA7(int numPolys, __global int *DegA, __global int *DegB, __global mp_int *MPA, 
     __global mp_int *MPB, __global int64_t *G, __global int64_t *H )
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;

  // Skip any polynomial for which degB is not 6 or degA is not 7.
  if(DegB[index]!=6 || DegA[index]!=7) return;


  // Multi-precision declarations
  mp_int mpA[8], mpB[7], mpR[7], mpT1, mpT2;

  // Copy data from global memory into local memory for this thread
  for(int col=0; col<=7; col++)  mp_copy_g2p(&(MPA[index*10+col]), &(mpA[col]));
  for(int col=0; col<=6; col++)  mp_copy_g2p(&(MPB[index*9 +col]), &(mpB[col]));


  // The remaining multi-precision initializations.
  // Note: These need to either be set or zeroed out one time.
  for(int k=0; k<=6; k++)  mp_zero(&(mpR[k]));
  mp_zero(&mpT1);
  mp_zero(&mpT2);


  //////////////////////////////////////////////////////////////////////////////
  // Compute R.
  // What follows is the mp equivalent of this:
  //    R[0] = B[6]*A[0];
  //    for(int k=1;k<=6;++k)  R[k] = B[6]*A[k] - A[7]*B[k-1];
  //    for(int k=0;k<=5;++k)  R[k] = B[6]*R[k] - R[6]*B[k];

  mp_mul( &(mpB[6]), &(mpA[0]), &(mpR[0]) );
  for(int k=1;k<=6;++k) {
    mp_mul( &(mpB[6]), &(mpA[k]),   &mpT1 );  // 1st term
    mp_mul( &(mpA[7]), &(mpB[k-1]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  for(int k=0;k<=5;++k) {
    mp_mul( &(mpB[6]), &(mpR[k]), &mpT1 );  // 1st term
    mp_mul( &(mpR[6]), &(mpB[k]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  //////////////////////////////////////////////////////////////////////////////


  // Determine the degree of R (it must be less than or equal to 5)
  int degR = 0;
  for(int k=5; k>0; k--)  {
    if( mpR[k].used>0 ) { degR=k; break; }
    }


  // Scale R by g*h.
  // Analysis shows g and h each easily fit within 31 bits, but their product might
  // exceed 31 bits.  So to be safe we use full multi-precision division.
  mp_int gh;
  mp_set_int64(&gh, G[index]*H[index]);
  for(int k=0;k<=degR;++k) {
    mp_div( &(mpR[k]), &gh, &(mpR[k]), NULL );  // R[k] = R[k]/gh
    }


  // Set A=B
  DegA[index] = 6;
  for(int col=0; col<=6; col++)  mp_copy_p2g( &(mpB[col]), &(MPA[index*10+col]) );

  // Set B = R
  DegB[index] = degR;
  for(int col=0; col<=degR; col++)  mp_copy_p2g( &(mpR[col]), &(MPB[index*9+col]) );

  // Set g = B[6].
  // Since there are only 31 bits in a digit, we need to do some work to get int64_t.
  int64_t g = (((uint64_t)mpB[6].dp[1])<<DIGIT_BIT) + (uint64_t)mpB[6].dp[0];
  g = g * mpB[6].sign;

  // Set G and H.
  G[index] = g;  // g = leading coeff of A = B[6]
  H[index] = g;  // h = g (since delta=1)


#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB6, degA7:\n");
    printf("  A = "); mp_print_poly_g(&(MPA[index*10]),DegA[index]); printf("\n");
    printf("  B = "); mp_print_poly_g(&(MPB[index*9]), DegB[index]); printf("\n");
    printf("  g = %ld\n", G[index]);
    printf("  h = %ld\n\n", H[index]);
    }
#endif

}  // End of pdtKernelSubResultantDegB6DegA7





// OpenCL kernel function to run the iteration of the sub-resultant for the case when degB=5.
// Analysis has shown that the vast majority of cases will have degA=6, so we assume degA=6
// and any other case will be kicked back to the cpu.
__kernel
void pdtKernelSubResultantDegB5(int numPolys,  __global char *validFlag, __global int *DegA, __global int *DegB, 
     __global mp_int *MPA, __global mp_int *MPB, __global int64_t *G, __global int64_t *H )
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;

  // Skip any polynomial for which degB is not 5 or degA is not 6.
  // We hijack the memory overflow flag to force the CPU to handle it.
  if(DegB[index]!=5 || DegA[index]!=6) { validFlag[index] = MEM_ERR; return; }


  // Multi-precision declarations
  mp_int mpA[7], mpB[6], mpR[6], mpG, mpH, mpT1, mpT2;

  // Copy data from global memory into local memory for this thread
  for(int col=0; col<=6; col++)  mp_copy_g2p(&(MPA[index*10+col]), &(mpA[col]));
  for(int col=0; col<=5; col++)  mp_copy_g2p(&(MPB[index*9 +col]), &(mpB[col]));

  // Transfer G and H into multi-precision variables.
  mp_set_int64( &mpG, G[index] );
  mp_set_int64( &mpH, H[index] );

  // The remaining multi-precision initializations.
  // Note: These need to either be set or zeroed out one time.
  for(int k=0; k<=5; k++)  mp_zero(&(mpR[k]));
  mp_zero(&mpT1);
  mp_zero(&mpT2);


  //////////////////////////////////////////////////////////////////////////////
  // Compute R.
  // What follows is the mp equivalent of this:
  //    R[0] = B[5]*A[0];
  //    for(int k=1;k<=5;++k)  R[k] = B[5]*A[k] - A[6]*B[k-1];
  //    for(int k=0;k<=4;++k)  R[k] = B[5]*R[k] - R[5]*B[k];

  mp_mul( &(mpB[5]), &(mpA[0]), &(mpR[0]) );
  for(int k=1;k<=5;++k) {
    mp_mul( &(mpB[5]), &(mpA[k]),   &mpT1 );  // 1st term
    mp_mul( &(mpA[6]), &(mpB[k-1]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  for(int k=0;k<=4;++k) {
    mp_mul( &(mpB[5]), &(mpR[k]), &mpT1 );  // 1st term
    mp_mul( &(mpR[5]), &(mpB[k]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  //////////////////////////////////////////////////////////////////////////////


  // Determine the degree of R (it must be less than or equal to 4)
  int degR = 0;
  for(int k=4; k>0; k--)  {
    if( mpR[k].used>0 ) { degR=k; break; }
    }
  // Analysis has shown degR=4 99.9999% of the time.  So if its not 4, let the cpu handle it.
  if( degR!=4 ) {
    validFlag[index] = MEM_ERR;
    return;
    }


  // Set A=B
  DegA[index] = 5;
  for(int col=0; col<=5; col++)  mp_copy_p2g( &(mpB[col]), &(MPA[index*10+col]) );

  // Set B = R/(gh)
  DegB[index] = 4;
  mp_mul( &mpG, &mpH, &mpT1 );  // Set T1 = g*h
  for(int col=0; col<=4; col++)  {
    mp_div( &(mpR[col]), &mpT1, &(mpB[col]), NULL ); // Set B[k] = R[k] / T1;
    mp_copy_p2g( &(mpB[col]), &(MPB[index*9+col]) );
    }

#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB5:\n");
    printf("  A = "); mp_print_poly_g(&(MPA[index*10]),DegA[index]); printf("\n");
    printf("  B = "); mp_print_poly_g(&(MPB[index*9]), DegB[index]); printf("\n");
    printf("  g = "); mp_printf( MPA[index*10+5] ); printf("\n");
    printf("  h = "); mp_printf( MPA[index*10+5] ); printf("\n\n");
    }
#endif

}  // End of pdtKernelSubResultantDegB5











// OpenCL kernel function to run the iteration of the sub-resultant for the case when degB=4.
// This kernel will complete the sub-resultant calculation.
// Analysis has shown that the vast majority of cases will have degA=5 and in all subsequent
// iterations, the degrees of A and B will drop by 1.  Whenever this does not occur, the
// polynomial is kicked back to the cpu for processing (less than 1 in 100000 polys).
__kernel
void pdtKernelSubResultantDegB4( int numPolys, __global char *validFlag, __global mp_int *polDiscArray,
     __global int *DegA, __global int *DegB, __global mp_int *MPA, __global mp_int *MPB )
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;

  int degA = DegA[index];
  int degB = DegB[index];

  // Skip any polynomial for which degB is not 5 or degA is not 6.
  // We hijack the memory overflow flag to force the CPU to handle it.
  if(degB!=4 || degA!=5) { validFlag[index] = MEM_ERR; return; }


  // Multi-precision declarations
  mp_int mpA[6], mpB[5], mpR[5], mpT1, mpT2;

  // Copy data from global memory into local memory for this thread
  for(int col=0; col<=5; col++)  mp_copy_g2p(&(MPA[index*10+col]), &(mpA[col]));
  for(int col=0; col<=4; col++)  mp_copy_g2p(&(MPB[index*9 +col]), &(mpB[col]));

  // The remaining multi-precision initializations.
  // Note: These need to either be set or zeroed out one time.
  for(int k=0; k<=4; k++)  mp_zero(&(mpR[k]));
  mp_zero(&mpT1);
  mp_zero(&mpT2);


  //////////////////////////////////////////////////////////////////////////////
  // Compute R.
  // What follows is the mp equivalent of this:
  //    R[0] = B[4]*A[0];
  //    for(int k=1;k<=4;++k)  R[k] = B[4]*A[k] - A[5]*B[k-1];
  //    for(int k=0;k<=3;++k)  R[k] = B[4]*R[k] - R[4]*B[k];

  mp_mul( &(mpB[4]), &(mpA[0]), &(mpR[0]) );
  for(int k=1;k<=4;++k) {
    mp_mul( &(mpB[4]), &(mpA[k]),   &mpT1 );  // 1st term
    mp_mul( &(mpA[5]), &(mpB[k-1]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  for(int k=0;k<=3;++k) {
    mp_mul( &(mpB[4]), &(mpR[k]), &mpT1 );  // 1st term
    mp_mul( &(mpR[4]), &(mpB[k]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  ////////////////////////////////////////////////////////////////////////////////


  // Determine the degree of R (it must be less than or equal to 3)
  int degR = 0;
  for(int k=3; k>0; k--)  {
    if( mpR[k].used>0 ) { degR=k; break; }
    }
  // Analysis has shown degR=3 the vast majority of the time.  So if its not 3, let the cpu handle it.
  if( degR<3 ) {
    validFlag[index] = MEM_ERR;
    return;
    }

  // From previous iteration, g=h=A[5]
  mp_mul( &(mpA[5]), &(mpA[5]), &mpT1 );  // Set T1 = g^2


  // NOTE: To save ops, we interchange the role of A and B.
  // Set A = B
  //degA = 4;
  //for(int k=0; k<=4; k++)  mp_copy( &(mpB[k]), &(mpA[k]) );

  // Set B = R/(g^2) (delta=1 and g=h)
  //degB = 3;
  for(int col=0; col<=3; col++) {
    mp_div( &(mpR[col]), &mpT1, &(mpA[col]), NULL ); // Set A[k] = R[k] / T1;
    }

#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB4:\n");
    printf("  A = "); mp_print_poly(mpB, 4); printf("\n"); // A and B have been interchanged.
    printf("  B = "); mp_print_poly(mpA, 3); printf("\n");
    printf("  g = "); mp_printf( mpB[4] ); printf("\n");
    printf("  h = "); mp_printf( mpB[4] ); printf("\n\n");
    }
#endif


  //////////////////////////////////////////////////////////////////////////////
  //
  // Here starts the iteration for degB=3
  //
  // Compute R.
  // What follows is the mp equivalent of this (but A and B must be swapped):
  //    R[0] = B[3]*A[0];
  //    for(int k=1;k<=3;++k)  R[k] = B[3]*A[k] - A[4]*B[k-1];
  //    for(int k=0;k<=2;++k)  R[k] = B[3]*R[k] - R[3]*B[k];

  mp_mul( &(mpA[3]), &(mpB[0]), &(mpR[0]) );
  for(int k=1;k<=3;++k) {
    mp_mul( &(mpA[3]), &(mpB[k]),   &mpT1 );  // 1st term
    mp_mul( &(mpB[4]), &(mpA[k-1]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  for(int k=0;k<=2;++k) {
    mp_mul( &(mpA[3]), &(mpR[k]), &mpT1 );  // 1st term
    mp_mul( &(mpR[3]), &(mpA[k]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }

  // Determine the degree of R (it must be less than or equal to 2)
  degR = 0;
  for(int k=2; k>0; k--)  {
    if( mpR[k].used>0 ) { degR=k; break; }
    }
  if( degR!=2 ) {
    validFlag[index] = MEM_ERR;
    return;
    }

  // From previous iteration, g=h=A[4].  Don't forget A and B have been swapped.
  mp_mul( &(mpB[4]), &(mpB[4]), &mpT1 );  // Set T1 = g^2


  // We would normally set A=B here, but since they were swapped A is now back to being itself.

  // Set B = R/(g^2) (delta=1 and g=h)
  for(int col=0; col<=2; col++) {
    mp_div( &(mpR[col]), &mpT1, &(mpB[col]), NULL ); // Set B[k] = R[k] / T1;
    }

#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB3:\n");
    printf("  A = "); mp_print_poly(mpA, 3); printf("\n");
    printf("  B = "); mp_print_poly(mpB, 2); printf("\n");
    printf("  g = "); mp_printf( mpA[3] ); printf("\n");
    printf("  h = "); mp_printf( mpA[3] ); printf("\n\n");
    }
#endif


  //////////////////////////////////////////////////////////////////////////////
  //
  // Here starts the iteration for degB=2
  //
  // Compute R.
  // What follows is the mp equivalent of this:
  //    R[0] = B[2]*A[0];
  //    for(int k=1;k<=2;++k)  R[k] = B[2]*A[k] - A[3]*B[k-1];
  //    for(int k=0;k<=1;++k)  R[k] = B[2]*R[k] - R[2]*B[k];

  int retVal = mp_mul( &(mpB[2]), &(mpA[0]), &(mpR[0]) );
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
  for(int k=1;k<=2;++k) {
    retVal = mp_mul( &(mpB[2]), &(mpA[k]),   &mpT1 );  // 1st term
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
    retVal = mp_mul( &(mpA[3]), &(mpB[k-1]), &mpT2 );  // 2nd term
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  for(int k=0;k<=1;++k) {
    retVal = mp_mul( &(mpB[2]), &(mpR[k]), &mpT1 );  // 1st term
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
    retVal = mp_mul( &(mpR[2]), &(mpB[k]), &mpT2 );  // 2nd term
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }


  // Determine the degree of R (it must be less than or equal to 1)
  if( mpR[1].used>0 )  degR=1;
  else                 degR=0;


  // From previous iteration, g=h=A[3]
  retVal = mp_mul( &(mpA[3]), &(mpA[3]), &mpT1 );  // Set T1 = g^2
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }


  // Instead of setting A=B and B=R/g^2, we swap the roles of A and B.
  // Set A = B
  //for(int k=0; k<=2; k++)  mp_copy( &(mpB[k]), &(mpA[k]) );

  // Set B = R/(g^2) (delta=1 and g=h)
  retVal = mp_div( &(mpR[0]), &mpT1, &(mpA[0]), NULL );
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
  retVal = mp_div( &(mpR[1]), &mpT1, &(mpA[1]), NULL );
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }

#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB2:\n");
    printf("  A = "); mp_print_poly(mpB,2); printf("\n");  // A and B have been swapped
    printf("  B = "); mp_print_poly(mpA,1); printf("\n");
    printf("  g = "); mp_printf( mpB[2] ); printf("\n");
    printf("  h = "); mp_printf( mpB[2] ); printf("\n\n");
    }
#endif


  // If degR=0 then we are done.  Set the polDisc value and return.
  if( degR==0 ) {  // h=g=A[2]
    if( IS_ZERO(mpB) ) { validFlag[index] = FALSE; return; }
    mp_int *polDisc;
    polDisc = &(mpB[2]);  // Set polDisc = h = A[2].  But A and B have been swapped.
    polDisc->sign = MP_ZPOS;  // Make sure the discriminant is positive.
    mp_copy_p2g(polDisc, &(polDiscArray[index]));  // Store in global memory.
    #ifdef DEBUG
      if(index==DBG_THREAD) { printf("polDisc = ");  mp_printf(*polDisc); printf("\n"); }
    #endif
    return;
    }


  //////////////////////////////////////////////////////////////////////////////
  //
  // Here starts the iteration for degB=1.
  //
  // Compute R.
  // What follows is the mp equivalent of this (but A and B must be swapped):
  //    R[0] = B[1]*A[0];
  //    R[1] = B[1]*A[1] - A[2]*B[0];
  //    R[0] = B[1]*R[0] - R[1]*B[0];

  retVal = mp_mul( &(mpA[1]), &(mpB[0]), &(mpR[0]) );
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
  retVal = mp_mul( &(mpB[1]), &(mpA[1]), &mpT1 );  // 1st term
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
  retVal = mp_mul( &(mpB[2]), &(mpA[0]), &mpT2 );  // 2nd term
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
  mpT2.sign = -mpT2.sign;  // negate the 2nd term
  mp_add( &mpT1, &mpT2, &(mpR[1]) );  // Sum the terms

  retVal = mp_mul( &(mpA[1]), &(mpR[0]), &mpT1 );  // 1st term
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
  retVal = mp_mul( &(mpR[1]), &(mpA[0]), &mpT2 );  // 2nd term
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
  mpT2.sign = -mpT2.sign;  // negate the 2nd term
  mp_add( &mpT1, &mpT2, &(mpR[0]) );  // Sum the terms

  // Set B = R/(g^2) (delta=1 and g=h) where from previous iteration, g=A[2]
  // And don't forget, A and B have been swapped.
  mp_mul( &(mpB[2]), &(mpB[2]), &mpT1 );  // Set T1 = g^2
  mp_div( &(mpR[0]), &mpT1, &(mpR[0]), NULL );


#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("Sub-resultant complete:\n");
    printf("  A = "); mp_print_poly(mpA,1); printf("\n");
    printf("  B = "); mp_printf(mpR[0]); printf("\n\n");
    }
#endif


  // Now complete the polDisc calculation.
  if( IS_ZERO(mpR) ) { validFlag[index] = FALSE; return; }
  mp_int *polDisc;
  polDisc = &(mpR[0]);   // Set polDisc = R[0]
  polDisc->sign = MP_ZPOS;  // Make sure the discriminant is positive.
  mp_copy_p2g(polDisc, &(polDiscArray[index]));  // Store in global memory.


#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("polDisc = ");  mp_printf(*polDisc); printf("\n");
    }
#endif

}  // End of pdtKernelSubResultantDegB4








// XXXXX

// OpenCL generic function to complete the sub-resultant calculation.
// This function does all remaining iterations of the sub-resultant, starting from the current state
// of A, B, g, and h.  It is mainly used for debugging and timing purposes, and should not be used 
// in the final implementation of the application.
__kernel
void pdtKernelSubResultantFinish( int numPolys, __global char *validFlag, __global mp_int *polDiscArray,
     __global int *DegA, __global int *DegB, __global mp_int *MPA, __global mp_int *MPB,
     __global int64_t *G, __global int64_t *H )
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;


  // Multi-precision declarations
  mp_int g, h, mpA[10], mpB[9], mpR[10], BR, SB[9];
  mp_int q, gPow, hPow, scale;


  // Copy data from gpu memory into local memory for this thread
  int degA = DegA[index];
  int degB = DegB[index];
  for(int col=0; col<=degA; col++)  mp_copy_g2p(&(MPA[index*10+col]), &(mpA[col]));
  for(int col=0; col<=degB; col++)  mp_copy_g2p(&(MPB[index*9 +col]), &(mpB[col]));
  if(degB>5) {
    mp_set_int64(&g, G[index]);
    mp_set_int64(&h, H[index]);
    }
  else { // Set g = h = leading coeff of A
    mp_copy( &(mpA[degA]), &g );
    mp_copy( &(mpA[degA]), &h );
    }


  // The remaining multi-precision initializations.
  // Note: These need to either be set or zeroed out one time.
  for(int k=0; k<10; k++)  mp_zero(&(mpR[k]));
  mp_zero(&BR);
  for(int k=0; k<9; k++)  mp_zero(&(SB[k]));
  mp_zero(&gPow);
  mp_zero(&hPow);
  mp_zero(&scale);


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
    int degR = degA;
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


#ifdef DEBUG
  if(index==DBG_THREAD) {
    // Print iteration header before changing the values of A and B
    printf("After iteration degB%d, degA%d:\n", degB, degA);
    }
#endif


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
  if(index==DBG_THREAD) {
    printf("  A = "); mp_print_poly(mpA,degA); printf("\n");
    printf("  B = "); mp_print_poly(mpB,degB); printf("\n");
    printf("  g = "); mp_printf(g); printf("\n");
    printf("  h = "); mp_printf(h); printf("\n\n");
    }
#endif

    }  // End of outer for loop


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
    printf("Sub-resultant complete:\n");
    printf("polDisc = ");  mp_printf(*polDisc); printf("\n\n");
    }
#endif

  // Make sure the discriminant is positive
  polDisc->sign = MP_ZPOS;

  // Store discriminant in device memory
  mp_copy_p2g(polDisc, &(polDiscArray[index]));

}  // End of pdtKernelSubResultantFinish





/*
// NOTE: This kernel is now deprecated
// OpenCL kernel function to do the pol disc test (stage 2)
__kernel
void pdtKernelStg2(int numPolys, __global char *validFlag, __global mp_int *polDiscArray, int p1, int p2)
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;


  int numP, pSet[2] = {p1, p2};
  numP = (p1==p2) ? 1 : 2;


  // Extract polynomial discriminant for this thread
  mp_int polDisc;
  //mp_copy(&(polDiscArray[index]), &polDisc);
  for (int n = 0; n < MP_PREC; n++)  polDisc.dp[n] = polDiscArray[index].dp[n];
  polDisc.used = polDiscArray[index].used;
  polDisc.sign = polDiscArray[index].sign;


  // Initialize local variables
  mp_int q, Mod;
  mp_zero(&q);
  mp_zero(&Mod);


  // Divide out all factors of p for each prime in pSet
  for(int k=0; k<numP; k++)  {
    int thisP = pSet[k];
    if(thisP==2) {
      // We treat the p=2 case special.  For two reasons, one it can be handled 
      // much more efficiently, and two there are usually many factors of 2.
      for(;;) {  // We remove 10 powers of 2 at a time
        mp_mod_2d( &polDisc, 10, &Mod );  // Set Mod = polDisc%1024
        if( !IS_ZERO(&Mod) ) break;  // Exit once there are no more factors of 1024
        mp_div_2d( &polDisc, 10, &polDisc, NULL ); // Set polDisc = polDisc/1024
        }
      // What remains has at most 9 powers of 2.
      // We remove the rest 1 at a time
      for(;;) {
        mp_mod_2d( &polDisc, 1, &Mod );  // Set Mod = polDisc%2
        if( !IS_ZERO(&Mod) ) break;  // Exit once there are no more factors of 2
        mp_div_2d( &polDisc, 1, &polDisc, NULL ); // Set polDisc = polDisc/2
        }
      }
    else if(thisP==5) {
      // We handle 5 separately since polDisc can have many factors of 5.
      mp_digit rem;
      for(;;) {  // We remove 8 powers of 5 at a time
        mp_div_d( &polDisc, 390625, &q, &rem );  // polDisc = q*5^8 + rem
        if( rem!=0 ) break;  // Exit once there are no more factors of 5^8
        mp_copy( &q, &polDisc );  // Otherwise, since the remainder is zero, set polDisc = q
        }
      // What remains has at most 7 powers of 5.
      // We remove them 1 at a time
      for(;;) {
        mp_div_d( &polDisc, 5, &q, &rem );  // polDisc = q*5 + rem
        if( rem!=0 ) break;  // Exit once there are no more factors of 5
        mp_copy( &q, &polDisc );  // Otherwise, since the remainder is zero, set polDisc = q
        }
      }
    else {
      // Remove the other primes, 1 power at a time.
      mp_digit rem;
      for(;;) {
        mp_div_d( &polDisc, thisP, &q, &rem );  // polDisc = q*p + rem
        if( rem!=0 ) break;  // Exit once there are no more factors of thisP
        mp_copy( &q, &polDisc );  // Otherwise, since the remainder is zero, set polDisc = q
        }
      }

    } // End of loop on k

  // Put modified discriminant back into device memory
  //mp_copy(&polDisc, &(polDiscArray[index]));
  for (int n = 0; n < MP_PREC; n++)  polDiscArray[index].dp[n] = polDisc.dp[n];
  polDiscArray[index].used = polDisc.used;
  polDiscArray[index].sign = polDisc.sign;

}  // End of pdtKernelStg2
*/




// OpenCL kernel function to divide out all factors of 2 from the polynomial discriminant.
__kernel
void pdtKernelDiv2(int numPolys, __global char *validFlag, __global mp_int *polDiscArray )
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;

  // Extract polynomial discriminant for this thread
  mp_int polDisc;
  mp_copy_g2p( &(polDiscArray[index]), &polDisc );
  //polDisc.used = polDiscArray[index].used;
  //polDisc.sign = polDiscArray[index].sign;
  //for (int n = 0; n < polDisc.used; n++)  polDisc.dp[n] = polDiscArray[index].dp[n];


  mp_digit N = polDisc.dp[0];
  while(N==0) {
    mp_div_2d( &polDisc, DIGIT_BIT, &polDisc, NULL ); // Divide out one digit's worth of bits
    N = polDisc.dp[0];
    }
  mp_digit pow2 = N & (-N);   // Power of 2 dividing N

  // pow2 = 2^d.  We need the power d.
  int d = 0;
  if (DIGIT_BIT>32) {
    if( (pow2 & 0xFFFFFFFF)==0 ) { d  = 32; pow2 >>= 32; }
    }
  if( (pow2 & 0xFFFF)==0 )  { d += 16; pow2 >>= 16; }
  if( (pow2 & 0xFF)==0 )    { d +=  8; pow2 >>= 8;  }
  if( (pow2 & 0xF)==0 )     { d +=  4; pow2 >>= 4;  }
  if( (pow2 & 0x3)==0 )     { d +=  2; pow2 >>= 2;  }
  if( (pow2 & 0x1)==0 )     { d +=  1; pow2 >>= 1;  }
  mp_div_2d( &polDisc, d, &polDisc, NULL ); // Set polDisc = polDisc/2^d


  // Put modified discriminant back into global memory
  mp_copy_p2g( &polDisc, &(polDiscArray[index]) );
  //for (int n = 0; n < polDisc.used; n++)  polDiscArray[index].dp[n] = polDisc.dp[n];
  //polDiscArray[index].used = polDisc.used;
  //polDiscArray[index].sign = polDisc.sign;

  #ifdef DEBUG
    if(index==DBG_THREAD) {
      printf("After removing all factors of 2, polDisc = ");  mp_printf(polDisc); printf("\n");
      }
  #endif

}  // End of pdtKernelDiv2





// OpenCL kernel function to divide out all factors of 5 from the polynomial discriminant.
__kernel
void pdtKernelDiv5(int numPolys, __global char *validFlag, __global mp_int *polDiscArray )
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;

  // Extract polynomial discriminant for this thread
  mp_int polDisc;
  mp_copy_g2p( &(polDiscArray[index]), &polDisc );


  // Initialize local variables
  mp_digit rem;
  mp_int q;
  mp_zero(&q);


  for(;;) {  // We remove 8 powers of 5 at a time
    mp_div_d( &polDisc, 390625, &q, &rem );  // polDisc = q*5^8 + rem
    if( rem!=0 ) break;  // Exit once there are no more factors of 5^8
    mp_copy( &q, &polDisc );  // Otherwise, since the remainder is zero, set polDisc = q
    }

  // Divide out 5^4
  mp_div_d( &polDisc, 625, &q, &rem ); // polDisc = q*5^4 + rem
  if( rem==0 )  mp_copy( &q, &polDisc );

  // Divide out 5^2
  mp_div_d( &polDisc, 25, &q, &rem ); // polDisc = q*5^2 + rem
  if( rem==0 )  mp_copy( &q, &polDisc );

  // Divide out 5
  mp_div_d( &polDisc, 5, &q, &rem ); // polDisc = q*5 + rem
  if( rem==0 )  mp_copy( &q, &polDisc );


  // Put modified discriminant back into global memory
  mp_copy_p2g( &polDisc, &(polDiscArray[index]) );

  #ifdef DEBUG
    if(index==DBG_THREAD) {
      printf("After removing all factors of 5, polDisc = ");  mp_printf(polDisc); printf("\n");
      }
  #endif

}  // End of pdtKernelDiv5





// OpenCL kernel function to divide out all factors of P from the polynomial discriminant.
__kernel
void pdtKernelDivP(int numPolys, __global char *validFlag, __global mp_int *polDiscArray, int P )
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;

  // Extract polynomial discriminant for this thread
  mp_int polDisc;
  mp_copy_g2p( &(polDiscArray[index]), &polDisc );

  // Initialize local variables
  mp_digit rem;
  mp_int q;
  mp_zero(&q);

  for(;;) {
    mp_div_d( &polDisc, P, &q, &rem );  // polDisc = q*P + rem
    if( rem!=0 ) break;  // Exit once there are no more factors of P
    mp_copy( &q, &polDisc );  // Otherwise, since the remainder is zero, set polDisc = q
    }
 
  // Put modified discriminant back into global memory
  mp_copy_p2g( &polDisc, &(polDiscArray[index]) );

  #ifdef DEBUG
    if(index==DBG_THREAD) {
      printf("After removing all factors of %d, polDisc = ", P);  mp_printf(polDisc); printf("\n");
      }
  #endif

}  // End of pdtKernelDivP





// OpenCL kernel function to do the pol disc test (stage 3)
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
__kernel
void pdtKernelStg3(int numPolys, __global char *validFlag, __global mp_int *polDiscArray)
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  // Also return early if validFlag is already false, which can be set in stage 1.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;


  // Extract polynomial discriminant for this thread
  mp_int polDisc;
  mp_copy_g2p( &(polDiscArray[index]), &polDisc );


  // These are the residues Mod 64,63,65,11
  char resMod64[]={
    1,1,0,0,1,0,0,0,0,1, 0,0,0,0,0,0,1,1,0,0, 0,0,0,0,0,1,0,0,0,0,
    0,0,0,1,0,0,1,0,0,0, 0,1,0,0,0,0,0,0,0,1, 0,0,0,0,0,0,0,1,0,0, 0,0,0,0};
  char resMod63[]={
    1,1,0,0,1,0,0,1,0,1, 0,0,0,0,0,0,1,0,1,0, 0,0,1,0,0,1,0,0,1,0,
    0,0,0,0,0,0,1,1,0,0, 0,0,0,1,0,0,1,0,0,1, 0,0,0,0,0,0,0,0,1,0, 0,0,0};
  char resMod65[]={
    1,1,0,0,1,0,0,0,0,1, 1,0,0,0,1,0,1,0,0,0, 0,0,0,0,0,1,1,0,0,1,
    1,0,0,0,0,1,1,0,0,1, 1,0,0,0,0,0,0,0,0,1, 0,1,0,0,0,1,1,0,0,0, 0,1,0,0,1};
  char resMod11[]={1,1,0,1,1,1,0,0,0,1, 0};


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
