
/* This is supposed to give printf functionality on AMD */
/* But it doesn't work, and neither does printf by itself */
//#pragma OPENCL EXTENSION cl_amd_printf : enable

#define TRUE  1
#define FALSE 0


//#define DEBUG
#define DBG_THREAD 0


// WARNING: printf can have problems with some OpenCL implementations
// We only enable it for debug purposes.
// The PRINTF_ENABLED is used in gpuMultiPrec to turn on the printing functions.
#ifdef DEBUG
  #define PRINTF_ENABLED
#endif


#include "gpuMultiPrec.h"


// OpenCL kernel function to do the pol disc test
__kernel
void pdtKernel(int numPolys, __global int64_t *polys, __global char *validFlag, int p1, int p2)
{
  int index = get_global_id(0);

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;


  // We error on the side of caution and initialize validFlag to true.
  // This setting keeps the polynomial on the list for further testing.
  // We do this in case the kernel aborts early before properly setting the flag.
  validFlag[index] = TRUE;


  int numP, pSet[2] = {p1, p2};
  numP = (p1==p2) ? 1 : 2;


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


  // Multi-precision declarations
  mp_int g, h, mpA[11], mpB[10], R[11], BR, SB[10];
  mp_int q, gPow, hPow, scale, Mod;

  // Multi-precision initializations.
  // Note: Values used below only need to be zeroed out one time (we do that here).
  mp_set(&g, 1);
  mp_set(&h, 1);
  mp_set_vec_ll(mpA, A, 11);  // initialize mpA to A.
  mp_set_vec_ll(mpB, B, 10);  // initialize mpB to B.
  for(int k=0; k<11; k++)  mp_zero(&(R[k]));
  mp_zero(&BR);
  for(int k=0; k<10; k++)  mp_zero(&(SB[k]));
  //mp_zero(&q);  // This one is not needed at this point.
  mp_zero(&gPow);
  mp_zero(&hPow);
  mp_zero(&scale);
  mp_zero(&Mod);


#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("long versions:\n");
    printf("  A = %ld ", A[0]);
    for(int k=1; k<11; k++) printf("+ %ld x^%d ", A[k], k);
    printf("\n  B = %ld ", B[0]);
    for(int k=1; k<10; k++) printf("+ %ld x^%d ", B[k], k);
    printf("\nMulti-precision versions:");
    printf("\nmpA = ");  mp_print_poly(mpA, 10);
    printf("\nmpB = ");  mp_print_poly(mpB,  9);
    }
#endif


  //////////////////////////////////////////////////////////////////////////////
  // Steps 2/3: Pseudo Division and Reduction.
  //////////////////////////////////////////////////////////////////////////////

  int degB = 9;
  int degA = 10;
  while(degB>0) {
    int delta = degA - degB;

    ////////////////////////////////////////////////////////////////////////////
    // Pseudo Division.  This is Algorithm 3.1.2 on p.112 of Cohen's book.
    // This computes R such that B[degB]^(delta+1)*A = B*Q + R where degR < degB
    // Note, since we don't need Q, we don't compute it.

    // Initialize R to A.
    int degR = degA;
    mp_copy_vec(mpA, R, degA+1);

    int e = delta + 1;

    while(degR>=degB) {
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
        int retVal = mp_mul( &(R[degR]), &(mpB[k-degS]), &(SB[k]) );
        if ( retVal == MP_MEM )  return;  // ValidFlag was already set, so just return.
        }
      // Compute R = B[degB]*R - S*B
      // What follows is the mp equivalent of this:
      //      for(int k=0; k<degR; k++)  R[k] = B[degB]*R[k]-SB[k];
      for(int k=0; k<degR; k++) {
        int retVal = mp_mul( &(mpB[degB]), &(R[k]), &BR );
        if ( retVal == MP_MEM )  return;  // ValidFlag was already set, so just return.
        mp_sub( &BR, &(SB[k]), &(R[k]) );
        }

      // Determine the degree of the new R.
      int degRnew = 0;
      for(int k=degR-1; k>0; k--)  {
        if( !IS_ZERO(&(R[k])) ) { degRnew=k; break; }
        }
      degR = degRnew;

      --e;
      }

    // Compute q = B[degB]^e
    mp_set(&q, 1);
    for(int k=1; k<=e; k++)  {
      int retVal = mp_mul( &q, &(mpB[degB]), &q );   // Set q = q * B[degB]
      if ( retVal == MP_MEM )  return;  // ValidFlag was already set, so just return.
      }

    // Compute R = q*R.
    for(int k=0; k<=degR; k++)  {
      int retVal = mp_mul( &(R[k]), &q, &(R[k]) );  // R[k] = R[k] * q;
      if ( retVal == MP_MEM )  return;  // ValidFlag was already set, so just return.
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
      if ( retVal == MP_MEM )  return;  // ValidFlag was already set, so just return.
      }

    int retVal = mp_mul( &g, &hPow, &scale );  // scale = g*hPow
    if ( retVal == MP_MEM )  return;  // ValidFlag was already set, so just return.

    degB = degR;
    for(int k=0; k<=degR; k++)  {
      int retVal = mp_div( &(R[k]), &scale, &(mpB[k]), NULL ); // Set B[k] = R[k] / scale;
      if ( retVal == MP_MEM )  return;  // ValidFlag was already set, so just return.
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
        if ( retVal == MP_MEM )  return;  // ValidFlag was already set, so just return.
        }

      // Then compute h^(delta-1):
      mp_copy(&h, &hPow);  // Init hPow = h
      for(int k=1; k<=delta-2; k++)  {
        int retVal = mp_mul( &hPow, &h, &hPow );  // Set hPow = hPow*h
        if ( retVal == MP_MEM )  return;  // ValidFlag was already set, so just return.
        }

      // Finally, divide them:
      int retVal = mp_div( &gPow, &hPow, &h, NULL );  // Set h = gPow / hPow;
      if ( retVal == MP_MEM )  return;  // ValidFlag was already set, so just return.

      }

    }  // End while loop on deg(B)


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
  // In this case, the polynomial is invalid.  Set the flag and return.
  if( IS_ZERO(mpB) ) {  // mpB is the address of mpB[0]
    validFlag[index] = FALSE;
    return;
    }

  mp_int *polDisc;
  if(degA%2==0)  polDisc = &h;         // Set polDisc = h
  else           polDisc = &(mpB[0]);  // Set polDisc = B[0]


#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("\npolDisc = ");  mp_printf(*polDisc);
    }
#endif


  // Make sure the discriminant is positive
  polDisc->sign = MP_ZPOS;


  // Divide out all factors of p for each prime in pSet
  for(int k=0; k<numP; k++)  {
    int thisP = pSet[k];
    if(thisP==2) {
      // We treat the p=2 case special.  For two reasons, one it can be handled 
      // much more efficiently, and two there are usually many factors of 2.
      for(;;) {  // We remove 10 powers of 2 at a time
        mp_mod_2d( polDisc, 10, &Mod );  // Set Mod = polDisc%1024
        if( !IS_ZERO(&Mod) ) break;  // Exit once there are no more factors of 1024
        mp_div_2d( polDisc, 10, polDisc, NULL ); // Set polDisc = polDisc/1024
        }
      // What remains has at most 9 powers of 2.
      // We remove the rest 1 at a time
      for(;;) {
        mp_mod_2d( polDisc, 1, &Mod );  // Set Mod = polDisc%2
        if( !IS_ZERO(&Mod) ) break;  // Exit once there are no more factors of 2
        mp_div_2d( polDisc, 1, polDisc, NULL ); // Set polDisc = polDisc/2
        }
      }
    else if(thisP==5) {
      // We handle 5 separately since polDisc can have many factors of 5.
      mp_digit rem;
      for(;;) {  // We remove 8 powers of 5 at a time
        mp_div_d( polDisc, 390625, &q, &rem );  // polDisc = q*5^8 + rem
        if( rem!=0 ) break;  // Exit once there are no more factors of 5^8
        mp_copy( &q, polDisc );  // Otherwise, since the remainder is zero, set polDisc = q
        }
      // What remains has at most 7 powers of 5.
      // We remove them 1 at a time
      for(;;) {
        mp_div_d( polDisc, 5, &q, &rem );  // polDisc = q*5 + rem
        if( rem!=0 ) break;  // Exit once there are no more factors of 5
        mp_copy( &q, polDisc );  // Otherwise, since the remainder is zero, set polDisc = q
        }
      }
    else {
      // Remove the other primes, 1 power at a time.
      mp_digit rem;
      for(;;) {
        mp_div_d( polDisc, thisP, &q, &rem );  // polDisc = q*p + rem
        if( rem!=0 ) break;  // Exit once there are no more factors of thisP
        mp_copy( &q, polDisc );  // Otherwise, since the remainder is zero, set polDisc = q
        }
      }

    } // End of loop on k


  // We use old variables to save on initialization ops.
  // Note, we cannot use h, since that may be the same as polDisc.
  mp_int *sqrtDisc   = &g;
  mp_int *sqrtDiscSq = &q;


  // Check if what remains of the discriminant is a perfect square.
  // NOTE: The sqrt algorithm needs a few more digits, so we need to check for overflow.
  int retVal = mp_sqrt( polDisc, sqrtDisc );   // Compute the sqrt of polDisc
  if ( retVal == MP_MEM )  return;  // ValidFlag was already set, so just return.
  mp_sqr( sqrtDisc, sqrtDiscSq ); // Square the sqrt.  This should never overflow.

#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("\nReduced polDisc = ");  mp_printf(*polDisc);
    printf("\nsqrtDisc   = ");  mp_printf(*sqrtDisc);
    printf("\nsqrtDisc^2 = ");  mp_printf(*sqrtDiscSq);
    }
#endif

  if ( mp_cmp_mag( sqrtDiscSq, polDisc ) == MP_EQ ) {
    validFlag[index] = TRUE;
    }
  else {
    validFlag[index] = FALSE;
    }

}
