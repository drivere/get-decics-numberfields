// System includes
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <math.h>
#include <gmp.h>


// Use this to turn on DEBUG mode
//#define DEBUG


#define FAIL  1
#define TRUE  1
#define FALSE 0


void gmp_print_poly(mpz_t*, int);



extern "C" int
polDiscTest_cpu(long long *polBuf, int numPolys, char *polGoodFlag, int numP, int *pSet)
  {

  /* Multi-precision declarations */
  mpz_t g, h, mpA[11], mpB[10], R[11], BR, SB[10];
  mpz_t q, gPow, hPow, scale, polDisc, rem, sqrtDisc;


  /* Multi-precision initializations. */
  /* We do this one time outside the for loop to minimize the number of memory allocations */
  mpz_inits(g, h, BR, NULL);
  for(int k=0; k<11; ++k)  mpz_init(mpA[k]);
  for(int k=0; k<10; ++k)  mpz_init(mpB[k]);
  for(int k=0; k<11; ++k)  mpz_init(R[k]);
  for(int k=0; k<10; ++k)  mpz_init(SB[k]);
  mpz_inits(q, gPow, hPow, scale, polDisc, rem, sqrtDisc, NULL);


  /* Loop over every polynomial in the buffer, applying the discriminant test to each. */
  for(int pIdx=0; pIdx<numPolys; ++pIdx)
    {

    // Extract the polynomial under test
    // It is assummed the input coefficients are in decreasing order of degree.
    // (i.e. A[0]*x^10 + A[1]*x^9 + ... + A[9]*x + A[10])
    // BUT FOR IMPLEMENTATION REASONS, WE REVERSE THE ORDER.
    int64_t A[11];
    for(int col = 0; col < 11; col++)  A[10-col] = polBuf[pIdx*11+col];

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


    // Set g=h=1, mpA[]=A[], and mpB[]=B[].
    mpz_set_ui(g, 1);
    mpz_set_ui(h, 1);
    for(int k=0; k<11; ++k)  mpz_set_si(mpA[k], A[k]);
    for(int k=0; k<10; ++k)  mpz_set_si(mpB[k], B[k]);


#ifdef DEBUG
    printf("long versions:\n");
    printf("  A = %ld ", A[0]);
    for(int k=1; k<11; k++) printf("+ %ld x^%d ", A[k], k);
    printf("\n  B = %ld ", B[0]);
    for(int k=1; k<10; k++) printf("+ %ld x^%d ", B[k], k);
    printf("\nMulti-precision versions:");
    printf("\nmpA = ");  gmp_print_poly(mpA, 10);
    printf("\nmpB = ");  gmp_print_poly(mpB,  9);
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
      for(int k=0; k<degA+1; k++)  mpz_set(R[k], mpA[k]);

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
        for(int k=0; k<=degS-1; k++)  mpz_set_ui(SB[k], 0);
        for(int k=degS; k<degR; k++)  mpz_mul( SB[k], R[degR], mpB[k-degS] );

        // Compute R = B[degB]*R - S*B
        // What follows is the mp equivalent of this:
        //      for(int k=0; k<degR; k++)  R[k] = B[degB]*R[k]-SB[k];
        for(int k=0; k<degR; k++) {
          mpz_mul( BR, mpB[degB], R[k] );
          mpz_sub( R[k], BR, SB[k] );
          }

        // Determine the degree of the new R.
        int degRnew = 0;
        for(int k=degR-1; k>0; k--)  {
          if( mpz_sgn(R[k])!=0 ) { degRnew=k; break; }
          }
        degR = degRnew;

        --e;
        }

      // Compute q = B[degB]^e
      mpz_set_ui(q, 1);
      for(int k=1; k<=e; k++)  mpz_mul( q, mpB[degB], q );  // Set q = q * B[degB]

      // Compute R = q*R.
      for(int k=0; k<=degR; k++)  mpz_mul( R[k], q, R[k] );  // R[k] = R[k] * q;

      // End of Pseudo Division
      ////////////////////////////////////////////////////////////////////////////


      // Set A = B
      degA = degB;
      for(int k=0; k<degB+1; k++)  mpz_set(mpA[k], mpB[k]);

      // Set B = R/(g*h^delta)
      mpz_set(hPow, h);  // Set hPow = h
      for(int k=1; k<=delta-1; k++)  mpz_mul( hPow, h, hPow );  // Set hPow = hPow*h
      mpz_mul( scale, g, hPow );  // scale = g*hPow
      degB = degR;
      for(int k=0; k<=degR; k++)  mpz_divexact( mpB[k], R[k], scale ); // Set B[k] = R[k] / scale;

      // Get new g for next iteration.  g = leading coeff of A
      mpz_set(g, mpA[degA]);

      // Compute the new h = g^delta * h^(1-delta)
      // Note: degA > degB so delta is always > 0.
      if(delta==1) {
        mpz_set(h, g);
        }
      else {
        // The power on h will be negative, so compute h = g^delta / h^(delta-1)

        // First compute g^delta:
        mpz_set(gPow, g);  // Init gPow = g
        for(int k=1; k<=delta-1; k++)  mpz_mul( gPow, g, gPow );  // Set gPow = gPow*g

        // Then compute h^(delta-1):
        mpz_set(hPow, h);  // Init hPow = h
        for(int k=1; k<=delta-2; k++)  mpz_mul( hPow, h, hPow );  // Set hPow = hPow*h

        // Finally, divide them:
        mpz_divexact( h, gPow, hPow );  // Set h = gPow / hPow;

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
    // In this case, the polynomial is invalid.  Set the flag and skip to next polynomial.
    if( mpz_sgn(mpB[0])==0 ) {
      polGoodFlag[pIdx] = FALSE;
      continue;
      }

    if(degA%2==0)  mpz_set( polDisc,   h    );  // Set polDisc = h
    else           mpz_set( polDisc, mpB[0] );  // Set polDisc = B[0]


#ifdef DEBUG
    gmp_printf("\npolDisc = %Zd\n", polDisc);
#endif


    // Make sure the discriminant is positive
    mpz_abs(polDisc,polDisc);


    // Divide out all factors of p for each prime in pSet
    for(int k=0; k<numP; k++)  {
      int thisP = pSet[k];
      if(thisP==2) {
        // We treat the p=2 case special.  For two reasons, one it can be handled 
        // much more efficiently, and two there are usually many factors of 2.
        for(;;) {  // We remove 10 powers of 2 at a time
          mpz_tdiv_r_2exp( rem, polDisc, 10 );  // Set rem = polDisc%1024
          if( mpz_sgn(rem)!=0 ) break;  // Exit once there are no more factors of 1024
          mpz_tdiv_q_2exp( polDisc, polDisc, 10 ); // Set polDisc = polDisc/1024
          }
        // What remains has at most 9 powers of 2.
        // We remove the rest 1 at a time
        for(;;) {
          mpz_tdiv_r_2exp( rem, polDisc, 1 );  // Set rem = polDisc%2
          if( mpz_sgn(rem)!=0 ) break;  // Exit once there are no more factors of 2
          mpz_tdiv_q_2exp( polDisc, polDisc, 1 ); // Set polDisc = polDisc/2
          }
        }
      else if(thisP==5) {
        // We handle 5 separately since polDisc can have many factors of 5.
        for(;;) {  // We remove 8 powers of 5 at a time
          mpz_tdiv_qr_ui (q, rem, polDisc, 390625 );  // polDisc = q*5^8 + rem
          if( mpz_sgn(rem)!=0 ) break;  // Exit once there are no more factors of 5^8
          mpz_set(polDisc, q);  // Otherwise, since the remainder is zero, set polDisc = q
          }
        // What remains has at most 7 powers of 5.
        // We remove them 1 at a time
        for(;;) {
          mpz_tdiv_qr_ui (q, rem, polDisc, 5 );  // polDisc = q*5 + rem
          if( mpz_sgn(rem)!=0 ) break;  // Exit once there are no more factors of 5
          mpz_set(polDisc, q);  // Otherwise, since the remainder is zero, set polDisc = q
          }
        }
      else {
        // Remove the other primes, 1 power at a time.
        for(;;) {
          mpz_tdiv_qr_ui (q, rem, polDisc, thisP );  // polDisc = q*p + rem
          if( mpz_sgn(rem)!=0 ) break;  // Exit once there are no more factors of thisP
          mpz_set(polDisc, q);  // Otherwise, since the remainder is zero, set polDisc = q
          }
        }

      } // End of loop on k


    // Check if what remains of the discriminant is a perfect square.

    // This is supposed to the faster but is not??
    //if( mpz_perfect_square_p(polDisc) )  polGoodFlag[pIdx] = TRUE;
    //else                                 polGoodFlag[pIdx] = FALSE;

    mpz_sqrtrem(sqrtDisc, rem, polDisc);  // sqrtDisc = sqrt(polDisc) rounded down, rem = polDisc - sqrtDisc^2
    if( mpz_sgn(rem)==0 ) polGoodFlag[pIdx] = TRUE;
    else                  polGoodFlag[pIdx] = FALSE;

#ifdef DEBUG
    gmp_printf("Reduced polDisc = %Zd\n", polDisc);
    gmp_printf("sqrtDisc = %Zd\n", sqrtDisc);
#endif

    }  // End of loop over polynomials


  /* Release all memory resources */
  mpz_clears(g, h, BR, NULL);
  for(int k=0; k<11; ++k)  mpz_clear(mpA[k]);
  for(int k=0; k<10; ++k)  mpz_clear(mpB[k]);
  for(int k=0; k<11; ++k)  mpz_clear(R[k]);
  for(int k=0; k<10; ++k)  mpz_clear(SB[k]);
  mpz_clears(q, gPow, hPow, scale, polDisc, rem, sqrtDisc, NULL);


  return 0;

}



/* Debug helper function to print out a multi-precision polynomial */
void gmp_print_poly(mpz_t *poly, int deg)
{
   gmp_printf("%Zd", poly[0]);
   for(int k=1; k<=deg; k++) {
      printf(" + ");
      gmp_printf("%Zd", poly[k]);
      printf(" x^%d", k);
   }
}
