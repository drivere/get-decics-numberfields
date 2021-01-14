
// System includes
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <math.h>
#include <gmp.h>
#include <string.h>


// Use this to turn on DEBUG mode
//#define DEBUG

// Use this to turn on the special content test.
// Used in conjunction with COEFF_SIZE_TEST - not to be used in production code.
//#define CONTENT_TEST

// This is for testing how large the polynomial coefficients get with each iteration.
// It is used to tell us how best to set the hard coded multi-precision size.
// It also tells us how many iterations we can go before needing multi-precision.
// It is best to turn off "UNWRAP_TWO_ITERS" when using this
// Also helps to run with command line option numBlocks set to a large value since
// the data array is dumped out with each pass.  For example:
//    ./GetDecics --numBlocks 150000000 > output  (this will handle 150mil polys)
//#define COEFF_SIZE_TEST

// This will unwrap the first two iterations before going to multi-precision.
// This yields the fastest code.  But only works on 64 bit machines.
#define UNWRAP_TWO_ITERS


#define FAIL  1
#define TRUE  1
#define FALSE 0


#ifdef DEBUG
  void debugPrintPolyInfo(int, mpz_t*, int, mpz_t*, int, mpz_t, mpz_t);
  void debugPrintPolyInfoLong(int, int64_t*, int, int64_t*, int, int64_t, int64_t);
  void gmp_print_poly(mpz_t*, int);
#endif

#ifdef CONTENT_TEST
  inline uint64_t getPolyContentAt2(mpz_t*, int, uint64_t);
  inline int      getPolyContentAt5(mpz_t*, mpz_t, mpz_t, int, int);
#endif

#ifdef MINGW
  inline void mpz_set_int64(mpz_t, int64_t);
#endif




extern "C" int
polDiscTest_cpu(long long *polBuf, int numPolys, char *polGoodFlag, char *polyMask, int numP, int *pSet)
  {

  /* Multi-precision declarations */
  mpz_t g, h, mpA[10], mpB[9], mpR[10], BR, SB[9];
  mpz_t q, gPow, hPow, scale, polDisc, rem;

  /* Multi-precision initializations. */
  /* We do this one time outside the for loop to minimize the number of memory allocations */
  mpz_inits(g, h, BR, NULL);
  for(int k=0; k<10; ++k)  mpz_init(mpA[k]);
  for(int k=0; k<9;  ++k)  mpz_init(mpB[k]);
  for(int k=0; k<10; ++k)  mpz_init(mpR[k]);
  for(int k=0; k<9;  ++k)  mpz_init(SB[k]);
  mpz_inits(q, gPow, hPow, scale, polDisc, rem, NULL);


#ifdef COEFF_SIZE_TEST
  // maxBits[i][j] = max bits required when starting an iteration with degA=i and degB=j.
  int maxBits[11][10];
  int maxBitsGH[11][10];  // A separate measurement for g and h.
  long freq[11][10];
  for(int i=0; i<=10; ++i) {
    for(int j=0; j<=9; ++j) { maxBits[i][j]=0; maxBitsGH[i][j]=0; freq[i][j]=0; }
    }
  mpz_t absB, absR, absGH;
  mpz_inits(absB, absR, absGH, NULL);
#endif


  /* Loop over every polynomial in the buffer, applying the discriminant test to each. */
  for(int pIdx=0; pIdx<numPolys; ++pIdx)
    {

    // Only consider those polynomials whose mask is non-zero.
    if (polyMask && polyMask[pIdx]==0)  continue;

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


#ifdef DEBUG
    int iter = 0;
    printf("\n\nInitialization Step:\n");
    printf("  A = %ld ", A[0]);
    for(int k=1; k<11; k++) printf("+ %ld x^%d ", A[k], k);
    printf("\n  B = %ld ", B[0]);
    for(int k=1; k<10; k++) printf("+ %ld x^%d ", B[k], k);
#endif


    ////////////////////////////////////////////////////////////////////////////////
    /* Do the first iteration of the sub-resultant algorithm.  This allows us to  */
    /* stay with longs a little longer before transitioning to multi-precision.   */

    // This computes: R = d*A-S*B in Algorithm 3.1.2
    int64_t R[10];
    R[0] = B[9]*A[0];
    for(int k=1;k<=9;++k)  R[k] = B[9]*A[k] - B[k-1];
    for(int k=0;k<=8;++k)  R[k] = B[9]*R[k] - R[9]*B[k];

    // Determine the degree of R (it must be less than or equal to 8)
    int degR = 0;
    for(int k=8; k>0; k--)  {
      if( R[k]!=0 ) { degR=k; break; }
      }

    /*  This completes the first iteration of sub-resultant.                      */
    ////////////////////////////////////////////////////////////////////////////////


    #ifdef DEBUG
      ++iter;
      // Here A is B and B is R.
      debugPrintPolyInfoLong(iter, B, 9, R, degR, B[9], B[9]);
    #endif


#ifdef COEFF_SIZE_TEST
    // The maximum required bits are determined by B and R. (poly A is always smaller)
    // First loop over coeffs of B.
    ++freq[10][9];
    for(int k = 0; k<10; k++)  {
      int64_t numBits = ceil( log2( llabs(B[k])+1.0 ) );
      if(maxBits[10][9]<numBits) maxBits[10][9]=numBits;
      }
    // Then loop over coeffs of R.
    for(int k = 0; k<=degR; k++)  {
      int64_t numBits = ceil( log2( labs(R[k])+1.0 ) );
      if(maxBits[10][9]<numBits) maxBits[10][9]=numBits;
      }
    // Measure max bits for g and h. Note that here g=h=B[9].
    int64_t numBits = ceil( log2( labs(B[9])+1.0 ) );
    if(maxBitsGH[10][9]<numBits) maxBitsGH[10][9]=numBits;
#endif


#ifdef UNWRAP_TWO_ITERS
    ///////////////////////////////////////////////////////////////////////
    /* Do the 2nd iteration of the sub-resultant algorithm using longs.  */
    /* This will depend on the degree of R.                              */

    int degA, degB;

    if(degR==8) {
      degA = degR; // This is the final value for degA.  To save ops, we set it now.
      // Set A=B and B=R.
      for(int k=0; k<10; ++k)     A[k]=B[k];
      for(int k=0; k<=degR; ++k)  B[k]=R[k];

      R[0] = B[8]*A[0];
      for(int k=1;k<=8;++k)  R[k] = B[8]*A[k] - A[9]*B[k-1];
      for(int k=0;k<=7;++k)  R[k] = B[8]*R[k] - R[8]*B[k];
      // Determine the degree of R (it must be less than or equal to 7)
      degR = 0;
      for(int k=7; k>0; k--)  {
        if( R[k]!=0 ) { degR=k; break; }
        }
      int64_t Rscale = B[9]*B[9];  // scale factor = g*h
      for(int k=0;k<=degR;++k)  R[k] = R[k]/Rscale;
      // Setup the next iteration: A=B, B=R, g=l(A), h=g.
      degB = degR;

      #ifndef MINGW
        for(int k=0; k<=degA; ++k)  mpz_set_si(mpA[k], B[k]);
        for(int k=0; k<=degB; ++k)  mpz_set_si(mpB[k], R[k]); // R was already scaled above
        mpz_set_si(g, B[8]);  // g = leading coeff of A = B[8]
        mpz_set_si(h, B[8]);  // h = g
      #else
        for(int k=0; k<=degA; ++k)  mpz_set_int64(mpA[k], B[k]);
        for(int k=0; k<=degB; ++k)  mpz_set_int64(mpB[k], R[k]); // R was already scaled above
        mpz_set_int64(g, B[8]);  // g = leading coeff of A = B[8]
        mpz_set_int64(h, B[8]);  // h = g
      #endif

      #ifdef DEBUG
        ++iter;  debugPrintPolyInfo(iter,mpA,degA,mpB,degB,g,h);
      #endif
      }
    else if(degR==7) {
      degA = degR; // This is the final value for degA.  To save ops, we set it now.
      // Set A=B and B=R.
      for(int k=0; k<10; ++k)     A[k]=B[k];
      for(int k=0; k<=degR; ++k)  B[k]=R[k];

      R[0] = B[7]*A[0];  R[1] = B[7]*A[1];
      for(int k=2;k<=8;++k)  R[k] = B[7]*A[k] - A[9]*B[k-2];
      R[0] = B[7]*R[0];
      for(int k=1;k<=7;++k)  R[k] = B[7]*R[k] - R[8]*B[k-1];
      for(int k=0;k<=6;++k)  R[k] = B[7]*R[k] - R[7]*B[k];
      // Determine the degree of R (it must be less than or equal to 6)
      degR = 0;
      for(int k=6; k>0; k--)  {
        if( R[k]!=0 ) { degR=k; break; }
        }
      int64_t Rscale = B[9]*B[9]*B[9];  // scale factor = gh^2
      for(int k=0;k<=degR;++k) R[k] = R[k]/Rscale;
      // Setup the next iteration: A=B, B=R, g=l(A), h=g^2/h (=h^(1-delta)g^delta).
      degB = degR;

      #ifndef MINGW
        for(int k=0; k<=degA; ++k)  mpz_set_si(mpA[k], B[k]);
        for(int k=0; k<=degB; ++k)  mpz_set_si(mpB[k], R[k]); // R was already scaled above
        mpz_set_si(g, B[7]);  // g = leading coeff of A = B[7]
        mpz_set_si(h, (B[7]*B[7])/B[9] );  // h = (g^2)/h
      #else
        for(int k=0; k<=degA; ++k)  mpz_set_int64(mpA[k], B[k]);
        for(int k=0; k<=degB; ++k)  mpz_set_int64(mpB[k], R[k]); // R was already scaled above
        mpz_set_int64(g, B[7]);  // g = leading coeff of A = B[7]
        mpz_set_int64(h, (B[7]*B[7])/B[9] );  // h = (g^2)/h
      #endif

      #ifdef DEBUG
        ++iter;  debugPrintPolyInfo(iter,mpA,degA,mpB,degB,g,h);
      #endif
      }
    else { // degR<7
      // For a small number of cases, when degR<7, the result would exceed a long.
      // So we dont unwrap.  Instead, we setup for multi-precision.
      degA = 9;
      degB = degR;

      #ifndef MINGW
        for(int k=0; k<10; ++k)  mpz_set_si(mpA[k], B[k]);
        for(int k=0; k<=degR; ++k)  mpz_set_si(mpB[k], R[k]);
        mpz_set_si(g, B[9]);
        mpz_set_si(h, B[9]);
      #else
        for(int k=0; k<10; ++k)  mpz_set_int64(mpA[k], B[k]);
        for(int k=0; k<=degR; ++k)  mpz_set_int64(mpB[k], R[k]);
        mpz_set_int64(g, B[9]);
        mpz_set_int64(h, B[9]);
      #endif
      }

    /*  End of 2nd iteration of sub-resultant (with longs).       */
    ////////////////////////////////////////////////////////////////
#else
    // Setup the 2nd iteration to use multi-precision
    int degA = 9;
    int degB = degR;

    #ifndef MINGW
      for(int k=0; k<10; ++k)  mpz_set_si(mpA[k], B[k]);
      for(int k=0; k<=degR; ++k)  mpz_set_si(mpB[k], R[k]);
      mpz_set_si(g, B[9]);
      mpz_set_si(h, B[9]);
    #else
      for(int k=0; k<10; ++k)  mpz_set_int64(mpA[k], B[k]);
      for(int k=0; k<=degR; ++k)  mpz_set_int64(mpB[k], R[k]);
      mpz_set_int64(g, B[9]);
      mpz_set_int64(h, B[9]);
    #endif
#endif


    //////////////////////////////////////////////////////////////////////////////
    // Steps 2/3: Pseudo Division and Reduction.
    //////////////////////////////////////////////////////////////////////////////

    while(degB>0) {
      int delta = degA - degB;


      #ifdef CONTENT_TEST
        int cont25 = 1;
        if(degB==7 || (degB==6 && degA==9) ) {
          uint64_t cont2 = getPolyContentAt2(mpB, degB, 4194304);

          int64_t cont5 = 25;
          for(int k = degB; k >= 0; k--) {
            if( mpz_fdiv_ui(mpB[k], 25) != 0 ) { cont5 = 5; break;}
            }
          if(cont5==5) {
            for(int k = degB; k >= 0; k--) {
              if( mpz_fdiv_ui(mpB[k], 5) != 0 ) { cont5 = 1; break;}
              }
            }

          // Divide out the content from each coefficient
          cont25 = cont2*cont5;
          for(int k = 0; k <= degB; k++) {
            mpz_divexact_ui(mpB[k], mpB[k], cont25);  // Set mpB[k] = mpB[k]/cont25
            }
          }
      #endif


      ////////////////////////////////////////////////////////////////////////////
      // Pseudo Division.  This is Algorithm 3.1.2 on p.112 of Cohen's book.
      // This computes R such that B[degB]^(delta+1)*A = B*Q + R where degR < degB
      // Note, since we don't need Q, we don't compute it.

      // Initialize R to A.
      int degR = degA;
      for(int k=0; k<degA+1; k++)  mpz_set(mpR[k], mpA[k]);

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
        for(int k=degS; k<degR; k++)  mpz_mul( SB[k], mpR[degR], mpB[k-degS] );

        // Compute R = B[degB]*R - S*B
        // What follows is the mp equivalent of this:
        //      for(int k=0; k<degR; k++)  R[k] = B[degB]*R[k]-SB[k];
        for(int k=0; k<degR; k++) {
          mpz_mul( BR, mpB[degB], mpR[k] );
          mpz_sub( mpR[k], BR, SB[k] );
          }

        // Determine the degree of the new R.
        int degRnew = 0;
        for(int k=degR-1; k>0; k--)  {
          if( mpz_sgn(mpR[k])!=0 ) { degRnew=k; break; }
          }
        degR = degRnew;

        --e;
        }

      // Compute q = B[degB]^e
      mpz_set_ui(q, 1);
      for(int k=1; k<=e; k++)  mpz_mul( q, mpB[degB], q );  // Set q = q * B[degB]

      // Compute R = q*R.
      for(int k=0; k<=degR; k++)  mpz_mul( mpR[k], q, mpR[k] );  // R[k] = R[k] * q;

      // End of Pseudo Division
      ////////////////////////////////////////////////////////////////////////////


      #ifdef COEFF_SIZE_TEST
        ++freq[degA][degB];
        for(int k = 0; k <= degB; k++)  {
          int64_t numBits;
          mpz_abs(absB,mpB[k]);    // Get absolute value of B[k]
          mpz_add_ui(absB,absB,1); // Add 1 to make sure it's non-zero.
          mpz_get_d_2exp(&numBits, absB );
          if(maxBits[degA][degB]<numBits) maxBits[degA][degB]=numBits;
          }
        for(int k = 0; k <= degR; k++)  {
          int64_t numBits;
          mpz_abs(absR,mpR[k]);    // Get absolute value of R[k]
          mpz_add_ui(absR,absR,1); // Add 1 to make sure it's non-zero.
          mpz_get_d_2exp(&numBits, absR );
          if(maxBits[degA][degB]<numBits) maxBits[degA][degB]=numBits;
          }
        // Save old degrees of A and B, needed for indexing maxBitsGH down below.
        int degAold = degA;
        int degBold = degB;
      #endif


      #ifdef CONTENT_TEST
        if(degB==7 || (degB==6 && degA==9) ) {
          // Put B and R back to what they should be.
          for(int k = 0; k <= degB; k++) {
            mpz_mul_ui(mpB[k], mpB[k], cont25);  // Set mpB[k] = mpB[k]*cont25
            }
          // Number of factors is 1+(degA-degB)
          uint64_t RmultFactor = cont25*cont25;  // This is the factor when degB=7, degA=8
          if(degA==9) RmultFactor*=cont25;   // When degA=9, use one more factor.
          if(degB==6) RmultFactor*=cont25;   // When degB=6, use another factor.
          for(int k = 0; k <= degR; k++) {
            mpz_mul_ui(mpR[k], mpR[k], RmultFactor);
            }
          }
      #endif


      // Set A = B
      degA = degB;
      for(int k=0; k<degB+1; k++)  mpz_set(mpA[k], mpB[k]);

      // Set B = R/(g*h^delta)
      mpz_set(hPow, h);  // Set hPow = h
      for(int k=1; k<=delta-1; k++)  mpz_mul( hPow, h, hPow );  // Set hPow = hPow*h
      mpz_mul( scale, g, hPow );  // scale = g*hPow
      degB = degR;
      for(int k=0; k<=degR; k++)  mpz_divexact( mpB[k], mpR[k], scale ); // Set B[k] = R[k] / scale;



      #ifdef CONTENT_TEST

        ////////////////////////////////////////////////////////////////////////////
        // This test removes factors of 2 and 5 from gcd of coeffs of A and B.
        // This trick only works when delta=1.
        // This actually slowed things down, so is not worth using.

        if(0) {
        //if(delta==1) {
          // First get the content at 2 for the polynomial B.
          int64_t cont2 = getPolyContentAt2(mpB, degB, 4194304);

          // Then get the content at 2 for the polynomial A.
          // If content is already 1, then no reason to do polynomial A.
          if(cont2>1)  cont2 = getPolyContentAt2(mpA, degA, cont2);

          // Now get the content at 5 for the polynomial B.
          //int pow5 = getPolyContentAt5(mpB, q, rem, degB, 16);

          // Now get the content at 5 for the polynomial A.
          // If the power of 5 is 0, then we are done.
          //if(pow5>0)  pow5 = getPolyContentAt5(mpA, q, rem, degA, pow5);
          //int64_t cont5 = (int64_t)(pow(5,pow5)+.5);
          //printf("\n  cont5 = %ld\n", cont5);

          int64_t contAB = cont2; // * cont5;
          //printf("\n  contAB = %ld\n", contAB);

          // Divide out the content from each coefficient
          for(int k = 0; k <= degB; k++) {
            mpz_divexact_ui(mpB[k], mpB[k], contAB);  // Set mpB[k] = mpB[k]/contAB
            }
          for(int k = 0; k <= degA; k++) {
            mpz_divexact_ui(mpA[k], mpA[k], contAB);  // Set mpA[k] = mpA[k]/contAB
            }

          } // End of if(delta==1)
        ////////////////////////////////////////////////////////////////////////////

      #endif



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

      #ifdef COEFF_SIZE_TEST
        // Measure max bits for g:
        int64_t numBits;
        mpz_abs(absGH,g);    // Get absolute value of g
        mpz_add_ui(absGH,absGH,1); // Add 1 to make sure it's non-zero.
        mpz_get_d_2exp(&numBits, absGH);
        if(maxBitsGH[degAold][degBold]<numBits) maxBitsGH[degAold][degBold]=numBits;
        // Measure max bits for h:
        mpz_abs(absGH,h);    // Get absolute value of h
        mpz_add_ui(absGH,absGH,1); // Add 1 to make sure it's non-zero.
        mpz_get_d_2exp(&numBits, absGH);
        if(maxBitsGH[degAold][degBold]<numBits) maxBitsGH[degAold][degBold]=numBits;
      #endif


      #ifdef DEBUG
        ++iter;
        debugPrintPolyInfo(iter,mpA,degA,mpB,degB,g,h);
      #endif


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
        // Divide out zero limbs, 1 at a time (this divides out chunks of 2^n for n bit limbs).
        uint64_t N = mpz_getlimbn(polDisc, 0); // First limb of the number
        while(N==0) {
          mpz_tdiv_q_2exp( polDisc, polDisc, 8*sizeof(mp_limb_t) ); // Set polDisc = polDisc/2^n
          N = mpz_getlimbn(polDisc, 0); // Get next limb of the number
          }
        // N is now the first non-zero limb.  Get the corresponding power of 2 and divide it out.
        int64_t pow2 = N & (-N);   // Power of 2 dividing N

        #ifdef MINGW
          // Since a Windows long is 32 bits, we need to check if the power of 2 exceeds 32 bits, and
          // if so, divide it out.  This is because the gmp divexact functions only work with "longs".
          if( (pow2 & 0xFFFFFFFF)==0 ) {
            mpz_tdiv_q_2exp(polDisc, polDisc, 32);  // Divide out 2^32
            pow2 /= 4294967296ULL;  // Update pow2.  The new value is now less than 2^32.
            }
        #endif

        mpz_divexact_ui(polDisc, polDisc, pow2);  // Set polDisc = polDisc/pow2
        //mpz_tdiv_q_2exp( polDisc, polDisc, ffsll(pow2)-1 ); // This method is a tad slower.
        }
      else if(thisP==5) {
        // We handle 5 separately since polDisc can have many factors of 5.
        for(;;) {  // We remove 8 powers of 5 at a time
          mpz_tdiv_qr_ui (q, rem, polDisc, 390625 );  // polDisc = q*5^8 + rem
          if( mpz_sgn(rem)!=0 ) break;  // Exit once there are no more factors of 5^8
          mpz_set(polDisc, q);  // Otherwise, since the remainder is zero, set polDisc = q
          }
        // What remains has at most 7 powers of 5.  We remove them 1 at a time
        for(int kk=1; kk<=7; ++kk) {  // loop a maximum of 7 times
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

    // This is supposed to the faster but may actually be a tad slower.
    if( mpz_perfect_square_p(polDisc) )  polGoodFlag[pIdx] = TRUE;
    else                                 polGoodFlag[pIdx] = FALSE;

    //mpz_sqrtrem(sqrtDisc, rem, polDisc);  // sqrtDisc = sqrt(polDisc) rounded down, rem = polDisc - sqrtDisc^2
    //if( mpz_sgn(rem)==0 ) polGoodFlag[pIdx] = TRUE;
    //else                  polGoodFlag[pIdx] = FALSE;

#ifdef DEBUG
    gmp_printf("Reduced polDisc = %Zd\n", polDisc);
    //gmp_printf("sqrtDisc = %Zd\n", sqrtDisc);
    if(0) {
      if(polGoodFlag[pIdx] == TRUE) {
        for(int col = 0; col < 11; col++)  A[10-col] = polBuf[pIdx*11+col];
        printf("  Poly = %ld ", A[0]);
        for(int k=1; k<11; k++) printf("+ %ld x^%d ", A[k], k);
        printf("\n");
      }
    }
#endif


    }  // End of loop over polynomials


#ifdef COEFF_SIZE_TEST
  printf("\nMax bits required:\n");
  for(int i=10; i>=0; --i) {
    printf("degA=%2d: [ %4d", i, maxBits[i][9]);
    for(int j=8; j>=0; --j)  printf(",  %4d", maxBits[i][j]);
    printf(" ]\n");
    }
/*
  printf("\nMax bits required for g and h:\n");
  for(int i=10; i>=0; --i) {
    printf("degA=%2d: [ %4d", i, maxBitsGH[i][9]);
    for(int j=8; j>=0; --j)  printf(",  %4d", maxBitsGH[i][j]);
    printf(" ]\n");
    }
  printf("\n\nFrequency of occurance:\n");
  for(int i=10; i>=0; --i) {
    printf("degA=%2d: [ %9ld", i, freq[i][9]);
    for(int j=8; j>=0; --j)  printf(",  %9ld", freq[i][j]);
    printf(" ]\n");
    }
*/
#endif


  /* Release all memory resources */
  mpz_clears(g, h, BR, NULL);
  for(int k=0; k<10; ++k)  mpz_clear(mpA[k]);
  for(int k=0; k<9;  ++k)  mpz_clear(mpB[k]);
  for(int k=0; k<10; ++k)  mpz_clear(mpR[k]);
  for(int k=0; k<9;  ++k)  mpz_clear(SB[k]);
  mpz_clears(q, gPow, hPow, scale, polDisc, rem, NULL);

  return 0;

}  // End of main code





#ifdef DEBUG
void debugPrintPolyInfo(int iter, mpz_t *mpA, int degA, mpz_t *mpB, int degB, mpz_t g, mpz_t h)
{
  printf("\n\n");
  printf("Iteration %d complete:\n", iter);
  printf("  A = ");  gmp_print_poly(mpA, degA);
  printf("\n  B = ");  gmp_print_poly(mpB, degB);
  printf("\n  g = "); gmp_printf("%Zd\n", g);
  printf("  h = "); gmp_printf("%Zd\n", h);
}

// This is a long version:
void debugPrintPolyInfoLong(int iter, int64_t *A, int degA, int64_t *B, int degB, int64_t g, int64_t h)
{
  printf("\n\n");
  printf("Iteration %d complete:\n", iter);
  printf("  A = %ld ", A[0]);
  for(int k=1; k<10; k++) printf("+ %ld x^%d ", A[k], k);
  printf("\n  B = %ld ", B[0]);
  for(int k=1; k<=degB; k++) printf("+ %ld x^%d ", B[k], k);
  printf("\n  g = %ld\n", g);
  printf("  h = %ld\n", h);
}

/* Helper function to print out a multi-precision polynomial */
void gmp_print_poly(mpz_t *poly, int deg)
{
  gmp_printf("%Zd", poly[0]);
  for(int k=1; k<=deg; k++) {
    printf(" + ");
    gmp_printf("%Zd", poly[k]);
    printf(" x^%d", k);
  }
}
#endif




#ifdef CONTENT_TEST
/* Function for computing the content of a polynomial at 2 */
/* This function returns the largest power of 2 dividing all coeffs of poly */
/* NOTE: it returns 2^power, and not the power. */
inline uint64_t getPolyContentAt2(mpz_t *poly, int deg, uint64_t maxContent)
{
  uint64_t cont2 = maxContent;

  for(int k = 0; k <= deg; k++) {
    uint64_t N = mpz_getlimbn(poly[k], 0); // First limb of the number
    if(N>0) {  // The method below breaks down when N=0.
      uint64_t thisPow2 = (N & (~(N - 1)));   // Power of 2 dividing coeff B[k]
      if(thisPow2<cont2) cont2=thisPow2;  // Retain the minimum over all coeffs.
      if(cont2==1) break;
      }
    }
  return cont2;
}

/* Function for computing the content of a polynomial at 5                   */
/* This function returns the largest power of 5 dividing all coeffs of poly  */
/* NOTE: it returns the power, not 5^power.                                  */
/*       q and rem are workspace variables.  They are passed in so they dont */
/*       need to be initialized every time, thereby saving ops.              */
inline int getPolyContentAt5(mpz_t *poly, mpz_t q, mpz_t rem, int deg, int maxPow)
{
  int pow5 = maxPow;

  for(int k = 0; k <= deg; k++) {
    mpz_tdiv_qr_ui(q, rem, poly[k], 10000000000 );  // rem = least significant 10 decimal digits
    int64_t N = mpz_get_ui(rem);
    if(N>0) {
      int thisPow5 = 0;
      if( pow5>=8 && N%390625 == 0 ) { N /= 390625; thisPow5 += 8; }
      if( pow5>=4 && N%625    == 0 ) { N /= 625;    thisPow5 += 4; }
      if( pow5>=2 && N%25     == 0 ) { N /= 25;     thisPow5 += 2; }
      if( pow5>=1 && N%5      == 0 ) {              thisPow5 += 1; }
      if(thisPow5<pow5) pow5=thisPow5;
      }
    if(pow5==0) break;
    }
  return pow5;
}
#endif




#ifdef MINGW
// limbs in mingW64 are 64 bits but longs are 32 bits.
// So the gmp mpz_set functions dont work properly for 64 bit inputs.
// This function gets around that.
inline void mpz_set_int64(mpz_t mpA, int64_t A)
{
  uint64_t* mpA_limb = mpz_limbs_write(mpA, 1);  // Get a pointer to first limb of A
  if(A==0) {
    mpz_limbs_finish(mpA, 0);  // Zero is represented with a size of 0.
    }
  else if(A>0) {
    mpA_limb[0] = A;
    mpz_limbs_finish(mpA, 1);  // Size of mpA is now 1 limb.
    }
  else {
    mpA_limb[0] = -A;
    mpz_limbs_finish(mpA, -1); // Size of mpA is now 1 limb. Since negative, set to -1.
    }                          // Recall: In gmp, negative numbers are represented by negative sizes.
}
#endif
