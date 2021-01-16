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
#define DBG_THREAD 0


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



// CUDA pdt kernel function to do the sub-resultant initialization and first iteration.
__global__
void pdtKernel_sr_init(int numPolys, int64_t *polys, int64_t *polyA, int64_t *polyB, 
         int *DegA, int *DegB, int64_t *G, int64_t *H)
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;


  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;


#ifdef CUDA_PROFILER
  unsigned int time1 = clock();
#endif


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
  /*  Do the first iteration of the sub-resultant algorithm.    */
  /*  This allows us to stay with longs a little longer before  */
  /*  transitioning to multi-precision.                         */

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

  /*  The first iteration of sub-resultant is now complete. */
  ////////////////////////////////////////////////////////////


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

}  // End of pdtKernel_sr_init





// This kernel runs the 2nd iteration of sub-resultant for the case when degB = 8.
__global__
void pdtKernel_sr_degB8(int numPolys, int64_t *polyA, int64_t *polyB, int *DegA, int *DegB, int64_t *G, int64_t *H)
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;

  // Skip any polynomial for which degB is not 8.
  if(DegB[index]<8) return;

#ifdef CUDA_PROFILER
  unsigned int time1 = clock();
#endif

  // Extract A and B polynomials from previous stage
  int64_t A[10], B[9];
  for(int col=0; col<=9; col++) A[col] = polyA[index*10+col];
  for(int col=0; col<=8; col++) B[col] = polyB[index*9 +col];

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
  __syncwarp();

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

}  // End of pdtKernel_sr_degB8





// This kernel runs an iteration of sub-resultant for the case when degB=7.
__global__
void pdtKernel_sr_degB7(int numPolys, int64_t *polyA, int64_t *polyB, int *DegA, int *DegB, int64_t *G, int64_t *H, uint64_t *Bscale)
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;

  // Initialize the Bscale to 1 before checking the degree of B.
  // In this way we guarantee that it has been initialized for every polynomial.
  Bscale[index] = 1;

  // Skip any polynomial for which degB is not 7.
  if(DegB[index]<7) return;


#ifdef CUDA_PROFILER
  unsigned int time1 = clock();
#endif

  // Extract A and B polynomials from previous stage
  int degA = DegA[index];
  int64_t A[10], B[8];
  for(int col=0; col<=degA; col++)  A[col] = polyA[index*10+col];
  for(int col=0; col<=7; col++)     B[col] = polyB[index*9 +col];
  __syncwarp();


  // This is for the next iteration, but we need to set it now before modifying B.
  for(int col=0; col<=7; col++)    polyA[index*10+col] = B[col];
  G[index] = B[7];  // g = leading coeff of A = B[7]
  if(degA==9)  H[index] = (B[7]*B[7])/H[index];   // h = (g^2)/h
  else         H[index] = B[7];  // h = g when degA=8
  __syncwarp();


  //////////////////////////////////////////////////////////////////////////////
  // Just to be safe, we remove as many factors of 2 and 5 from B as we can.
  // Without doing this, there is risk that the R computation might exceed 64 bits.
  // NOTE: During testing of billions of polynomials, max bits required was 62.
  //       This only included several WU files and there are millions of WUs.
  //       By scaling the B coeffs, the max bits required was reduced to 55.

  int cont2 = 4194304;  // Initialize to a large value
  for(int k=0; k<=7; k++) {
    uint64_t N = (B[k]>=0) ? B[k] : -B[k];  // N = |B[k]|
    if(N>0) {  // The method below breaks down when N=0.
      uint64_t thisPow2 = (N & (~(N - 1)));  // Power of 2 dividing coeff B[k]
      if(thisPow2<cont2) cont2=thisPow2;  // Retain the minimum over all coeffs.
      if(cont2==1) break;
      }
    }
  __syncwarp();

  int cont5 = 25;  // We only retain a max of 25 from the content at 5.
  for(int k=7; k>=0; k--) {
    if( (B[k]%25) != 0 ) { cont5=5; break;}
    }
  if(cont5==5) {
    for(int k=7; k>=0; k--) {
      if( (B[k]%5) != 0 ) { cont5=1; break;}
      }
    }
  __syncwarp();

  // Scale B by its content.
  int64_t contB = cont2 * cont5;
  for(int k=0; k<=7; k++)  B[k] = B[k] / contB;

  //////////////////////////////////////////////////////////////////////////////


  // Compute R.
  // The first iteration depends on the degree of A
  int64_t R[9];
  if(degA==9) {
    R[0] = B[7]*A[0];  R[1] = B[7]*A[1];
    for(int k=2;k<=8;++k)  R[k] = B[7]*A[k] - A[9]*B[k-2];
    }
  else {
    for(int k=0;k<=8;++k)  R[k] = A[k];
    }
  __syncwarp();

  R[0] = B[7]*R[0];
  for(int k=1;k<=7;++k)  R[k] = B[7]*R[k] - R[8]*B[k-1];
  for(int k=0;k<=6;++k)  R[k] = B[7]*R[k] - R[7]*B[k];

  // Determine the degree of R (it must be less than or equal to 6)
  int degR = 0;
  for(int k=6; k>0; k--)  {
    if( R[k]!=0 ) { degR=k; break; }
    }
  __syncwarp();


  // Before scaling R, we need to compensate for the scaling done to B.
  // This is because factors of 2 and 5 in the scale factor may need to
  // be removed from the multiplicative scale factor of B (i.e. there 
  // is no guarantee the scale factor divides evenly into the smaller R)
  int64_t leadA, leadAscale=1;
  if(degA==8) leadA = A[8];
  else        leadA = A[9];

  // Find common factors of 5 from cont5 and leadA
  if(cont5==25) {
    if(leadA%25==0)     { leadAscale=25; cont5 = 1; }
    else if(leadA%5==0) { leadAscale=5;  cont5 = 5; }
    }
  else if(cont5==5) {
    if(leadA%5==0) { leadAscale=5; cont5 = 1; }
    }

  // Find common factors of 2 from cont2 and leadA
  uint64_t N = (leadA>=0) ? leadA : -leadA;  // N = |leadA|
  uint64_t pow2 = (N & (~(N - 1)));  // Power of 2 dividing leading coeff of A
  if(pow2>=cont2)  { leadAscale = leadAscale*cont2; cont2 = 1; }
  else             { leadAscale = leadAscale*pow2;  cont2 = cont2/pow2; }

  // Divide out common factors from leadA.  Get the new contB term.
  leadA = leadA / leadAscale;
  contB = cont2 * cont5;


  // Scale R by g*h^delta.  g=h=A[degA]
  // When degA=9 scale by g*h^2, otherwise when degA=8 scale by g*h.
  int64_t Rscale = leadA * leadA;
  if(degA==9)  Rscale *= leadA;
  for(int k=0;k<=degR;++k) R[k] = R[k]/Rscale;


  // Get the multiplicative factor that arises from scaling B above.
  // This needs to be applied when multi-precision is initialized.
  // We cant apply it here without risking overflow of 64bit variables.
  Bscale[index] = contB * contB;
  if(degA==9)  Bscale[index] *= contB;


  // Setup the next iteration: A=B, B=R, g=l(A), h=h^(1-delta)g^delta.
  // When degA=9, h=g^2/h.  When degA=8, h=g;
  // NOTE: A, g, and h were already set above before scaling B.
  DegA[index] = 7;
  DegB[index] = degR;
  for(int col=0; col<=degR; col++) polyB[index*9+col] = R[col];

#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB7:\n");
    printf("  A = %ld ", polyA[index*10]);
    for(int k=1; k<=DegA[index]; k++) printf("+ %ld x^%d ", polyA[index*10+k], k);
    printf("\n");
    printf("  B = %ld ", polyB[index*9]);
    for(int k=1; k<=DegB[index]; k++) printf("+ %ld x^%d ", polyB[index*9+k], k);
    printf("\n  g = %ld\n", G[index]);
    printf("  h = %ld\n\n", H[index]);
    }
#endif

}  // End of pdtKernel_sr_degB7





// This kernel runs an iteration of sub-resultant for the case when degB=6 and degA=9.
// For this case, the results stay within 64 bits, provided we scale B appropriately.
__global__
void pdtKernel_sr_degB6degA9(int numPolys, int64_t *polyA, int64_t *polyB, int *DegA, int *DegB, int64_t *G, int64_t *H, uint64_t *Bscale)
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;

  // Skip any polynomial for which degB is not 6 and degA is not 9.
  if(DegB[index]<6 || DegA[index]<9) return;


#ifdef CUDA_PROFILER
  unsigned int time1 = clock();
#endif


  // Extract A and B polynomials from previous stage
  int64_t A[10], B[7];
  for(int col=0; col<=9; col++)  A[col] = polyA[index*10+col];
  for(int col=0; col<=6; col++)  B[col] = polyB[index*9 +col];


  // This is for the next iteration, but we need to set it now before modifying B.
  // NOTE: We are guaranteed that g^3 fits inside 63 bits.
  //       (maximum was 29 bits over a test of billions of polys.)
  for(int col=0; col<=6; col++)  polyA[index*10+col] = B[col];
  G[index] = B[6];  // g = leading coeff of A = B[6]
  H[index] = (B[6]*B[6]*B[6])/(H[index]*H[index]);   // h = (g^3)/(h^2)


  //////////////////////////////////////////////////////////////////////////////
  // Just to be safe, we remove as many factors of 2 and 5 from B as we can.
  // Without doing this, there is risk that the R computation might exceed 64 bits.
  // NOTE: During testing of billions of polynomials, max bits required were 62.
  //       This only included several WU files and there are millions of WUs.
  //       By scaling the B coeffs, the max bits required were reduced to 55.

  int cont2 = 4194304;  // Initialize to a large value
  for(int k=0; k<=6; k++) {
    uint64_t N = (B[k]>=0) ? B[k] : -B[k];  // N = |B[k]|
    if(N>0) {  // The method below breaks down when N=0.
      uint64_t thisPow2 = (N & (~(N - 1)));  // Power of 2 dividing coeff B[k]
      if(thisPow2<cont2) cont2=thisPow2;  // Retain the minimum over all coeffs.
      if(cont2==1) break;
      }
    }

  int cont5 = 25;  // We only retain a max of 25 from the content at 5.
  for(int k=6; k>=0; k--) {
    if( (B[k]%25) != 0 ) { cont5=5; break;}
    }
  if(cont5==5) {
    for(int k=6; k>=0; k--) {
      if( (B[k]%5) != 0 ) { cont5=1; break;}
      }
    }
  __syncwarp();

  // Scale B by its content.
  int64_t contB = cont2 * cont5;
  for(int k=0; k<=6; k++)  B[k] = B[k] / contB;

  //////////////////////////////////////////////////////////////////////////////


  // Compute R
  int64_t R[9];
  R[0] = B[6]*A[0];  R[1] = B[6]*A[1];  R[2] = B[6]*A[2];
  for(int k=3;k<=8;++k)  R[k] = B[6]*A[k] - A[9]*B[k-3];
  R[0] = B[6]*R[0];  R[1] = B[6]*R[1];
  for(int k=2;k<=7;++k)  R[k] = B[6]*R[k] - R[8]*B[k-2];
  R[0] = B[6]*R[0];
  for(int k=1;k<=6;++k)  R[k] = B[6]*R[k] - R[7]*B[k-1];
  for(int k=0;k<=5;++k)  R[k] = B[6]*R[k] - R[6]*B[k];


  // Determine the degree of R (it must be less than or equal to 5)
  int degR = 0;
  for(int k=5; k>0; k--)  {
    if( R[k]!=0 ) { degR=k; break; }
    }
  __syncwarp();


  // Before scaling R, we need to compensate for the scaling done to B.
  // This is because factors of 2 and 5 in the scale factor may need to
  // be removed from the multiplicative scale factor of B (i.e. there 
  // is no guarantee the scale factor divides evenly into the smaller R)
  int64_t leadA, leadAscale=1;
  leadA = A[9];

  // Find common factors of 5 from cont5 and leadA
  if(cont5==25) {
    if(leadA%25==0)     { leadAscale=25; cont5 = 1; }
    else if(leadA%5==0) { leadAscale=5;  cont5 = 5; }
    }
  else if(cont5==5) {
    if(leadA%5==0) { leadAscale=5; cont5 = 1; }
    }

  // Find common factors of 2 from cont2 and leadA
  uint64_t N = (leadA>=0) ? leadA : -leadA;  // N = |leadA|
  uint64_t pow2 = (N & (~(N - 1)));  // Power of 2 dividing leading coeff of A
  if(pow2>=cont2)  { leadAscale = leadAscale*cont2; cont2 = 1; }
  else             { leadAscale = leadAscale*pow2;  cont2 = cont2/pow2; }

  // Divide out common factors from leadA.  Get the new contB term.
  leadA = leadA / leadAscale;
  contB = cont2 * cont5;


  // Scale R by g*h^3 where g=h=A[9].
  int64_t Rscale = leadA * leadA * leadA * leadA;
  for(int k=0;k<=degR;++k) R[k] = R[k]/Rscale;


  // Get the multiplicative factor that arises from scaling B above.
  // This needs to be applied when multi-precision is initialized.
  // We cant apply it here without risking overflow of 64bit variables.
  Bscale[index] = contB * contB * contB * contB;


  // Setup the next iteration: A=B, B=R, g=l(A), h=(g^3)/(h^2).
  // NOTE: A, g, and h were already set above before scaling B.
  DegA[index] = 6;
  DegB[index] = degR;
  for(int col=0; col<=degR; col++) polyB[index*9+col] = R[col];

#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB6, degA9:\n");
    printf("  A = %ld ", polyA[index*10]);
    for(int k=1; k<=DegA[index]; k++) printf("+ %ld x^%d ", polyA[index*10+k], k);
    printf("\n");
    printf("  B = %ld ", polyB[index*9]);
    for(int k=1; k<=DegB[index]; k++) printf("+ %ld x^%d ", polyB[index*9+k], k);
    printf("\n  g = %ld\n", G[index]);
    printf("  h = %ld\n", H[index]);
    }
#endif

}  // End of pdtKernel_sr_degB6degA9





// This kernel initializes the multi-precision variables
__global__
void pdtKernel_sr_mpInit(int numPolys, char *validFlag, int64_t *polyA, int64_t *polyB, int *DegA, int *DegB, 
         uint64_t *Bscale, mp_int *mpA, mp_int *mpB )
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;

  // We error on the side of caution and initialize validFlag to true.
  // This setting keeps the polynomial on the list for further testing.
  // We do this in case the kernel aborts early before properly setting the flag.
  validFlag[index] = TRUE;

  // Transfer the int64_t data into the multi-precision variables
  // We only do the polynomials A and B for now, G/H can stay 64 bits for a couple more iterations.
  for(int col=0; col<=DegA[index]; col++)  mp_set_int64(&(mpA[index*10+col]), polyA[index*10+col]);
  for(int col=0; col<=DegB[index]; col++)  mp_set_int64(&(mpB[index*9 +col]), polyB[index*9 +col]);


  // Apply the multiplicative scale factor to the polynomial B.
  for(int k=0; k<=DegB[index]; k++) {
    int Idx = index*9 + k;
    mp_word T = mul128(mpB[Idx].dp[0], Bscale[index]);  // Do 128 bit multiply by the scale.
    mpB[Idx].dp[0] = T.lo & MP_MASK;  // Mask out the sign bit
    T = T<<1;  // Shift the 64th bit of T from lower digit into upper digit.
    mpB[Idx].dp[1] = T.hi;  // The higher part of T becomes the upper digit of mpB[k]
    // Now set the used field.  I'm still unsure if this is really necessary.
    if(mpB[Idx].dp[1] != 0)  mpB[Idx].used = 2;
    else {
      if(mpB[Idx].dp[0] != 0)  mpB[Idx].used = 1;
      else { mpB[Idx].used = 0; mpB[Idx].sign = MP_ZPOS; }
      }
    }

#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After multi-precision initialization:\n");
    printf("  A = "); mp_print_poly(&(mpA[index*10]),DegA[index]); printf("\n");
    printf("  B = "); mp_print_poly(&(mpB[index*9]), DegB[index]); printf("\n\n");
    }
#endif

}  // End of pdtKernel_sr_mpInit





// This kernel runs an iteration of sub-resultant for the case when degB=6 and degA=8.
// For this case, the results fit in a 2 digit multi-prec.
__global__
void pdtKernel_sr_degB6degA8(int numPolys, int *DegA, int *DegB, mp_int *MPA, mp_int *MPB, int64_t *G, int64_t *H )
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;

  // Skip any polynomial for which degB is not 6 and degA is not 8.
  if(DegB[index]<6 || DegA[index]<8) return;


#ifdef CUDA_PROFILER
  unsigned int time1 = clock();
#endif


  // Multi-precision declarations
  mp_int mpA[9], mpB[7], mpR[8], mpT1, mpT2;

  // Copy data from gpu memory into local memory for this thread
#pragma unroll
  for(int col=0; col<=8; col++)  mp_copy(&(MPA[index*10+col]), &(mpA[col]));
#pragma unroll
  for(int col=0; col<=6; col++)  mp_copy(&(MPB[index*9 +col]), &(mpB[col]));


  // The remaining multi-precision initializations.
  // Note: These need to either be set or zeroed out one time.
  for(int k=0; k<=7; k++)  mp_zero_2dig(&(mpR[k]));
  mp_zero_2dig(&mpT1);
  mp_zero_2dig(&mpT2);

//  __syncwarp();


////////////////////////////////////////////////////////////////////////////////
// Compute R.
// What follows is the mp equivalent of this:
//    int64_t R[8];
//    R[0] = B[6]*A[0];  R[1] = B[6]*A[1];
//    for(int k=2;k<=7;++k)  R[k] = B[6]*A[k] - A[8]*B[k-2];
//    R[0] = B[6]*R[0];
//    for(int k=1;k<=6;++k)  R[k] = B[6]*R[k] - R[7]*B[k-1];
//    for(int k=0;k<=5;++k)  R[k] = B[6]*R[k] - R[6]*B[k];

  mp_mul_2dig( &(mpB[6]), &(mpA[0]), &(mpR[0]) );
  mp_mul_2dig( &(mpB[6]), &(mpA[1]), &(mpR[1]) );
#pragma unroll
  for(int k=2;k<=7;++k) {
    mp_mul_2dig( &(mpB[6]), &(mpA[k]),   &mpT1 );  // 1st term
    mp_mul_2dig( &(mpA[8]), &(mpB[k-2]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add_2dig( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
  mp_mul_2dig( &(mpB[6]), &(mpR[0]), &mpT1 );
  mp_copy( &mpT1, &(mpR[0]) );
#pragma unroll
  for(int k=1;k<=6;++k) {
    mp_mul_2dig( &(mpB[6]), &(mpR[k]),   &mpT1 );  // 1st term
    mp_mul_2dig( &(mpR[7]), &(mpB[k-1]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add_2dig( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
#pragma unroll
  for(int k=0;k<=5;++k) {
    mp_mul_2dig( &(mpB[6]), &(mpR[k]), &mpT1 );  // 1st term
    mp_mul_2dig( &(mpR[6]), &(mpB[k]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add_2dig( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
////////////////////////////////////////////////////////////////////////////////


  // Determine the degree of R (it must be less than or equal to 5)
  int degR = 0;
  for(int k=5; k>0; k--)  {
    if( mpR[k].used>0 ) { degR=k; break; }
    }
  __syncwarp();


  // The previous iteration must have been degB=8, degA=9.
  // At the end of that iteration we would have g=h=A[8] (since delta=1).
  // So we scale R by g*h^2 = A[8]^3.
  // NOTE: We are guaranteed that A[8]^3 easily fits inside 63 bits,
  //       allowing us to use the more optimal mp_div_d_2dig function.
  uint64_t Rscale = mpA[8].dp[0] * mpA[8].dp[0] * mpA[8].dp[0];
  for(int k=0;k<=degR;++k) {
    mp_div_d_2dig(&(mpR[k]), Rscale);
    mpR[k].sign = mpR[k].sign * mpA[8].sign;  // Adjust the sign accordingly
    }


  // Copy data back into gpu memory for this thread
  // This sets up the next iteration: A=B, B=R, g=l(A), h=g^2/h.
  // NOTE: Analysis has shown that B[6]^2 fits within 50 bits,
  //       so there should be no risk of H overflowing.
  DegA[index] = 6;
  DegB[index] = degR;
  for(int col=0; col<=6; col++)     mp_copy( &(mpB[col]), &(MPA[index*10+col]) );
  for(int col=0; col<=degR; col++)  mp_copy( &(mpR[col]), &(MPB[index*9 +col]) );
  G[index] = mpB[6].sign * (int64_t)(mpB[6].dp[0]);  // g = leading coeff of A = B[6]
  H[index] = mpA[8].sign * (int64_t)((mpB[6].dp[0]*mpB[6].dp[0]) / mpA[8].dp[0]); // h = (B[6]^2)/A[8]


#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB6, degA8:\n");
    printf("  A = "); mp_print_poly(&(MPA[index*10]),DegA[index]); printf("\n");
    printf("  B = "); mp_print_poly(&(MPB[index*9]), DegB[index]); printf("\n");
    printf("  g = %ld\n", G[index]);
    printf("  h = %ld\n\n", H[index]);
    }
#endif

}  // End of pdtKernel_sr_degB6degA8





// This kernel runs an iteration of sub-resultant for the case when degB=6 and degA=7.
// For this case, the results fit in a 3 digit multi-prec.
__global__
void pdtKernel_sr_degB6degA7(int numPolys, int *DegA, int *DegB, mp_int *MPA, mp_int *MPB, int64_t *G, int64_t *H )
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;

  // Skip any polynomial for which degB is not 6.  It is assummed that the degA=8,9 kernels have 
  // been previously run, so that degA is now guaranteed to be 7.
  if(DegB[index]<6) return;


#ifdef CUDA_PROFILER
  unsigned int time1 = clock();
#endif


  // Multi-precision declarations
  mp_int mpA[8], mpB[7], mpR[7], mpT1, mpT2;

  // Copy data from gpu memory into local memory for this thread
#pragma unroll
  for(int col=0; col<=7; col++)  mp_copy(&(MPA[index*10+col]), &(mpA[col]));
#pragma unroll
  for(int col=0; col<=6; col++)  mp_copy(&(MPB[index*9 +col]), &(mpB[col]));


  // The remaining multi-precision initializations.
  // Note: These need to either be set or zeroed out one time.
  for(int k=0; k<=6; k++)  mp_zero_3dig(&(mpR[k]));
  mp_zero_3dig(&mpT1);
  mp_zero_3dig(&mpT2);

//  __syncwarp();


////////////////////////////////////////////////////////////////////////////////
// Compute R.
// What follows is the mp equivalent of this:
//    int64_t R[7];
//    R[0] = B[6]*A[0];
//    for(int k=1;k<=6;++k)  R[k] = B[6]*A[k] - A[7]*B[k-1];
//    for(int k=0;k<=5;++k)  R[k] = B[6]*R[k] - R[6]*B[k];


  mp_mul_3dig( &(mpB[6]), &(mpA[0]), &(mpR[0]) );
#pragma unroll
  for(int k=1;k<=6;++k) {
    mp_mul_3dig( &(mpB[6]), &(mpA[k]),   &mpT1 );  // 1st term
    mp_mul_3dig( &(mpA[7]), &(mpB[k-1]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add_3dig( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
#pragma unroll
  for(int k=0;k<=5;++k) {
    mp_mul_3dig( &(mpB[6]), &(mpR[k]), &mpT1 );  // 1st term
    mp_mul_3dig( &(mpR[6]), &(mpB[k]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add_3dig( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }


////////////////////////////////////////////////////////////////////////////////



  // Determine the degree of R (it must be less than or equal to 5)
  int degR = 0;
  for(int k=5; k>0; k--)  {
    if( mpR[k].used>0 ) { degR=k; break; }
    }
  __syncwarp();


  // Scale R by g*h (delta=1).
  // NOTE: We are guaranteed that g*h easily fits inside 63 bits,
  //       allowing us to use the more optimal mp_div_d_3dig function.
  int64_t  RscaleSigned = G[index] * H[index];
  uint64_t Rscale;
  int sign;
  if(RscaleSigned<0) { sign=-1; Rscale = -RscaleSigned; }
  else               { sign= 1; Rscale =  RscaleSigned; }
  __syncwarp();
#pragma unroll
  for(int k=0;k<=degR;++k) {
    mp_div_d_3dig(&(mpR[k]), Rscale);
    mpR[k].sign = mpR[k].sign * sign;  // Adjust the sign accordingly
    }


  // Copy data back into gpu memory for this thread.
  // This sets up the next iteration: A=B, B=R, g=l(A), h=g.
  // NOTE: Analysis has shown that g=h=B[6] fits within 48 bits,
  //       so there should be no risk of G and H overflowing.
  DegA[index] = 6;
  DegB[index] = degR;
  for(int col=0; col<=6; col++)     mp_copy( &(mpB[col]), &(MPA[index*10+col]) );
  for(int col=0; col<=degR; col++)  mp_copy( &(mpR[col]), &(MPB[index*9 +col]) );
  G[index] = mpB[6].sign * (int64_t)(mpB[6].dp[0]);  // g = leading coeff of A = B[6]
  H[index] = G[index];

#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB6, degA7:\n");
    printf("  A = "); mp_print_poly(&(MPA[index*10]),DegA[index]); printf("\n");
    printf("  B = "); mp_print_poly(&(MPB[index*9]), DegB[index]); printf("\n");
    printf("  g = %ld\n", G[index]);
    printf("  h = %ld\n\n", H[index]);
    }
#endif

}  // End of pdtKernel_sr_degB6degA7





// This kernel runs an iteration of sub-resultant for the case when degB=5 and degA=6.
// For this case, the results fit in a 4 digit multi-prec.
__global__
void pdtKernel_sr_degB5(int numPolys, char *validFlag, int *DegA, int *DegB, mp_int *MPA, mp_int *MPB, 
         int64_t *G, int64_t *H )
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1) return;


  // Skip any polynomial for which degB is not 5 or degA is not 6.
  // Analysis has shown that the other cases comprise less than .0005% of the total.
  // Although this is not a memory overflow error, we set the validFlag to MEM_ERR
  // to force the CPU to handle it.
  if(DegB[index]!=5 || DegA[index]!=6) { validFlag[index] = MEM_ERR; return; }


#ifdef CUDA_PROFILER
  unsigned int time1 = clock();
#endif


  // Multi-precision declarations
  mp_int mpA[7], mpB[6], mpR[6], mpG, mpH, mpT1, mpT2;

  // Copy data from gpu memory into local memory for this thread
#pragma unroll
  for(int col=0; col<=6; col++)  mp_copy(&(MPA[index*10+col]), &(mpA[col]));
#pragma unroll
  for(int col=0; col<=5; col++)  mp_copy(&(MPB[index*9 +col]), &(mpB[col]));

  // Transfer G and H into multi-precision variables.
  mp_set_int64( &mpG, G[index] );
  mp_set_int64( &mpH, H[index] );

  // The remaining multi-precision initializations.
  // Note: These need to either be set or zeroed out one time.
#pragma unroll
  for(int k=0; k<=5; k++)  mp_zero_4dig(&(mpR[k]));
  mp_zero_4dig(&mpT1);
  mp_zero_4dig(&mpT2);


////////////////////////////////////////////////////////////////////////////////
// Compute R.
// What follows is the mp equivalent of this:
//    int64_t R[6];
//    R[0] = B[5]*A[0];
//    for(int k=1;k<=5;++k)  R[k] = B[5]*A[k] - A[6]*B[k-1];
//    for(int k=0;k<=4;++k)  R[k] = B[5]*R[k] - R[5]*B[k];

  mp_mul_4dig( &(mpB[5]), &(mpA[0]), &(mpR[0]) );
#pragma unroll
  for(int k=1;k<=5;++k) {
    mp_mul_4dig( &(mpB[5]), &(mpA[k]),   &mpT1 );  // 1st term
    mp_mul_4dig( &(mpA[6]), &(mpB[k-1]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add_4dig( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
#pragma unroll
  for(int k=0;k<=4;++k) {
    mp_mul_4dig( &(mpB[5]), &(mpR[k]), &mpT1 );  // 1st term
    mp_mul_4dig( &(mpR[5]), &(mpB[k]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add_4dig( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
////////////////////////////////////////////////////////////////////////////////


  // Determine the degree of R (it must be less than or equal to 4)
  int degR = 0;
  for(int k=4; k>0; k--)  {
    if( mpR[k].used>0 ) { degR=k; break; }
    }
  // Analysis has shown degR=4 99.9999% of the time.  So if its not 4, let the cpu handle it.
  if( degR<4 ) {
    validFlag[index] = MEM_ERR;
    return;
    }
  __syncwarp();


  // Set A = B
  DegA[index] = 5;
  for(int col=0; col<=5; col++)  mp_copy( &(mpB[col]), &(MPA[index*10+col]) );

  // Set B = R/(g^2) (delta=1 and g=h)
  DegB[index] = 4;
  mp_mul_2dig( &mpG, &mpH, &mpT1 );  // Set T1 = g*h
  for(int col=0; col<=4; col++) {
    mp_div( &(mpR[col]), &mpT1, &(MPB[index*9 +col]), NULL ); // Set B[k] = R[k] / T1;
    }
  // We do not set g or h, since from here on out we will always have g = h = A[degA].


#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB5:\n");
    printf("  A = "); mp_print_poly(&(MPA[index*10]),DegA[index]); printf("\n");
    printf("  B = "); mp_print_poly(&(MPB[index*9]), DegB[index]); printf("\n");
    printf("  g = "); mp_printf( MPA[index*10+5] ); printf("\n");
    printf("  h = "); mp_printf( MPA[index*10+5] ); printf("\n\n");
    }
#endif

}  // End of pdtKernel_sr_degB5





// This kernel runs an iteration of sub-resultant for the case when degB=4 and degA=5.
// For this case, the results fit in a 6 digit multi-prec, but we use the standard routines.
// This kernel will complete the sub-resultant calculation.
// Analysis has shown that the vast majority of cases will have degA=5 and in all subsequent
// iterations, the degrees of A and B will drop by 1.  Whenever this does not occur, the
// polynomial is kicked back to the cpu for processing (less than 1 in 100000 polys).

__global__
void pdtKernel_sr_degB4_3_2(int numPolys, char *validFlag, mp_int* polDiscArray, int *DegA, int *DegB, mp_int *MPA, mp_int *MPB )
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;

  int degA = DegA[index];
  int degB = DegB[index];

  // Skip any polynomial for which degB is not 4 or degA is not 5.
  // Analysis has shown that the other cases are extremely rare, so we let the CPU handle them.
  if(degB!=4 || degA!=5) { validFlag[index] = MEM_ERR; return; }


#ifdef CUDA_PROFILER
  unsigned int time1 = clock();
#endif


  // Multi-precision declarations
  mp_int mpA[6], mpB[5], mpR[5], mpT1, mpT2;

  // Copy data from gpu memory into local memory for this thread
#pragma unroll
  for(int col=0; col<=5; col++)  mp_copy(&(MPA[index*10+col]), &(mpA[col]));
#pragma unroll
  for(int col=0; col<=4; col++)  mp_copy(&(MPB[index*9 +col]), &(mpB[col]));


  // The above is faster than using the device memory directly as done here:
  //mp_int *mpA, *mpB, mpR[5], mpT1, mpT2;
  //mpA = &(MPA[index*10]);  // Setup pointers for A and B polynomials
  //mpB = &(MPB[index*9]);


  // The remaining multi-precision initializations.
  // Note: These need to either be set or zeroed out one time.
#pragma unroll
  for(int k=0; k<=4; k++)  mp_zero(&(mpR[k]));
  mp_zero(&mpT1);
  mp_zero(&mpT2);


  ////////////////////////////////////////////////////////////////////////////////
  // Compute R.
  // What follows is the mp equivalent of this:
  //    int64_t R[5];
  //    R[0] = B[4]*A[0];
  //    for(int k=1;k<=4;++k)  R[k] = B[4]*A[k] - A[5]*B[k-1];
  //    for(int k=0;k<=3;++k)  R[k] = B[4]*R[k] - R[4]*B[k];

  mp_mul( &(mpB[4]), &(mpA[0]), &(mpR[0]) );
#pragma unroll
  for(int k=1;k<=4;++k) {
    mp_mul( &(mpB[4]), &(mpA[k]),   &mpT1 );  // 1st term
    mp_mul( &(mpA[5]), &(mpB[k-1]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
#pragma unroll
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
  __syncwarp();

  // From previous iteration, g=h=A[5]
  mp_mul( &(mpA[5]), &(mpA[5]), &mpT1 );  // Set T1 = g^2

  // NOTE: To save ops, we interchange the role of A and B.
  // So we skip setting A=B, and instead set A=R/g^2.
  // We do not set g or h, since here on out we will always assume g = h = lead coef of A.
#pragma unroll
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
#pragma unroll
  for(int k=1;k<=3;++k) {
    mp_mul( &(mpA[3]), &(mpB[k]),   &mpT1 );  // 1st term
    mp_mul( &(mpB[4]), &(mpA[k-1]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
#pragma unroll
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
  __syncwarp();

  // From previous iteration, g=h=A[4].  Don't forget A and B have been swapped.
  mp_mul( &(mpB[4]), &(mpB[4]), &mpT1 );  // Set T1 = g^2

  // We would normally set A=B here, but since they were swapped A is now back to being itself.

  // Set B = R/(g^2) (delta=1 and g=h)
  mp_div( &(mpR[0]), &mpT1, &(mpB[0]), NULL );
  mp_div( &(mpR[1]), &mpT1, &(mpB[1]), NULL );
  mp_div( &(mpR[2]), &mpT1, &(mpB[2]), NULL );

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
  // So we leave B alone and set A = R/(g^2) (delta=1 and g=h)
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
    mp_copy(polDisc, &(polDiscArray[index]));  // Store in global memory.
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
  mp_copy(polDisc, &(polDiscArray[index]));  // Store in global memory.

#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("polDisc = ");  mp_printf(*polDisc); printf("\n");
    }
#endif

}  // End of pdtKernel_sr_degB4_3_2





// This kernel runs an iteration of sub-resultant for the case when degB=4 and degA=5.
// For this case, the results fit in a 6 digit multi-prec.
__global__
void pdtKernel_sr_degB4(int numPolys, char *validFlag, int *DegA, int *DegB, mp_int *MPA, mp_int *MPB )
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;

  // Skip any polynomial for which degB is not 4 or degA is not 5.
  // Analysis has shown that the other cases are extremely rare, so we let the CPU handle them.
  if(DegB[index]!=4 || DegA[index]!=5) { validFlag[index] = MEM_ERR; return; }


#ifdef CUDA_PROFILER
  unsigned int time1 = clock();
#endif


  // Multi-precision declarations
  mp_int mpA[6], mpB[5], mpR[5], mpT1, mpT2;

  // Copy data from gpu memory into local memory for this thread
#pragma unroll
  for(int col=0; col<=5; col++)  mp_copy(&(MPA[index*10+col]), &(mpA[col]));
#pragma unroll
  for(int col=0; col<=4; col++)  mp_copy(&(MPB[index*9 +col]), &(mpB[col]));


  // The above is faster than using the device memory directly as done here:
  //mp_int *mpA, *mpB, mpR[5], mpT1, mpT2;
  //mpA = &(MPA[index*10]);  // Setup pointers for A and B polynomials
  //mpB = &(MPB[index*9]);


  // The remaining multi-precision initializations.
  // Note: These need to either be set or zeroed out one time.
#pragma unroll
  for(int k=0; k<=4; k++)  mp_zero(&(mpR[k]));
  mp_zero(&mpT1);
  mp_zero(&mpT2);


////////////////////////////////////////////////////////////////////////////////
// Compute R.
// What follows is the mp equivalent of this:
//    int64_t R[5];
//    R[0] = B[4]*A[0];
//    for(int k=1;k<=4;++k)  R[k] = B[4]*A[k] - A[5]*B[k-1];
//    for(int k=0;k<=3;++k)  R[k] = B[4]*R[k] - R[4]*B[k];

  mp_mul( &(mpB[4]), &(mpA[0]), &(mpR[0]) );
#pragma unroll
  for(int k=1;k<=4;++k) {
    mp_mul( &(mpB[4]), &(mpA[k]),   &mpT1 );  // 1st term
    mp_mul( &(mpA[5]), &(mpB[k-1]), &mpT2 );  // 2nd term
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
#pragma unroll
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
  __syncwarp();


  // From previous iteration, g=h=A[5]
  mp_mul( &(mpA[5]), &(mpA[5]), &mpT1 );  // Set T1 = g^2


  // Set A = B
  DegA[index] = 4;
  //for(int k=0; k<=4; k++)  mp_copy( &(mpB[k]), &(mpA[k]) );
  for(int col=0; col<=4; col++)  mp_copy( &(mpB[col]), &(MPA[index*10+col]) );

  // Set B = R/(g^2) (delta=1 and g=h)
  DegB[index] = 3;
  for(int col=0; col<=3; col++) {
    //mp_div( &(mpR[col]), &mpT1, &(mpB[col]), NULL ); // Set B[k] = R[k] / T1;
    mp_div( &(mpR[col]), &mpT1, &(MPB[index*9 +col]), NULL ); // Set B[k] = R[k] / T1;
    }

  // We do not set g or h, since here on out we will always assume g = h = lead coef of A.


#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB4:\n");
    printf("  A = "); mp_print_poly(&(MPA[index*10]),DegA[index]); printf("\n");
    printf("  B = "); mp_print_poly(&(MPB[index*9]), DegB[index]); printf("\n");
    printf("  g = "); mp_printf( MPA[index*10+4] ); printf("\n");
    printf("  h = "); mp_printf( MPA[index*10+4] ); printf("\n\n");
    }
#endif

}  // End of pdtKernel_sr_degB4





// This kernel runs an iteration of sub-resultant for the case when degB=3 and degA=4.
__global__
void pdtKernel_sr_degB3(int numPolys, char *validFlag, int *DegA, int *DegB, mp_int *MPA, mp_int *MPB )
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;


  // Skip any polynomial for which degB is not 3 or degA is not 4.
  if(DegB[index]!=3 || DegA[index]!=4) { validFlag[index] = MEM_ERR; return; }


#ifdef CUDA_PROFILER
  unsigned int time1 = clock();
#endif


  // Multi-precision declarations
  mp_int mpA[5], mpB[4], mpR[4], mpT1, mpT2;

  // Copy data from gpu memory into local memory for this thread
#pragma unroll
  for(int col=0; col<=4; col++)  mp_copy(&(MPA[index*10+col]), &(mpA[col]));
#pragma unroll
  for(int col=0; col<=3; col++)  mp_copy(&(MPB[index*9 +col]), &(mpB[col]));


  // The remaining multi-precision initializations.
  // Note: These need to either be set or zeroed out one time.
#pragma unroll
  for(int k=0; k<=3; k++)  mp_zero(&(mpR[k]));
  mp_zero(&mpT1);
  mp_zero(&mpT2);


////////////////////////////////////////////////////////////////////////////////
// Compute R.
// What follows is the mp equivalent of this:
//    int64_t R[4];
//    R[0] = B[3]*A[0];
//    for(int k=1;k<=3;++k)  R[k] = B[3]*A[k] - A[4]*B[k-1];
//    for(int k=0;k<=2;++k)  R[k] = B[3]*R[k] - R[3]*B[k];

  int retVal = mp_mul( &(mpB[3]), &(mpA[0]), &(mpR[0]) );
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
#pragma unroll
  for(int k=1;k<=3;++k) {
    retVal = mp_mul( &(mpB[3]), &(mpA[k]),   &mpT1 );  // 1st term
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
    retVal = mp_mul( &(mpA[4]), &(mpB[k-1]), &mpT2 );  // 2nd term
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
#pragma unroll
  for(int k=0;k<=2;++k) {
    retVal = mp_mul( &(mpB[3]), &(mpR[k]), &mpT1 );  // 1st term
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
    retVal = mp_mul( &(mpR[3]), &(mpB[k]), &mpT2 );  // 2nd term
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
////////////////////////////////////////////////////////////////////////////////


  // Determine the degree of R (it must be less than or equal to 2)
  int degR = 0;
  for(int k=2; k>0; k--)  {
    if( mpR[k].used>0 ) { degR=k; break; }
    }
  // Analysis has shown degR=2 the vast majority of the time.  So if its not 2, let the cpu handle it.
  if( degR<2 ) {
    validFlag[index] = MEM_ERR;
    return;
    }
  __syncwarp();


  // From previous iteration, g=h=A[4]
  retVal = mp_mul( &(mpA[4]), &(mpA[4]), &mpT1 );  // Set T1 = g^2
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }


  // Set A = B
  DegA[index] = 3;
  for(int col=0; col<=3; col++)  mp_copy( &(mpB[col]), &(MPA[index*10+col]) );

  // Set B = R/(g^2) (delta=1 and g=h)
  DegB[index] = 2;
  for(int col=0; col<=2; col++) {
    retVal = mp_div( &(mpR[col]), &mpT1, &(MPB[index*9+col]), NULL ); // Set B[k] = R[k] / T1;
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
    }


#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB3:\n");
    printf("  A = "); mp_print_poly(&(MPA[index*10]),DegA[index]); printf("\n");
    printf("  B = "); mp_print_poly(&(MPB[index*9]), DegB[index]); printf("\n");
    printf("  g = "); mp_printf( MPA[index*10+3] ); printf("\n");
    printf("  h = "); mp_printf( MPA[index*10+3] ); printf("\n\n");
    }
#endif

}  // End of pdtKernel_sr_degB3





// This kernel runs the final iterations of sub-resultant for the case when degB starts at 2.
__global__
void pdtKernel_sr_degB2(int numPolys, char *validFlag, mp_int* polDiscArray, int *DegA, int *DegB, mp_int *MPA, mp_int *MPB )
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;


  // Skip any polynomial for which degB is not 2 or degA is not 3.
  if(DegB[index]!=2 || DegA[index]!=3) { validFlag[index] = MEM_ERR; return; }


#ifdef CUDA_PROFILER
  unsigned int time1 = clock();
#endif


  // Multi-precision declarations
  mp_int mpA[4], mpB[3], mpR[3], mpT1, mpT2;

  // Copy data from gpu memory into local memory for this thread
#pragma unroll
  for(int col=0; col<=3; col++)  mp_copy(&(MPA[index*10+col]), &(mpA[col]));
#pragma unroll
  for(int col=0; col<=2; col++)  mp_copy(&(MPB[index*9 +col]), &(mpB[col]));


  // The remaining multi-precision initializations.
  // Note: These need to either be set or zeroed out one time.
#pragma unroll
  for(int k=0; k<=2; k++)  mp_zero(&(mpR[k]));
  mp_zero(&mpT1);
  mp_zero(&mpT2);


////////////////////////////////////////////////////////////////////////////////
// Compute R.
// What follows is the mp equivalent of this:
//    int64_t R[3];
//    R[0] = B[2]*A[0];
//    for(int k=1;k<=2;++k)  R[k] = B[2]*A[k] - A[3]*B[k-1];
//    for(int k=0;k<=1;++k)  R[k] = B[2]*R[k] - R[2]*B[k];

  int retVal = mp_mul( &(mpB[2]), &(mpA[0]), &(mpR[0]) );
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
#pragma unroll
  for(int k=1;k<=2;++k) {
    retVal = mp_mul( &(mpB[2]), &(mpA[k]),   &mpT1 );  // 1st term
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
    retVal = mp_mul( &(mpA[3]), &(mpB[k-1]), &mpT2 );  // 2nd term
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
#pragma unroll
  for(int k=0;k<=1;++k) {
    retVal = mp_mul( &(mpB[2]), &(mpR[k]), &mpT1 );  // 1st term
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
    retVal = mp_mul( &(mpR[2]), &(mpB[k]), &mpT2 );  // 2nd term
      if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
    mpT2.sign = -mpT2.sign;  // negate the 2nd term
    mp_add( &mpT1, &mpT2, &(mpR[k]) );  // Sum the terms
    }
////////////////////////////////////////////////////////////////////////////////


  // Determine the degree of R (it must be less than or equal to 1)
  int degR;
  if( mpR[1].used>0 )  degR=1;
  else                 degR=0;


  // From previous iteration, g=h=A[3]
  retVal = mp_mul( &(mpA[3]), &(mpA[3]), &mpT1 );  // Set T1 = g^2
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }


  // Set A = B
  //DegA[index] = 2;
  for(int k=0; k<=2; k++)  mp_copy( &(mpB[k]), &(mpA[k]) );

  // Set B = R/(g^2) (delta=1 and g=h)
  //DegB[index] = 1;
  retVal = mp_div( &(mpR[0]), &mpT1, &(mpB[0]), NULL );
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
  retVal = mp_div( &(mpR[1]), &mpT1, &(mpB[1]), NULL );
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }


#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("After iteration degB2:\n");
    printf("  A = "); mp_print_poly(mpA,2); printf("\n");
    printf("  B = "); mp_print_poly(mpB,1); printf("\n");
    printf("  g = "); mp_printf( mpA[2] ); printf("\n");
    printf("  h = "); mp_printf( mpA[2] ); printf("\n\n");
    }
#endif


  // If degR=0 then we are done.  Set the polDisc value and return.
  if( degR==0 ) {  // h=g=A[2]
    if( IS_ZERO(mpB) ) { validFlag[index] = FALSE; return; }
    mp_int *polDisc;
    polDisc = &(mpA[2]);  // Set polDisc = h = A[2]
    polDisc->sign = MP_ZPOS;  // Make sure the discriminant is positive.
    mp_copy(polDisc, &(polDiscArray[index]));  // Store in device memory.
    #ifdef DEBUG
      if(index==DBG_THREAD) { printf("polDisc = ");  mp_printf(*polDisc); printf("\n"); }
    #endif
    return;
    }


  // If we make it this far, then degR=1.  We complete the sub-resultant calculation


  ////////////////////////////////////////////////////////////////////////////////
  // Compute new R.
  // What follows is the mp equivalent of this:
  //    int64_t R[2];
  //    R[0] = B[1]*A[0];
  //    R[1] = B[1]*A[1] - A[2]*B[0];
  //    R[0] = B[1]*R[0] - R[1]*B[0];

  retVal = mp_mul( &(mpB[1]), &(mpA[0]), &(mpR[0]) );
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
  retVal = mp_mul( &(mpB[1]), &(mpA[1]), &mpT1 );  // 1st term
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
  retVal = mp_mul( &(mpA[2]), &(mpB[0]), &mpT2 );  // 2nd term
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
  mpT2.sign = -mpT2.sign;  // negate the 2nd term
  mp_add( &mpT1, &mpT2, &(mpR[1]) );  // Sum the terms

  retVal = mp_mul( &(mpB[1]), &(mpR[0]), &mpT1 );  // 1st term
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
  retVal = mp_mul( &(mpR[1]), &(mpB[0]), &mpT2 );  // 2nd term
    if ( retVal == MP_MEM )  { validFlag[index] = MEM_ERR; return; }
  mpT2.sign = -mpT2.sign;  // negate the 2nd term
  mp_add( &mpT1, &mpT2, &(mpR[0]) );  // Sum the terms

  ////////////////////////////////////////////////////////////////////////////////


  // Set A = B
  //mp_copy( &(mpB[0]), &(mpA[0]) );
  //mp_copy( &(mpB[1]), &(mpA[1]) );

  // Since we don't care about square factors, we could ignore this last division by g^2;
  // however, this actually slows down the later stages since polDisc would be much larger.
  // Set B = R/(g^2) (delta=1 and g=h) where from previous iteration, g=A[2]
  mp_mul( &(mpA[2]), &(mpA[2]), &mpT1 );  // Set T1 = g^2
  mp_div( &(mpR[0]), &mpT1, &(mpR[0]), NULL );


#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("Sub-resultant complete:\n");
    printf("  A = "); mp_print_poly(mpB,1); printf("\n"); // A is B
    printf("  B = "); mp_printf(mpR[0]); printf("\n\n");  // B is R
    }
#endif


  // Now complete the polDisc calculation.
  if( IS_ZERO(mpR) ) { validFlag[index] = FALSE; return; }
  mp_int *polDisc;
  polDisc = &(mpR[0]);   // Set polDisc = R[0]
  polDisc->sign = MP_ZPOS;  // Make sure the discriminant is positive.
  mp_copy(polDisc, &(polDiscArray[index]));  // Store in device memory.


#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("polDisc = ");  mp_printf(*polDisc); printf("\n");
    }
#endif

}  // End of pdtKernel_sr_degB2






// NOTE:   This function is now deprecated.
// This kernel completes the sub-resultant calculation.
__global__
void pdtKernel_sr_finish(int numPolys, char *validFlag, mp_int* polDiscArray, int *DegA, int *DegB, 
         mp_int *MPA, mp_int *MPB )
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;


#ifdef CUDA_PROFILER
  unsigned int time1 = clock();
#endif


  // Multi-precision declarations
  mp_int g, h, mpA[10], mpB[9], mpR[10], BR, SB[9];
  mp_int q, gPow, hPow, scale;


  // Copy data from gpu memory into local memory for this thread
  int degA = DegA[index];
  int degB = DegB[index];
  for(int col=0; col<=degA; col++)  mp_copy(&(MPA[index*10+col]), &(mpA[col]));
  for(int col=0; col<=degB; col++)  mp_copy(&(MPB[index*9 +col]), &(mpB[col]));
//  mp_copy(&(MPG[index]), &g);
//  mp_copy(&(MPG[index]), &h);

  // Set g = h = leading coeff of A
  mp_copy( &(mpA[degA]), &g );
  mp_copy( &(mpA[degA]), &h );



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





// NOTE: This function is now deprecated.
// CUDA kernel function to divide out factors of p1 and p2 from the polynomial discriminant.
__global__
void pdtKernel_divP(int numPolys, char *validFlag, mp_int* polDiscArray, int p1, int p2)
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;


  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;


  int numP, pSet[2] = {p1, p2};
  numP = (p1==p2) ? 1 : 2;


  // Extract polynomial discriminant for this thread
  mp_int polDisc;
  polDisc.used = polDiscArray[index].used;
  polDisc.sign = polDiscArray[index].sign;
  for (int n = 0; n<polDisc.used; n++)  polDisc.dp[n] = polDiscArray[index].dp[n];


  // Initialize local variables
  mp_int q;
  mp_zero(&q);


  // Divide out all factors of p for each prime in pSet
  for(int k=0; k<numP; k++)  {
    int thisP = pSet[k];

    if(thisP==2) {
      uint64_t N = polDisc.dp[0] & MP_MASK;
      while(N==0) {
        mp_div_2d( &polDisc, DIGIT_BIT, &polDisc, NULL ); // Set polDisc = polDisc/2^63
        N = polDisc.dp[0] & MP_MASK;
        }
      uint64_t pow2 = N & (-N);   // Power of 2 dividing N

      // pow2 = 2^d.  We need the power d.
      int d = 0;
      if( (pow2 & 0xFFFFFFFF)==0 ) { d  = 32; pow2 >>= 32; }
      if( (pow2 & 0xFFFF)==0 )     { d += 16; pow2 >>= 16; }
      if( (pow2 & 0xFF)==0 )       { d +=  8; pow2 >>= 8;  }
      if( (pow2 & 0xF)==0 )        { d +=  4; pow2 >>= 4;  }
      if( (pow2 & 0x3)==0 )        { d +=  2; pow2 >>= 2;  }
      if( (pow2 & 0x1)==0 )        { d +=  1; pow2 >>= 1;  }
      mp_div_2d( &polDisc, d, &polDisc, NULL ); // Set polDisc = polDisc/2^d

      /*
      // This is the DeBruijn Method for getting the power d, given 2^d.
      // It is a tad slower than the above method.
      int d = 0;
      static const int MultiplyDeBruijnBitPosition[32] = {
        0,  9,  1, 10, 13, 21,  2, 29, 11, 14, 16, 18, 22, 25, 3, 30,
        8, 12, 20, 28, 15, 17, 24,  7, 19, 27, 23,  6, 26,  5, 4, 31 };
      uint32_t v = (uint32_t)(pow2 & 0xFFFFFFFF);
      if( v==0 ) { d  = 32; v = (uint32_t)((pow2>>32) & 0xFFFFFFFF); }
      v |= v >> 1;
      v |= v >> 2;
      v |= v >> 4;
      v |= v >> 8;
      v |= v >> 16;
      d += MultiplyDeBruijnBitPosition[(uint32_t)(v*0x07C4ACDDU) >> 27];
      mp_div_2d( &polDisc, d, &polDisc, NULL ); // Set polDisc = polDisc/2^d
      */

      }

    else if(thisP==5) {
      // We handle 5 separately since polDisc can have many factors of 5.
      mp_digit rem;

      for(;;) {  // We remove 16 powers of 5 at a time
        mp_div_d( &polDisc, 152587890625, &q, &rem );  // polDisc = q*5^16 + rem
        if( rem!=0 ) break;  // Exit once there are no more factors of 5^16
        mp_copy( &q, &polDisc );  // Otherwise, since the remainder is zero, set polDisc = q
        }

      // Divide out 5^8
      mp_div_d( &polDisc, 390625, &q, &rem ); // polDisc = q*5^8 + rem
      if( rem==0 )  mp_copy( &q, &polDisc );

      // Divide out 5^4
      mp_div_d( &polDisc, 625, &q, &rem ); // polDisc = q*5^4 + rem
      if( rem==0 )  mp_copy( &q, &polDisc );

      // Divide out 5^2
      mp_div_d( &polDisc, 25, &q, &rem ); // polDisc = q*5^2 + rem
      if( rem==0 )  mp_copy( &q, &polDisc );

      // Divide out 5
      mp_div_d( &polDisc, 5, &q, &rem ); // polDisc = q*5 + rem
      if( rem==0 )  mp_copy( &q, &polDisc );

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
  mp_copy(&polDisc, &(polDiscArray[index]));

#ifdef DEBUG
  if(index==DBG_THREAD) {
    printf("Reduced polDisc = ");  mp_printf(polDisc); printf("\n");
    }
#endif

}  // End of pdtKernel_divP (now deprecated)





// CUDA kernel function to divide out factors of 2 from the polynomial discriminant.
__global__
void pdtKernel_div2(int numPolys, char *validFlag, mp_int* polDiscArray)
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;


  // Extract polynomial discriminant for this thread
  mp_int polDisc;
//  polDisc.used = polDiscArray[index].used;
//  polDisc.sign = polDiscArray[index].sign;
//  for (int n = 0; n<polDisc.used; n++)  polDisc.dp[n] = polDiscArray[index].dp[n];
  mp_copy( &(polDiscArray[index]), &polDisc );


  uint64_t N = polDisc.dp[0];
  while(N==0) {
    mp_div_2d( &polDisc, DIGIT_BIT, &polDisc, NULL ); // Set polDisc = polDisc/2^63
    N = polDisc.dp[0];
    }
  uint64_t pow2 = N & (-N);   // Power of 2 dividing N

  // pow2 = 2^d.  We need the power d.
  int d = 0;
  if( (pow2 & 0xFFFFFFFF)==0 ) { d  = 32; pow2 >>= 32; }
  if( (pow2 & 0xFFFF)==0 )     { d += 16; pow2 >>= 16; }
  if( (pow2 & 0xFF)==0 )       { d +=  8; pow2 >>= 8;  }
  if( (pow2 & 0xF)==0 )        { d +=  4; pow2 >>= 4;  }
  if( (pow2 & 0x3)==0 )        { d +=  2; pow2 >>= 2;  }
  if( (pow2 & 0x1)==0 )        { d +=  1; pow2 >>= 1;  }
  mp_div_2d( &polDisc, d, &polDisc, NULL ); // Set polDisc = polDisc/2^d
 
  // Put modified discriminant back into device memory
  mp_copy(&polDisc, &(polDiscArray[index]));

  #ifdef DEBUG
    if(index==DBG_THREAD) {
      printf("After removing all factors of 2, polDisc = ");  mp_printf(polDisc); printf("\n");
      }
  #endif

}  // End of pdtKernel_div2





// CUDA kernel function to divide out factors of 5 from the polynomial discriminant.
__global__
void pdtKernel_div5(int numPolys, char *validFlag, mp_int* polDiscArray)
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;

  // Extract polynomial discriminant for this thread
  mp_int polDisc;
  mp_copy( &(polDiscArray[index]), &polDisc );

  // Initialize local variables
  mp_digit rem;
  mp_int q;
  mp_zero(&q);


  for(;;) {  // We remove 16 powers of 5 at a time
    mp_div_d_gpu( &polDisc, 152587890625, &q, &rem );  // polDisc = q*5^16 + rem
    if( rem!=0 ) break;  // Exit once there are no more factors of 5^16
    mp_copy( &q, &polDisc );  // Otherwise, since the remainder is zero, set polDisc = q
    }

  // Divide out 5^8
  mp_div_d_gpu( &polDisc, 390625, &q, &rem ); // polDisc = q*5^8 + rem
  if( rem==0 )  mp_copy( &q, &polDisc );

  // Divide out 5^4
  mp_div_d_gpu( &polDisc, 625, &q, &rem ); // polDisc = q*5^4 + rem
  if( rem==0 )  mp_copy( &q, &polDisc );

  // Divide out 5^2
  mp_div_d_gpu( &polDisc, 25, &q, &rem ); // polDisc = q*5^2 + rem
  if( rem==0 )  mp_copy( &q, &polDisc );

  // Divide out 5
  mp_div_d_gpu( &polDisc, 5, &q, &rem ); // polDisc = q*5 + rem
  if( rem==0 )  mp_copy( &q, &polDisc );


  // Put modified discriminant back into device memory
  mp_copy(&polDisc, &(polDiscArray[index]));

  #ifdef DEBUG
    if(index==DBG_THREAD) {
      printf("After removing all factors of 5, polDisc = ");  mp_printf(polDisc); printf("\n");
      }
  #endif

}  // End of pdtKernel_div5





// CUDA kernel function to divide out factors of 2 and 5 from the polynomial discriminant.
__global__
void pdtKernel_div25(int numPolys, char *validFlag, mp_int* polDiscArray)
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;


  // Extract polynomial discriminant for this thread
  mp_int polDisc;
//  polDisc.used = polDiscArray[index].used;
//  polDisc.sign = polDiscArray[index].sign;
//  for (int n = 0; n<polDisc.used; n++)  polDisc.dp[n] = polDiscArray[index].dp[n];
  mp_copy( &(polDiscArray[index]), &polDisc );


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // First divide out factors of 2

  uint64_t N = polDisc.dp[0];
  while(N==0) {
    mp_div_2d( &polDisc, DIGIT_BIT, &polDisc, NULL ); // Set polDisc = polDisc/2^63
    N = polDisc.dp[0];
    }
  uint64_t pow2 = N & (-N);   // Power of 2 dividing N

  // pow2 = 2^d.  We need the power d.
  int d = 0;
  if( (pow2 & 0xFFFFFFFF)==0 ) { d  = 32; pow2 >>= 32; }
  if( (pow2 & 0xFFFF)==0 )     { d += 16; pow2 >>= 16; }
  if( (pow2 & 0xFF)==0 )       { d +=  8; pow2 >>= 8;  }
  if( (pow2 & 0xF)==0 )        { d +=  4; pow2 >>= 4;  }
  if( (pow2 & 0x3)==0 )        { d +=  2; pow2 >>= 2;  }
  if( (pow2 & 0x1)==0 )        { d +=  1; pow2 >>= 1;  }
  mp_div_2d( &polDisc, d, &polDisc, NULL ); // Set polDisc = polDisc/2^d


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Then divide out factors of 5 

  mp_digit rem;
  mp_int q;
  mp_zero(&q);

  for(;;) {  // We remove 16 powers of 5 at a time
    mp_div_d_gpu( &polDisc, 152587890625, &q, &rem );  // polDisc = q*5^16 + rem
    if( rem!=0 ) break;  // Exit once there are no more factors of 5^16
    mp_copy( &q, &polDisc );  // Otherwise, since the remainder is zero, set polDisc = q
    }

  // Divide out 5^8
  mp_div_d_gpu( &polDisc, 390625, &q, &rem ); // polDisc = q*5^8 + rem
  if( rem==0 )  mp_copy( &q, &polDisc );

  // Divide out 5^4
  mp_div_d_gpu( &polDisc, 625, &q, &rem ); // polDisc = q*5^4 + rem
  if( rem==0 )  mp_copy( &q, &polDisc );

  // Divide out 5^2
  mp_div_d_gpu( &polDisc, 25, &q, &rem ); // polDisc = q*5^2 + rem
  if( rem==0 )  mp_copy( &q, &polDisc );

  // Divide out 5
  mp_div_d_gpu( &polDisc, 5, &q, &rem ); // polDisc = q*5 + rem
  if( rem==0 )  mp_copy( &q, &polDisc );

  //////////////////////////////////////////////////////////////////////////////////////////////////


  // Put modified discriminant back into device memory
  mp_copy(&polDisc, &(polDiscArray[index]));

  #ifdef DEBUG
    if(index==DBG_THREAD) {
      printf("After removing all factors of 2 and 5, polDisc = ");  mp_printf(polDisc); printf("\n");
      }
  #endif

}  // End of pdtKernel_div25






// CUDA kernel function to divide out factors of P from the polynomial discriminant.
__global__
void pdtKernel_divPgen(int numPolys, char *validFlag, mp_int* polDiscArray, int P )
{
  int index = blockIdx.x * blockDim.x + threadIdx.x;

  // Valid indices are 0 through numPolys-1.  Exit if this is an invalid index.
  // This can happen if numPolys is not equal to numBlocks * threadsPerBlock.
  if(index>numPolys-1 || validFlag[index]!=TRUE) return;

  // Extract polynomial discriminant for this thread
  mp_int polDisc;
  mp_copy( &(polDiscArray[index]), &polDisc );

  // Initialize local variables
  mp_digit rem;
  mp_int q;
  mp_zero(&q);

  // Remove factors of P, one at a time.
  for(;;) {
    mp_div_d_gpu( &polDisc, P, &q, &rem );  // polDisc = q*P + rem
    if( rem!=0 ) break;  // Exit once there are no more factors of P
    mp_copy( &q, &polDisc );  // Otherwise, since the remainder is zero, set polDisc = q
    }

  // Put modified discriminant back into device memory
  mp_copy(&polDisc, &(polDiscArray[index]));

  #ifdef DEBUG
    if(index==DBG_THREAD) {
      printf("After removing all factors of %d, polDisc = ", P);  mp_printf(polDisc); printf("\n");
      }
  #endif

}  // End of pdtKernel_divPgen





// CUDA kernel function to determine if poly disc is a perfect square.  This will complete the pol disc test.
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
void pdtKernel_perfSqTest(int numPolys, char *validFlag, mp_int* polDiscArray)
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
  mp_div_d_gpu( &polDisc, 2882880, NULL, &rem );

//    __syncwarp();


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
  mp_div_d_gpu( &polDisc, 6678671, NULL, &rem );

//    __syncwarp();

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
    for (int k=0;k<numPolysPrev;k++)  polGoodFlag[k] = gpuFlagBuffer[k];

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


  if(numP>2) { printf("Error: This function only supports 2 primes max."); return FAIL; }
  int doP2=0, doP5=0, doPgen=0;
  for( int k=0; k<numP; ++k) {
    if(pSet[k]==2) doP2 = 1;
    if(pSet[k]==5) doP5 = 1;
    }
  if( (doP2+doP5)<numP )  doPgen = 1;


  // Copy polynomials to the device memory
  for (int row = 0; row < numPolys; row++) {
    for (int col = 0; col < 11; col++) {
      gpuPolyBuffer[row*11+col] = polBuf[row][col];
    }
  }


  int numBlocksNew = (numPolys + threadsPerBlock - 1) / threadsPerBlock;


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Launch stage 1 threads
  //

  pdtKernel_sr_init<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, gpuPolyBuffer, gpuPolyA, gpuPolyB, gpuDegA, gpuDegB, gpuG, gpuH);
  CUDACHECK;

  pdtKernel_sr_degB8<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, gpuPolyA, gpuPolyB, gpuDegA, gpuDegB, gpuG, gpuH);
  CUDACHECK;

  pdtKernel_sr_degB7<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, gpuPolyA, gpuPolyB, gpuDegA, gpuDegB, gpuG, gpuH, gpuScale);
  CUDACHECK;

  // At this point we may assume degB<7.  (degA arbitrary)

  pdtKernel_sr_degB6degA9<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, gpuPolyA, gpuPolyB, gpuDegA, gpuDegB, gpuG, gpuH, gpuScale);
  CUDACHECK;

  // That is as much as we can do with 64bits.  We now move to multi-precision.

  // Initialize the multi-precision variables
  pdtKernel_sr_mpInit<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, gpuFlagBuffer, gpuPolyA, gpuPolyB, gpuDegA, gpuDegB, gpuScale, gpu_mpA, gpu_mpB);
  CUDACHECK;

  // Do the degB=6, degA=8 case.
  pdtKernel_sr_degB6degA8<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, gpuDegA, gpuDegB, gpu_mpA, gpu_mpB, gpuG, gpuH );
  CUDACHECK;

  // Do the degB=6, degA=7 case.
  pdtKernel_sr_degB6degA7<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, gpuDegA, gpuDegB, gpu_mpA, gpu_mpB, gpuG, gpuH );
  CUDACHECK;

  // At this point we may assume degB<6.  (degA arbitrary)

  // Do the degB=5, degA=6 case.
  pdtKernel_sr_degB5<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, gpuFlagBuffer, gpuDegA, gpuDegB, gpu_mpA, gpu_mpB, gpuG, gpuH );
  CUDACHECK;


  // We can complete in two different ways.  Method 2 appears to be faster.
  if(0) {  // METHOD 1
    // Do the degB=4, degB=3, and degB=2 cases in the same kernel.
    // This kernel will complete the polDisc computation and store it in gpuDiscBuffer
    pdtKernel_sr_degB4_3_2<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, gpuFlagBuffer, gpuDiscBuffer, gpuDegA, gpuDegB, gpu_mpA, gpu_mpB );
    CUDACHECK;
    }
  else { //METHOD 2
    // Do the degB=4, degA=5 case.
    pdtKernel_sr_degB4<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, gpuFlagBuffer, gpuDegA, gpuDegB, gpu_mpA, gpu_mpB );
    CUDACHECK;

    // Do the degB=3, degA=4 case.
    pdtKernel_sr_degB3<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, gpuFlagBuffer, gpuDegA, gpuDegB, gpu_mpA, gpu_mpB );
    CUDACHECK;

    // Do the degB=2, degA=3 case.
    // This kernel will complete the polDisc computation and store it in gpuDiscBuffer
    pdtKernel_sr_degB2<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, gpuFlagBuffer, gpuDiscBuffer, gpuDegA, gpuDegB, gpu_mpA, gpu_mpB );
    CUDACHECK;
    }

//  pdtKernel_sr_finish<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, gpuFlagBuffer, gpuDiscBuffer, gpuDegA, gpuDegB, gpu_mpA, gpu_mpB, gpuG, gpuH );
//  CUDACHECK;


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Launch stage 2 threads
  //

  // Divide out factors of 2
  if(doP2) {
    pdtKernel_div2<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, gpuFlagBuffer, gpuDiscBuffer);
    CUDACHECK;
    }

  // Divide out factors of 5
  if(doP5) {
    pdtKernel_div5<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, gpuFlagBuffer, gpuDiscBuffer);
    CUDACHECK;
    }

  // Divide out any general prime factors from pSet that are not 2 or 5.
  if(doPgen) {
    for( int k=0; k<numP; ++k) {
      if(pSet[k]!=2 && pSet[k]!=5) {
        pdtKernel_divPgen<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, gpuFlagBuffer, gpuDiscBuffer, pSet[k]);
        CUDACHECK;
        }
      }
    }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //
  // Launch stage 3 threads
  //

  //printf("Launching Stage 3.\n\n");
  pdtKernel_perfSqTest<<<numBlocksNew, threadsPerBlock, 0, pdtStream>>>(numPolys, gpuFlagBuffer, gpuDiscBuffer);
  CUDACHECK;
  #ifdef DEBUG
    cudaStreamSynchronize(pdtStream);  // We only do this for debug in order to flush the printf buffers
    CUDACHECK;
  #endif


#ifdef CUDA_PROFILER
  cudaProfilerStop();
#endif


  // If we make it this far, we assume success.  So return 0.
  return 0;

  }
