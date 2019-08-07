// A multi-precision integer system for GPUs
// This version uses a 64bit digit and 128bit word.
// Currently only works with Cuda.
// Hacked together from LibTomMath by hard coding the precision.
//
//
// WARNING: This file should not be used outside of GPUs.  The typedefs below are safe
//          according to the OpenCL standard (long=64bit and int=32bit).  This is true
//          for all versions of OpenCL, even 1.0.  Since long is 32 bits in windows, 
//          this code will fail if compiled for a windows target (gpu on windows host 
//          is ok since that would abide by the OpenCL standard).



#ifndef GPUMULTIPREC_H
#define GPUMULTIPREC_H


#ifdef CUDA
  #ifndef __CUDA_ARCH__
    #define __CUDA_ARCH__
  #endif
  /* These includes are to get CHAR_BIT, uint32_t, and uint64_t. */
  #include <limits.h>
  #include <stdint.h>
  #include "cuda_uint128.h"
#endif

#ifdef OPENCL
//  #include <CL/opencl.h>
//  #include <CL/opencl-c.h>  // NULL should be defined in here
//  OpenCL does not like including system headers, so explicitly set what we need.
  #ifndef CHAR_BIT
    #define CHAR_BIT 8  // CHAR_BIT is the number of bits in a CHAR
  #endif
  #ifndef NULL
    #define NULL ((void*)0)  // AMD's implementation does not define NULL
  #endif
  #ifndef MINGW
    typedef unsigned int    uint32_t;
    typedef unsigned long   uint64_t;
    typedef long            int64_t;
  #endif
  #define __device__   // This will turn off the "__device__" qualifier that cuda needs.
#endif


#ifndef MIN
#define MIN(x, y) (((x) < (y)) ? (x) : (y))
#endif


// This is the hard-coded amount of precision to be used.
// It is the number of mp_digits. A "digit" is 64bits.
// But only 63 bits of each digit is actually used.  So 63*12 = 756 bits max.
// EDD 8-5-19: Noticed some sf4_DS15x271 cases were failing with memory errors,
//             so bumped precision up to 15 (63*15=945 bits)
#define MP_PREC  15

#define MP_OKAY       0   /* ok result */
#define MP_VAL       -3   /* invalid input */
#define MP_ZPOS       0   /* positive integer */
#define MP_NEG        1   /* negative */
#define MP_MEM       -2   /* out of mem */

/* equalities */
#define MP_LT        -1   /* less than */
#define MP_EQ         0   /* equal to */
#define MP_GT         1   /* greater than */

/* ---> Basic Manipulations <--- */
#define IS_ZERO(a) ((a)->used == 0)
#define IS_EVEN(a) (((a)->used == 0) || (((a)->dp[0] & 1u) == 0u))
#define IS_ODD(a)  (((a)->used > 0) && (((a)->dp[0] & 1u) == 1u))


typedef uint64_t   mp_digit;
typedef uint128_t  mp_word;
#define DIGIT_BIT 63
#define MP_MASK  ((((mp_digit)1)<<((mp_digit)DIGIT_BIT))-((mp_digit)1))

/* size of comba arrays, should be at least 2 * 2**(BITS_PER_WORD - BITS_PER_DIGIT*2) */
#define MP_WARRAY  8


/* This is the structure that defines the multi-precision data type */
typedef struct  {
   int used, sign;
   mp_digit dp[MP_PREC];
} mp_int;



// Function Prototypes
__device__ int  mp_init(mp_int*);
__device__ void mp_zero(mp_int*);
__device__ void mp_set(mp_int*, mp_digit);
__device__ void mp_set_vec_int64(mp_int*, int64_t*, int);
__device__ int  mp_set_int64(mp_int*, int64_t);
__device__ int  mp_set_ull(mp_int*, uint64_t);
__device__ void mp_clamp(mp_int*);
__device__ int  mp_copy(mp_int*, mp_int*);
__device__ int  mp_copy_vec(mp_int*, mp_int*, int);
__device__ int  mp_count_bits(mp_int*);
__device__ int  mp_cmp(mp_int*, mp_int*);
__device__ int  mp_cmp_mag(mp_int*, mp_int*);
__device__ int  mp_lshd(mp_int*, int);
__device__ void mp_rshd(mp_int*, int);
__device__ int  mp_add(mp_int*, mp_int*, mp_int*);
__device__ int  mp_sub(mp_int*, mp_int*, mp_int*);
__device__ int  s_mp_add(mp_int*, mp_int*, mp_int*);
__device__ int  s_mp_sub(mp_int*, mp_int*, mp_int*);
__device__ int  mp_mul(mp_int*, mp_int*, mp_int*);
__device__ int  s_mp_mul_digs(mp_int*, mp_int*, mp_int*, int);
__device__ int  fast_s_mp_mul_digs(mp_int*, mp_int*, mp_int*, int);
__device__ int  mp_mul_d(mp_int*, mp_digit, mp_int*);
__device__ int  mp_mul_2d(mp_int*, int, mp_int*);
__device__ int  mp_div(mp_int*, mp_int*, mp_int*, mp_int*);
__device__ int  mp_div_d(mp_int*, mp_digit, mp_int*, mp_digit*);
__device__ int  mp_mod_d(mp_int*, mp_digit, mp_digit*);
__device__ int  mp_div_2(mp_int*, mp_int*);
__device__ int  mp_div_2d(mp_int*, int, mp_int*, mp_int*);
__device__ int  mp_mod_2d(mp_int*, int, mp_int*);
#ifdef PRINTF_ENABLED
__device__ int  mp_toradix(mp_int*, char*, int);
__device__ void bn_reverse(unsigned char*, int);
__device__ void mp_printf(mp_int);
__device__ void mp_print_poly(mp_int*, int);
#endif


__device__ inline
int mp_init(mp_int *a)
{
   /* set the digits to zero */
//#pragma unroll
   for (int i = 0; i < MP_PREC; i++)  a->dp[i] = 0;

   /* set the used to zero and sign to positive */
   a->used  = 0;
   a->sign  = MP_ZPOS;

   return MP_OKAY;
}



/* set to zero */
__device__ inline
void mp_zero(mp_int *a)
{
   a->sign = MP_ZPOS;
   a->used = 0;

//#pragma unroll
   for (int i = 0; i < MP_PREC; i++)  a->dp[i] = 0;
}



// This only works on positive inputs and assumes b fits within 63bits
__device__ inline
void mp_set(mp_int *a, mp_digit b)
{
   a->dp[0] = b;
//#pragma unroll
   for (int i = 1; i < MP_PREC; i++)  a->dp[i] = 0;

   a->sign = MP_ZPOS;
   a->used  = (a->dp[0] != 0) ? 1 : 0;
}



/* Use this to initialize a vector of mp_ints from a vector of type int64 */
__device__ inline
void mp_set_vec_int64(mp_int *a, int64_t *b, int numElem)
{
//#pragma unroll
   for (int k = 0; k < numElem; k++)  mp_set_int64(&(a[k]), b[k]);
}



__device__ inline
int mp_set_int64(mp_int *a, int64_t b)
{
   int sgn = 1;
   if(b<0) {
      b=-b;
      sgn = -1;
      }
   mp_set(a, b);
   if(sgn==-1)  a->sign = MP_NEG;

   return MP_OKAY;
}




/* trim unused digits
 *
 * This is used to ensure that leading zero digits are trimed and the leading "used" digit will
 * be non-zero.  Typically very fast.  Also fixes the sign if there are no more leading digits.
 */
__device__ inline
void mp_clamp(mp_int *a)
{
   /* decrease used while the most significant digit is zero. */
   //   while ((a->used > 0) && (a->dp[a->used - 1] == 0u))  --(a->used);
   int k;
   for (k=a->used-1; k>=0; --k) { if(a->dp[k] != 0)  break; }
   a->used = k+1;

   /* reset the sign flag if used == 0 */
   if (a->used == 0)  a->sign = MP_ZPOS;
}



/* copy, b = a */
__device__ inline
int mp_copy(mp_int *a, mp_int *b)
{
   /* if dst == src do nothing */
   //if (a == b)  return MP_OKAY;

   // I thought this would keep threads in lock-step, but it actually made the code slower.
   //for (int n = 0; n < MP_PREC; n++)  b->dp[n] = a->dp[n];

   int n;
   for (n = 0; n < a->used; n++)  b->dp[n] = a->dp[n];
   //for (; n < b->used; n++)  b->dp[n] = 0;
   for (; n < MP_PREC; n++)  b->dp[n] = 0;

   /* copy used count and sign */
   b->used = a->used;
   b->sign = a->sign;
   return MP_OKAY;
}


/* copy a vector of mp_ints */
__device__ inline
int mp_copy_vec(mp_int *a, mp_int *b, int numElem)
{
   for (int k = 0; k < numElem; k++)  mp_copy(&(a[k]), &(b[k]));
   return MP_OKAY;
}



/* returns the number of bits in an int */
__device__ inline
int mp_count_bits(mp_int *a)
{
   int r;
   mp_digit q;

   /* shortcut */
   if (IS_ZERO(a))  return 0;

   /* get number of digits and add that */
   r = (a->used - 1) * DIGIT_BIT;

   /* take the last digit and count the bits in it */
   q = a->dp[a->used - 1];
   while (q > (mp_digit)0) {
      ++r;
      q >>= (mp_digit)1;
   }
   return r;
}



/* compare two ints (signed)*/
__device__ inline
int mp_cmp(mp_int *a, mp_int *b)
{
   /* compare based on sign */
   if (a->sign != b->sign) {
      if (a->sign == MP_NEG)  return MP_LT;
      else                    return MP_GT;
   }

   /* compare digits */
   /* if negative compare opposite direction */
   if (a->sign == MP_NEG)  return mp_cmp_mag(b, a);
   else                    return mp_cmp_mag(a, b);
}



/* compare maginitude of two ints (unsigned) */
__device__ inline
int mp_cmp_mag(mp_int *a, mp_int *b)
{
   mp_digit *tmpa, *tmpb;

   /* compare based on # of non-zero digits */
   if (a->used > b->used)  return MP_GT;
   if (a->used < b->used)  return MP_LT;

   /* alias for a */
   tmpa = a->dp + (a->used - 1);

   /* alias for b */
   tmpb = b->dp + (a->used - 1);

   /* compare based on digits  */
#pragma unroll
   for (int n = 0; n < a->used; ++n, --tmpa, --tmpb) {
      if (*tmpa > *tmpb)  return MP_GT;
      if (*tmpa < *tmpb)  return MP_LT;
   }
   return MP_EQ;
}



/* shift left a certain amount of digits */
__device__ inline
int mp_lshd(mp_int *a, int b)
{
   int x;

   /* if its less than zero return */
   if (b <= 0)  return MP_OKAY;

   /* no need to shift 0 around */
   if (IS_ZERO(a))  return MP_OKAY;

   mp_digit *top, *bottom;

   /* exit with error if set precision is exceeded */
   if ( (a->used+b) > MP_PREC)  return MP_MEM;

   /* increment the used by the shift amount then copy upwards */
   a->used += b;

   /* top */
   top = a->dp + a->used - 1;

   /* base */
   bottom = (a->dp + a->used - 1) - b;

   /* much like mp_rshd this is implemented using a sliding window
    * except the window goes the otherway around.  Copying from
    * the bottom to the top.  see bn_mp_rshd.c for more info.
    */
#pragma unroll
   for (x = a->used - 1; x >= b; x--)  *top-- = *bottom--;

   /* zero the lower digits */
   top = a->dp;
#pragma unroll
   for (x = 0; x < b; x++)  *top++ = 0;

   return MP_OKAY;
}



/* shift right a certain amount of digits */
__device__ inline
void mp_rshd(mp_int *a, int b)
{
   int x;

   /* if b <= 0 then ignore it */
   if (b <= 0)  return;

   /* if b > used then simply zero it and return */
   if (a->used <= b) {
      mp_zero(a);
      return;
   }

   mp_digit *bottom, *top;

   /* bottom */
   bottom = a->dp;

   /* top [offset into digits] */
   top = a->dp + b;

   /* this is implemented as a sliding window where
    * the window is b-digits long and digits from
    * the top of the window are copied to the bottom
    *
    * e.g.

    b-2 | b-1 | b0 | b1 | b2 | ... | bb |   ---->
                /\                   |      ---->
                 \-------------------/      ---->
    */
#pragma unroll
   for (x = 0; x < (a->used - b); x++)  *bottom++ = *top++;

   /* zero the top digits */
#pragma unroll
   for (; x < a->used; x++)  *bottom++ = 0;

   /* remove excess digits */
   a->used -= b;
}



/* high level addition (handles signs) */
__device__ inline
int mp_add(mp_int *a, mp_int *b, mp_int *c)
{
   /* handle two cases, not four */
   if ( a->sign == b->sign ) {
      /* both positive or both negative */
      /* add their magnitudes, copy the sign */
      c->sign = a->sign;
      return( s_mp_add(a, b, c) );
   } else {
      /* one positive, the other negative */
      /* subtract the one with the greater magnitude from */
      /* the one of the lesser magnitude.  The result gets */
      /* the sign of the one with the greater magnitude. */
      if (mp_cmp_mag(a, b) == MP_LT) {
         c->sign = b->sign;
         return( s_mp_sub(b, a, c) );
      } else {
         c->sign = a->sign;
         return( s_mp_sub(a, b, c) );
      }
   }
}



/* high level subtraction (handles signs)  c = a - b */
__device__ inline
int mp_sub(mp_int *a, mp_int *b, mp_int *c)
{
   if ( a->sign != b->sign ) {
      /* subtract a negative from a positive, OR */
      /* subtract a positive from a negative. */
      /* In either case, ADD their magnitudes, */
      /* and use the sign of the first number. */
      c->sign = a->sign;
      return( s_mp_add(a, b, c) );
   } else {
      /* subtract a positive from a positive, OR */
      /* subtract a negative from a negative. */
      /* First, take the difference between their */
      /* magnitudes, then... */
      if (mp_cmp_mag(a, b) != MP_LT) {
         /* Copy the sign from the first */
         c->sign = a->sign;
         /* The first has a larger or equal magnitude */
         return( s_mp_sub(a, b, c) );
      } else {
         /* The result has the *opposite* sign from */
         /* the first number. */
         c->sign = (a->sign == MP_ZPOS) ? MP_NEG : MP_ZPOS;
         /* The second has a larger magnitude */
         return( s_mp_sub(b, a, c) );
      }
   }
}



/* low level addition, based on HAC pp.594, Algorithm 14.7 */
__device__ inline
int s_mp_add(mp_int *a, mp_int *b, mp_int *c)
{
   const mp_int *x;
   int i, olduse, min, max;

   /* find sizes, we let |a| <= |b| which means we have to sort
    * them.  "x" will point to the input with the most digits
    */
   if (a->used > b->used) {
      min = b->used;
      max = a->used;
      x = a;
   } else {
      min = a->used;
      max = b->used;
      x = b;
   }

   /* exit with error if set precision is exceeded */
   if ( max+1 > MP_PREC)  return MP_MEM;

   /* get old used digit count and set new one */
   olduse = c->used;
   c->used = max + 1;

   mp_digit u, *tmpa, *tmpb, *tmpc;

   /* first input */
   tmpa = a->dp;

   /* second input */
   tmpb = b->dp;

   /* destination */
   tmpc = c->dp;

   /* zero the carry */
   u = 0;
#pragma unroll
   for (i = 0; i < min; i++) {
      /* Compute the sum at one digit, T[i] = A[i] + B[i] + U */
      *tmpc = *tmpa++ + *tmpb++ + u;

      /* U = carry bit of T[i] */
      u = *tmpc >> (mp_digit)DIGIT_BIT;

      /* take away carry bit from T[i] */
      *tmpc++ &= MP_MASK;
   }

   /* now copy higher words if any, that is in A+B
    * if A or B has more digits add those in
    */
   if (min != max) {
#pragma unroll
      for (; i < max; i++) {
         /* T[i] = X[i] + U */
         *tmpc = x->dp[i] + u;

         /* U = carry bit of T[i] */
         u = *tmpc >> (mp_digit)DIGIT_BIT;

         /* take away carry bit from T[i] */
         *tmpc++ &= MP_MASK;
      }
   }

   /* add carry */
   *tmpc++ = u;

   /* clear digits above oldused */
#pragma unroll
   for (i = c->used; i < olduse; i++)  *tmpc++ = 0;

   mp_clamp(c);
   return MP_OKAY;
}



/* low level subtraction (assumes |a| > |b|), HAC pp.595 Algorithm 14.9 */
__device__ inline
int s_mp_sub(mp_int *a, mp_int *b, mp_int *c)
{
   int i, olduse, min, max;

   /* find sizes */
   min = b->used;
   max = a->used;

   olduse = c->used;
   c->used = max;

   mp_digit u, *tmpa, *tmpb, *tmpc;

   /* alias for digit pointers */
   tmpa = a->dp;
   tmpb = b->dp;
   tmpc = c->dp;

   /* set carry to zero */
   u = 0;
#pragma unroll
   for (i = 0; i < min; i++) {
      /* T[i] = A[i] - B[i] - U */
      *tmpc = (*tmpa++ - *tmpb++) - u;

      /* U = carry bit of T[i]
       * Note this saves performing an AND operation since
       * if a carry does occur it will propagate all the way to the
       * MSB.  As a result a single shift is enough to get the carry
       */
      u = *tmpc >> (((size_t)CHAR_BIT * sizeof(mp_digit)) - 1u);

      /* Clear carry from T[i] */
      *tmpc++ &= MP_MASK;
   }

   /* now copy higher words if any, e.g. if A has more digits than B  */
#pragma unroll
   for (; i < max; i++) {
      /* T[i] = A[i] - U */
      *tmpc = *tmpa++ - u;

      /* U = carry bit of T[i] */
      u = *tmpc >> (((size_t)CHAR_BIT * sizeof(mp_digit)) - 1u);

      /* Clear carry from T[i] */
      *tmpc++ &= MP_MASK;
   }

   /* clear digits above used (since we may not have grown result above) */
#pragma unroll
   for (i = c->used; i < olduse; i++)  *tmpc++ = 0;

   mp_clamp(c);
   return MP_OKAY;
}



/* high level multiplication (handles sign) */
__device__ inline
int mp_mul(mp_int *a, mp_int *b, mp_int *c)
{
   int neg = (a->sign == b->sign) ? MP_ZPOS : MP_NEG;

   /* can we use the fast multiplier?
    *
    * The fast multiplier can be used if the output will
    * have less than MP_WARRAY digits and the number of
    * digits won't affect carry propagation
    */

   /* exit with error if required digits exceeds set precision */
   int digs = a->used + b->used + 1;
   if ( digs > MP_PREC)  return MP_MEM;

   int retVal;
   if ( (digs<8) && (MIN(a->used, b->used) <= 4) )
      retVal = fast_s_mp_mul_digs(a, b, c, digs);
   else
      retVal = s_mp_mul_digs(a, b, c, digs);

   c->sign = (c->used > 0) ? neg : MP_ZPOS;
   return retVal;
}



/* multiplies |a| * |b| and only computes upto digs digits of result
 * HAC pp. 595, Algorithm 14.12  Modified so you can control how
 * many digits of output are created.
 */
__device__ inline
int s_mp_mul_digs(mp_int *a, mp_int *b, mp_int *c, int digs)
{
   mp_int t;
   int pa, pb, ix, iy;
   mp_digit u;
   mp_word r;
   mp_digit tmpx, *tmpt, *tmpy;

   /* exit with error if set precision is exceeded */
   //if ( digs > MP_PREC)  return MP_MEM;

   mp_init(&t);
   t.used = digs;

   /* compute the digits of the product directly */
   pa = a->used;
#pragma unroll
   for (ix = 0; ix < pa; ix++) {
      /* set the carry to zero */
      u = 0;

      /* limit ourselves to making digs digits of output */
      pb = MIN(b->used, digs - ix);

      /* setup some aliases */
      /* copy of the digit from a used within the nested loop */
      tmpx = a->dp[ix];

      /* an alias for the destination shifted ix places */
      tmpt = t.dp + ix;

      /* an alias for the digits of b */
      tmpy = b->dp;

      /* compute the columns of the output and propagate the carry */
#pragma unroll
      for (iy = 0; iy < pb; iy++) {
         /* compute the column as a mp_word */
         //r = (mp_word)*tmpt + ((mp_word)tmpx * (mp_word)*tmpy++) + (mp_word)u;
         r = (mp_word)*tmpt + ((mp_word)tmpx * (*tmpy++)) + (mp_word)u;

         /* the new column is the lower part of the result */
         *tmpt++ = (mp_digit)(r & (mp_word)MP_MASK);

         /* get the carry word from the result */
         u = (mp_digit)(r >> DIGIT_BIT);
      }
      /* set carry if it is placed below digs */
      if ((ix + iy) < digs)  *tmpt = u;
   }

   mp_clamp(&t);

   // Since our structures are fixed size, we cant just swap pointers.
   //mp_exch(&t, c);
   mp_copy(&t, c);

   return MP_OKAY;
}



/* Fast (comba) multiplier
 *
 * This is the fast column-array [comba] multiplier.  It is
 * designed to compute the columns of the product first
 * then handle the carries afterwards.  This has the effect
 * of making the nested loops that compute the columns very
 * simple and schedulable on super-scalar processors.
 *
 * This has been modified to produce a variable number of
 * digits of output so if say only a half-product is required
 * you don't have to compute the upper half (a feature
 * required for fast Barrett reduction).
 *
 * Based on Algorithm 14.12 on pp.595 of HAC.
 *
 */
__device__ inline
int fast_s_mp_mul_digs(mp_int *a, mp_int *b, mp_int *c, int digs)
{
   int olduse, pa, ix, iz;
   mp_digit W[MP_WARRAY];
   mp_word  _W;

   /* exit with error if set precision is exceeded */
   //if ( digs > MP_PREC)  return MP_MEM;

   /* number of output digits to produce */
   pa = MIN(digs, a->used + b->used);

   /* clear the carry */
   _W = 0;
#pragma unroll
   for (ix = 0; ix < pa; ix++) {
      int tx, ty, iy;
      mp_digit *tmpx, *tmpy;

      /* get offsets into the two bignums */
      ty = MIN(b->used-1, ix);
      tx = ix - ty;

      /* setup temp aliases */
      tmpx = a->dp + tx;
      tmpy = b->dp + ty;

      /* this is the number of times the loop will iterrate, essentially
         while (tx++ < a->used && ty-- >= 0) { ... }
       */
      iy = MIN(a->used-tx, ty+1);

      /* execute loop */
#pragma unroll
      for (iz = 0; iz < iy; ++iz) {
//         _W += (mp_word)*tmpx++ * (mp_word)*tmpy--;
         _W += (mp_word)*tmpx++ * (*tmpy--);
      }

      /* store term */
      W[ix] = (mp_digit)_W & MP_MASK;

      /* make next carry */
      _W = _W >> DIGIT_BIT;
   }

   /* setup dest */
   olduse  = c->used;
   c->used = pa;

   mp_digit *tmpc;
   tmpc = c->dp;
#pragma unroll
   for (ix = 0; ix < pa; ix++) {
      /* now extract the previous digit [below the carry] */
      *tmpc++ = W[ix];
   }

   /* clear unused digits [that existed in the old copy of c] */
#pragma unroll
   for (; ix < olduse; ix++)  *tmpc++ = 0;

   mp_clamp(c);
   return MP_OKAY;
}



/* multiply by a digit */
__device__ inline
int mp_mul_d(mp_int *a, mp_digit b, mp_int *c)
{
   mp_digit u, *tmpa, *tmpc;
   mp_word  r;
   int ix, olduse;

   /* exit with error if set precision is exceeded */
   if ( (a->used+1) > MP_PREC)  return MP_MEM;

   /* get the original destinations used count */
   olduse = c->used;

   /* set the sign */
   c->sign = a->sign;

   /* alias for a->dp [source] */
   tmpa = a->dp;

   /* alias for c->dp [dest] */
   tmpc = c->dp;

   /* zero carry */
   u = 0;

   /* compute columns */
#pragma unroll
   for (ix = 0; ix < a->used; ix++) {
      /* compute product and carry sum for this term */
      //r = (mp_word)u + ((mp_word)*tmpa++ * (mp_word)b);
      r = (mp_word)u + ((mp_word)*tmpa++ * b);

      /* mask off higher bits to get a single digit */
      *tmpc++ = (mp_digit)(r & (mp_word)MP_MASK);

      /* send carry into next iteration */
      u = (mp_digit)(r >> DIGIT_BIT);
   }

   /* store final carry [if any] and increment ix offset  */
   *tmpc++ = u;
   ++ix;

   /* now zero digits above the top */
#pragma unroll
   while (ix++ < olduse)  *tmpc++ = 0;

   /* set used count */
   c->used = a->used + 1;
   mp_clamp(c);

   return MP_OKAY;
}



/* shift left by a certain bit count */
__device__ inline
int mp_mul_2d(mp_int *a, int b, mp_int *c)
{
   mp_digit d;

   /* copy */
   if (a != c)  mp_copy(a, c);

   /* exit with error if set precision is exceeded */
   if ( (c->used + (b/DIGIT_BIT) + 1) > MP_PREC)  return MP_MEM;

   /* shift by as many digits in the bit count */
   if (b >= DIGIT_BIT)  mp_lshd(c, b / DIGIT_BIT);

   /* shift any bit count < DIGIT_BIT */
   d = (mp_digit)(b % DIGIT_BIT);
   if (d != 0u) {
      mp_digit *tmpc, shift, mask, r, rr;
      int x;

      /* bitmask for carries */
      mask = ((mp_digit)1 << d) - (mp_digit)1;

      /* shift for msbs */
      shift = (mp_digit)DIGIT_BIT - d;

      /* alias */
      tmpc = c->dp;

      /* carry */
      r    = 0;
#pragma unroll
      for (x = 0; x < c->used; x++) {
         /* get the higher bits of the current word */
         rr = (*tmpc >> shift) & mask;

         /* shift the current word and OR in the carry */
         *tmpc = ((*tmpc << d) | r) & MP_MASK;
         ++tmpc;

         /* set the carry to the carry bits of the current word */
         r = rr;
      }

      /* set final carry */
      if (r != 0u)  c->dp[(c->used)++] = r;
   }
   mp_clamp(c);
   return MP_OKAY;
}




/* integer signed division.
 * c*b + d == a [e.g. a/b, c=quotient, d=remainder]
 * HAC pp.598 Algorithm 14.20
 *
 * Note that the description in HAC is horribly
 * incomplete.  For example, it doesn't consider
 * the case where digits are removed from 'x' in
 * the inner loop.  It also doesn't consider the
 * case that y has fewer than three digits, etc..
 *
 * The overall algorithm is as described as
 * 14.20 from HAC but fixed to treat these cases.
*/
__device__ inline
int mp_div(mp_int *a, mp_int *b, mp_int *c, mp_int *d)
{
   mp_int q, x, y, t1, t2;
   int n, t, i, norm, neg;

   /* is divisor zero ? */
   if (IS_ZERO(b))  return MP_VAL;

   /* if a < b then q=0, r = a */
   if (mp_cmp_mag(a, b) == MP_LT) {
      if (d != NULL)  mp_copy(a, d);
      if (c != NULL)  mp_zero(c);
      return MP_OKAY;
   }

   /* exit with error if set precision is exceeded */
   if ( (a->used+2) > MP_PREC)  return MP_MEM;

   mp_init(&q);
   q.used = a->used + 2;
   mp_init(&t1);
   mp_init(&t2);

   mp_init(&x);  mp_copy(a, &x);
   mp_init(&y);  mp_copy(b, &y);

   /* fix the sign */
   neg = (a->sign == b->sign) ? MP_ZPOS : MP_NEG;
   x.sign = y.sign = MP_ZPOS;

   /* normalize both x and y, ensure that y >= b/2, [b == 2**DIGIT_BIT] */
   norm = mp_count_bits(&y) % DIGIT_BIT;
   if (norm < (DIGIT_BIT - 1)) {
      norm = (DIGIT_BIT - 1) - norm;
      if( mp_mul_2d(&x, norm, &x) != MP_OKAY )  return MP_MEM;
      if( mp_mul_2d(&y, norm, &y) != MP_OKAY )  return MP_MEM;
   } else {
      norm = 0;
   }

   /* note hac does 0 based, so if used==5 then its 0,1,2,3,4, e.g. use 4 */
   n = x.used - 1;
   t = y.used - 1;

   /* while (x >= y*b**n-t) do { q[n-t] += 1; x -= y*b**{n-t} } */
   if( mp_lshd(&y, n - t) != MP_OKAY )  return MP_MEM;  /* y = y*b**{n-t} */

#pragma unroll
   while (mp_cmp(&x, &y) != MP_LT) {
      ++(q.dp[n - t]);
      mp_sub(&x, &y, &x);
   }

   /* reset y by shifting it back down */
   mp_rshd(&y, n - t);

   /* step 3. for i from n down to (t + 1) */
#pragma unroll
   for (i = n; i >= (t + 1); i--) {
      if (i > x.used)  continue;

      /* step 3.1 if xi == yt then set q{i-t-1} to b-1,
       * otherwise set q{i-t-1} to (xi*b + x{i-1})/yt */
      if (x.dp[i] == y.dp[t]) {
         q.dp[(i - t) - 1] = ((mp_digit)1 << (mp_digit)DIGIT_BIT) - (mp_digit)1;
      } else {
         mp_word tmp;
         tmp = (mp_word)x.dp[i] << DIGIT_BIT;
         tmp |= (mp_word)x.dp[i - 1];
         tmp = tmp / y.dp[t];
         if (tmp > (mp_word)MP_MASK)  tmp = MP_MASK;
         q.dp[(i - t) - 1] = (mp_digit)(tmp & (mp_word)MP_MASK);
      }

      /* while (q{i-t-1} * (yt * b + y{t-1})) > xi * b**2 + xi-1 * b + xi-2
         do q{i-t-1} -= 1;
      */
      q.dp[(i - t) - 1] = (q.dp[(i - t) - 1] + 1uL) & (mp_digit)MP_MASK;
      do {
         q.dp[(i - t) - 1] = (q.dp[(i - t) - 1] - 1uL) & (mp_digit)MP_MASK;

         /* find left hand */
         mp_zero(&t1);
         t1.dp[0] = ((t - 1) < 0) ? 0u : y.dp[t - 1];
         t1.dp[1] = y.dp[t];
         t1.used = 2;
         if( mp_mul_d(&t1, q.dp[(i - t) - 1], &t1) != MP_OKAY )  return MP_MEM;

         /* find right hand */
         t2.dp[0] = ((i - 2) < 0) ? 0u : x.dp[i - 2];
         t2.dp[1] = ((i - 1) < 0) ? 0u : x.dp[i - 1];
         t2.dp[2] = x.dp[i];
         t2.used = 3;
      } while (mp_cmp_mag(&t1, &t2) == MP_GT);

      /* step 3.3 x = x - q{i-t-1} * y * b**{i-t-1} */
      if( mp_mul_d(&y, q.dp[(i - t) - 1], &t1) != MP_OKAY )  return MP_MEM;
      if( mp_lshd(&t1, (i - t) - 1) != MP_OKAY )  return MP_MEM;
      mp_sub(&x, &t1, &x);

      /* if x < 0 then { x = x + y*b**{i-t-1}; q{i-t-1} -= 1; } */
      if (x.sign == MP_NEG) {
         mp_copy(&y, &t1);
         if( mp_lshd(&t1, (i - t) - 1) != MP_OKAY )  return MP_MEM;
         if( mp_add(&x, &t1, &x) != MP_OKAY )  return MP_MEM;
         q.dp[(i - t) - 1] = (q.dp[(i - t) - 1] - 1uL) & MP_MASK;
      }
   }

   /* now q is the quotient and x is the remainder[which we have to normalize] */

   /* get sign before writing to c */
   x.sign = (x.used == 0) ? MP_ZPOS : a->sign;

   if (c != NULL) {
      mp_clamp(&q);
      mp_copy(&q, c);
      c->sign = neg;
   }

   if (d != NULL) {
      mp_div_2d(&x, norm, &x, NULL);  /* This is safe from overflow */
      mp_copy(&x, d);
   }

   return MP_OKAY;
}



/* single digit division (based on routine from MPI) a = b*c + d  */
// I removed the power of 2 check (not needed for my use case)
__device__ inline
int mp_div_d(mp_int *a, mp_digit b, mp_int *c, mp_digit *d)
{
   mp_int  q;
   mp_word w;
   mp_digit t;
   int ix;

//printf("      Entering mp_div_d\n");

   /* cannot divide by zero */
   if (b == 0u)  return MP_VAL;

   /* quick outs */
   if ((b == 1u) || IS_ZERO(a)) {
      if (d != NULL)  *d = 0;
      if (c != NULL)  mp_copy(a, c);
      return MP_OKAY;
   }

   /* no easy answer [c'est la vie].  Just division */

   q.used = a->used;
   q.sign = a->sign;
   w = 0;

#pragma unroll
   for (ix = a->used - 1; ix >= 0; ix--) {
      w = (w << DIGIT_BIT) | (mp_word)a->dp[ix];
      if (w >= (mp_word)b) {
         t = (mp_digit)(w / b);
         w = w - (mp_word)t * b;
      } else {
         t = 0;
      }
      q.dp[ix] = t;
   }

   if (d != NULL)  *d = (mp_digit)w;

   if (c != NULL) {
      mp_clamp(&q);
      mp_copy(&q, c);
   }

   return MP_OKAY;
}


/* Given a and b, compute c:  a = c (mod b) */
__device__ inline
int mp_mod_d(mp_int *a, mp_digit b, mp_digit *c)
{
   return mp_div_d(a, b, NULL, c);
}



/* b = a/2 */
__device__ inline
int mp_div_2(mp_int *a, mp_int *b)
{
   int x, oldused;

   oldused = b->used;
   b->used = a->used;

   mp_digit r, rr, *tmpa, *tmpb;

   /* source alias */
   tmpa = a->dp + b->used - 1;

   /* dest alias */
   tmpb = b->dp + b->used - 1;

   /* carry */
   r = 0;
#pragma unroll
   for (x = b->used - 1; x >= 0; x--) {
      /* get the carry for the next iteration */
      rr = *tmpa & 1u;

      /* shift the current digit, add in carry and store */
      *tmpb-- = (*tmpa-- >> 1) | (r << (DIGIT_BIT - 1));

      /* forward carry to next iteration */
      r = rr;
   }

   /* zero excess digits */
   tmpb = b->dp + b->used;
#pragma unroll
   for (x = b->used; x < oldused; x++)  *tmpb++ = 0;

   b->sign = a->sign;
   mp_clamp(b);
   return MP_OKAY;
}




/* shift right by a certain bit count (store quotient in c, optional remainder in d) */
__device__ inline
int mp_div_2d(mp_int *a, int b, mp_int *c, mp_int *d)
{
   mp_digit D, r, rr;
   int x;

   /* if the shift count is <= 0 then we do no work */
   if (b <= 0) {
      mp_copy(a, c);
      if (d != NULL)  mp_zero(d);
      return MP_OKAY;
   }

   /* copy */
   mp_copy(a, c);

   /* 'a' should not be used after here - it might be the same as d */

   /* get the remainder */
   if (d != NULL)  mp_mod_2d(a, b, d);

   /* shift by as many digits in the bit count */
   if (b >= DIGIT_BIT)  mp_rshd(c, b / DIGIT_BIT);

   /* shift any bit count < DIGIT_BIT */
   D = (mp_digit)(b % DIGIT_BIT);
   if (D != 0u) {
      mp_digit *tmpc, mask, shift;

      /* mask */
      mask = ((mp_digit)1 << D) - 1uL;

      /* shift for lsb */
      shift = (mp_digit)DIGIT_BIT - D;

      /* alias */
      tmpc = c->dp + (c->used - 1);

      /* carry */
      r = 0;
#pragma unroll
      for (x = c->used - 1; x >= 0; x--) {
         /* get the lower  bits of this word in a temp */
         rr = *tmpc & mask;

         /* shift the current word and mix in the carry bits from the previous word */
         *tmpc = (*tmpc >> D) | (r << shift);
         --tmpc;

         /* set the carry to the carry bits of the current word found above */
         r = rr;
      }
   }
   mp_clamp(c);
   return MP_OKAY;
}



/* calc a value mod 2**b */
__device__ inline
int mp_mod_2d(mp_int *a, int b, mp_int *c)
{
   int x;

   /* if b is <= 0 then zero the int */
   if (b <= 0) {
      mp_zero(c);
      return MP_OKAY;
   }

   /* if the modulus is larger than the value then return */
   if (b >= (a->used * DIGIT_BIT)) {
      mp_copy(a, c);
      return MP_OKAY;
   }

   /* copy */
   mp_copy(a, c);

   /* zero digits above the last digit of the modulus */
#pragma unroll
   for (x = (b / DIGIT_BIT) + (((b % DIGIT_BIT) == 0) ? 0 : 1); x < c->used; x++) {
      c->dp[x] = 0;
   }

   /* clear the digit that is not completely outside/inside the modulus */
   c->dp[b / DIGIT_BIT] &= ((mp_digit)1 << (mp_digit)(b % DIGIT_BIT)) - (mp_digit)1;

   mp_clamp(c);
   return MP_OKAY;
}




/* all the code below here is only needed for printing */

#ifdef PRINTF_ENABLED

/* stores a bignum as a ASCII string in a given radix (2..64) */
__device__
int mp_toradix(mp_int *a, char *str, int radix)
{
   int digs;
   mp_int  t;
   mp_digit d;
   char   *_s = str;
   //const char *const mp_s_rmap = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz+/";
   char mp_s_rmap[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz+/";


   /* check range of the radix */
   if ((radix < 2) || (radix > 64)) return MP_VAL;

   /* quick out if its zero */
   if (IS_ZERO(a)) {
      *str++ = '0';
      *str = '\0';
      return MP_OKAY;
   }

   mp_zero(&t);
   mp_copy(a, &t);

   /* if it is negative output a - */
   if (t.sign == MP_NEG) {
      ++_s;
      *str++ = '-';
      t.sign = MP_ZPOS;
   }

   digs = 0;
   while (!IS_ZERO(&t)) {
      mp_div_d(&t, (mp_digit)radix, &t, &d);  /* this is safe from overflow */
      *str++ = mp_s_rmap[d];
      ++digs;
   }

   /* reverse the digits of the string.  In this case _s points
    * to the first digit [exluding the sign] of the number]
    */
   bn_reverse((unsigned char *)_s, digs);

   /* append a NULL so the string is properly terminated */
   *str = '\0';

   return MP_OKAY;
}



/* reverse an array, used for radix code */
__device__
void bn_reverse(unsigned char *s, int len)
{
   int ix, iy;
   unsigned char t;

   ix = 0;
   iy = len - 1;
   while (ix < iy) {
      t     = s[ix];
      s[ix] = s[iy];
      s[iy] = t;
      ++ix;
      --iy;
   }
}



/* Like printf("%ld",a) but with arbitrary precision (max of 256 characters) */
__device__
void mp_printf(mp_int a)
{
  char str[256];

  mp_toradix(&a, str, 10);

  // The Open CL standard does not define %s for non-literal strings.  Works for Cuda though!
  #ifdef OPENCL
    for(int i=0; str[i]!='\0'; i++)  printf("%c", str[i]);
  #else
    printf("%s", str);
  #endif

}


__device__
void mp_printf_thread(int threadIdx, const char* prefix, mp_int a)
{
  char str[256];

  mp_toradix(&a, str, 10);

  // The Open CL standard does not define %s for non-literal strings.  Works for Cuda though!
  printf("idx %d: %s %s\n", threadIdx, prefix, str);

}



/* Prints a polynomial whose coefficients are of type mp_int   */
/* Assumes coefficients are in ascending order of powers of x. */
/* poly[] should be of length deg+1.                           */
__device__
void mp_print_poly(mp_int *poly, int deg)
{
   mp_printf(poly[0]);
   for(int k=1; k<=deg; k++) {
      printf(" + ");
      mp_printf(poly[k]);
      printf(" x^%d", k);
   }
}

#endif



#endif
