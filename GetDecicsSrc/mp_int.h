#ifndef MP_INT_H
#define MP_INT_H


// This is the hard-coded amount of precision to be used.
// It is the number of mp_digits.
// In Cuda, we use 64 bits for a "digit".
// But only 63 bits of each digit are actually used.  So 63*12 = 756 bits max.
// EDD 8-5-19: Noticed some sf4_DS15x271 cases were failing with memory errors,
//             so bumped precision up to 15 (63*15=945 bits)
// For openCL (any vendor) we use 32 bits for a "digit".
#ifdef CUDA
  #define MP_PREC  15
  typedef uint64_t mp_digit;
#else
  #define MP_PREC  32
  typedef uint32_t mp_digit;
#endif


/* This is the structure that defines the multi-precision data type */
typedef struct  {
   int used, sign;
   mp_digit dp[MP_PREC];
} mp_int;


#endif
