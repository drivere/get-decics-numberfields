/*
  Header file to define uint256_t class for Cuda.
  Mimics the uint128_t class written by Curtis Seizert.
*/

#ifndef _UINT256_T_CUDA_H
#define _UINT256_T_CUDA_H

#include <cinttypes>
#include <cuda.h>
#include <cmath>
#include "cuda_uint128.h"


class uint256_t{
public:
#ifdef __CUDA_ARCH__ // dynamic initialization not supported in some device code
  uint128_t lo, hi;
#else
  uint128_t lo = 0, hi = 0;
#endif
#ifdef __CUDA_ARCH__
  __device__
#endif
  uint256_t(){};


                    ////////////////
                    //  Operators //
                    ////////////////

  template<typename T>
#ifdef __CUDA_ARCH__
  __device__
#endif
  uint256_t(const T & a)
  {
    this->lo = (uint128_t)a;
    this->hi = 0;
  }

#ifdef __CUDA_ARCH__
  __device__
#endif
 static inline uint128_t u256tou128(uint256_t x){return x.lo;}


#ifdef __CUDA_ARCH__
  __device__
#endif
operator uint128_t () {return lo;}


 #ifdef __CUDA_ARCH__
   __device__
 #endif
   uint256_t & operator=(const uint256_t & n)
  {
    lo = n.lo;
    hi = n.hi;
    return * this;
  }


 #ifdef __CUDA_ARCH__
   __device__
 #endif
   uint256_t & operator=(const uint128_t & n)
  {
    lo = n;
    hi = 0;
    return * this;
  }


// operator overloading
  template <typename T>
  #ifdef __CUDA_ARCH__
    __device__
  #endif
    uint256_t & operator=(const T n){hi = 0; lo = n; return * this;}

  template <typename T>
  #ifdef __CUDA_ARCH__
    __device__
  #endif
    friend uint256_t operator+(uint256_t a, const T & b){return add256(a, (uint256_t)b);}

  template <typename T>
  #ifdef __CUDA_ARCH__
    __device__
  #endif
  inline uint256_t & operator+=(const T & b)
  {
    *this = add256(*this, (uint256_t)b );
    return *this;
  }

  template <typename T>
  #ifdef __CUDA_ARCH__
    __device__
  #endif
  inline uint256_t & operator-=(const T & b)
  {
    uint256_t temp = (uint256_t)b;
    hi = hi - temp.hi;
    if(lo < temp.lo) --hi;
    lo = lo - temp.lo;
    return *this;
  }

  template <typename T>
  #ifdef __CUDA_ARCH__
    __device__
  #endif
  inline uint256_t & operator>>=(const T & b)
  {
    (b < 128) ? ( lo = (lo >> b) | (hi << (int)(128-b)) ) : ( lo = hi >> (int)(b-128) );
    (b < 128) ? hi >>= b : hi = 0;
    return *this;
  }

  template <typename T>
  #ifdef __CUDA_ARCH__
    __device__
  #endif
  inline uint256_t & operator<<=(const T & b)
  {
    (b < 128) ? ( hi = (hi << b) | (lo >> (int)(128-b)) ) : ( hi = lo << (int)(b-128) );
    (b < 128) ? lo <<= b : lo = 0;
    return *this;
  }

  template <typename T>
  #ifdef __CUDA_ARCH__
    __device__
  #endif
  friend inline uint256_t operator>>(uint256_t a, const T & b){a >>= b; return a;}

  template <typename T>
  #ifdef __CUDA_ARCH__
    __device__
  #endif
  friend inline uint256_t operator<<(uint256_t a, const T & b){a <<= b; return a;}

  #ifdef __CUDA_ARCH__
    __device__
  #endif
  inline uint256_t & operator--(){return *this -=1;}

  #ifdef __CUDA_ARCH__
    __device__
  #endif
  inline uint256_t & operator++(){return *this +=1;}

  template <typename T>
  #ifdef __CUDA_ARCH__
    __device__
  #endif
  friend uint256_t operator-(uint256_t a, const T & b){return sub256(a, (uint256_t)b);}

  #ifdef __CUDA_ARCH__
    __device__
  #endif
  friend uint256_t operator*(uint256_t a, const uint128_t &b){ return mul256(a,b); }

  #ifdef __CUDA_ARCH__
    __device__
  #endif
  friend uint256_t operator*(uint128_t a, const uint256_t &b){ return mul256(b,a); }

  template <typename T>
  #ifdef __CUDA_ARCH__
    __device__
  #endif
  friend uint256_t operator*(const T &a, uint256_t b){return mul256(b, (uint128_t)a);}

  template <typename T>
  #ifdef __CUDA_ARCH__
    __device__
  #endif
  friend uint256_t operator*(uint256_t a, const T & b){return mul256(a, (uint128_t)b);}

  #ifdef __CUDA_ARCH__
    __device__
  #endif
  friend uint256_t operator/(uint256_t x, const uint128_t &v) { return div256to256(x,v); }

  #ifdef __CUDA_ARCH__
    __device__
  #endif
  friend uint256_t operator/(uint256_t x, const uint256_t &v) { return div256to256(x,v); }

  template <typename T>
  #ifdef __CUDA_ARCH__
    __device__
  #endif
  friend T operator/(uint256_t x, const T & v){return div256to256(x, (uint256_t)v);}


  #ifdef __CUDA_ARCH__
    __device__
  #endif
  friend uint128_t operator%(uint256_t x, const uint128_t &v)
  {
    uint128_t res;
    div256to256(x, v, &res);
    return res;
  }

  #ifdef __CUDA_ARCH__
    __device__
  #endif
  friend uint256_t operator%(uint256_t x, const uint256_t &v)
  {
    uint256_t res;
    div256to256(x, v, &res);
    return res;
  }

  template <typename T>
  #ifdef __CUDA_ARCH__
    __device__
  #endif
  friend T operator%(uint256_t x, const T & v)
  {
    uint128_t res;
    div256to256(x, (uint128_t)v, &res);
    return (T)res;
  }

#ifdef __CUDA_ARCH__
  __device__
#endif
  friend bool operator<(uint256_t a, uint256_t b){return isLessThan(a, b);}
#ifdef __CUDA_ARCH__
  __device__
#endif
  friend bool operator>(uint256_t a, uint256_t b){return isGreaterThan(a, b);}
#ifdef __CUDA_ARCH__
  __device__
#endif
  friend bool operator<=(uint256_t a, uint256_t b){return isLessThanOrEqual(a, b);}
#ifdef __CUDA_ARCH__
  __device__
#endif
  friend bool operator>=(uint256_t a, uint256_t b){return isGreaterThanOrEqual(a, b);}
#ifdef __CUDA_ARCH__
  __device__
#endif
  friend bool operator==(uint256_t a, uint256_t b){return isEqualTo(a, b);}
#ifdef __CUDA_ARCH__
  __device__
#endif
friend bool operator!=(uint256_t a, uint256_t b){return isNotEqualTo(a, b);}

template <typename T>
#ifdef __CUDA_ARCH__
  __device__
#endif
  friend uint256_t operator|(uint256_t a, const T & b){return bitwiseOr(a, (uint256_t)b);}

template <typename T>
#ifdef __CUDA_ARCH__
  __device__
#endif
  uint256_t & operator|=(const T & b){*this = *this | b; return *this;}

template <typename T>
#ifdef __CUDA_ARCH__
  __device__
#endif
  friend uint256_t operator&(uint256_t a, const T & b){return bitwiseAnd(a, (uint256_t)b);}

template <typename T>
#ifdef __CUDA_ARCH__
  __device__
#endif
  uint256_t & operator&=(const T & b){*this = *this & b; return *this;}

template <typename T>
#ifdef __CUDA_ARCH__
  __device__
#endif
  friend uint256_t operator^(uint256_t a, const T & b){return bitwiseXor(a, (uint256_t)b);}

template <typename T>
#ifdef __CUDA_ARCH__
  __device__
#endif
  uint256_t & operator^=(const T & b){*this = *this ^ b; return *this;}

#ifdef __CUDA_ARCH__
  __device__
#endif
  friend uint256_t operator~(uint256_t a){return bitwiseNot(a);}


                      ////////////////////
                      //    Comparisons
                      ////////////////////


  #ifdef __CUDA_ARCH__
    __device__
  #endif
  static  bool isLessThan(uint256_t a, uint256_t b)
  {
    if(a.hi < b.hi) return 1;
    if(a.hi > b.hi) return 0;
    if(a.lo < b.lo) return 1;
    else return 0;
  }

  #ifdef __CUDA_ARCH__
    __device__
  #endif
  static  bool isLessThanOrEqual(uint256_t a, uint256_t b)
  {
    if(a.hi <  b.hi) return 1;
    if(a.hi >  b.hi) return 0;
    if(a.lo <= b.lo) return 1;
    else return 0;
  }

  #ifdef __CUDA_ARCH__
    __device__
  #endif
  static  bool isGreaterThan(uint256_t a, uint256_t b)
  {
    if(a.hi <  b.hi) return 0;
    if(a.hi >  b.hi) return 1;
    if(a.lo <= b.lo) return 0;
    else return 1;
  }

  #ifdef __CUDA_ARCH__
    __device__
  #endif
  static  bool isGreaterThanOrEqual(uint256_t a, uint256_t b)
  {
    if(a.hi < b.hi) return 0;
    if(a.hi > b.hi) return 1;
    if(a.lo < b.lo) return 0;
    else return 1;
  }

  #ifdef __CUDA_ARCH__
    __device__
  #endif
  static  bool isEqualTo(uint256_t a, uint256_t b)
  {
    if(a.lo == b.lo && a.hi == b.hi) return 1;
    else return 0;
  }

  #ifdef __CUDA_ARCH__
    __device__
  #endif
  static  bool isNotEqualTo(uint256_t a, uint256_t b)
  {
    if(a.lo != b.lo || a.hi != b.hi) return 1;
    else return 0;
  }

  #ifdef __CUDA_ARCH__
    __device__
  #endif
  friend uint256_t min(uint256_t a, uint256_t b)
  {
    return a < b ? a : b;
  }

  #ifdef __CUDA_ARCH__
    __device__
  #endif
  friend uint256_t max(uint256_t a, uint256_t b)
  {
    return a > b ? a : b;
  }


                      //////////////////////
                      //   bit operations
                      //////////////////////

// Count leading zeros for uint256_t
#ifdef __CUDA_ARCH__
  __device__
#endif
  friend inline int clz256(uint256_t x)
  {
    int res;
    res = x.hi != 0 ? clz128(x.hi) : 128 + clz128(x.lo);
    return res;
  }

#ifdef __CUDA_ARCH__
  __device__
#endif
  static  uint256_t bitwiseOr(uint256_t a, uint256_t b)
  {
    a.lo |= b.lo;
    a.hi |= b.hi;
    return a;
  }

#ifdef __CUDA_ARCH__
  __device__
#endif
  static  uint256_t bitwiseAnd(uint256_t a, uint256_t b)
  {
    a.lo &= b.lo;
    a.hi &= b.hi;
    return a;
  }

#ifdef __CUDA_ARCH__
  __device__
#endif
  static  uint256_t bitwiseXor(uint256_t a, uint256_t b)
  {
    a.lo ^= b.lo;
    a.hi ^= b.hi;
    return a;
  }

#ifdef __CUDA_ARCH__
  __device__
#endif
  static  uint256_t bitwiseNot(uint256_t a)
  {
    a.lo = ~a.lo;
    a.hi = ~a.hi;
    return a;
  }

                          //////////////////
                          //   arithmetic
                          //////////////////

#ifdef __CUDA_ARCH__
  __device__
#endif
  static inline uint256_t add256(uint256_t x, uint256_t y)
  {
    uint256_t res;
    res.lo = x.lo + y.lo;
    res.hi = x.hi + y.hi;
    if(res.lo<x.lo) ++res.hi;
    return res;
  }


#ifdef __CUDA_ARCH__
  __device__
#endif
  static inline uint256_t mul256(uint128_t x, uint128_t y)
  {
    uint256_t res;
    uint128_t::mul128(x, y, &res.lo, &res.hi);
    return res;
  }

// NOTE: This assumes the 256bit x 128bit product fits in a 256bit variable.
#ifdef __CUDA_ARCH__
  __device__
#endif
  static inline uint256_t mul256(uint256_t x, uint128_t y)
  {
    uint256_t tmp = mul256(x.lo, y);
    uint256_t res;
    res.lo = tmp.lo;

    // This does not work since it uses the templated type cast in uint128 instead of the one
    // defined in this file.
    //res.hi = ((uint128_t)mul256(x.hi, y)) + tmp.hi;

    uint256_t tmp2 = mul256(x.hi, y);  // This explicitly does the desired type cast.
    res.hi = tmp2.lo + tmp.hi;

    return res;
  }


// This is the full 256x256 multiplication.
// The result is a 512bit number, represented by two 256bit values (rhi and rlo).
// Let x=a*2^128 + b be the 1st 256 bit number (i.e. x.hi=a and x.lo=b).
// Let y=c*2^128 + d be the 2nd 256 bit number (i.e. y.hi=c and y.lo=d).
// Then r = x*y = (ac)2^256 + (ad+bc)2^128 + bd.
// r.lo will be bd + ad<<128 + bc<<128
// r.hi will be ac + ad>>128 + bc>>128 + carry
// Extra logic is needed to determine the carry from the r.lo computation.
// Note that there are 2 potential carries since r.lo is the sum of 3 256bit values.
#ifdef __CUDA_ARCH__
  __device__
#endif
  static inline void mul256(uint256_t x, uint256_t y, uint256_t *rlo, uint256_t *rhi)
  {
  uint256_t ad = mul256(x.hi, y.lo);
  uint256_t bc = mul256(x.lo, y.hi);
  uint256_t bd = mul256(x.lo, y.lo);

  int carry = 0;
  uint256_t ad128 = ad<<128;
  *rlo = ad128 + (bc<<128);
  if(*rlo<ad128) ++carry;
  *rlo = *rlo + bd;
  if(*rlo<bd) ++carry;

  *rhi = (ad>>128) + (bc>>128) + mul256(x.hi, y.hi) + carry;
  }


// taken from libdivide's adaptation of this implementation origininally in
// Hacker's Delight: http://www.hackersdelight.org/hdcodetxt/divDouble.c.txt
// License permits inclusion here per:
// http://www.hackersdelight.org/permissions.htm
// NOTE: This function assumes x.hi<v, so the result fits in a uint128_t
#ifdef __CUDA_ARCH__
  __device__
#endif
  static inline uint128_t div256to128(uint256_t x, uint128_t v, uint128_t * r = NULL) // x / v
  {
    //printf("cuda_uint256: doing 256 by 128 division with 128 bit output\n");
    const uint128_t b = ( (uint128_t)1 << 64 );

    // Note: I removed the overflow check, so user must be careful when calling this function.
    //       (i.e. we MUST have x.hi<v).

    // If x.hi is zero we can use standard 128bit divide.
    if(x.hi==0) {
      if(r != NULL) *r = (x.lo)%v;
      return  x.lo/v;
    }

    // Count the leading zeros of v.
    int s = clz128(v);

    uint128_t un128, un10;
    if(s > 0){
      // Normalize divisor so that it's MSB is 1
      v = v << s;
//      un128 = (x.hi << s) | ( (x.lo>>(128-s)) & (-s>>31) );
//      un128 = (x.hi << s) | ( (x.lo>>(128-s)) & (0xFFFFFFFFFFFFFFFF) );
      // Shift entire numerator 128-s bits to the right
      un128 = (x.hi << s) | ( x.lo>>(128-s) );
      un10 = x.lo << s; // Shift dividend left
      }
    else{
      // Avoid undefined behavior
      un128 = x.hi;
      un10 = x.lo;
      }

    uint128_t q1 = un128/v.hi;
    uint128_t rhat = un128 - q1*v.hi;

    while (q1 >= b || (uint256_t)q1 * v.lo > (uint256_t)b * rhat + un10.hi) {
      q1 = q1 - 1;
      rhat = rhat + v.hi;
      if (rhat >= b)  break;
      }

    uint128_t un21 = (uint256_t)un128*b + un10.hi - (uint256_t)q1*v;

    uint128_t q0 = un21/v.hi;
    rhat = un21 - q0*v.hi;

    while (q0 >= b || (uint256_t)q0 * v.lo > (uint256_t)b * rhat + un10.lo) {
      q0 = q0 - 1;
      rhat = rhat + v.hi;
      if (rhat >= b)  break;
      }

    if(r != NULL) {
      uint256_t tmp = ((uint256_t)un21*b + un10.lo - (uint256_t)q0*v) >> s;
      *r = tmp.lo;
      }

    uint256_t tmp = (uint256_t)q1*b + q0;
    return tmp.lo;

  }


  #ifdef __CUDA_ARCH__
    __device__
  #endif
  static inline uint256_t div256to256(uint256_t x, uint128_t v, uint128_t * r = NULL)
  {
    //printf("cuda_uint256: doing 256 by 128 division with 256 bit output\n");

    uint256_t res;
    uint128_t rem;
    res.hi = uint128_t::div128to128(x.hi, v, &rem);  // Compute x.hi/v
    x.hi = rem;

    res.lo = div256to128(x, v, r);

    return res;
  }


  // This is the complete division 256bit divided by 256bit, returned as 256bit.
  #ifdef __CUDA_ARCH__
    __device__
  #endif
  static inline uint256_t div256to256(uint256_t x, uint256_t v, uint256_t *r = NULL)
  {

    // First dispense with the case when v is actually only 128 bits.
    if(v.hi == 0) {
      if(r != NULL) {
        r->hi = 0;
        return div256to256(x, v.lo, &(r->lo));
        }
      else {
        return div256to256(x, v.lo);
        }
      }

    // Dispense with the case when the denominator exceeds the numerator.
    // Then result is 0 and remainder is x.
    if(v > x) {
      uint256_t res;
      res.lo = 0;  res.hi=0;
      if(r != NULL) { r->lo = x.lo;  r->hi = x.hi; }
      return res;
      }

    // We may now assume 0 < v.hi <= x.hi
    // The max x will be 2^256-1 and the min v will be 2^128.
    // This implies that the quotient fits into 128 bits (i.e. res.hi=0)
    uint256_t res;
    res.hi = 0;

    // We know that v.hi>0, so clz128 is OK to use.  We have 0 <= s <= 127.
    int s = clz128(v.hi);

    // Normalize the divisor so its MSB is 1
    uint256_t v1t = v<<s;
    uint128_t v1 = v1t.hi;

    // Shift x right by 1 to ensure x.hi<v so we can use div256to128.
    uint256_t x1 = x>>1;

    // Do the division
    //uint256_t q0 = (uint256_t)div256to128(x1, v1);
    uint128_t q0 = div256to128(x1, v1);

    // Undo normalization and division of x by 2.
    q0 = q0>>(127-s);

    // Make q0 correct or too small by 1.
    if (q0 != 0)  --q0;

    // Compute q0 * v as q0v.
    // q0v = q0 * (v.hi << 128 + v.lo)
    //     = (q0 * v.hi) << 128 + q0.lo * v.lo
    uint256_t q0v = (mul256(q0,v.hi)<<128) + mul256(q0,v.lo);

    // Compute x - q0v as x_q0v.  This is the remainder.
    uint256_t x_q0v = x - q0v;

    // Check if x_q0v >= v
    // This checks if our remainder is larger than the divisor
    if ( x_q0v >= v) {
      ++q0;
      x_q0v = x_q0v - v;  // Subtract v from remainder
      }

    if(r != NULL) {
      r->hi = x_q0v.hi;
      r->lo = x_q0v.lo;
      }

    res.lo = q0;
    return res;
  }


  #ifdef __CUDA_ARCH__
    __device__
  #endif
  static inline uint256_t sub256(uint256_t x, uint256_t y) // x - y
  {
    uint256_t res;

    res.lo = x.lo - y.lo;
    res.hi = x.hi - y.hi;
    if(x.lo < y.lo) --res.hi;

    return res;
  }

  #ifdef __CUDA_ARCH__
    __device__
  #endif
  friend inline uint256_t sub256(uint256_t x, uint256_t y);



                            /////////////////
                            //  typecasting
                            /////////////////

/*
  #ifdef __CUDA_ARCH__
    __device__
  #endif
    friend inline double u128_to_double(uint128_t x)
  {
    double dbl;
    #ifdef __CUDA_ARCH__
    if(x.hi == 0) return __ull2double_rd(x.lo);
    #else
    if(x.hi == 0) return (double) x.lo;
    #endif
    uint64_t r = clz64(x.hi);
    x <<= r;

    #ifdef __CUDA_ARCH__
    dbl = __ull2double_rd(x.hi);
    #else
    dbl = (double) x.lo;
    #endif

    dbl *= (1ull << (64-r));

    return dbl;
  }

  #ifdef __CUDA_ARCH__
    __device__
  #endif
    friend inline float u128_to_float(uint128_t x)
  {
    float flt;
    #ifdef __CUDA_ARCH__
    if(x.hi == 0) return __ull2float_rd(x.lo);
    #else
    if(x.hi == 0) return (float) x.lo;
    #endif
    uint64_t r = clz64(x.hi);
    x <<= r;

    #ifdef __CUDA_ARCH__
    flt = __ull2float_rd(x.hi);
    #else
    flt = (float) x.hi;
    #endif

    flt *= (1ull << (64-r));
    flt *= 2;

    return flt;
  }

  #ifdef __CUDA_ARCH__
    __device__
  #endif
    static inline uint128_t double_to_u128(double dbl)
  {
    uint128_t x;
    if(dbl < 1 || dbl > 1e39) return 0;
    else{

  #ifdef __CUDA_ARCH__
      uint32_t shft = __double2uint_rd(log2(dbl));
      uint64_t divisor = 1ull << shft;
      dbl /= divisor;
      x.lo = __double2ull_rd(dbl);
      x <<= shft;
  #else
      uint32_t shft = (uint32_t) log2(dbl);
      uint64_t divisor = 1ull << shft;
      dbl /= divisor;
      x.lo = (uint64_t) dbl;
      x <<= shft;
  #endif
      return x;
    }
  }

  #ifdef __CUDA_ARCH__
    __device__
  #endif
    static inline uint128_t float_to_u128(float flt)
  {
    uint128_t x;
    if(flt < 1 || flt > 1e39) return 0;
    else{

  #ifdef __CUDA_ARCH__
      uint32_t shft = __double2uint_rd(log2(flt));
      uint64_t divisor = 1ull << shft;
      flt /= divisor;
      x.lo = __double2ull_rd(flt);
      x <<= shft;
  #else
      uint32_t shft = (uint32_t) log2(flt);
      uint64_t divisor = 1ull << shft;
      flt /= divisor;
      x.lo = (uint64_t) flt;
      x <<= shft;
  #endif
    return x;
    }
  }
*/
                              //////////////
                              //  iostream
                              //////////////

/*
#ifdef __CUDA_ARCH__
  __host__
#endif
  friend inline std::ostream & operator<<(std::ostream & out, uint128_t x)
  {
    std::vector<uint16_t> rout;
    uint64_t v = 10, r = 0;
    if ( (uint64_t)x == 0) {
      out << "0";
      return out;
    }
    do {
      x = div128to128(x, v, &r);
      rout.push_back(r);
    } while(x != (uint128_t)0);
    for(std::reverse_iterator<std::vector<uint16_t>::iterator> rit = rout.rbegin(); rit != rout.rend(); rit++){
      out << *rit;
    }
    return out;
  }
*/

}; // class uint256_t



#ifdef __CUDA_ARCH__
  __device__
#endif
  inline uint256_t mul256(uint128_t x, uint128_t y)
{
  return uint256_t::mul256(x, y);
}

#ifdef __CUDA_ARCH__
  __device__
#endif
  inline uint256_t mul256(uint256_t x, uint128_t y)
{
  return uint256_t::mul256(x, y);
}

#ifdef __CUDA_ARCH__
  __device__
#endif
  inline uint128_t div256to128(uint256_t x, uint128_t v, uint128_t * r = NULL)
{
  return uint256_t::div256to128(x, v, r);
}

#ifdef __CUDA_ARCH__
  __device__
#endif
  inline uint256_t div256to256(uint256_t x, uint128_t v, uint128_t * r = NULL)
{
  return uint256_t::div256to256(x, v, r);
}

#ifdef __CUDA_ARCH__
  __device__
#endif
  inline uint256_t add256(uint256_t x, uint256_t y)
{
  return uint256_t::add256(x, y);
}


#ifdef __CUDA_ARCH__
  __device__
#endif
  inline uint256_t sub256(uint256_t x, uint256_t y) // x - y
{
  return x - y;
}


/*
#ifdef __CUDA_ARCH__
  __host__
#endif
 inline uint256_t string_to_u256(std::string s)
 {
   return uint256_t::string_to_u256(s);
 }
*/


#endif
