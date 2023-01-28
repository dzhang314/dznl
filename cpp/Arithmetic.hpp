#ifndef DZNL_ARITHMETIC_HPP_INCLUDED
#define DZNL_ARITHMETIC_HPP_INCLUDED

#include "Constants.hpp" // for one

namespace dznl {


/**
 * @brief Given a number x (of any type T, integer or floating-point) and a
 * natural number n, compute and return x^n.
 *
 * This function does NOT use the exponentiation-by-squaring optimization, so
 * it performs fully-left-associated multiplications (e.g., ((x * x) * x) * x)
 * in the computation of x^n.
 */
template <typename T, typename U>
constexpr T pow_slow(T base, U exponent) {
    T result = one<T>();
    for (; exponent > zero<U>(); --exponent) {
        result *= base;
    }
    return result;
}


/**
 * @brief Given a number x (of any type T, integer or floating-point) and a
 * natural number n, compute and return x^n.
 *
 * This function uses the exponentiation-by-squaring optimization, so it may
 * reassociate multiplications in the computation of x^n.
 */
template <typename T, typename U>
constexpr T pow(T base, U exponent) {
    T accum = base;
    T result = one<T>();
    for (; exponent > zero<U>(); --exponent) {
        if (exponent & one<U>()) {
            result *= accum;
        }
        accum *= accum;
    }
    return result;
}


float sqrt(float x) { return __builtin_sqrtf(x); }
double sqrt(double x) { return __builtin_sqrt(x); }
long double sqrt(long double x) { return __builtin_sqrtl(x); }


} // namespace dznl

#endif // DZNL_ARITHMETIC_HPP_INCLUDED
