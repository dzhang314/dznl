#ifndef DZNL_FLOATING_POINT_HPP_INCLUDED
#define DZNL_FLOATING_POINT_HPP_INCLUDED

#include "Arithmetic.hpp" // for pow_slow
#include "Constants.hpp"  // for one

namespace dznl {


/**
 * @brief Given a floating-point number b, compute and return the first natural
 * number n such that b^n is large.
 *
 * We say that a floating-point number x is "large" if the least significant
 * digit of x has magnitude greater than one, i.e., ulp(x) > 1.
 */
template <typename T, typename U>
constexpr U compute_large_exponent(T base) {
    constexpr T ONE = one<T>();
    T power = ONE;
    U result = zero<U>();
    while ((power + ONE) - power == ONE) {
        power *= base;
        ++result;
    }
    return result;
}


/**
 * @brief Given a floating-point type T, compute and return the floating-point
 * radix of T.
 *
 * For example, conventional binary floating-point types have radix 2, and
 * decimal floating-point types have radix 10.
 */
template <typename T, typename U>
constexpr T compute_radix() noexcept {
    constexpr T ONE = one<T>();
    constexpr T TWO = ONE + ONE;
    constexpr T large_pow2 = pow_slow(TWO, compute_large_exponent<T, U>(TWO));
    T result = ONE;
    while ((large_pow2 + result) - large_pow2 != result) {
        result += ONE;
    }
    return result;
}


/**
 * @brief Given a floating-point type T, compute and return the floating-point
 * precision of T.
 *
 * For example, the IEEE 754-2008 binary32 type, usually called "float" in C,
 * has precision 24. The IEEE 754-2008 binary64 type, usually called "double"
 * in C, has precision 53.
 */
template <typename T, typename U>
constexpr U compute_precision() noexcept {
    return compute_large_exponent<T, U>(compute_radix<T, U>());
}


} // namespace dznl

#endif // DZNL_FLOATING_POINT_HPP_INCLUDED
