#ifndef DZNL_FLOATING_POINT_PROPERTIES_HPP_INCLUDED
#define DZNL_FLOATING_POINT_PROPERTIES_HPP_INCLUDED

#include "Macros.hpp"
#include "NumericFunctions.hpp"
#include "Tuple.hpp"

namespace dznl {


/**
 * @brief Test whether a given floating-point number is NaN.
 */
template <typename FLOAT_T>
constexpr bool is_nan(DZNL_CONST FLOAT_T &x) noexcept {
    return !(x == x);
}


/**
 * @brief Test whether a given floating-point number is finite.
 */
template <typename FLOAT_T>
constexpr bool is_finite(DZNL_CONST FLOAT_T &x) noexcept {
    return !is_nan(x - x);
}


namespace internal {


/**
 * @brief Return `true` if `ulp(big) > small`.
 */
template <typename FLOAT_T>
constexpr bool
is_negligible(DZNL_CONST FLOAT_T &big, DZNL_CONST FLOAT_T small) noexcept {
    return !((big + small) - big == small);
}


/**
 * @brief Given a floating-point number `x`, compute and return the first
 *        nonnegative integer `n` such that `pow(x, n)` is dominant.
 *
 * We say that a floating-point number is "dominant" if its least significant
 * digit has magnitude greater than one, i.e., `ulp(pow(x, n)) > 1.0`.
 */
template <typename FLOAT_T, typename INTEGER_T>
constexpr Tuple<FLOAT_T, INTEGER_T> compute_dominant_power(DZNL_CONST FLOAT_T &x
) noexcept {
    DZNL_CONST FLOAT_T FLOAT_ONE = one<FLOAT_T>();
    INTEGER_T n = zero<INTEGER_T>();
    FLOAT_T x_pow_n = FLOAT_ONE;
    while (!internal::is_negligible(x_pow_n, FLOAT_ONE)) {
        x_pow_n *= x;
        ++n;
    }
    return {x_pow_n, n};
}


} // namespace internal


/**
 * @brief Compute and return the radix of a floating-point type `FLOAT_T`.
 *
 * For example, conventional binary floating-point types have radix 2, and
 * decimal floating-point types have radix 10.
 */
template <typename FLOAT_T, typename INTEGER_T>
constexpr Tuple<FLOAT_T, INTEGER_T> compute_float_radix() noexcept {

    // This algorithm is based on the following observation: in any
    // floating-point system with radix r, the unit in the last place (ulp) of
    // any finite number is a power of r. Therefore, we can recover the radix r
    // by computing ulp(x) for the smallest number x that satisfies ulp(x) > 1.
    DZNL_CONST FLOAT_T FLOAT_ONE = one<FLOAT_T>();
    DZNL_CONST FLOAT_T FLOAT_TWO = FLOAT_ONE + FLOAT_ONE;

    // We could perform a binary search to find x, but we don't need to!
    // As long as r >= 2, a power of two is guaranteed to lie in every range
    // of the form [r^n, r^(n+1)). This means we can simply take x to be the
    // first dominant power of two.
    DZNL_CONST FLOAT_T dominant_number =
        internal::compute_dominant_power<FLOAT_T, INTEGER_T>(FLOAT_TWO).first;

    // Now, to compute ulp(x), we find the smallest positive integer y
    // that satisfies (x + y) - x == y.
    FLOAT_T float_radix = FLOAT_ONE;
    INTEGER_T integer_radix = one<INTEGER_T>();
    while (internal::is_negligible(dominant_number, float_radix)) {
        float_radix += FLOAT_ONE;
        ++integer_radix;
    }
    return {float_radix, integer_radix};
}


/**
 * @brief Compute and return the precision of a floating-point type `FLOAT_T`.
 *
 * For example, the IEEE 754-2008 binary32 type, usually called `float` in C,
 * has precision 24. The IEEE 754-2008 binary64 type, usually called `double`
 * in C, has precision 53.
 */
template <typename FLOAT_T, typename INTEGER_T>
constexpr INTEGER_T compute_float_precision() noexcept {

    // In a floating-point system with radix r and precision p, the number r^p
    // is the smallest number satisfying ulp(r^p) > 1. Hence, we can compute p
    // by computing the first dominant power of r.
    DZNL_CONST FLOAT_T radix = compute_float_radix<FLOAT_T, INTEGER_T>().first;
    return internal::compute_dominant_power<FLOAT_T, INTEGER_T>(radix).second;
}


} // namespace dznl

#endif // DZNL_FLOATING_POINT_PROPERTIES_HPP_INCLUDED
