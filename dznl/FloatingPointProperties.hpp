#ifndef DZNL_FLOATING_POINT_PROPERTIES_HPP_INCLUDED
#define DZNL_FLOATING_POINT_PROPERTIES_HPP_INCLUDED

#include "NumericFunctions.hpp"
#include "Tuple.hpp"

namespace dznl {


/**
 * @brief Given a floating-point number b, compute and return the first
 *        nonnegative integer n such that b^n is dominant.
 *
 * We say that a floating-point number x is "dominant" if the least significant
 * digit of x has magnitude greater than one, i.e., ulp(x) > 1.
 */
template <typename FLOAT_T, typename INTEGER_T>
constexpr Tuple<FLOAT_T, INTEGER_T>
compute_float_dominant_power(const FLOAT_T &base) noexcept {
    const FLOAT_T ONE = one<FLOAT_T>();
    FLOAT_T power = ONE;
    INTEGER_T exponent = zero<INTEGER_T>();
    while ((power + ONE) - power == ONE) {
        power *= base;
        ++exponent;
    }
    return {power, exponent};
}


/**
 * @brief Compute and return the radix of a floating-point type FLOAT_T.
 *
 * For example, conventional binary floating-point types have radix 2, and
 * decimal floating-point types have radix 10.
 */
template <typename FLOAT_T, typename INTEGER_T>
constexpr FLOAT_T compute_float_radix() noexcept {
    const FLOAT_T ONE = one<FLOAT_T>();
    const FLOAT_T large_power_of_two =
        compute_float_dominant_power<FLOAT_T, INTEGER_T>(ONE + ONE).first;
    FLOAT_T radix = ONE;
    while ((large_power_of_two + radix) - large_power_of_two != radix) {
        radix += ONE;
    }
    return radix;
}


/**
 * @brief Compute and return the precision of a floating-point type FLOAT_T.
 *
 * For example, the IEEE 754-2008 binary32 type, usually called "float" in C,
 * has precision 24. The IEEE 754-2008 binary64 type, usually called "double"
 * in C, has precision 53.
 */
template <typename FLOAT_T, typename INTEGER_T>
constexpr INTEGER_T compute_float_precision() noexcept {
    const FLOAT_T radix = compute_float_radix<FLOAT_T, INTEGER_T>();
    return compute_float_dominant_power<FLOAT_T, INTEGER_T>(radix).second;
}


} // namespace dznl

#endif // DZNL_FLOATING_POINT_PROPERTIES_HPP_INCLUDED
