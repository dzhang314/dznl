#ifndef DZNL_FLOATING_POINT_PROPERTIES_HPP_INCLUDED
#define DZNL_FLOATING_POINT_PROPERTIES_HPP_INCLUDED

#include "Containers.hpp"
#include "NumericTypeInterface.hpp"

namespace dznl {


/**
 * @brief Given a floating-point number b, compute and return the first
 *        nonnegative integer n such that b^n is large.
 *
 * We say that a floating-point number x is "large" if the least significant
 * digit of x has magnitude greater than one, i.e., ulp(x) > 1.
 */
template <typename T, typename U>
constexpr pair<T, U> compute_large_power(const T &base) noexcept {
    constexpr T ONE = one<T>();
    T power = ONE;
    U exponent = zero<U>();
    while ((power + ONE) - power == ONE) {
        power *= base;
        ++exponent;
    }
    return {power, exponent};
}


/**
 * @brief Compute and return the radix of a given floating-point type T.
 *
 * For example, conventional binary floating-point types have radix 2, and
 * decimal floating-point types have radix 10.
 */
template <typename T, typename U>
constexpr T compute_radix() noexcept {
    constexpr T ONE = one<T>();
    constexpr T large_power_of_two =
        compute_large_power<T, U>(double_value<T>(ONE)).first;
    T radix = ONE;
    while ((large_power_of_two + radix) - large_power_of_two != radix) {
        radix += ONE;
    }
    return radix;
}


/**
 * @brief Compute and return the precision of a given floating-point type T.
 *
 * For example, the IEEE 754-2008 binary32 type, usually called "float" in C,
 * has precision 24. The IEEE 754-2008 binary64 type, usually called "double"
 * in C, has precision 53.
 */
template <typename T, typename U>
constexpr U compute_precision() noexcept {
    return compute_large_power<T, U>(compute_radix<T, U>()).second;
}


} // namespace dznl

#endif // DZNL_FLOATING_POINT_PROPERTIES_HPP_INCLUDED
