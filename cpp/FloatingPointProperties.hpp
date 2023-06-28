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


template <typename T, typename U>
struct Pair {
    T first;
    U second;
}; // struct Pair


template <typename T, typename U, U lo_width>
constexpr Pair<T, T> veltkamp_split(T x) noexcept {
    constexpr T veltkamp_constant =
        pow_slow<T, U>(compute_radix<T, U>(), lo_width) + one<T>();
    const T vx = veltkamp_constant * x;
    const T x_hi = vx - (vx - x);
    const T x_lo = x - x_hi;
    return {x_hi, x_lo};
}


template <typename T>
constexpr Pair<T, T> fast_two_sum(T a, T b) noexcept {
    const T sum = a + b;
    const T b_prime = sum - a;
    const T err = b - b_prime;
    return {sum, err};
}


template <typename T>
constexpr Pair<T, T> two_sum(T a, T b) noexcept {
    const T sum = a + b;
    const T a_prime = sum - b;
    const T b_prime = sum - a_prime;
    const T a_err = a - a_prime;
    const T b_err = b - b_prime;
    const T err = a_err + b_err;
    return {sum, err};
}


template <typename T>
constexpr Pair<T, T> two_prod(T a, T b) noexcept {
    constexpr int half_width = (compute_precision<T, int>() + 1) / 2;
    const auto [a_hi, a_lo] = veltkamp_split<T, int, half_width>(a);
    const auto [b_hi, b_lo] = veltkamp_split<T, int, half_width>(b);
    const T hi_hi = a_hi * b_hi;
    const T hi_lo = a_hi * b_lo;
    const T lo_hi = a_lo * b_hi;
    const T lo_lo = a_lo * b_lo;
    const T prod = a * b;
    const T err_1 = hi_hi - prod;
    const T err_2 = err_1 + hi_lo;
    const T err_3 = err_2 + lo_hi;
    const T err = err_3 + lo_lo;
    return {prod, err};
}


} // namespace dznl

#endif // DZNL_FLOATING_POINT_HPP_INCLUDED
