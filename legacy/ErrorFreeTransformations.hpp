/*
#ifndef DZNL_ERROR_FREE_TRANSFORMATIONS_HPP_INCLUDED
#define DZNL_ERROR_FREE_TRANSFORMATIONS_HPP_INCLUDED

#include "FloatingPointProperties.hpp"
#include "MathematicalFunctions.hpp"
#include "NumericTypeInterface.hpp"
#include "Tuple.hpp"

namespace dznl {


template <typename T, typename U, U width>
constexpr Tuple<T, T> veltkamp_split(const T &x) noexcept {
    constexpr T veltkamp_constant =
        pow<T, U>(compute_radix<T, U>(), width) + one<T>();
    const T vx = veltkamp_constant * x;
    const T x_hi = vx - (vx - x);
    const T x_lo = x - x_hi;
    return {x_hi, x_lo};
}


template <typename T>
constexpr Tuple<T, T> fast_two_sum(const T &a, const T &b) noexcept {
    const T sum = a + b;
    const T b_prime = sum - a;
    const T err = b - b_prime;
    return {sum, err};
}


template <typename T>
constexpr Tuple<T, T> fast_two_diff(const T &a, const T &b) noexcept {
    const T diff = a - b;
    const T b_prime = a - diff;
    const T err = b_prime - b;
    return {diff, err};
}


template <typename T>
constexpr Tuple<T, T> two_sum(const T &a, const T &b) noexcept {
    const T sum = a + b;
    const T a_prime = sum - b;
    const T b_prime = sum - a_prime;
    const T a_err = a - a_prime;
    const T b_err = b - b_prime;
    const T err = a_err + b_err;
    return {sum, err};
}


template <typename T>
constexpr Tuple<T, T> two_diff(const T &a, const T &b) noexcept {
    const T diff = a - b;
    const T a_prime = diff + b;
    const T b_prime = a_prime - diff;
    const T a_err = a - a_prime;
    const T b_err = b_prime - b;
    const T err = a_err + b_err;
    return {diff, err};
}


template <typename T>
constexpr Tuple<T, T> two_prod(const T &a, const T &b) noexcept {
    constexpr unsigned half_width = (compute_precision<T, unsigned>() + 1) / 2;
    const auto [a_hi, a_lo] = veltkamp_split<T, unsigned, half_width>(a);
    const auto [b_hi, b_lo] = veltkamp_split<T, unsigned, half_width>(b);
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

#endif // DZNL_ERROR_FREE_TRANSFORMATIONS_HPP_INCLUDED
*/
