#ifndef DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED
#define DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED

#include "NumericConstants.hpp"

namespace dznl {


template <typename T>
constexpr bool iszero(const T &x) {
    return x == zero<T>();
}


template <typename T>
constexpr bool isone(const T &x) {
    return x == one<T>();
}


template <typename T>
constexpr bool isnan(const T &x) {
    return !(x == x);
}


template <typename T>
constexpr bool isinf(const T &x) {
    return (!isnan(x)) & isnan(x - x);
}


template <typename T>
constexpr bool isfinite(const T &x) {
    return !(isnan(x)) & !(isnan(x - x));
}


template <typename T>
constexpr bool signbit(const T &x) {
    return x < zero<T>();
}


template <typename T>
constexpr T fma(const T &x, const T &y, const T &z) {
    return __builtin_fma(x, y, z);
}


namespace internal {


template <typename T, typename INTEGER_T>
constexpr T mul_by_doubling(const T &x, const INTEGER_T &n) {
    if (iszero(n)) {
        return zero<T>();
    } else if (isone(n)) {
        return x;
    } else {
        const T y = mul_by_doubling(x, n >> 1);
        const T z = y + y;
        return (n & 1) ? (z + x) : z;
    }
}


template <typename T, typename INTEGER_T>
constexpr T pow_by_squaring(const T &x, const INTEGER_T &n) {
    if (iszero(n)) {
        return one<T>();
    } else if (isone(n)) {
        return x;
    } else {
        const T y = pow_by_squaring(x, n >> 1);
        const T z = y * y;
        return (n & 1) ? (z * x) : z;
    }
}


template <typename T, typename INTEGER_T>
constexpr T bbp_pi_term(const INTEGER_T &n) {
    const T ONE = one<T>();
    const T TWO = ONE + ONE;
    const T FOUR = TWO + TWO;
    const T FIVE = FOUR + ONE;
    const T SIX = FOUR + TWO;
    const T EIGHT = FOUR + FOUR;
    const T SIXTEEN = EIGHT + EIGHT;
    const T eight_n = mul_by_doubling(EIGHT, n);
    const T term = FOUR / (eight_n + ONE) - TWO / (eight_n + FOUR) -
                   ONE / (eight_n + FIVE) - ONE / (eight_n + SIX);
    return term / pow_by_squaring(SIXTEEN, n);
}


template <typename T, typename INTEGER_T>
constexpr T bbp_pi_partial_sum(const INTEGER_T &n) {
    T result = zero<T>();
    for (INTEGER_T i = n; !iszero(i); --i) { result += bbp_pi_term<T>(i); }
    result += bbp_pi_term<T>(0);
    return result;
}


template <typename T, typename INTEGER_T>
constexpr T e_partial_sum(const INTEGER_T &n) {
    const T ONE = one<T>();
    T result = ONE;
    for (INTEGER_T i = n; !iszero(i); --i) {
        result = ONE + result / mul_by_doubling(ONE, i);
    }
    return result;
}


} // namespace internal


template <typename T>
constexpr T compute_pi() {
    T a = internal::bbp_pi_partial_sum<T>(0);
    T b = internal::bbp_pi_partial_sum<T>(1);
    for (int n = 2;; ++n) {
        const T c = internal::bbp_pi_partial_sum<T>(n);
        if ((a == b) && (b == c)) { return a; }
        a = b;
        b = c;
    }
}


template <typename T>
constexpr T compute_e() {
    T a = internal::e_partial_sum<T>(0);
    T b = internal::e_partial_sum<T>(1);
    for (int n = 2;; ++n) {
        const T c = internal::e_partial_sum<T>(n);
        if ((a == b) && (b == c)) { return a; }
        a = b;
        b = c;
    }
}


} // namespace dznl

#endif // DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED
