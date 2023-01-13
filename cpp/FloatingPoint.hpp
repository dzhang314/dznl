#ifndef DZNL_FLOATING_POINT_HPP_INCLUDED
#define DZNL_FLOATING_POINT_HPP_INCLUDED

namespace dznl {


/**
 * @brief Given a number x (of any type T, integer or floating-point) and a
 * natural number n, compute and return x^n.
 *
 * This function does NOT use the exponentiation-by-squaring optimization, so
 * it performs fully-left-associated multiplications (e.g., ((x * x) * x) * x)
 * in the computation of x^n.
 */
template <typename T>
constexpr T pow_slow(T base, unsigned int exponent) {
    T result = static_cast<T>(1.0);
    for (unsigned int i = 0; i < exponent; ++i) {
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
template <typename T>
constexpr T pow(T base, unsigned int exponent) {
    T accum = base;
    T result = static_cast<T>(1.0);
    while (exponent) {
        if (exponent & 1) {
            result *= accum;
        }
        accum *= accum;
        exponent >>= 1;
    }
    return result;
}


/**
 * @brief Given a floating-point number b, compute and return the first natural
 * number n such that b^n is large.
 *
 * We say that a floating-point number x is "large" if the least significant
 * digit of x has magnitude greater than one, i.e., ulp(x) > 1.
 */
template <typename T>
constexpr unsigned int compute_large_exponent(T base) {
    constexpr T one = static_cast<T>(1.0);
    T power = one;
    unsigned int result = 0;
    while ((power + one) - power == one) {
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
template <typename T>
constexpr T compute_radix() noexcept {
    constexpr T one = static_cast<T>(1.0);
    constexpr T two = static_cast<T>(2.0);
    constexpr T large_pow2 = pow_slow(two, compute_large_exponent<T>(two));
    T result = one;
    while ((large_pow2 + result) - large_pow2 != result) {
        result += one;
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
template <typename T>
constexpr unsigned int compute_precision() noexcept {
    return compute_large_exponent<T>(compute_radix<T>());
}


} // namespace dznl

#endif // DZNL_FLOATING_POINT_HPP_INCLUDED
