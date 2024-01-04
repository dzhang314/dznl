#ifndef DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED
#define DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED

#include "Macros.hpp"

namespace dznl {


/**
 * @brief Return the additive identity element of a given numeric type T.
 */
template <typename T>
constexpr T zero() noexcept {
    return static_cast<T>(0);
}

/**
 * @brief Return the multiplicative identity element of a given numeric type T.
 */
template <typename T>
constexpr T one() noexcept {
    return static_cast<T>(1);
}

#define DZNL_DEFINE_NUMERIC_CONSTANT(TYPE, NAME, VALUE)                        \
    template <>                                                                \
    constexpr TYPE NAME<TYPE>() noexcept {                                     \
        return VALUE;                                                          \
    }

DZNL_DEFINE_NUMERIC_CONSTANT(signed char, zero, '\0')
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned char, zero, '\0')
DZNL_DEFINE_NUMERIC_CONSTANT(signed short int, zero, 0)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned short int, zero, 0U)
DZNL_DEFINE_NUMERIC_CONSTANT(signed int, zero, 0)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned int, zero, 0U)
DZNL_DEFINE_NUMERIC_CONSTANT(signed long int, zero, 0L)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned long int, zero, 0UL)
DZNL_DEFINE_NUMERIC_CONSTANT(signed long long int, zero, 0LL)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned long long int, zero, 0ULL)
DZNL_DEFINE_NUMERIC_CONSTANT(float, zero, 0.0F)
DZNL_DEFINE_NUMERIC_CONSTANT(double, zero, 0.0)
DZNL_DEFINE_NUMERIC_CONSTANT(long double, zero, 0.0L)

DZNL_DEFINE_NUMERIC_CONSTANT(signed char, one, '\1')
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned char, one, '\1')
DZNL_DEFINE_NUMERIC_CONSTANT(signed short int, one, 1)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned short int, one, 1U)
DZNL_DEFINE_NUMERIC_CONSTANT(signed int, one, 1)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned int, one, 1U)
DZNL_DEFINE_NUMERIC_CONSTANT(signed long int, one, 1L)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned long int, one, 1UL)
DZNL_DEFINE_NUMERIC_CONSTANT(signed long long int, one, 1LL)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned long long int, one, 1ULL)
DZNL_DEFINE_NUMERIC_CONSTANT(float, one, 1.0F)
DZNL_DEFINE_NUMERIC_CONSTANT(double, one, 1.0)
DZNL_DEFINE_NUMERIC_CONSTANT(long double, one, 1.0L)

#undef DZNL_DEFINE_NUMERIC_CONSTANT


/**
 * @brief Return the sum of a given element x of a numeric type T with itself.
 *
 * The expressions twice(x) and x + x should always be equivalent, but
 * twice(x) can be computed more efficiently than x + x for some types T.
 *
 * I would prefer to name this function "double,"
 * but `double` is a reserved keyword in C++.
 */
template <typename T>
constexpr T twice(DZNL_CONST T &x) noexcept {
    return x + x;
}

/**
 * @brief Return the product of a given element x
 *        of a numeric type T with itself.
 *
 * The expressions square(x) and x * x should always be equivalent, but
 * square(x) can be computed more efficiently than x * x for some types T.
 */
template <typename T>
constexpr T square(DZNL_CONST T &x) noexcept {
    return x * x;
}

/**
 * @brief Return the multiplicative inverse of a given element x
 *        of a numeric type T.
 */
template <typename T>
constexpr T inv(DZNL_CONST T &x) noexcept {
    return one<T>() / x;
}


/**
 * @brief Return the square root of a given element of a numeric type T.
 */
template <typename T>
constexpr T sqrt(DZNL_CONST T &) noexcept;

// In these implementations, we prefer inline assembly when possible
// because __builtin_sqrt() and friends can interact with errno.

#ifdef __x86_64__
template <>
float sqrt<float>(DZNL_CONST float &x) noexcept {
    float y;
    asm("sqrtss %1, %0" : "=x"(y) : "x"(x));
    return y;
}
#elif DZNL_HAS_BUILTIN(__builtin_sqrtf)
template <>
float sqrt<float>(DZNL_CONST float &x) noexcept {
    return __builtin_sqrtf(x);
}
#endif

#ifdef __x86_64__
template <>
double sqrt<double>(DZNL_CONST double &x) noexcept {
    double y;
    asm("sqrtsd %1, %0" : "=x"(y) : "x"(x));
    return y;
}

#elif DZNL_HAS_BUILTIN(__builtin_sqrt)
template <>
double sqrt<double>(DZNL_CONST double &x) noexcept {
    return __builtin_sqrt(x);
}
#endif

#ifdef __x86_64__
template <>
long double sqrt<long double>(DZNL_CONST long double &x) noexcept {
    long double y;
    asm("fsqrt" : "=t"(y) : "0"(x));
    return y;
}
#elif DZNL_HAS_BUILTIN(__builtin_sqrtl)
template <>
long double sqrt<long double>(DZNL_CONST long double &x) noexcept {
    return __builtin_sqrtl(x);
}
#endif


/**
 * @brief Return the absolute value of a given element of a numeric type T.
 */
template <typename T>
constexpr T abs(DZNL_CONST T &) noexcept;

#if DZNL_HAS_BUILTIN(__builtin_fabsf)
template <>
constexpr float abs<float>(DZNL_CONST float &x) noexcept {
    return __builtin_fabsf(x);
}
#endif

#if DZNL_HAS_BUILTIN(__builtin_fabs)
template <>
constexpr double abs<double>(DZNL_CONST double &x) noexcept {
    return __builtin_fabs(x);
}
#endif

#if DZNL_HAS_BUILTIN(__builtin_fabsl)
template <>
constexpr long double abs<long double>(DZNL_CONST long double &x) noexcept {
    return __builtin_fabsl(x);
}
#endif


} // namespace dznl

#endif // DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED
