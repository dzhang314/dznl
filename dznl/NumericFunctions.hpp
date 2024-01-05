#ifndef DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED
#define DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED

#include "Macros.hpp"

namespace dznl {


namespace internal {

template <typename T>
[[deprecated(
    "WARNING: You are using the default implementation of dznl::zero(). "
    "If possible, please provide a template specialization of dznl::zero<T>() "
    "with an optimized constructor for this specific type T."
)]] constexpr T
zero_default_impl() noexcept {
    return static_cast<T>(0);
}

template <typename T>
[[deprecated(
    "WARNING: You are using the default implementation of dznl::one(). "
    "If possible, please provide a template specialization of dznl::one<T>() "
    "with an optimized constructor for this specific type T."
)]] constexpr T
one_default_impl() noexcept {
    return static_cast<T>(1);
}

} // namespace internal

/**
 * @brief Construct and return an additive identity element
 *        of a numeric type `T`.
 */
template <typename T>
constexpr T zero() noexcept {
    return internal::zero_default_impl<T>();
}

/**
 * @brief Construct and return a multiplicative identity element
 *        of a numeric type `T`.
 */
template <typename T>
constexpr T one() noexcept {
    return internal::one_default_impl<T>();
}

#define DZNL_DEFINE_NUMERIC_CONSTANT(TYPE, NAME, VALUE)                        \
    template <>                                                                \
    constexpr TYPE NAME<TYPE>() noexcept {                                     \
        return VALUE;                                                          \
    }

DZNL_DEFINE_NUMERIC_CONSTANT(signed char, zero, '\0')
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned char, zero, '\0')
DZNL_DEFINE_NUMERIC_CONSTANT(signed short, zero, 0)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned short, zero, 0U)
DZNL_DEFINE_NUMERIC_CONSTANT(signed int, zero, 0)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned int, zero, 0U)
DZNL_DEFINE_NUMERIC_CONSTANT(signed long, zero, 0L)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned long, zero, 0UL)
DZNL_DEFINE_NUMERIC_CONSTANT(signed long long, zero, 0LL)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned long long, zero, 0ULL)
DZNL_DEFINE_NUMERIC_CONSTANT(float, zero, 0.0F)
DZNL_DEFINE_NUMERIC_CONSTANT(double, zero, 0.0)
DZNL_DEFINE_NUMERIC_CONSTANT(long double, zero, 0.0L)

DZNL_DEFINE_NUMERIC_CONSTANT(signed char, one, '\1')
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned char, one, '\1')
DZNL_DEFINE_NUMERIC_CONSTANT(signed short, one, 1)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned short, one, 1U)
DZNL_DEFINE_NUMERIC_CONSTANT(signed int, one, 1)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned int, one, 1U)
DZNL_DEFINE_NUMERIC_CONSTANT(signed long, one, 1L)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned long, one, 1UL)
DZNL_DEFINE_NUMERIC_CONSTANT(signed long long, one, 1LL)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned long long, one, 1ULL)
DZNL_DEFINE_NUMERIC_CONSTANT(float, one, 1.0F)
DZNL_DEFINE_NUMERIC_CONSTANT(double, one, 1.0)
DZNL_DEFINE_NUMERIC_CONSTANT(long double, one, 1.0L)

#ifdef __SIZEOF_INT128__
DZNL_DEFINE_NUMERIC_CONSTANT(__int128_t, zero, 0LL)
DZNL_DEFINE_NUMERIC_CONSTANT(__uint128_t, zero, 0ULL)
DZNL_DEFINE_NUMERIC_CONSTANT(__int128_t, one, 1LL)
DZNL_DEFINE_NUMERIC_CONSTANT(__uint128_t, one, 1ULL)
#endif // __SIZEOF_INT128__

#undef DZNL_DEFINE_NUMERIC_CONSTANT


/**
 * @brief Return the sum of a number `x` with itself.
 *
 * The expressions `dznl::twice(x)` and `x + x` should always be equivalent,
 * but in some cases, `dznl::twice(x)` can be computed more efficiently than
 * `x + x`.
 *
 * I would prefer to name this function `double`,
 * but `double` is a reserved keyword in C++.
 */
template <typename T>
[[deprecated(
    "WARNING: You are using the default implementation of dznl::twice(). "
    "If possible, please overload dznl::twice(T) or dznl::twice(const T &) "
    "with an optimized implementation for this specific type T."
)]] constexpr T
twice(DZNL_CONST T &x) noexcept {
    return x + x;
}

#define DZNL_LOOP_BODY(T)                                                      \
    constexpr T twice(T x) noexcept { return x + x; }
DZNL_LOOP_OVER_INTRINSIC_NUMERIC_TYPES
#undef DZNL_LOOP_BODY


/**
 * @brief Return the product of a number `x` with itself.
 *
 * The expressions `dznl::square(x)` and `x * x` should always be equivalent,
 * but in some cases, `dznl::square(x)` can be computed more efficiently than
 * `x * x`.
 */
template <typename T>
[[deprecated(
    "WARNING: You are using the default implementation of dznl::square(). "
    "If possible, please overload dznl::square(T) or dznl::square(const T &) "
    "with an optimized implementation for this specific type T."
)]] constexpr T
square(DZNL_CONST T &x) noexcept {
    return x * x;
}

#define DZNL_LOOP_BODY(T)                                                      \
    constexpr T square(T x) noexcept { return x * x; }
DZNL_LOOP_OVER_INTRINSIC_NUMERIC_TYPES
#undef DZNL_LOOP_BODY


/**
 * @brief Return the multiplicative inverse of a number `x`.
 *
 * `dznl::inv()` should not be defined for numeric types whose elements do not
 * have multiplicative inverses in general, such as integral types.
 */
template <typename T>
[[deprecated(
    "WARNING: You are using the default implementation of dznl::inv(). "
    "If possible, please overload dznl::inv(T) or dznl::inv(const T &) "
    "with an optimized implementation for this specific type T."
)]] constexpr T
inv(DZNL_CONST T &x) noexcept {
    return one<T>() / x;
}

#define DZNL_LOOP_BODY(T)                                                      \
    constexpr T inv(T x) noexcept { return one<T>() / x; }
DZNL_LOOP_OVER_FUNDAMENTAL_FLOATING_POINT_TYPES
#undef DZNL_LOOP_BODY


/**
 * @brief Return the square root of a number.
 *
 * `dznl::sqrt()` should not be defined for numeric types whose elements do not
 * have square roots in general, such as integral types.
 */
template <typename T>
constexpr T sqrt(DZNL_CONST T &) noexcept {
    static_assert(false, "dznl::sqrt() is not implemented for this type T.");
}

// In these implementations, we prefer inline assembly when possible
// because __builtin_sqrt() and friends can interact with errno.

#ifdef __x86_64__
inline float sqrt(float x) noexcept {
    float y;
    asm("sqrtss %1, %0" : "=x"(y) : "x"(x));
    return y;
}
#elif DZNL_HAS_BUILTIN(__builtin_sqrtf)
inline float sqrt(float x) noexcept { return __builtin_sqrtf(x); }
#endif

#ifdef __x86_64__
inline double sqrt(double x) noexcept {
    double y;
    asm("sqrtsd %1, %0" : "=x"(y) : "x"(x));
    return y;
}
#elif DZNL_HAS_BUILTIN(__builtin_sqrt)
inline double sqrt(double x) noexcept { return __builtin_sqrt(x); }
#endif

#ifdef __x86_64__
inline long double sqrt(long double x) noexcept {
    long double y;
    asm("fsqrt" : "=t"(y) : "0"(x));
    return y;
}
#elif DZNL_HAS_BUILTIN(__builtin_sqrtl)
inline long double sqrt(long double x) noexcept { return __builtin_sqrtl(x); }
#endif


/**
 * @brief Return the absolute value of a number.
 */
template <typename T>
constexpr T abs(const T &) noexcept {
    static_assert(false, "dznl::abs is not implemented for this type T.");
}

#if DZNL_HAS_BUILTIN(__builtin_fabsf)
constexpr float abs(float x) noexcept { return __builtin_fabsf(x); }
#endif

#if DZNL_HAS_BUILTIN(__builtin_fabs)
constexpr double abs(double x) noexcept { return __builtin_fabs(x); }
#endif

#if DZNL_HAS_BUILTIN(__builtin_fabsl)
constexpr long double abs(long double x) noexcept { return __builtin_fabsl(x); }
#endif


} // namespace dznl

#endif // DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED
