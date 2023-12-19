#ifndef DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED
#define DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED

namespace dznl {


/**
 * @brief Return the additive identity element of a given numeric type T.
 */
template <typename T>
constexpr T zero() noexcept;

/**
 * @brief Return the multiplicative identity element of a given numeric type T.
 */
template <typename T>
constexpr T one() noexcept;

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
DZNL_DEFINE_NUMERIC_CONSTANT(float, zero, 0.0F);
DZNL_DEFINE_NUMERIC_CONSTANT(double, zero, 0.0);
DZNL_DEFINE_NUMERIC_CONSTANT(long double, zero, 0.0L);

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
DZNL_DEFINE_NUMERIC_CONSTANT(float, one, 1.0F);
DZNL_DEFINE_NUMERIC_CONSTANT(double, one, 1.0);
DZNL_DEFINE_NUMERIC_CONSTANT(long double, one, 1.0L);

#undef DZNL_DEFINE_NUMERIC_CONSTANT


/**
 * @brief Test whether a given element of a numeric type T
 *        is an additive identity element.
 */
template <typename T>
constexpr bool is_zero(const T &) noexcept;

/**
 * @brief Test whether a given element of a numeric type T
 *        is a multiplicative identity element.
 */
template <typename T>
constexpr bool is_one(const T &) noexcept;

/**
 * @brief Return the sum of a given element of a numeric type T with itself.
 *
 * The expressions twice(x) and x + x should always be equivalent, but
 * twice(x) can be computed more efficiently than x + x for some types T.
 *
 * I would prefer to name this function "double,"
 * but "double" is a reserved keyword in C++.
 */
template <typename T>
constexpr T twice(const T &) noexcept;

/**
 * @brief Return the product of a given element of a numeric type T with itself.
 *
 * The expressions square(x) and x * x should always be equivalent, but
 * square(x) can be computed more efficiently than x * x for some types T.
 */
template <typename T>
constexpr T square(const T &) noexcept;

#define DZNL_DEFAULT_NUMERIC_FUNCTION_IMPLEMENTATIONS(TYPE)                    \
    template <>                                                                \
    constexpr bool is_zero(const TYPE &x) noexcept {                           \
        return x == zero<TYPE>();                                              \
    }                                                                          \
    template <>                                                                \
    constexpr bool is_one(const TYPE &x) noexcept {                            \
        return x == one<TYPE>();                                               \
    }                                                                          \
    template <>                                                                \
    constexpr TYPE twice(const TYPE &x) noexcept {                             \
        return x + x;                                                          \
    }                                                                          \
    template <>                                                                \
    constexpr TYPE square(const TYPE &x) noexcept {                            \
        return x * x;                                                          \
    }

DZNL_DEFAULT_NUMERIC_FUNCTION_IMPLEMENTATIONS(signed char)
DZNL_DEFAULT_NUMERIC_FUNCTION_IMPLEMENTATIONS(unsigned char)
DZNL_DEFAULT_NUMERIC_FUNCTION_IMPLEMENTATIONS(signed short int)
DZNL_DEFAULT_NUMERIC_FUNCTION_IMPLEMENTATIONS(unsigned short int)
DZNL_DEFAULT_NUMERIC_FUNCTION_IMPLEMENTATIONS(signed int)
DZNL_DEFAULT_NUMERIC_FUNCTION_IMPLEMENTATIONS(unsigned int)
DZNL_DEFAULT_NUMERIC_FUNCTION_IMPLEMENTATIONS(signed long int)
DZNL_DEFAULT_NUMERIC_FUNCTION_IMPLEMENTATIONS(unsigned long int)
DZNL_DEFAULT_NUMERIC_FUNCTION_IMPLEMENTATIONS(signed long long int)
DZNL_DEFAULT_NUMERIC_FUNCTION_IMPLEMENTATIONS(unsigned long long int)
DZNL_DEFAULT_NUMERIC_FUNCTION_IMPLEMENTATIONS(float)
DZNL_DEFAULT_NUMERIC_FUNCTION_IMPLEMENTATIONS(double)
DZNL_DEFAULT_NUMERIC_FUNCTION_IMPLEMENTATIONS(long double)

#undef DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS


/**
 * @brief Return the multiplicative inverse of a given element
 *        of a numeric type T.
 */
template <typename T>
constexpr T inv(const T &) noexcept;

#define DZNL_DEFAULT_INV_IMPLEMENTATION(TYPE)                                  \
    template <>                                                                \
    constexpr TYPE inv(const TYPE &x) noexcept {                               \
        return one<TYPE>() / x;                                                \
    }

DZNL_DEFAULT_INV_IMPLEMENTATION(float)
DZNL_DEFAULT_INV_IMPLEMENTATION(double)
DZNL_DEFAULT_INV_IMPLEMENTATION(long double)

#undef DZNL_DEFAULT_INV_IMPLEMENTATION


/**
 * @brief Return the square root of a given element of a numeric type T.
 */
template <typename T>
constexpr T sqrt(const T &) noexcept;

#if __has_builtin(__builtin_sqrtf)
template <>
constexpr float sqrt<float>(const float &x) noexcept {
    return __builtin_sqrtf(x);
}
#endif

#if __has_builtin(__builtin_sqrt)
template <>
constexpr double sqrt<double>(const double &x) noexcept {
    return __builtin_sqrt(x);
}
#endif

#if __has_builtin(__builtin_sqrtl)
template <>
constexpr long double sqrt<long double>(const long double &x) noexcept {
    return __builtin_sqrtl(x);
}
#endif


/**
 * @brief Return the absolute value of a given element of a numeric type T.
 */
template <typename T>
constexpr T abs(const T &) noexcept;

#if __has_builtin(__builtin_fabsf)
template <>
constexpr float abs<float>(const float &x) noexcept {
    return __builtin_fabsf(x);
}
#endif

#if __has_builtin(__builtin_fabs)
template <>
constexpr double abs<double>(const double &x) noexcept {
    return __builtin_fabs(x);
}
#endif

#if __has_builtin(__builtin_fabsl)
template <>
constexpr long double abs<long double>(const long double &x) noexcept {
    return __builtin_fabsl(x);
}
#endif


} // namespace dznl

#endif // DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED
