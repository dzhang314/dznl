#ifndef DZNL_NUMERIC_TYPE_INTERFACE_HPP_INCLUDED
#define DZNL_NUMERIC_TYPE_INTERFACE_HPP_INCLUDED

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
 * The expressions double_value(x) and x + x should always be equivalent, but
 * double_value(x) can be computed more efficiently than x + x for some types T.
 */
template <typename T>
constexpr T double_value(const T &) noexcept;


/**
 * @brief Return the product of a given element of a numeric type T with itself.
 *
 * The expressions square(x) and x * x should always be equivalent, but
 * square(x) can be computed more efficiently than x * x for some types T.
 */
template <typename T>
constexpr T square(const T &) noexcept;


/**
 * @brief Return the additive inverse of a given element of a numeric type T.
 */
template <typename T>
constexpr T negate(const T &) noexcept;


/**
 * @brief Return the multiplicative inverse of a given element
 *        of a numeric type T.
 */
template <typename T>
constexpr T inv(const T &) noexcept;


#define DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(TYPE)              \
    template <>                                                                \
    constexpr bool is_zero(const TYPE &x) noexcept {                           \
        return x == zero<TYPE>();                                              \
    }                                                                          \
    template <>                                                                \
    constexpr bool is_one(const TYPE &x) noexcept {                            \
        return x == one<TYPE>();                                               \
    }                                                                          \
    template <>                                                                \
    constexpr TYPE double_value(const TYPE &x) noexcept {                      \
        return x + x;                                                          \
    }                                                                          \
    template <>                                                                \
    constexpr TYPE square(const TYPE &x) noexcept {                            \
        return x * x;                                                          \
    }                                                                          \
    template <>                                                                \
    constexpr TYPE negate(const TYPE &x) noexcept {                            \
        return -x;                                                             \
    }


#define DZNL_DEFAULT_INV_IMPLEMENTATION(TYPE)                                  \
    template <>                                                                \
    constexpr TYPE inv(const TYPE &x) noexcept {                               \
        return one<TYPE>() / x;                                                \
    }


} // namespace dznl

#endif // DZNL_NUMERIC_TYPE_INTERFACE_HPP_INCLUDED
