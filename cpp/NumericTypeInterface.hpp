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


} // namespace dznl

#endif // DZNL_NUMERIC_TYPE_INTERFACE_HPP_INCLUDED
