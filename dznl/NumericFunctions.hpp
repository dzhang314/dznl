#ifndef DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED
#define DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED

#include "NumericConstants.hpp"

namespace dznl {


template <typename T>
constexpr bool is_zero(const T &x) {
    return x == zero<T>();
}


template <typename T>
constexpr bool is_one(const T &x) {
    return x == one<T>();
}


template <typename T>
constexpr bool is_nan(const T &x) {
    return !(x == x);
}


template <typename T>
constexpr bool is_inf(const T &x) {
    return (!is_nan(x)) & is_nan(x - x);
}


template <typename T>
constexpr bool sign_bit(const T &x) {
    return x < zero<T>();
}


} // namespace dznl

#endif // DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED
