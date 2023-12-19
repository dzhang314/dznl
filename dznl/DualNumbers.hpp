#ifndef DZNL_DUAL_NUMBERS_HPP_INCLUDED
#define DZNL_DUAL_NUMBERS_HPP_INCLUDED

#include "NumericFunctions.hpp"

namespace dznl {


template <typename T>
struct DualNumber {

    T real;
    T dual;

    constexpr DualNumber &operator+=(const DualNumber &rhs) noexcept {
        real += rhs.real;
        dual += rhs.dual;
        return *this;
    }

    constexpr DualNumber &operator+=(const T &rhs) noexcept {
        real += rhs;
        return *this;
    }

    constexpr DualNumber &operator-=(const DualNumber &rhs) noexcept {
        real -= rhs.real;
        dual -= rhs.dual;
        return *this;
    }

    constexpr DualNumber &operator-=(const T &rhs) noexcept {
        real -= rhs;
        return *this;
    }

    constexpr DualNumber &operator*=(const T &rhs) noexcept {
        real *= rhs;
        dual *= rhs;
        return *this;
    }

    constexpr DualNumber &operator/=(const T &rhs) noexcept {
        real /= rhs;
        dual /= rhs;
        return *this;
    }

}; // struct DualNumber<T>


template <typename T>
constexpr DualNumber<T>
operator*(const DualNumber<T> &lhs, const DualNumber<T> &rhs) noexcept {
    return {lhs.real * rhs.real, lhs.real * rhs.dual + lhs.dual * rhs.real};
}


template <typename T>
constexpr DualNumber<T> zero<DualNumber<T>>() noexcept {
    return {zero<T>(), zero<T>()};
}


template <typename T>
constexpr DualNumber<T> one<DualNumber<T>>() noexcept {
    return {one<T>(), zero<T>()};
}


template <typename T>
constexpr bool is_zero<DualNumber<T>>(const DualNumber<T> &x) noexcept {
    return is_zero(x.real) && is_zero(x.dual);
}


template <typename T>
constexpr bool is_one<DualNumber<T>>(const DualNumber<T> &x) noexcept {
    return is_one(x.real) && is_zero(x.dual);
}


} // namespace dznl

#endif // DZNL_DUAL_NUMBERS_HPP_INCLUDED
