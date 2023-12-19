#ifndef DZNL_COMPLEX_NUMBERS_HPP_INCLUDED
#define DZNL_COMPLEX_NUMBERS_HPP_INCLUDED

#include "NumericTypeInterface.hpp"

namespace dznl {


template <typename T>
struct ComplexNumber {

    T real;
    T imag;

    constexpr ComplexNumber &operator+=(const ComplexNumber &rhs) noexcept {
        real += rhs.real;
        imag += rhs.imag;
        return *this;
    }

    constexpr ComplexNumber &operator+=(const T &rhs) noexcept {
        real += rhs;
        return *this;
    }

    constexpr ComplexNumber &operator-=(const ComplexNumber &rhs) noexcept {
        real -= rhs.real;
        imag -= rhs.imag;
        return *this;
    }

    constexpr ComplexNumber &operator+=(const T &rhs) noexcept {
        real += rhs;
        return *this;
    }

    constexpr ComplexNumber &operator*=(const T &rhs) noexcept {
        real *= rhs;
        imag *= rhs;
        return *this;
    }

    constexpr ComplexNumber &operator/=(const T &rhs) noexcept {
        real /= rhs;
        imag /= rhs;
        return *this;
    }

}; // struct ComplexNumber<T>


template <typename T>
constexpr ComplexNumber<T>
operator*(const ComplexNumber<T> &lhs, const ComplexNumber<T> &rhs) noexcept {
    return {
        lhs.real * rhs.real - lhs.imag * rhs.imag,
        lhs.real * rhs.imag + lhs.imag * rhs.real
    };
}


template <typename T>
constexpr ComplexNumber<T> zero<ComplexNumber<T>>() noexcept {
    return {zero<T>(), zero<T>()};
}


template <typename T>
constexpr ComplexNumber<T> one<ComplexNumber<T>>() noexcept {
    return {one<T>(), zero<T>()};
}


template <typename T>
constexpr bool is_zero<ComplexNumber<T>>(const ComplexNumber<T> &x) noexcept {
    return is_zero(x.real) && is_zero(x.dual);
}


template <typename T>
constexpr bool is_one<ComplexNumber<T>>(const ComplexNumber<T> &x) noexcept {
    return is_one(x.real) && is_zero(x.dual);
}


} // namespace dznl

#endif // DZNL_COMPLEX_NUMBERS_HPP_INCLUDED
