#ifndef DZNL_MULTI_FLOAT_HPP_INCLUDED
#define DZNL_MULTI_FLOAT_HPP_INCLUDED

#include "NumericConstants.hpp"
#include "Tuple.hpp"

namespace dznl {


template <typename T>
constexpr Tuple<T, T> two_sum(const T &x, const T &y) {
    const T sum = x + y;
    const T x_prime = sum - y;
    const T y_prime = sum - x_prime;
    const T delta_x = x - x_prime;
    const T delta_y = y - y_prime;
    const T err = delta_x + delta_y;
    return {sum, err};
}


template <typename T>
constexpr Tuple<T, T> two_prod(const T &x, const T &y) {
    const T prod = x * y;
    const T err = __builtin_fma(x, y, -prod);
    return {prod, err};
}


template <typename T, int N>
struct MultiFloat {

    T limbs[N];

    constexpr bool operator==(const MultiFloat &other) const noexcept {
        bool result = true;
        for (int i = 0; i < N; ++i) { result &= (limbs[i] == other.limbs[i]); }
        return result;
    }

    constexpr bool operator!=(const MultiFloat &other) const noexcept {
        bool result = false;
        for (int i = 0; i < N; ++i) { result |= (limbs[i] != other.limbs[i]); }
        return result;
    }

    constexpr void top_down_renorm_pass() noexcept {
        for (int i = 1; i < N; ++i) {
            const auto [sum, err] = two_sum(limbs[i - 1], limbs[i]);
            limbs[i - 1] = sum;
            limbs[i] = err;
        }
    }

    constexpr void bottom_up_renorm_pass() noexcept {
        for (int i = N; i > 1; --i) {
            const auto [sum, err] = two_sum(limbs[i - 2], limbs[i - 1]);
            limbs[i - 2] = sum;
            limbs[i - 1] = err;
        }
    }

    constexpr void top_down_renorm_pass(MultiFloat &dst) const noexcept {
        if constexpr (N > 0) {
            T carry = limbs[0];
            for (int i = 1; i < N; ++i) {
                const auto [sum, err] = two_sum(carry, limbs[i]);
                dst.limbs[i - 1] = sum;
                carry = err;
            }
            dst.limbs[N - 1] = carry;
        }
    }

    constexpr void bottom_up_renorm_pass(MultiFloat &dst) const noexcept {
        if constexpr (N > 0) {
            T carry = limbs[N - 1];
            for (int i = N; i > 1; --i) {
                const auto [sum, err] = two_sum(limbs[i - 2], carry);
                carry = sum;
                dst.limbs[i - 1] = err;
            }
            dst.limbs[0] = carry;
        }
    }

    void top_down_renormalize() noexcept {
        MultiFloat<T, N> temp;
        while (true) {
            top_down_renorm_pass(temp);
            if (*this == temp) { break; }
            temp.top_down_renorm_pass(*this);
            if (*this == temp) { break; }
        }
    }

    void bottom_up_renormalize() noexcept {
        MultiFloat<T, N> temp;
        while (true) {
            bottom_up_renorm_pass(temp);
            if (*this == temp) { break; }
            temp.bottom_up_renorm_pass(*this);
            if (*this == temp) { break; }
        }
    }

    void renormalize() noexcept {
        // top_down_renormalize();
        bottom_up_renormalize();
    }

    constexpr MultiFloat() noexcept {
        for (int i = 0; i < N; ++i) { limbs[i] = zero<T>(); }
    }

    template <int M>
    constexpr MultiFloat(MultiFloat<T, M> other) noexcept {
        other.renormalize();
        if constexpr (M < N) {
            for (int i = 0; i < M; ++i) { limbs[i] = other.limbs[i]; }
            for (int i = M; i < N; ++i) { limbs[i] = zero<T>(); }
        } else {
            for (int i = 0; i < N; ++i) { limbs[i] = other.limbs[i]; }
        }
    }

}; // struct MultiFloat<T, N>


namespace internal {


template <typename T, int L, int M, int N>
constexpr MultiFloat<T, L>
multifloat_add(const MultiFloat<T, M> &lhs, const MultiFloat<T, N> &rhs) {
    MultiFloat<T, M + N> temp;
    for (int i = 0; i < M; ++i) { temp.limbs[i] = lhs.limbs[i]; }
    for (int i = 0; i < N; ++i) { temp.limbs[M + i] = rhs.limbs[i]; }
    temp.renormalize();
    return MultiFloat<T, L>(temp);
}


template <typename T, int L, int M, int N>
constexpr MultiFloat<T, L>
multifloat_sub(const MultiFloat<T, M> &lhs, const MultiFloat<T, N> &rhs) {
    MultiFloat<T, M + N> temp;
    for (int i = 0; i < M; ++i) { temp.limbs[i] = lhs.limbs[i]; }
    for (int i = 0; i < N; ++i) { temp.limbs[M + i] = -rhs.limbs[i]; }
    temp.renormalize();
    return MultiFloat<T, L>(temp);
}


template <typename T, int L, int M, int N>
constexpr MultiFloat<T, L>
multifloat_mul(const MultiFloat<T, M> &lhs, const MultiFloat<T, N> &rhs) {
    MultiFloat<T, 2 * M * N> temp;
    int k = 0;
    for (int i = 0; i < M; ++i) {
        for (int j = 0; j < N; ++j) {
            const auto [prod, err] = two_prod(lhs.limbs[i], rhs.limbs[j]);
            temp.limbs[k++] = prod;
            temp.limbs[k++] = err;
        }
    }
    temp.renormalize();
    return MultiFloat<T, L>(temp);
}


} // namespace internal


} // namespace dznl

#endif // DZNL_MULTI_FLOAT_HPP_INCLUDED
