#ifndef DZNL_MULTI_FLOAT_HPP_INCLUDED
#define DZNL_MULTI_FLOAT_HPP_INCLUDED

#ifdef DZNL_REQUEST_FLOAT_TO_STRING
#include <boost/multiprecision/cpp_int.hpp>
#include <sstream>
#include <string>
#endif // DZNL_REQUEST_FLOAT_TO_STRING

#include "FloatingPoint.hpp" // IWYU pragma: keep
#include "NumericConstants.hpp"
#include "NumericFunctions.hpp"
#include "Tuple.hpp"

namespace dznl {


template <typename T>
constexpr Tuple<T, T> two_sum(const T &x, const T &y) noexcept {
    const T sum = x + y;
    const T x_prime = sum - y;
    const T y_prime = sum - x_prime;
    const T delta_x = x - x_prime;
    const T delta_y = y - y_prime;
    const T err = delta_x + delta_y;
    return {sum, err};
}


template <typename T>
constexpr Tuple<T, T> two_prod(const T &x, const T &y) noexcept {
    const T prod = x * y;
    const T err = fma(x, y, -prod);
    return {prod, err};
}


template <typename T, int N>
struct MultiFloat {

    T limbs[N];

    constexpr MultiFloat() noexcept
        : limbs{} {
        for (int i = 0; i < N; ++i) { limbs[i] = zero<T>(); }
    }

    constexpr MultiFloat(const T &x) noexcept
        : limbs{} {
        if (isfinite(x)) {
            if constexpr (N > 0) { limbs[0] = x; }
            for (int i = 1; i < N; ++i) { limbs[i] = zero<T>(); }
        } else {
            for (int i = 0; i < N; ++i) { limbs[i] = x; }
        }
    }

    template <int M>
    explicit constexpr MultiFloat(const MultiFloat<T, M> &rhs) noexcept
        : limbs{} {
        if constexpr (M < N) {
            for (int i = 0; i < M; ++i) { limbs[i] = rhs.limbs[i]; }
            for (int i = M; i < N; ++i) { limbs[i] = zero<T>(); }
        } else {
            for (int i = 0; i < N; ++i) { limbs[i] = rhs.limbs[i]; }
        }
    }

    constexpr MultiFloat operator+() const noexcept {
        MultiFloat result;
        for (int i = 0; i < N; ++i) { result.limbs[i] = +limbs[i]; }
        return result;
    }

    constexpr MultiFloat operator-() const noexcept {
        MultiFloat result;
        for (int i = 0; i < N; ++i) { result.limbs[i] = -limbs[i]; }
        return result;
    }

    constexpr bool identical(const MultiFloat &rhs) const noexcept {
        bool result = true;
        for (int i = 0; i < N; ++i) {
            result &= (limbs[i] == rhs.limbs[i]) |
                      (isnan(limbs[i]) && isnan(rhs.limbs[i]));
        }
        return result;
    }

private:

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

    constexpr void top_down_renormalize() noexcept {
        MultiFloat temp;
        while (true) {
            top_down_renorm_pass(temp);
            if (identical(temp)) { break; }
            temp.top_down_renorm_pass(*this);
            if (identical(temp)) { break; }
        }
    }

    constexpr void bottom_up_renormalize() noexcept {
        MultiFloat temp;
        while (true) {
            bottom_up_renorm_pass(temp);
            if (identical(temp)) { break; }
            temp.bottom_up_renorm_pass(*this);
            if (identical(temp)) { break; }
        }
    }

public:

    constexpr void renormalize() noexcept {
        for (int i = 0; i < N; ++i) {
            if (isnan(limbs[i])) {
                const T nan = limbs[i];
                for (int j = 0; j < N; ++j) { limbs[j] = nan; }
                return;
            }
        }
        int pos_inf_index = -1;
        int neg_inf_index = -1;
        for (int i = 0; i < N; ++i) {
            if (isinf(limbs[i])) {
                if (signbit(limbs[i])) {
                    if (neg_inf_index == -1) { neg_inf_index = i; }
                } else {
                    if (pos_inf_index == -1) { pos_inf_index = i; }
                }
            }
        }
        if ((pos_inf_index != -1) && (neg_inf_index != -1)) {
            const T nan = limbs[pos_inf_index] + limbs[neg_inf_index];
            for (int i = 0; i < N; ++i) { limbs[i] = nan; }
        } else if (pos_inf_index != -1) {
            const T pos_inf = limbs[pos_inf_index];
            for (int i = 0; i < N; ++i) { limbs[i] = pos_inf; }
        } else if (neg_inf_index != -1) {
            const T neg_inf = limbs[neg_inf_index];
            for (int i = 0; i < N; ++i) { limbs[i] = neg_inf; }
        } else {
            // top_down_renormalize();
            bottom_up_renormalize();
        }
    }

}; // struct MultiFloat<T, N>


template <typename T, int N>
struct constants<MultiFloat<T, N>> {

    static constexpr MultiFloat<T, N> zero() noexcept {
        return MultiFloat<T, N>();
    }

    static constexpr MultiFloat<T, N> one() noexcept {
        return MultiFloat<T, N>(constants<T>::one());
    }

}; // struct constants<MultiFloat<T, N>>


namespace internal {


template <int N, typename T, int L, int R>
[[deprecated("WARNING: You are using a large or unusual MultiFloat size that"
             " no optimized addition algorithm has been developed for."
             " A slow fallback algorithm will be used instead.")]]
constexpr MultiFloat<T, N> multifloat_add_fallback(
    const MultiFloat<T, L> &lhs, const MultiFloat<T, R> &rhs
) noexcept {
    MultiFloat<T, L + R> temp;
    for (int i = 0; i < L; ++i) { temp.limbs[i] = lhs.limbs[i]; }
    for (int i = 0; i < R; ++i) { temp.limbs[L + i] = rhs.limbs[i]; }
    temp.renormalize();
    return MultiFloat<T, N>(temp);
}


inline constexpr int
multifloat_mul_fallback_limb_count(int N, int L, int R) noexcept {
    int k = 0;
    for (int i = 0; i < L; ++i) {
        for (int j = 0; j < R; ++j) {
            if (i + j + 1 < N) {
                k += 2;
            } else if (i + j + 1 == N) {
                k += 1;
            }
        }
    }
    return k;
}


template <int N, typename T, int L, int R>
[[deprecated("WARNING: You are using a large or unusual MultiFloat size that"
             " no optimized multiplication algorithm has been developed for."
             " A slow fallback algorithm will be used instead.")]]
constexpr MultiFloat<T, N> multifloat_mul_fallback(
    const MultiFloat<T, L> &lhs, const MultiFloat<T, R> &rhs
) noexcept {
    constexpr int K = multifloat_mul_fallback_limb_count(N, L, R);
    MultiFloat<T, K> temp;
    int k = 0;
    for (int i = 0; i < L; ++i) {
        for (int j = 0; j < R; ++j) {
            if (i + j + 1 < N) {
                const auto [prod, err] = two_prod(lhs.limbs[i], rhs.limbs[j]);
                temp.limbs[k++] = prod;
                temp.limbs[k++] = err;
            } else if (i + j + 1 == N) {
                temp.limbs[k++] = lhs.limbs[i] * rhs.limbs[j];
            }
        }
    }
    temp.renormalize();
    return MultiFloat<T, N>(temp);
}


template <int N, int L, int R>
struct MultiFloatAlgorithms {

    template <typename T>
    static constexpr MultiFloat<T, N>
    add(const MultiFloat<T, L> &lhs, const MultiFloat<T, R> &rhs) noexcept {
        return multifloat_add_fallback<N>(lhs, rhs);
    }

    template <typename T>
    static constexpr MultiFloat<T, N>
    mul(const MultiFloat<T, L> &lhs, const MultiFloat<T, R> &rhs) noexcept {
        return multifloat_mul_fallback<N>(lhs, rhs);
    }

}; // struct MultiFloatAlgorithms<L, M, N>


template <>
struct MultiFloatAlgorithms<1, 1, 1> {

    template <typename T>
    static constexpr MultiFloat<T, 1>
    add(const MultiFloat<T, 1> &lhs, const MultiFloat<T, 1> &rhs) noexcept {
        return MultiFloat<T, 1>(lhs.limbs[0] + rhs.limbs[0]);
    }

    template <typename T>
    static constexpr MultiFloat<T, 1>
    mul(const MultiFloat<T, 1> &lhs, const MultiFloat<T, 1> &rhs) noexcept {
        return MultiFloat<T, 1>(lhs.limbs[0] * rhs.limbs[0]);
    }

}; // struct MultiFloatAlgorithms<1, 1, 1>


template <>
struct MultiFloatAlgorithms<2, 1, 1> {

    template <typename T>
    static constexpr MultiFloat<T, 2>
    add(const MultiFloat<T, 1> &lhs, const MultiFloat<T, 1> &rhs) noexcept {
        const auto [sum, err] = two_sum(lhs.limbs[0], rhs.limbs[0]);
        MultiFloat<T, 2> result;
        result.limbs[0] = sum;
        result.limbs[1] = err;
        return result;
    }

    template <typename T>
    static constexpr MultiFloat<T, 2>
    mul(const MultiFloat<T, 1> &lhs, const MultiFloat<T, 1> &rhs) noexcept {
        const auto [prod, err] = two_prod(lhs.limbs[0], rhs.limbs[0]);
        MultiFloat<T, 2> result;
        result.limbs[0] = prod;
        result.limbs[1] = err;
        return result;
    }

}; // struct MultiFloatAlgorithms<2, 1, 1>


} // namespace internal


template <int N, typename T, int L, int R>
constexpr MultiFloat<T, N> multifloat_add(
    const MultiFloat<T, L> &lhs, const MultiFloat<T, R> &rhs
) noexcept {
    return internal::MultiFloatAlgorithms<N, L, R>::add(lhs, rhs);
}


template <int N, typename T, int L, int R>
constexpr MultiFloat<T, N> multifloat_mul(
    const MultiFloat<T, L> &lhs, const MultiFloat<T, R> &rhs
) noexcept {
    return internal::MultiFloatAlgorithms<N, L, R>::mul(lhs, rhs);
}


namespace internal {


template <int N, typename T, int X, int E>
constexpr MultiFloat<T, N> multifloat_inv_impl(
    const MultiFloat<T, X> &x, const MultiFloat<T, E> &estimate
) noexcept {
    constexpr MultiFloat<T, 1> ONE = one<T>();
    const MultiFloat<T, E> residual =
        multifloat_add<E>(ONE, -multifloat_mul<E + E>(x, estimate));
    const MultiFloat<T, E> correction = multifloat_mul<E>(estimate, residual);
    if constexpr (E + E >= N) {
        return multifloat_add<N>(estimate, correction);
    } else {
        return multifloat_inv_impl<N>(
            x, multifloat_add<E + E>(estimate, correction)
        );
    }
}


template <int N, typename T, int X, int Y, int E>
constexpr MultiFloat<T, N> multifloat_div_impl(
    const MultiFloat<T, X> &x,
    const MultiFloat<T, Y> &y,
    const MultiFloat<T, E> &estimate
) noexcept {
    if constexpr (E + E >= N) {
        const MultiFloat<T, E> quotient = multifloat_mul<E>(x, estimate);
        const MultiFloat<T, E> residual =
            multifloat_add<E>(x, -multifloat_mul<E + E>(y, quotient));
        const MultiFloat<T, E> correction =
            multifloat_mul<E>(estimate, residual);
        return multifloat_add<N>(quotient, correction);
    } else {
        constexpr MultiFloat<T, 1> ONE = one<T>();
        const MultiFloat<T, E> residual =
            multifloat_add<E>(ONE, -multifloat_mul<E + E>(y, estimate));
        const MultiFloat<T, E> correction =
            multifloat_mul<E>(estimate, residual);
        return multifloat_div_impl<N>(
            x, y, multifloat_add<E + E>(estimate, correction)
        );
    }
}


} // namespace internal


template <int N, typename T, int X>
constexpr MultiFloat<T, N> multifloat_inv(const MultiFloat<T, X> &x) noexcept {
    return internal::multifloat_inv_impl<N>(
        x, MultiFloat<T, 1>(one<T>() / x.limbs[0])
    );
}


template <int N, typename T, int L, int R>
constexpr MultiFloat<T, N> multifloat_div(
    const MultiFloat<T, L> &lhs, const MultiFloat<T, R> &rhs
) noexcept {
    return internal::multifloat_div_impl<N>(
        lhs, rhs, MultiFloat<T, 1>(one<T>() / rhs.limbs[0])
    );
}


template <typename T, int N>
constexpr MultiFloat<T, N>
operator+(const MultiFloat<T, N> &lhs, const MultiFloat<T, N> &rhs) noexcept {
    return multifloat_add<N>(lhs, rhs);
}


template <typename T, int N>
constexpr MultiFloat<T, N> &
operator+=(MultiFloat<T, N> &lhs, const MultiFloat<T, N> &rhs) noexcept {
    lhs = lhs + rhs;
    return lhs;
}


template <typename T, int N>
constexpr MultiFloat<T, N>
operator-(const MultiFloat<T, N> &lhs, const MultiFloat<T, N> &rhs) noexcept {
    return multifloat_add<N>(lhs, -rhs);
}


template <typename T, int N>
constexpr MultiFloat<T, N> &
operator-=(MultiFloat<T, N> &lhs, const MultiFloat<T, N> &rhs) noexcept {
    lhs = lhs - rhs;
    return lhs;
}


template <typename T, int N>
constexpr MultiFloat<T, N>
operator*(const MultiFloat<T, N> &lhs, const MultiFloat<T, N> &rhs) noexcept {
    return multifloat_mul<N>(lhs, rhs);
}


template <typename T, int N>
constexpr MultiFloat<T, N> &
operator*=(MultiFloat<T, N> &lhs, const MultiFloat<T, N> &rhs) noexcept {
    lhs = lhs * rhs;
    return lhs;
}


template <typename T, int N>
constexpr MultiFloat<T, N>
operator/(const MultiFloat<T, N> &lhs, const MultiFloat<T, N> &rhs) noexcept {
    return multifloat_div<N>(lhs, rhs);
}


template <typename T, int N>
constexpr MultiFloat<T, N> &
operator/=(MultiFloat<T, N> &lhs, const MultiFloat<T, N> &rhs) noexcept {
    lhs = lhs / rhs;
    return lhs;
}


#ifdef DZNL_REQUEST_FLOAT_TO_STRING


namespace internal {


template <typename SIGNED_T, typename UNSIGNED_T, typename FLOAT_T, int N>
::std::string ieee_binary_multifloat_to_string(
    MultiFloat<FLOAT_T, N> x, bool include_plus_sign = false
) {
    using FloatData = IEEEBinaryFloatData<FLOAT_T, SIGNED_T, UNSIGNED_T>;
    if constexpr (N > 0) {
        x.renormalize();
        const FloatData head(x.limbs[0]);
        if (head.is_nan()) {
            return "NaN";
        } else if (head.is_inf()) {
            return head.sign ? "-Inf" : (include_plus_sign ? "+Inf" : "Inf");
        } else if (head.is_zero()) {
            return head.sign ? "-0.0" : (include_plus_sign ? "+0.0" : "0.0");
        } else {
            const FloatData tail(x.limbs[N - 1]);
            const SIGNED_T tail_exponent = tail.exponent();
            ::boost::multiprecision::cpp_int total_mantissa = 0;
            for (int i = 0; i < N; ++i) {
                const FloatData limb(x.limbs[i]);
                ::boost::multiprecision::cpp_int scaled_mantissa =
                    limb.mantissa();
                scaled_mantissa <<= (limb.exponent() - tail_exponent);
                if (limb.sign) {
                    total_mantissa -= scaled_mantissa;
                } else {
                    total_mantissa += scaled_mantissa;
                }
            }
            if (head.sign) { total_mantissa = -total_mantissa; }
            const bool tail_boundary = tail.lies_on_exponent_boundary();
            return (
                (head.sign ? "-" : (include_plus_sign ? "+" : "")) +
                binary_float_to_string(
                    tail_exponent,
                    total_mantissa,
                    tail_boundary && (head.sign == tail.sign),
                    tail_boundary && (head.sign != tail.sign)
                )
            );
        }
    } else {
        return include_plus_sign ? "+0.0" : "0.0";
    }
}


} // namespace internal


template <int N>
::std::string
to_string(const MultiFloat<f32, N> &x, bool include_plus_sign = false) {
    return internal::ieee_binary_multifloat_to_string<i32, u32, f32, N>(
        x, include_plus_sign
    );
}


template <int N>
::std::string
to_string(const MultiFloat<f64, N> &x, bool include_plus_sign = false) {
    return internal::ieee_binary_multifloat_to_string<i64, u64, f64, N>(
        x, include_plus_sign
    );
}


#ifdef DZNL_REQUEST_F16
template <int N>
::std::string
to_string(const MultiFloat<f16, N> &x, bool include_plus_sign = false) {
    return internal::ieee_binary_multifloat_to_string<i16, u16, f16, N>(
        x, include_plus_sign
    );
}
#endif // DZNL_REQUEST_F16


#ifdef DZNL_REQUEST_BF16
template <int N>
::std::string
to_string(const MultiFloat<bf16, N> &x, bool include_plus_sign = false) {
    return internal::ieee_binary_multifloat_to_string<i16, u16, bf16, N>(
        x, include_plus_sign
    );
}
#endif // DZNL_REQUEST_BF16


#ifdef DZNL_REQUEST_F128
template <int N>
::std::string
to_string(const MultiFloat<f128, N> &x, bool include_plus_sign = false) {
    return internal::ieee_binary_multifloat_to_string<i128, u128, f128, N>(
        x, include_plus_sign
    );
}
#endif // DZNL_REQUEST_F128


#endif // DZNL_REQUEST_FLOAT_TO_STRING


} // namespace dznl

#endif // DZNL_MULTI_FLOAT_HPP_INCLUDED
