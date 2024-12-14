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

    constexpr MultiFloat() noexcept {
        for (int i = 0; i < N; ++i) { limbs[i] = zero<T>(); }
    }

    constexpr MultiFloat(const T &x) noexcept {
        if (isfinite(x)) {
            if constexpr (N > 0) { limbs[0] = x; }
            for (int i = 1; i < N; ++i) { limbs[i] = zero<T>(); }
        } else {
            for (int i = 0; i < N; ++i) { limbs[i] = x; }
        }
    }

    template <int M>
    explicit constexpr MultiFloat(const MultiFloat<T, M> &rhs) noexcept {
        if constexpr (M < N) {
            for (int i = 0; i < M; ++i) { limbs[i] = rhs.limbs[i]; }
            for (int i = M; i < N; ++i) { limbs[i] = zero<T>(); }
        } else {
            for (int i = 0; i < N; ++i) { limbs[i] = rhs.limbs[i]; }
        }
    }

    constexpr bool identical(const MultiFloat &rhs) const noexcept {
        bool result = true;
        for (int i = 0; i < N; ++i) {
            result &= (limbs[i] == rhs.limbs[i]) |
                      (isnan(limbs[i]) && isnan(rhs.limbs[i]));
        }
        return result;
    }

    constexpr bool operator==(const MultiFloat &rhs) const noexcept {
        bool result = true;
        for (int i = 0; i < N; ++i) { result &= (limbs[i] == rhs.limbs[i]); }
        return result;
    }

    constexpr bool operator!=(const MultiFloat &rhs) const noexcept {
        bool result = false;
        for (int i = 0; i < N; ++i) { result |= (limbs[i] != rhs.limbs[i]); }
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


namespace internal {


template <int L, typename T, int M, int N>
constexpr MultiFloat<T, L> multifloat_add(
    const MultiFloat<T, M> &lhs, const MultiFloat<T, N> &rhs
) noexcept {
    MultiFloat<T, M + N> temp;
    for (int i = 0; i < M; ++i) { temp.limbs[i] = lhs.limbs[i]; }
    for (int i = 0; i < N; ++i) { temp.limbs[M + i] = rhs.limbs[i]; }
    temp.renormalize();
    return MultiFloat<T, L>(temp);
}


template <int L, typename T, int M, int N>
constexpr MultiFloat<T, L> multifloat_sub(
    const MultiFloat<T, M> &lhs, const MultiFloat<T, N> &rhs
) noexcept {
    MultiFloat<T, M + N> temp;
    for (int i = 0; i < M; ++i) { temp.limbs[i] = lhs.limbs[i]; }
    for (int i = 0; i < N; ++i) { temp.limbs[M + i] = -rhs.limbs[i]; }
    temp.renormalize();
    return MultiFloat<T, L>(temp);
}


template <int L, typename T, int M, int N>
constexpr MultiFloat<T, L> multifloat_mul(
    const MultiFloat<T, M> &lhs, const MultiFloat<T, N> &rhs
) noexcept {
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


#ifdef DZNL_REQUEST_FLOAT_TO_STRING


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


template <int N>
::std::string
to_string(const MultiFloat<f32, N> &x, bool include_plus_sign = false) {
    return ieee_binary_multifloat_to_string<i32, u32, f32, N>(
        x, include_plus_sign
    );
}


template <int N>
::std::string
to_string(const MultiFloat<f64, N> &x, bool include_plus_sign = false) {
    return ieee_binary_multifloat_to_string<i64, u64, f64, N>(
        x, include_plus_sign
    );
}


#ifdef DZNL_REQUEST_F16
template <int N>
::std::string
to_string(const MultiFloat<f16, N> &x, bool include_plus_sign = false) {
    return ieee_binary_multifloat_to_string<i16, u16, f16, N>(
        x, include_plus_sign
    );
}
#endif // DZNL_REQUEST_F16


#ifdef DZNL_REQUEST_BF16
template <int N>
::std::string
to_string(const MultiFloat<bf16, N> &x, bool include_plus_sign = false) {
    return ieee_binary_multifloat_to_string<i16, u16, bf16, N>(
        x, include_plus_sign
    );
}
#endif // DZNL_REQUEST_BF16


#ifdef DZNL_REQUEST_F128
template <int N>
::std::string
to_string(const MultiFloat<f128, N> &x, bool include_plus_sign = false) {
    return ieee_binary_multifloat_to_string<i128, u128, f128, N>(
        x, include_plus_sign
    );
}
#endif // DZNL_REQUEST_F128


#endif // DZNL_REQUEST_FLOAT_TO_STRING


} // namespace internal


} // namespace dznl

#endif // DZNL_MULTI_FLOAT_HPP_INCLUDED
