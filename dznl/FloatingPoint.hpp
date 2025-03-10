#ifndef DZNL_FLOATING_POINT_HPP_INCLUDED
#define DZNL_FLOATING_POINT_HPP_INCLUDED

#include "Macros.hpp"
#include "Memory.hpp"
#include "NumericFunctions.hpp"
#include "NumericTypes.hpp" // IWYU pragma: keep
#include "Tuple.hpp"

#ifdef DZNL_REQUEST_FLOAT_TO_STRING
#include <boost/multiprecision/cpp_int.hpp>
#include <sstream>
#include <string>
#endif // DZNL_REQUEST_FLOAT_TO_STRING

namespace dznl {


template <typename FLOAT_T, typename INTEGER_T = int>
constexpr Tuple<FLOAT_T, INTEGER_T> compute_radix() {

    // The radix of a floating-point type is the smallest value of ulp(x) that
    // exceeds 1. For example, a binary floating-point type has possible ulp
    // values ..., 0.125, 0.25, 0.5, 1, **2**, 4, 8, ...; the radix is 2.
    // Similarly, a decimal floating-point type has possible ulp values
    // ..., 0.001, 0.01, 0.1, 1, **10**, 100, 1000, ...; the radix is 10.
    const FLOAT_T FLOAT_ONE = one<FLOAT_T>();

    // Step 1: Find a minimal floating-point number x such that ulp(x) > 1.
    // It suffices to consider powers of two, because for any radix r >= 2,
    // a power of two always lies between r^k and r^(k + 1) for any power k.
    FLOAT_T x = FLOAT_ONE;
    while (true) {
        const FLOAT_T y = x + FLOAT_ONE;
        const FLOAT_T z = y - x;
        if (!(z == FLOAT_ONE)) { break; }
        x += x;
    }

    // Step 2: Determine ulp(x). This is the radix.
    FLOAT_T float_radix = FLOAT_ONE;
    INTEGER_T integer_radix = one<INTEGER_T>();
    while (true) {
        const FLOAT_T y = x + float_radix;
        const FLOAT_T z = y - x;
        if (z == float_radix) { break; }
        float_radix += FLOAT_ONE;
        ++integer_radix;
    }
    return {float_radix, integer_radix};
}


template <typename FLOAT_T, typename INTEGER_T = int>
constexpr INTEGER_T compute_precision() {

    // Step 1: Compute the radix r as a floating-point number.
    const FLOAT_T float_radix = compute_radix<FLOAT_T, INTEGER_T>().first;

    // Step 2: Find the first power k such that ulp(r^k) > 1.
    const FLOAT_T FLOAT_ONE = one<FLOAT_T>();
    FLOAT_T power = FLOAT_ONE;
    INTEGER_T precision = 0;
    while (true) {
        const FLOAT_T y = power + FLOAT_ONE;
        const FLOAT_T z = y - power;
        if (!(z == FLOAT_ONE)) { break; }
        power *= float_radix;
        ++precision;
    }
    return precision;
}


template <typename FLOAT_T, typename SIGNED_T, typename UNSIGNED_T>
struct IEEEBinaryFloatData {

    static_assert(compute_radix<FLOAT_T>().second == 2);
    static_assert(sizeof(UNSIGNED_T) == sizeof(FLOAT_T));
    static constexpr UNSIGNED_T ONE = one<UNSIGNED_T>();

    static constexpr UNSIGNED_T BIT_SIZE = DZNL_CHAR_BIT * sizeof(FLOAT_T);
    static constexpr UNSIGNED_T SIGN_MASK = ONE << (BIT_SIZE - ONE);
    static constexpr UNSIGNED_T PRECISION =
        compute_precision<FLOAT_T, UNSIGNED_T>();
    static constexpr UNSIGNED_T EXPONENT_WIDTH = BIT_SIZE - PRECISION;
    static constexpr UNSIGNED_T MANTISSA_WIDTH = PRECISION - ONE;

    static_assert(DZNL_CHAR_BIT * sizeof(SIGNED_T) > EXPONENT_WIDTH);

    static constexpr UNSIGNED_T EXPONENT_BIAS =
        (ONE << (EXPONENT_WIDTH - ONE)) - ONE;
    static constexpr UNSIGNED_T MAX_RAW_EXPONENT =
        (ONE << EXPONENT_WIDTH) - ONE;
    static constexpr UNSIGNED_T EXPONENT_MASK = MAX_RAW_EXPONENT
                                                << MANTISSA_WIDTH;

    static constexpr UNSIGNED_T IMPLICIT_BIT = ONE << MANTISSA_WIDTH;
    static constexpr UNSIGNED_T MANTISSA_MASK = IMPLICIT_BIT - ONE;

    UNSIGNED_T data;
    UNSIGNED_T raw_exponent;
    UNSIGNED_T raw_mantissa;
    bool sign;

    explicit constexpr IEEEBinaryFloatData(const FLOAT_T &x) noexcept
        : data(bit_cast<UNSIGNED_T>(x))
        , raw_exponent((data & EXPONENT_MASK) >> MANTISSA_WIDTH)
        , raw_mantissa(data & MANTISSA_MASK)
        , sign((data & SIGN_MASK) >> (BIT_SIZE - ONE)) {}

    constexpr SIGNED_T exponent() const noexcept {
        return (
            (is_zero(raw_exponent) ? one<SIGNED_T>()
                                   : static_cast<SIGNED_T>(raw_exponent)) -
            static_cast<SIGNED_T>(EXPONENT_BIAS + MANTISSA_WIDTH)
        );
    }

    constexpr UNSIGNED_T mantissa() const noexcept {
        return is_zero(raw_exponent) ? raw_mantissa
                                     : (IMPLICIT_BIT | raw_mantissa);
    }

    constexpr bool is_ieee_nan() const noexcept {
        return (raw_exponent == MAX_RAW_EXPONENT) && !is_zero(raw_mantissa);
    }

    constexpr bool is_ieee_inf() const noexcept {
        return (raw_exponent == MAX_RAW_EXPONENT) && is_zero(raw_mantissa);
    }

    constexpr bool is_ieee_zero() const noexcept {
        return is_zero(raw_exponent) && is_zero(raw_mantissa);
    }

    constexpr bool lies_on_exponent_boundary() const noexcept {
        return (raw_exponent > ONE) && is_zero(raw_mantissa);
    }

}; // struct IEEEBinaryFloatData<FLOAT_T, SIGNED_T, UNSIGNED_T>


#ifdef DZNL_REQUEST_FLOAT_TO_STRING


namespace internal {


inline ::std::string binary_float_to_string(
    ::boost::multiprecision::cpp_int exponent,
    ::boost::multiprecision::cpp_int mantissa,
    bool tighten_lower_bound,
    bool tighten_upper_bound
) {

    if (mantissa == 0) { return "0.0"; }

    // Step 1: Compute immediate predecessor and successor mantissae
    // to determine the interval of information-preserving outputs.

    --exponent;
    mantissa <<= 1;
    ::boost::multiprecision::cpp_int lower_bound = mantissa;
    --lower_bound;
    ::boost::multiprecision::cpp_int upper_bound = mantissa;
    ++upper_bound;

    // Step 2: Tighten the lower bound if the input number
    // lies on a boundary between two exponent regimes.

    if (tighten_lower_bound || tighten_upper_bound) {
        --exponent;
        mantissa <<= 1;
        lower_bound <<= 1;
        upper_bound <<= 1;
        if (tighten_lower_bound) { ++lower_bound; }
        if (tighten_upper_bound) { --upper_bound; }
    }

    // Step 3: Convert exponent and mantissae from base 2 to base 10.

    if (exponent < 0) {
        for (::boost::multiprecision::cpp_int i = exponent; i < 0; ++i) {
            mantissa *= 5;
            lower_bound *= 5;
            upper_bound *= 5;
        }
    } else {
        while (exponent > 0) {
            --exponent;
            mantissa <<= 1;
            lower_bound <<= 1;
            upper_bound <<= 1;
        }
    }

    // Step 4: Trim unnecessary digits from the mantissae, using the interval
    // bounds to determine the shortest information-preserving representation.

    bool mantissa_exact = true;
    bool lower_exact = true;
    --upper_bound;
    ::boost::multiprecision::cpp_int next_digit = 0;

    while (true) {

        const ::boost::multiprecision::cpp_int lower_quot = lower_bound / 10;
        const ::boost::multiprecision::cpp_int upper_quot = upper_bound / 10;
        if (!(lower_quot < upper_quot)) { break; }

        const ::boost::multiprecision::cpp_int lower_rem = lower_bound % 10;
        const ::boost::multiprecision::cpp_int mantissa_rem = mantissa % 10;

        ++exponent;
        mantissa /= 10;
        lower_bound = lower_quot;
        upper_bound = upper_quot;

        mantissa_exact &= (next_digit == 0);
        lower_exact &= (lower_rem == 0);
        next_digit = mantissa_rem;
    }

    // Step 5: Adjust the final digit of the mantissa for correct rounding.

    if (mantissa < upper_bound) {
        if (next_digit > 5) {
            ++mantissa;
        } else if ((next_digit == 5) && ((mantissa & 1) || !mantissa_exact)) {
            ++mantissa;
        } else if ((mantissa == lower_bound) && !lower_exact) {
            ++mantissa;
        }
    }

    // Step 6: Convert the base-10 exponent and mantissa to a string,
    // taking the shorter between fixed-point and scientific notation.

    // I don't think mantissa == 0 is possible here, but just to be safe...
    if (mantissa == 0) { return "0.0"; }
    const ::std::string digits = mantissa.str();

    ::std::ostringstream result_scientific;
    if (digits.size() <= 1) {
        result_scientific << digits << ".0e" << exponent;
    } else {
        result_scientific << digits.substr(0, 1) << '.' << digits.substr(1)
                          << 'e' << (exponent + digits.size() - 1);
    }

    ::std::ostringstream result_fixed;
    if (exponent >= 0) {
        // All digits lie to the left of the decimal point.
        const ::std::string::size_type zero_count =
            static_cast<::std::string::size_type>(exponent);
        result_fixed << digits << ::std::string(zero_count, '0') << ".0";
    } else if (-exponent >= digits.size()) {
        // All digits lie to the right of the decimal point.
        const ::std::string::size_type zero_count =
            static_cast<::std::string::size_type>(-(exponent + digits.size()));
        result_fixed << "0." << ::std::string(zero_count, '0') << digits;
    } else {
        // Digits lie on both sides of the decimal point.
        const ::std::string::size_type break_point =
            static_cast<::std::string::size_type>(digits.size() + exponent);
        result_fixed << digits.substr(0, break_point) << '.'
                     << digits.substr(break_point);
    }

    const ::std::string sci_str = result_scientific.str();
    const ::std::string fix_str = result_fixed.str();
    return (sci_str.size() < fix_str.size()) ? sci_str : fix_str;
}


template <typename SIGNED_T, typename UNSIGNED_T, typename FLOAT_T>
::std::string
ieee_binary_float_to_string(const FLOAT_T &x, bool include_plus_sign = false) {
    IEEEBinaryFloatData<FLOAT_T, SIGNED_T, UNSIGNED_T> data(x);
    if (data.is_ieee_nan()) {
        return "NaN";
    } else if (data.is_ieee_inf()) {
        return data.sign ? "-Inf" : (include_plus_sign ? "+Inf" : "Inf");
    } else if (data.is_ieee_zero()) {
        return data.sign ? "-0.0" : (include_plus_sign ? "+0.0" : "0.0");
    } else {
        return (
            (data.sign ? "-" : (include_plus_sign ? "+" : "")) +
            binary_float_to_string(
                data.exponent(), data.mantissa(),
                data.lies_on_exponent_boundary(), false
            )
        );
    }
}


} // namespace internal


inline ::std::string to_string(const f32 &x, bool include_plus_sign = false) {
    return internal::ieee_binary_float_to_string<i32, u32>(
        x, include_plus_sign
    );
}


inline ::std::string to_string(const f64 &x, bool include_plus_sign = false) {
    return internal::ieee_binary_float_to_string<i64, u64>(
        x, include_plus_sign
    );
}


#ifdef DZNL_REQUEST_F16
inline ::std::string to_string(const f16 &x, bool include_plus_sign = false) {
    return internal::ieee_binary_float_to_string<i16, u16>(
        x, include_plus_sign
    );
}
#endif // DZNL_REQUEST_F16


#ifdef DZNL_REQUEST_BF16
inline ::std::string to_string(const bf16 &x, bool include_plus_sign = false) {
    return internal::ieee_binary_float_to_string<i16, u16>(
        x, include_plus_sign
    );
}
#endif // DZNL_REQUEST_BF16


#ifdef DZNL_REQUEST_F128
inline ::std::string to_string(const f128 &x, bool include_plus_sign = false) {
    return internal::ieee_binary_float_to_string<i128, u128>(
        x, include_plus_sign
    );
}
#endif // DZNL_REQUEST_F128


#ifdef DZNL_REQUEST_BOOST_MULTIPRECISION_INTEROP
template <
    unsigned Digits,
    ::boost::multiprecision::backends::digit_base_type DigitBase,
    typename Allocator,
    typename Exponent,
    Exponent MinExponent,
    Exponent MaxExponent,
    ::boost::multiprecision::expression_template_option ExpressionTemplates>
::std::string to_string(
    const ::boost::multiprecision::number<
        ::boost::multiprecision::cpp_bin_float<
            Digits,
            DigitBase,
            Allocator,
            Exponent,
            MinExponent,
            MaxExponent>,
        ExpressionTemplates> &x,
    bool include_plus_sign = false
) {
    const auto &backend = x.backend();
    const bool sign = backend.sign();
    const auto &exponent = backend.exponent();

    if (exponent == backend.exponent_nan) {
        return "NaN";
    } else if (exponent == backend.exponent_infinity) {
        return sign ? "-Inf" : (include_plus_sign ? "+Inf" : "Inf");
    } else if (exponent == backend.exponent_zero) {
        return sign ? "-0.0" : (include_plus_sign ? "+0.0" : "0.0");
    }

    ::boost::multiprecision::cpp_int adjusted_exponent = exponent;
    adjusted_exponent -= backend.bit_count;
    ++adjusted_exponent;

    const ::boost::multiprecision::cpp_int mantissa(backend.bits());
    ::boost::multiprecision::cpp_int boundary = 1;
    boundary <<= backend.bit_count;

    // TODO: Does boost::multiprecision::cpp_bin_float have subnormals?
    // For now, we assume it does not.

    return (
        (sign ? "-" : (include_plus_sign ? "+" : "")) +
        internal::binary_float_to_string(
            adjusted_exponent, mantissa, mantissa == boundary, false
        )
    );
}
#endif // DZNL_REQUEST_BOOST_MULTIPRECISION_INTEROP


#endif // DZNL_REQUEST_FLOAT_TO_STRING


} // namespace dznl

#endif // DZNL_FLOATING_POINT_HPP_INCLUDED
