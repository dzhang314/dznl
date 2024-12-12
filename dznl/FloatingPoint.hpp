#ifndef DZNL_FLOATING_POINT_HPP_INCLUDED
#define DZNL_FLOATING_POINT_HPP_INCLUDED

#include "Macros.hpp"
#include "Memory.hpp"
#include "NumericConstants.hpp"
#include "NumericFunctions.hpp" // IWYU pragma: keep
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


template <typename UNSIGNED_T, typename FLOAT_T>
Tuple<bool, UNSIGNED_T, UNSIGNED_T> split_ieee_binary_float(const FLOAT_T &x) {

    static_assert(sizeof(UNSIGNED_T) == sizeof(FLOAT_T));
    constexpr UNSIGNED_T ONE = one<UNSIGNED_T>();

    constexpr UNSIGNED_T NUM_BITS =
        static_cast<UNSIGNED_T>(DZNL_CHAR_BIT * sizeof(FLOAT_T));
    static_assert(compute_radix<FLOAT_T>().second == 2);
    constexpr UNSIGNED_T PRECISION = compute_precision<FLOAT_T, UNSIGNED_T>();
    static_assert(PRECISION + ONE < NUM_BITS);

    constexpr UNSIGNED_T EXPONENT_WIDTH = NUM_BITS - PRECISION;
    constexpr UNSIGNED_T MANTISSA_WIDTH = PRECISION - ONE;
    static_assert(ONE + EXPONENT_WIDTH + MANTISSA_WIDTH == NUM_BITS);

    constexpr UNSIGNED_T SIGN_MASK = ONE << (NUM_BITS - ONE);
    constexpr UNSIGNED_T EXPONENT_MASK = ((ONE << EXPONENT_WIDTH) - ONE)
                                         << MANTISSA_WIDTH;
    constexpr UNSIGNED_T MANTISSA_MASK = (ONE << MANTISSA_WIDTH) - ONE;

    const UNSIGNED_T data = bit_cast<UNSIGNED_T>(x);
    const bool sign = static_cast<bool>((data & SIGN_MASK) >> (NUM_BITS - ONE));
    const UNSIGNED_T raw_exponent = (data & EXPONENT_MASK) >> MANTISSA_WIDTH;
    const UNSIGNED_T raw_mantissa = data & MANTISSA_MASK;

    return {sign, raw_exponent, raw_mantissa};
}


#ifdef DZNL_REQUEST_FLOAT_TO_STRING

template <typename SIGNED_T, typename UNSIGNED_T, typename FLOAT_T>
std::string
ieee_binary_float_to_string(const FLOAT_T &x, bool include_plus_sign = false) {

    // Step 0: Compute the bit width of the provided floating-point type
    // and the size of its exponent and mantissa fields. This can be done
    // at compile-time using clever constexpr algorithms.

    static_assert(sizeof(SIGNED_T) == sizeof(FLOAT_T));
    static_assert(sizeof(UNSIGNED_T) == sizeof(FLOAT_T));
    constexpr SIGNED_T SIGNED_ONE = one<SIGNED_T>();
    constexpr UNSIGNED_T UNSIGNED_ONE = one<UNSIGNED_T>();

    constexpr UNSIGNED_T NUM_BITS =
        static_cast<UNSIGNED_T>(DZNL_CHAR_BIT * sizeof(FLOAT_T));
    static_assert(compute_radix<FLOAT_T>().second == 2);
    constexpr UNSIGNED_T PRECISION = compute_precision<FLOAT_T, UNSIGNED_T>();
    static_assert(PRECISION + UNSIGNED_ONE < NUM_BITS);

    constexpr UNSIGNED_T EXPONENT_WIDTH = NUM_BITS - PRECISION;
    constexpr UNSIGNED_T MANTISSA_WIDTH = PRECISION - UNSIGNED_ONE;
    static_assert(UNSIGNED_ONE + EXPONENT_WIDTH + MANTISSA_WIDTH == NUM_BITS);

    constexpr UNSIGNED_T MAX_RAW_EXPONENT =
        (UNSIGNED_ONE << EXPONENT_WIDTH) - UNSIGNED_ONE;
    constexpr SIGNED_T EXPONENT_BIAS =
        (SIGNED_ONE << (EXPONENT_WIDTH - UNSIGNED_ONE)) - SIGNED_ONE;
    constexpr UNSIGNED_T IMPLICIT_BIT = UNSIGNED_ONE << MANTISSA_WIDTH;

    // Step 1: Split the provided floating-point number
    // into its raw sign, exponent, and mantissa fields.

    const auto [sign, raw_exponent, raw_mantissa] =
        split_ieee_binary_float<UNSIGNED_T>(x);

    // Step 2: Handle special values, including NaN, positive
    // and negative infinity, and positive and negative zero.

    const bool is_subnormal = is_zero(raw_exponent);
    const bool raw_mantissa_zero = is_zero(raw_mantissa);

    if (raw_exponent == MAX_RAW_EXPONENT) {
        if (raw_mantissa_zero) {
            return sign ? "-Inf" : (include_plus_sign ? "+Inf" : "Inf");
        } else {
            return "NaN";
        }
    } else if (is_subnormal && raw_mantissa_zero) {
        return sign ? "-0.0" : (include_plus_sign ? "+0.0" : "0.0");
    }

    // Step 3: Decode the true exponent and mantissa from their raw binary
    // values, applying IEEE 754 exponent bias and subnormal number rules.

    const SIGNED_T exponent =
        (is_subnormal ? SIGNED_ONE : static_cast<SIGNED_T>(raw_exponent)) -
        (EXPONENT_BIAS + static_cast<SIGNED_T>(MANTISSA_WIDTH));
    const UNSIGNED_T mantissa =
        is_subnormal ? raw_mantissa : (IMPLICIT_BIT | raw_mantissa);

    boost::multiprecision::cpp_int exponent_mp = exponent;
    boost::multiprecision::cpp_int mantissa_mp = mantissa;

    // Step 4: Compute mantissae of immediate predecessor and successor
    // to determine the interval of information-preserving outputs.

    --exponent_mp;
    mantissa_mp <<= 1;
    boost::multiprecision::cpp_int mantissa_lo = mantissa_mp;
    boost::multiprecision::cpp_int mantissa_hi = mantissa_mp;
    --mantissa_lo;
    ++mantissa_hi;

    // Tighten the lower bound if the input number
    // lies on a boundary between two exponent regimes.

    if (raw_mantissa_zero && !is_one(raw_exponent)) {
        --exponent_mp;
        mantissa_lo <<= 1;
        mantissa_mp <<= 1;
        mantissa_hi <<= 1;
        ++mantissa_lo;
    }

    // Step 5: Use exact arbitrary-width integer arithmetic to
    // convert the exponent and mantissae from base 2 to base 10.

    if (exponent_mp < 0) {
        for (boost::multiprecision::cpp_int i = exponent_mp; i < 0; ++i) {
            mantissa_lo *= 5;
            mantissa_mp *= 5;
            mantissa_hi *= 5;
        }
    } else {
        while (exponent_mp > 0) {
            mantissa_lo <<= 1;
            mantissa_mp <<= 1;
            mantissa_hi <<= 1;
            --exponent_mp;
        }
    }

    // Step 6: Trim unnecessary digits from the mantissae, using the interval
    // bounds to determine the shortest information-preserving representation.

    --mantissa_hi;
    bool lo_exact = true;
    bool mp_exact = true;
    boost::multiprecision::cpp_int next_digit = 0;

    while (true) {

        const boost::multiprecision::cpp_int lo_quot = mantissa_lo / 10;
        const boost::multiprecision::cpp_int hi_quot = mantissa_hi / 10;
        if (!(lo_quot < hi_quot)) { break; }

        const boost::multiprecision::cpp_int lo_rem = mantissa_lo % 10;
        const boost::multiprecision::cpp_int mp_rem = mantissa_mp % 10;

        ++exponent_mp;
        mantissa_lo = lo_quot;
        mantissa_mp /= 10;
        mantissa_hi = hi_quot;

        lo_exact &= (lo_rem == 0);
        mp_exact &= (next_digit == 0);
        next_digit = mp_rem;
    }

    // Step 7: Adjust the final digit of the mantissa for correct rounding.

    if (mantissa_mp < mantissa_hi) {
        if (next_digit > 5) {
            ++mantissa_mp;
        } else if ((next_digit == 5) && ((mantissa_mp & 1) || !mp_exact)) {
            ++mantissa_mp;
        } else if ((mantissa_lo == mantissa_mp) && !lo_exact) {
            ++mantissa_mp;
        }
    }

    // Step 8: Convert the base-10 exponent and mantissa to a string.

    std::ostringstream digit_stream;
    digit_stream << mantissa_mp;
    const std::string digits = digit_stream.str();

    std::ostringstream result_scientific;
    std::ostringstream result_fixed;
    if (sign) {
        result_scientific << "-";
        result_fixed << "-";
    } else if (include_plus_sign) {
        result_scientific << "+";
        result_fixed << "+";
    }

    if (digits.size() <= 1) {
        result_scientific << digits << ".0e" << exponent_mp;
    } else {
        result_scientific << digits.substr(0, 1) << "." << digits.substr(1)
                          << "e" << (exponent_mp + (digits.size() - 1));
    }

    if (exponent_mp >= 0) {
        // All digits lie to the left of the decimal point.
        const std::string::size_type zero_count =
            static_cast<std::string::size_type>(exponent_mp);
        result_fixed << digits << std::string(zero_count, '0') << ".0";
    } else if (-exponent_mp >= digits.size()) {
        // All digits lie to the right of the decimal point.
        const std::string::size_type zero_count =
            static_cast<std::string::size_type>(-(exponent_mp + digits.size()));
        result_fixed << "0." << std::string(zero_count, '0') << digits;
    } else {
        // Digits lie on both sides of the decimal point.
        const std::string::size_type break_point =
            static_cast<std::string::size_type>(digits.size() + exponent_mp);
        result_fixed << digits.substr(0, break_point) << '.'
                     << digits.substr(break_point);
    }

    const std::string sci_str = result_scientific.str();
    const std::string fix_str = result_fixed.str();
    return (sci_str.size() < fix_str.size()) ? sci_str : fix_str;
}

std::string to_string(const f32 &x, bool include_plus_sign = false) {
    return ieee_binary_float_to_string<i32, u32>(x, include_plus_sign);
}

std::string to_string(const f64 &x, bool include_plus_sign = false) {
    return ieee_binary_float_to_string<i64, u64>(x, include_plus_sign);
}

#ifdef DZNL_REQUEST_F16
std::string to_string(const f16 &x, bool include_plus_sign = false) {
    return ieee_binary_float_to_string<i16, u16>(x, include_plus_sign);
}
#endif // DZNL_REQUEST_F16

#ifdef DZNL_REQUEST_BF16
std::string to_string(const bf16 &x, bool include_plus_sign = false) {
    return ieee_binary_float_to_string<i16, u16>(x, include_plus_sign);
}
#endif // DZNL_REQUEST_BF16

#ifdef DZNL_REQUEST_F128
std::string to_string(const f128 &x, bool include_plus_sign = false) {
    return ieee_binary_float_to_string<i128, u128>(x, include_plus_sign);
}
#endif // DZNL_REQUEST_F128

#endif // DZNL_REQUEST_FLOAT_TO_STRING


} // namespace dznl

#endif // DZNL_FLOATING_POINT_HPP_INCLUDED
