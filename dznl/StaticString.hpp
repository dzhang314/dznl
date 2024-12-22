#ifndef DZNL_STATIC_STRING_HPP_INCLUDED
#define DZNL_STATIC_STRING_HPP_INCLUDED

#include "FloatingPoint.hpp"
#include "Memory.hpp"
#include "NumericFunctions.hpp"
#include "NumericTypes.hpp"

namespace dznl {


// TODO: Revisit Clang unsafe-buffer-usage warnings when
// https://github.com/llvm/llvm-project/issues/64646 is resolved.
#ifdef __clang__
#pragma clang unsafe_buffer_usage begin
#endif // __clang__


template <int N>
struct StaticString {


    char data[N + 1];


    constexpr StaticString() noexcept
        : data{} {
        for (int i = 0; i < N; ++i) { data[i] = '\0'; }
        data[N] = '\0';
    }


    constexpr StaticString(const char *s) noexcept
        : data{} {
        bool done = false;
        for (int i = 0; i < N; ++i) {
            if (s[i] == '\0') { done = true; }
            data[i] = done ? '\0' : s[i];
        }
        data[N] = '\0';
    }


    constexpr StaticString &operator=(const char *s) noexcept {
        bool done = false;
        for (int i = 0; i < N; ++i) {
            if (s[i] == '\0') { done = true; }
            data[i] = done ? '\0' : s[i];
        }
        data[N] = '\0';
        return *this;
    }


    constexpr char &operator[](int i) noexcept {
        if (i < 0) {
            return data[0];
        } else if (i >= N) {
            return data[N - 1];
        } else {
            return data[i];
        }
    }


    constexpr int length() const noexcept {
        for (int i = 0; i < N; ++i) {
            if (data[i] == '\0') { return i; }
        }
        return N;
    }


    constexpr bool operator==(const char *s) const noexcept {
        for (int i = 0; i < N; ++i) {
            if (data[i] != s[i]) { return false; }
            if (data[i] == '\0') { return true; }
        }
        return (s[N] == '\0');
    }


}; // struct StaticString<N>


#ifdef __clang__
#pragma clang unsafe_buffer_usage end
#endif // __clang__


template <int N>
StaticString(const char (&)[N]) -> StaticString<N - 1>;


namespace internal {


constexpr char digit_char(int digit) noexcept {
    return static_cast<char>('0' + digit);
}


constexpr char nibble_to_hex_char(int nibble) noexcept {
    return (nibble < 10) ? static_cast<char>('0' + nibble)
                         : static_cast<char>('A' + (nibble - 10));
}


} // namespace internal


constexpr StaticString<4> to_hex_string(u8 x) noexcept {
    constexpr u8 NIBBLE_MASK = 0x0F;
    StaticString<4> result;
    result[0] = '0';
    result[1] = 'x';
    for (int i = 0; i < 2; ++i) {
        const int shift = 4 - 4 * i;
        result[i + 2] = internal::nibble_to_hex_char(
            static_cast<int>((x >> shift) & NIBBLE_MASK)
        );
    }
    return result;
}


constexpr StaticString<6> to_hex_string(u16 x) noexcept {
    constexpr u16 NIBBLE_MASK = 0x0F;
    StaticString<6> result;
    result[0] = '0';
    result[1] = 'x';
    for (int i = 0; i < 4; ++i) {
        const int shift = 12 - 4 * i;
        result[i + 2] = internal::nibble_to_hex_char(
            static_cast<int>((x >> shift) & NIBBLE_MASK)
        );
    }
    return result;
}


constexpr StaticString<10> to_hex_string(u32 x) noexcept {
    constexpr u32 NIBBLE_MASK = 0x0F;
    StaticString<10> result;
    result[0] = '0';
    result[1] = 'x';
    for (int i = 0; i < 8; ++i) {
        const int shift = 28 - 4 * i;
        result[i + 2] = internal::nibble_to_hex_char(
            static_cast<int>((x >> shift) & NIBBLE_MASK)
        );
    }
    return result;
}


constexpr StaticString<18> to_hex_string(u64 x) noexcept {
    constexpr u64 NIBBLE_MASK = 0x0F;
    StaticString<18> result;
    result[0] = '0';
    result[1] = 'x';
    for (int i = 0; i < 16; ++i) {
        const int shift = 60 - 4 * i;
        result[i + 2] = internal::nibble_to_hex_char(
            static_cast<int>((x >> shift) & NIBBLE_MASK)
        );
    }
    return result;
}


constexpr StaticString<24> to_hex_string(f64 x) noexcept {
    constexpr u64 NIBBLE_MASK = 0xF000000000000000;
    IEEEBinaryFloatData<f64, i64, u64> data(x);
    if (data.is_nan()) {
        return "NaN";
    } else if (data.is_inf()) {
        return data.sign ? "-Inf" : "+Inf";
    } else if (data.is_zero()) {
        return data.sign ? "-0x0.0000000000000p+0000"
                         : "+0x0.0000000000000p+0000";
    } else {
        StaticString<24> result;
        result[0] = data.sign ? '-' : '+';
        result[1] = '0';
        result[2] = 'x';
        result[3] = '1';
        result[4] = '.';
        u64 mantissa = data.mantissa();
        const int shift = leading_zeros(mantissa) + 1;
        mantissa <<= shift;
        for (int i = 0; i < 13; ++i) {
            result[i + 5] = internal::nibble_to_hex_char(
                static_cast<int>((mantissa & NIBBLE_MASK) >> 60)
            );
            mantissa <<= 4;
        }
        result[18] = 'p';
        int exponent = static_cast<int>(data.exponent()) + (64 - shift);
        if (signbit(exponent)) {
            result[19] = '-';
            exponent = -exponent;
        } else {
            result[19] = '+';
        }
        result[23] = internal::digit_char(exponent % 10);
        exponent /= 10;
        result[22] = internal::digit_char(exponent % 10);
        exponent /= 10;
        result[21] = internal::digit_char(exponent % 10);
        exponent /= 10;
        result[20] = internal::digit_char(exponent);
        return result;
    }
}


} // namespace dznl

#endif // DZNL_STATIC_STRING_HPP_INCLUDED
