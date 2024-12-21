#ifndef DZNL_STATIC_STRING_HPP_INCLUDED
#define DZNL_STATIC_STRING_HPP_INCLUDED

#include "FloatingPoint.hpp"
#include "Memory.hpp"
#include "NumericTypes.hpp"

namespace dznl {


template <int N>
struct StaticString {


    char data[N + 1];


    constexpr StaticString() noexcept
        : data{} {
        for (int i = 0; i < N; ++i) { data[i] = '\0'; }
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


    char &operator[](int i) noexcept { return data[i]; }


    const char &operator[](int i) const noexcept { return data[i]; }


    constexpr int length() const noexcept {
        for (int i = 0; i < N; ++i) {
            if (data[i] == '\0') { return i; }
        }
        return N;
    }


}; // struct StaticString<N>


template <int N>
StaticString(const char (&)[N]) -> StaticString<N - 1>;


namespace internal {


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
    result[4] = '\0';
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
    result[6] = '\0';
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
    result[10] = '\0';
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
    result[18] = '\0';
    return result;
}


} // namespace dznl

#endif // DZNL_STATIC_STRING_HPP_INCLUDED
