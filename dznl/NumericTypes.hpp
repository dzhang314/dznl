#ifndef DZNL_NUMERIC_TYPES_HPP_INCLUDED
#define DZNL_NUMERIC_TYPES_HPP_INCLUDED

#include "Macros.hpp"

namespace dznl {


using i8 = signed char;
using i16 = signed short int;
using i32 = signed int;
using i64 = signed long long int;
using u8 = unsigned char;
using u16 = unsigned short int;
using u32 = unsigned int;
using u64 = unsigned long long int;
using f32 = float;
using f64 = double;


static_assert(DZNL_CHAR_BIT * sizeof(i8) == 8);
static_assert(DZNL_CHAR_BIT * sizeof(i16) == 16);
static_assert(DZNL_CHAR_BIT * sizeof(i32) == 32);
static_assert(DZNL_CHAR_BIT * sizeof(i64) == 64);
static_assert(DZNL_CHAR_BIT * sizeof(u8) == 8);
static_assert(DZNL_CHAR_BIT * sizeof(u16) == 16);
static_assert(DZNL_CHAR_BIT * sizeof(u32) == 32);
static_assert(DZNL_CHAR_BIT * sizeof(u64) == 64);
static_assert(DZNL_CHAR_BIT * sizeof(f32) == 32);
static_assert(DZNL_CHAR_BIT * sizeof(f64) == 64);


#ifdef DZNL_REQUEST_I128
#ifndef __SIZEOF_INT128__
#error "128-bit integers are not supported on this platform"
#endif // __SIZEOF_INT128__
using i128 = __int128_t;
static_assert(DZNL_CHAR_BIT * sizeof(i128) == 128);
#endif // DZNL_REQUEST_I128


#ifdef DZNL_REQUEST_U128
#ifndef __SIZEOF_INT128__
#error "128-bit integers are not supported on this platform"
#endif // __SIZEOF_INT128__
using u128 = __uint128_t;
static_assert(DZNL_CHAR_BIT * sizeof(u128) == 128);
#endif // DZNL_REQUEST_U128


#ifdef DZNL_REQUEST_F16
#if (defined(__GNUC__) && (!defined(__clang__)) && (__GNUC__ < 12))
#error "float16 support requires GCC 12+"
#else
using f16 = _Float16;
static_assert(DZNL_CHAR_BIT * sizeof(f16) == 16);
#endif
#endif // DZNL_REQUEST_F16


#ifdef DZNL_REQUEST_BF16
#if (defined(__GNUC__) && (!defined(__clang__)) && (__GNUC__ < 13)) ||         \
    (defined(__clang__) && (!defined(__apple_build_version__)) &&              \
     (__clang_major__ < 17))
#error "bfloat16 support requires GCC 13+, Clang 17+, or Apple Clang"
#else
using bf16 = __bf16;
static_assert(DZNL_CHAR_BIT * sizeof(bf16) == 16);
#endif
#endif // DZNL_REQUEST_BF16


#ifdef DZNL_REQUEST_F128
#if defined(__clang__) || !defined(__GNUC__)
#error "128-bit floating-point support requires GCC"
#else
using f128 = __float128;
static_assert(DZNL_CHAR_BIT * sizeof(f128) == 128);
#endif
#endif // DZNL_REQUEST_F128


#ifdef DZNL_REQUEST_D32
#if defined(__clang__) || !defined(__GNUC__)
#error "decimal floating-point support requires GCC"
#else
using d32 = float [[gnu::mode(SD)]];
static_assert(DZNL_CHAR_BIT * sizeof(d32) == 32);
#endif
#endif // DZNL_REQUEST_D32


#ifdef DZNL_REQUEST_D64
#if defined(__clang__) || !defined(__GNUC__)
#error "decimal floating-point support requires GCC"
#else
using d64 = float [[gnu::mode(DD)]];
static_assert(DZNL_CHAR_BIT * sizeof(d64) == 64);
#endif
#endif // DZNL_REQUEST_D64


#ifdef DZNL_REQUEST_D128
#if defined(__clang__) || !defined(__GNUC__)
#error "decimal floating-point support requires GCC"
#else
using d128 = float [[gnu::mode(TD)]];
static_assert(DZNL_CHAR_BIT * sizeof(d128) == 128);
#endif
#endif // DZNL_REQUEST_D128


} // namespace dznl

#endif // DZNL_NUMERIC_TYPES_HPP_INCLUDED
