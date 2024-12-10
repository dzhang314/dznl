#ifndef DZNL_NUMERIC_TYPES_HPP_INCLUDED
#define DZNL_NUMERIC_TYPES_HPP_INCLUDED

namespace dznl {


using i8 = signed char;
using i16 = signed short int;
using i32 = signed int;
using i64 = signed long int;
using u8 = unsigned char;
using u16 = unsigned short int;
using u32 = unsigned int;
using u64 = unsigned long int;
using f32 = float;
using f64 = double;


static_assert(sizeof(i8) == 1);
static_assert(sizeof(i16) == 2);
static_assert(sizeof(i32) == 4);
static_assert(sizeof(i64) == 8);
static_assert(sizeof(u8) == 1);
static_assert(sizeof(u16) == 2);
static_assert(sizeof(u32) == 4);
static_assert(sizeof(u64) == 8);
static_assert(sizeof(f32) == 4);
static_assert(sizeof(f64) == 8);


#ifdef DZNL_REQUEST_I128
using i128 = __int128_t;
#endif // DZNL_REQUEST_I128


#ifdef DZNL_REQUEST_U128
using u128 = __uint128_t;
#endif // DZNL_REQUEST_U128


#ifdef DZNL_REQUEST_D32
#if defined(__clang__) || !defined(__GNUC__)
#error "decimal floating-point support requires GCC"
#endif // defined(__clang__) || !defined(__GNUC__)
using d32 = float [[gnu::mode(SD)]];
#endif // DZNL_REQUEST_D32


#ifdef DZNL_REQUEST_D64
#if defined(__clang__) || !defined(__GNUC__)
#error "decimal floating-point support requires GCC"
#endif // defined(__clang__) || !defined(__GNUC__)
using d64 = float [[gnu::mode(DD)]];
#endif // DZNL_REQUEST_D64


#ifdef DZNL_REQUEST_D128
#if defined(__clang__) || !defined(__GNUC__)
#error "decimal floating-point support requires GCC"
#endif // defined(__clang__) || !defined(__GNUC__)
using d128 = float [[gnu::mode(TD)]];
#endif // DZNL_REQUEST_D128


} // namespace dznl

#endif // DZNL_NUMERIC_TYPES_HPP_INCLUDED
