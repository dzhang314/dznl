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


#ifdef __SIZEOF_INT128__
using i128 = __int128_t;
using u128 = __uint128_t;
static_assert(sizeof(i128) == 16);
static_assert(sizeof(u128) == 16);
#endif // __SIZEOF_INT128__


} // namespace dznl

#endif // DZNL_NUMERIC_TYPES_HPP_INCLUDED
