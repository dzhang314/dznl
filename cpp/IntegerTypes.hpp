#ifndef DZNL_INTEGER_TYPES_HPP_INCLUDED
#define DZNL_INTEGER_TYPES_HPP_INCLUDED

#include "NumericTypeInterface.hpp"

namespace dznl {


using i8 = signed char;
using i16 = signed short int;
using i32 = signed int;
using i64 = signed long int;

static_assert(sizeof(i8) == 1);
static_assert(sizeof(i16) == 2);
static_assert(sizeof(i32) == 4);
static_assert(sizeof(i64) == 8);

// clang-format off
template <> constexpr  i8 zero< i8>() noexcept { return '\0'; }
template <> constexpr i16 zero<i16>() noexcept { return 0;    }
template <> constexpr i32 zero<i32>() noexcept { return 0;    }
template <> constexpr i64 zero<i64>() noexcept { return 0L;   }
template <> constexpr  i8 one< i8>() noexcept { return '\1'; }
template <> constexpr i16 one<i16>() noexcept { return 1;    }
template <> constexpr i32 one<i32>() noexcept { return 1;    }
template <> constexpr i64 one<i64>() noexcept { return 1L;   }
template <> constexpr bool is_zero< i8>(const  i8 &x) noexcept { return x == zero< i8>(); }
template <> constexpr bool is_zero<i16>(const i16 &x) noexcept { return x == zero<i16>(); }
template <> constexpr bool is_zero<i32>(const i32 &x) noexcept { return x == zero<i32>(); }
template <> constexpr bool is_zero<i64>(const i64 &x) noexcept { return x == zero<i64>(); }
template <> constexpr bool is_one< i8>(const  i8 &x) noexcept { return x == one< i8>(); }
template <> constexpr bool is_one<i16>(const i16 &x) noexcept { return x == one<i16>(); }
template <> constexpr bool is_one<i32>(const i32 &x) noexcept { return x == one<i32>(); }
template <> constexpr bool is_one<i64>(const i64 &x) noexcept { return x == one<i64>(); }
// clang-format on


using u8 = unsigned char;
using u16 = unsigned short int;
using u32 = unsigned int;
using u64 = unsigned long int;

static_assert(sizeof(u8) == 1);
static_assert(sizeof(u16) == 2);
static_assert(sizeof(u32) == 4);
static_assert(sizeof(u64) == 8);

// clang-format off
template <> constexpr  u8 zero< u8>() noexcept { return '\0'; }
template <> constexpr u16 zero<u16>() noexcept { return 0U;   }
template <> constexpr u32 zero<u32>() noexcept { return 0U;   }
template <> constexpr u64 zero<u64>() noexcept { return 0UL;  }
template <> constexpr  u8 one< u8>() noexcept { return '\1'; }
template <> constexpr u16 one<u16>() noexcept { return 1U;   }
template <> constexpr u32 one<u32>() noexcept { return 1U;   }
template <> constexpr u64 one<u64>() noexcept { return 1UL;  }
template <> constexpr bool is_zero< u8>(const  u8 &x) noexcept { return x == zero< u8>(); }
template <> constexpr bool is_zero<u16>(const u16 &x) noexcept { return x == zero<u16>(); }
template <> constexpr bool is_zero<u32>(const u32 &x) noexcept { return x == zero<u32>(); }
template <> constexpr bool is_zero<u64>(const u64 &x) noexcept { return x == zero<u64>(); }
template <> constexpr bool is_one< u8>(const  u8 &x) noexcept { return x == one< u8>(); }
template <> constexpr bool is_one<u16>(const u16 &x) noexcept { return x == one<u16>(); }
template <> constexpr bool is_one<u32>(const u32 &x) noexcept { return x == one<u32>(); }
template <> constexpr bool is_one<u64>(const u64 &x) noexcept { return x == one<u64>(); }
// clang-format on


} // namespace dznl

#endif // DZNL_INTEGER_TYPES_HPP_INCLUDED
