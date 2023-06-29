#ifndef DZNL_INTEGER_TYPES_HPP_INCLUDED
#define DZNL_INTEGER_TYPES_HPP_INCLUDED

#include "NumericTypeInterface.hpp"

namespace dznl {


using i8 = signed char;
using i16 = signed short int;
using i32 = signed int;
using i64 = signed long long int;

static_assert(sizeof(i8) == 1);
static_assert(sizeof(i16) == 2);
static_assert(sizeof(i32) == 4);
static_assert(sizeof(i64) == 8);

// clang-format off
template <> constexpr  i8 zero< i8>() noexcept { return '\0'; }
template <> constexpr i16 zero<i16>() noexcept { return 0;    }
template <> constexpr i32 zero<i32>() noexcept { return 0;    }
template <> constexpr i64 zero<i64>() noexcept { return 0LL;  }
template <> constexpr  i8 one< i8>() noexcept { return '\1'; }
template <> constexpr i16 one<i16>() noexcept { return 1;    }
template <> constexpr i32 one<i32>() noexcept { return 1;    }
template <> constexpr i64 one<i64>() noexcept { return 1LL;  }
// clang-format on

DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(i8)
DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(i16)
DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(i32)
DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(i64)


using u8 = unsigned char;
using u16 = unsigned short int;
using u32 = unsigned int;
using u64 = unsigned long long int;

static_assert(sizeof(u8) == 1);
static_assert(sizeof(u16) == 2);
static_assert(sizeof(u32) == 4);
static_assert(sizeof(u64) == 8);

// clang-format off
template <> constexpr  u8 zero< u8>() noexcept { return '\0'; }
template <> constexpr u16 zero<u16>() noexcept { return 0U;   }
template <> constexpr u32 zero<u32>() noexcept { return 0U;   }
template <> constexpr u64 zero<u64>() noexcept { return 0ULL; }
template <> constexpr  u8 one< u8>() noexcept { return '\1'; }
template <> constexpr u16 one<u16>() noexcept { return 1U;   }
template <> constexpr u32 one<u32>() noexcept { return 1U;   }
template <> constexpr u64 one<u64>() noexcept { return 1ULL; }
// clang-format on

DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(u8)
DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(u16)
DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(u32)
DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(u64)


} // namespace dznl

#endif // DZNL_INTEGER_TYPES_HPP_INCLUDED
