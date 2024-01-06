#ifndef DZNL_DECIMAL_TYPES_HPP_INCLUDED
#define DZNL_DECIMAL_TYPES_HPP_INCLUDED

#include "NumericFunctions.hpp"

#if defined(__GNUC__) && !defined(__clang__)
#define DZNL_HAS_DECIMAL
#include <decimal/decimal>

namespace dznl {


using d32 = std::decimal::decimal32;
using d64 = std::decimal::decimal64;
using d128 = std::decimal::decimal128;


// clang-format off
template <> d32 zero<d32>() noexcept { return static_cast<d32>(0); }
template <> d64 zero<d64>() noexcept { return static_cast<d64>(0); }
template <> d128 zero<d128>() noexcept { return static_cast<d128>(0); }
template <> d32 one<d32>() noexcept { return static_cast<d32>(1); }
template <> d64 one<d64>() noexcept { return static_cast<d64>(1); }
template <> d128 one<d128>() noexcept { return static_cast<d128>(1); }
// clang-format on


d32 twice(d32 x) noexcept { return x + x; }
d64 twice(d64 x) noexcept { return x + x; }
d128 twice(d128 x) noexcept { return x + x; }


d32 square(d32 x) noexcept { return x * x; }
d64 square(d64 x) noexcept { return x * x; }
d128 square(d128 x) noexcept { return x * x; }


d32 inv(d32 x) noexcept { return one<d32>() / x; }
d64 inv(d64 x) noexcept { return one<d64>() / x; }
d128 inv(d128 x) noexcept { return one<d128>() / x; }


}; // namespace dznl

#endif // defined(__GNUC__) && !defined(__clang__)

#endif // DZNL_DECIMAL_TYPES_HPP_INCLUDED
