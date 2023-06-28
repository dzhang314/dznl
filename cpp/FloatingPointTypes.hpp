#ifndef DZNL_FLOATING_POINT_TYPES_HPP_INCLUDED
#define DZNL_FLOATING_POINT_TYPES_HPP_INCLUDED

#include "NumericTypeInterface.hpp"

namespace dznl {


using f32 = float;
using f64 = double;

static_assert(sizeof(f32) == 4);
static_assert(sizeof(f64) == 8);

// clang-format off
template <> constexpr f32 zero<f32>() noexcept { return 0.0f; }
template <> constexpr f64 zero<f64>() noexcept { return 0.0; }
template <> constexpr f32 one<f32>() noexcept { return 1.0f; }
template <> constexpr f64 one<f64>() noexcept { return 1.0; }
template <> constexpr bool is_zero<f32>(const f32 &x) noexcept { return x == zero<f32>(); }
template <> constexpr bool is_zero<f64>(const f64 &x) noexcept { return x == zero<f64>(); }
template <> constexpr bool is_one<f32>(const f32 &x) noexcept { return x == one<f32>(); }
template <> constexpr bool is_one<f64>(const f64 &x) noexcept { return x == one<f64>(); }
// clang-format on


} // namespace dznl

#endif // DZNL_FLOATING_POINT_TYPES_HPP_INCLUDED
