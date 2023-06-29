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
// clang-format on

DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(f32)
DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(f64)
DZNL_DEFAULT_INV_IMPLEMENTATION(f32)
DZNL_DEFAULT_INV_IMPLEMENTATION(f64)


} // namespace dznl

#endif // DZNL_FLOATING_POINT_TYPES_HPP_INCLUDED
