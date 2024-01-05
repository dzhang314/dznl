#include "TestTypes.hpp"

#include <dznl/FloatingPointProperties.hpp>
#include <dznl/NumericFunctions.hpp>

#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#define DOCTEST_CONFIG_SUPER_FAST_ASSERTS
#include <doctest/doctest.h>

#include <cfloat>


TEST_CASE("compute_float_radix (IEEE binary)") {
    constexpr auto float_radix = dznl::compute_float_radix<float, int>();
    CHECK_EQ(float_radix.second, FLT_RADIX);
    constexpr auto double_radix = dznl::compute_float_radix<double, int>();
    CHECK_EQ(double_radix.second, FLT_RADIX);
    constexpr auto long_double_radix =
        dznl::compute_float_radix<long double, int>();
    CHECK_EQ(long_double_radix.second, FLT_RADIX);
}


TEST_CASE("compute_float_precision (IEEE binary)") {
    constexpr int float_precision = dznl::compute_float_precision<float, int>();
    CHECK_EQ(float_precision, FLT_MANT_DIG);
    constexpr int double_precision =
        dznl::compute_float_precision<double, int>();
    CHECK_EQ(double_precision, DBL_MANT_DIG);
    constexpr int long_double_precision =
        dznl::compute_float_precision<long double, int>();
    CHECK_EQ(long_double_precision, LDBL_MANT_DIG);
}


#if defined(__GNUC__) && !defined(__clang__)

#include <decimal/decimal>

using std::decimal::decimal128;
using std::decimal::decimal32;
using std::decimal::decimal64;

namespace dznl { // clang-format off
template <> decimal32 zero<decimal32>() noexcept { return 0; }
template <> decimal32 one<decimal32>() noexcept { return 1; }
template <> decimal64 zero<decimal64>() noexcept { return 0; }
template <> decimal64 one<decimal64>() noexcept { return 1; }
template <> decimal128 zero<decimal128>() noexcept { return 0; }
template <> decimal128 one<decimal128>() noexcept { return 1; }
} // clang-format on

TEST_CASE("compute_float_radix (IEEE decimal)") {
    const auto decimal32_radix = dznl::compute_float_radix<decimal32, int>();
    CHECK_EQ(decimal32_radix.second, 10);
    const auto decimal64_radix = dznl::compute_float_radix<decimal64, int>();
    CHECK_EQ(decimal64_radix.second, 10);
    const auto decimal128_radix = dznl::compute_float_radix<decimal128, int>();
    CHECK_EQ(decimal128_radix.second, 10);
}

TEST_CASE("compute_float_precision (IEEE decimal)") {
    const auto decimal32_precision =
        dznl::compute_float_precision<decimal32, int>();
    CHECK_EQ(decimal32_precision, 7);
    const auto decimal64_precision =
        dznl::compute_float_precision<decimal64, int>();
    CHECK_EQ(decimal64_precision, 16);
    const auto decimal128_precision =
        dznl::compute_float_precision<decimal128, int>();
    CHECK_EQ(decimal128_precision, 34);
}

#endif
