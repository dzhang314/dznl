#include "TestTypes.hpp"

#include <dznl/FloatingPointProperties.hpp>
#include <dznl/NumericFunctions.hpp>

#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#define DOCTEST_CONFIG_SUPER_FAST_ASSERTS
#include <doctest/doctest.h>

#include <cfloat>


TEST_CASE("compute_float_radix (IEEE binary)") {
    CHECK_EQ(dznl::compute_float_radix<float, int>().second, FLT_RADIX);
    CHECK_EQ(dznl::compute_float_radix<double, int>().second, FLT_RADIX);
    CHECK_EQ(dznl::compute_float_radix<long double, int>().second, FLT_RADIX);
}


TEST_CASE("compute_float_precision (IEEE binary)") {
    CHECK_EQ(dznl::compute_float_precision<float, int>(), FLT_MANT_DIG);
    CHECK_EQ(dznl::compute_float_precision<double, int>(), DBL_MANT_DIG);
    CHECK_EQ(dznl::compute_float_precision<long double, int>(), LDBL_MANT_DIG);
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
    CHECK_EQ(dznl::compute_float_radix<decimal32, int>().second, 10);
    CHECK_EQ(dznl::compute_float_radix<decimal64, int>().second, 10);
    CHECK_EQ(dznl::compute_float_radix<decimal128, int>().second, 10);
}

TEST_CASE("compute_float_precision (IEEE decimal)") {
    CHECK_EQ(dznl::compute_float_precision<decimal32, int>(), 7);
    CHECK_EQ(dznl::compute_float_precision<decimal64, int>(), 16);
    CHECK_EQ(dznl::compute_float_precision<decimal128, int>(), 34);
}

#endif
