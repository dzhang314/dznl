#include "TestTypes.hpp"

#include <dznl/FloatingPointProperties.hpp>

#include <catch2/catch_test_macros.hpp>

#include <cfloat>


TEST_CASE("compute_float_radix (IEEE binary)") {
    REQUIRE(dznl::compute_float_radix<float, int>().second == FLT_RADIX);
    REQUIRE(dznl::compute_float_radix<double, int>().second == FLT_RADIX);
    REQUIRE(dznl::compute_float_radix<long double, int>().second == FLT_RADIX);
}


TEST_CASE("compute_float_precision (IEEE binary)") {
    REQUIRE(dznl::compute_float_precision<float, int>() == FLT_MANT_DIG);
    REQUIRE(dznl::compute_float_precision<double, int>() == DBL_MANT_DIG);
    REQUIRE(dznl::compute_float_precision<long double, int>() == LDBL_MANT_DIG);
}


#if defined(__GNUC__) && !defined(__clang__)

#include <decimal/decimal>

namespace dznl {

template <>
std::decimal::decimal32 zero<std::decimal::decimal32>() noexcept {
    return 0;
}

template <>
std::decimal::decimal32 one<std::decimal::decimal32>() noexcept {
    return 1;
}

template <>
std::decimal::decimal64 zero<std::decimal::decimal64>() noexcept {
    return 0;
}

template <>
std::decimal::decimal64 one<std::decimal::decimal64>() noexcept {
    return 1;
}

template <>
std::decimal::decimal128 zero<std::decimal::decimal128>() noexcept {
    return 0;
}

template <>
std::decimal::decimal128 one<std::decimal::decimal128>() noexcept {
    return 1;
}

} // namespace dznl

TEST_CASE("compute_float_radix (IEEE decimal)") {
    using namespace std::decimal;
    REQUIRE(dznl::compute_float_radix<decimal32, int>().second == 10);
    REQUIRE(dznl::compute_float_radix<decimal64, int>().second == 10);
    REQUIRE(dznl::compute_float_radix<decimal128, int>().second == 10);
}

TEST_CASE("compute_float_precision (IEEE decimal)") {
    using namespace std::decimal;
    REQUIRE(dznl::compute_float_precision<decimal32, int>() == 7);
    REQUIRE(dznl::compute_float_precision<decimal64, int>() == 16);
    REQUIRE(dznl::compute_float_precision<decimal128, int>() == 34);
}

#endif
