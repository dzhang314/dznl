#include <dznl/FloatingPointProperties.hpp>

#include <catch2/catch_test_macros.hpp>

TEST_CASE("compute_float_radix") {
    REQUIRE(dznl::compute_float_radix<float, int>() == 2.0f);
    REQUIRE(dznl::compute_float_radix<double, int>() == 2.0);
}

TEST_CASE("compute_float_precision") {
    REQUIRE(dznl::compute_float_precision<float, int>() == 24);
    REQUIRE(dznl::compute_float_precision<double, int>() == 53);
}
