#include <dznl/RandomNumberGenerator.hpp>

#include <catch2/catch_test_macros.hpp>


TEST_CASE("RandomNumberGenerator::random_u32") {
    dznl::RandomNumberGenerator rng(0);
    REQUIRE(rng.random_u32() == 3894649422U);
    REQUIRE(rng.random_u32() == 2055130073U);
    REQUIRE(rng.random_u32() == 2315086854U);
    REQUIRE(rng.random_u32() == 2925816488U);
    REQUIRE(rng.random_u32() == 3443325253U);
    REQUIRE(rng.random_u32() == 1644475139U);
    REQUIRE(rng.random_u32() == 428639621U);
    REQUIRE(rng.random_u32() == 1241310737U);
    REQUIRE(rng.random_u32() == 3521718650U);
    REQUIRE(rng.random_u32() == 338531392U);
}
