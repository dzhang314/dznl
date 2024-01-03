#include <dznl/RandomNumberGenerator.hpp>

#include <catch2/catch_test_macros.hpp>


TEST_CASE("RandomNumberGenerator::random_u32 (seed 0)") {
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


TEST_CASE("RandomNumberGenerator::random_u32 (seed 1)") {
    dznl::RandomNumberGenerator rng(1);
    REQUIRE(rng.random_u32() == 1412771199U);
    REQUIRE(rng.random_u32() == 1791099446U);
    REQUIRE(rng.random_u32() == 124312908U);
    REQUIRE(rng.random_u32() == 1968572995U);
    REQUIRE(rng.random_u32() == 1080415314U);
    REQUIRE(rng.random_u32() == 2578637408U);
    REQUIRE(rng.random_u32() == 2103691749U);
    REQUIRE(rng.random_u32() == 1218125110U);
    REQUIRE(rng.random_u32() == 776621019U);
    REQUIRE(rng.random_u32() == 4155847760U);
}


TEST_CASE("RandomNumberGenerator::random_u32 (seed 2)") {
    dznl::RandomNumberGenerator rng(2);
    REQUIRE(rng.random_u32() == 3461116586U);
    REQUIRE(rng.random_u32() == 2338043315U);
    REQUIRE(rng.random_u32() == 3191287740U);
    REQUIRE(rng.random_u32() == 1237532498U);
    REQUIRE(rng.random_u32() == 3784629652U);
    REQUIRE(rng.random_u32() == 2907882346U);
    REQUIRE(rng.random_u32() == 2170804873U);
    REQUIRE(rng.random_u32() == 2823973565U);
    REQUIRE(rng.random_u32() == 18009116U);
    REQUIRE(rng.random_u32() == 3592974269U);
}
