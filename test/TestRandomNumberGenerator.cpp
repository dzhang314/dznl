#include <dznl/RandomNumberGenerator.hpp>

#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#define DOCTEST_CONFIG_SUPER_FAST_ASSERTS
#include <doctest/doctest.h>


TEST_CASE("RandomNumberGenerator::random_u32 (seed 0)") {
    dznl::RandomNumberGenerator rng(0);
    CHECK_EQ(rng.random_u32(), 3894649422U);
    CHECK_EQ(rng.random_u32(), 2055130073U);
    CHECK_EQ(rng.random_u32(), 2315086854U);
    CHECK_EQ(rng.random_u32(), 2925816488U);
    CHECK_EQ(rng.random_u32(), 3443325253U);
    CHECK_EQ(rng.random_u32(), 1644475139U);
    CHECK_EQ(rng.random_u32(), 428639621U);
    CHECK_EQ(rng.random_u32(), 1241310737U);
    CHECK_EQ(rng.random_u32(), 3521718650U);
    CHECK_EQ(rng.random_u32(), 338531392U);
}


TEST_CASE("RandomNumberGenerator::random_u32 (seed 1)") {
    dznl::RandomNumberGenerator rng(1);
    CHECK_EQ(rng.random_u32(), 1412771199U);
    CHECK_EQ(rng.random_u32(), 1791099446U);
    CHECK_EQ(rng.random_u32(), 124312908U);
    CHECK_EQ(rng.random_u32(), 1968572995U);
    CHECK_EQ(rng.random_u32(), 1080415314U);
    CHECK_EQ(rng.random_u32(), 2578637408U);
    CHECK_EQ(rng.random_u32(), 2103691749U);
    CHECK_EQ(rng.random_u32(), 1218125110U);
    CHECK_EQ(rng.random_u32(), 776621019U);
    CHECK_EQ(rng.random_u32(), 4155847760U);
}


TEST_CASE("RandomNumberGenerator::random_u32 (seed 2)") {
    dznl::RandomNumberGenerator rng(2);
    CHECK_EQ(rng.random_u32(), 3461116586U);
    CHECK_EQ(rng.random_u32(), 2338043315U);
    CHECK_EQ(rng.random_u32(), 3191287740U);
    CHECK_EQ(rng.random_u32(), 1237532498U);
    CHECK_EQ(rng.random_u32(), 3784629652U);
    CHECK_EQ(rng.random_u32(), 2907882346U);
    CHECK_EQ(rng.random_u32(), 2170804873U);
    CHECK_EQ(rng.random_u32(), 2823973565U);
    CHECK_EQ(rng.random_u32(), 18009116U);
    CHECK_EQ(rng.random_u32(), 3592974269U);
}
