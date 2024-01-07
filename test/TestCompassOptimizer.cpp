#include "OptimizationTestFunctions.hpp"
#include "TestTypes.hpp"

#include <dznl/DecimalTypes.hpp>
#include <dznl/NumericFunctions.hpp>

#include <dznl/CompassOptimizer.hpp>

#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#define DOCTEST_CONFIG_SUPER_FAST_ASSERTS
#include <doctest/doctest.h>

#include <vector>


template <typename REAL_T, typename INDEX_T>
void test_compass_optimizer() {

    constexpr INDEX_T workspace_size =
        dznl::compass_workspace_size(static_cast<INDEX_T>(2));

    std::vector<REAL_T> workspace(
        static_cast<typename std::vector<REAL_T>::size_type>(workspace_size)
    );
    workspace[0] = static_cast<REAL_T>(2.0);
    workspace[1] = static_cast<REAL_T>(4.0);

    auto optimizer = dznl::make_compass_optimizer(
        rosenbrock_function<REAL_T>,
        workspace.data(),
        static_cast<INDEX_T>(2),
        static_cast<REAL_T>(0.5)
    );

    CHECK_EQ(workspace[0], static_cast<REAL_T>(2.0));
    CHECK_EQ(workspace[1], static_cast<REAL_T>(4.0));

    while (optimizer.step()) {}

    // CHECK_EQ(workspace[0], static_cast<REAL_T>(1.0));
    // CHECK_EQ(workspace[1], static_cast<REAL_T>(1.0));
}


TEST_CASE("CompassOptimizer (float)") {
    test_compass_optimizer<float, signed char>();
    test_compass_optimizer<float, unsigned char>();
    test_compass_optimizer<float, int>();
    test_compass_optimizer<float, unsigned>();
    test_compass_optimizer<float, long long>();
    test_compass_optimizer<float, unsigned long long>();
}


TEST_CASE("CompassOptimizer (double)") {
    test_compass_optimizer<double, signed char>();
    test_compass_optimizer<double, unsigned char>();
    test_compass_optimizer<double, int>();
    test_compass_optimizer<double, unsigned>();
    test_compass_optimizer<double, long long>();
    test_compass_optimizer<double, unsigned long long>();
}


TEST_CASE("CompassOptimizer (long double)") {
    test_compass_optimizer<long double, signed char>();
    test_compass_optimizer<long double, unsigned char>();
    test_compass_optimizer<long double, int>();
    test_compass_optimizer<long double, unsigned>();
    test_compass_optimizer<long double, long long>();
    test_compass_optimizer<long double, unsigned long long>();
}


#ifdef DZNL_HAS_DECIMAL

TEST_CASE("CompassOptimizer (decimal32)") {
    test_compass_optimizer<dznl::d32, signed char>();
    test_compass_optimizer<dznl::d32, unsigned char>();
    test_compass_optimizer<dznl::d32, int>();
    test_compass_optimizer<dznl::d32, unsigned>();
    test_compass_optimizer<dznl::d32, long long>();
    test_compass_optimizer<dznl::d32, unsigned long long>();
}

TEST_CASE("CompassOptimizer (decimal64)") {
    test_compass_optimizer<dznl::d64, signed char>();
    test_compass_optimizer<dznl::d64, unsigned char>();
    test_compass_optimizer<dznl::d64, int>();
    test_compass_optimizer<dznl::d64, unsigned>();
    test_compass_optimizer<dznl::d64, long long>();
    test_compass_optimizer<dznl::d64, unsigned long long>();
}

TEST_CASE("CompassOptimizer (decimal128)") {
    test_compass_optimizer<dznl::d128, signed char>();
    test_compass_optimizer<dznl::d128, unsigned char>();
    test_compass_optimizer<dznl::d128, int>();
    test_compass_optimizer<dznl::d128, unsigned>();
    test_compass_optimizer<dznl::d128, long long>();
    test_compass_optimizer<dznl::d128, unsigned long long>();
}

#endif // DZNL_HAS_DECIMAL


TEST_CASE("CompassOptimizer (user-defined types)") {

    constexpr my_index workspace_size =
        dznl::compass_workspace_size(my_index::test_only_construct(2));

    void *workspace_memory = operator new(
        sizeof(my_real) * workspace_size.test_only_get_value()
    );
    my_real *workspace = reinterpret_cast<my_real *>(workspace_memory);
    DZNL_CONST my_real initial_x = my_real::test_only_construct(2.0);
    DZNL_CONST my_real initial_y = my_real::test_only_construct(4.0);
    workspace[0] = initial_x;
    workspace[1] = initial_y;

    auto optimizer = dznl::make_compass_optimizer(
        my_rosenbrock_function,
        my_accessor::test_only_construct(workspace),
        my_index::test_only_construct(2),
        my_real::test_only_construct(0.5)
    );

    CHECK_EQ(workspace[0].test_only_get_value(), 2.0);
    CHECK_EQ(workspace[1].test_only_get_value(), 4.0);

    while (optimizer.step()) {}

    // CHECK_EQ(workspace[0].test_only_get_value(), 1.0);
    // CHECK_EQ(workspace[1].test_only_get_value(), 1.0);

    operator delete(workspace_memory);
}
