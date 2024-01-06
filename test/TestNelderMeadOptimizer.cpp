#include "OptimizationTestFunctions.hpp"
#include "TestTypes.hpp"

#include <dznl/DecimalTypes.hpp>
#include <dznl/NumericFunctions.hpp>

#include <dznl/NelderMeadOptimizer.hpp>

#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#define DOCTEST_CONFIG_SUPER_FAST_ASSERTS
#include <doctest/doctest.h>

#include <iomanip>
#include <iostream>
#include <vector>


template <typename REAL_T, typename INDEX_T>
void test_nelder_mead_optimizer() {

    constexpr INDEX_T workspace_size =
        dznl::nelder_mead_workspace_size(static_cast<INDEX_T>(2));

    std::vector<REAL_T> workspace(
        static_cast<typename std::vector<REAL_T>::size_type>(workspace_size)
    );
    workspace[0] = static_cast<REAL_T>(2.0);
    workspace[1] = static_cast<REAL_T>(4.0);

    auto optimizer = dznl::make_nelder_mead_optimizer(
        rosenbrock_function<REAL_T>,
        workspace.data(),
        static_cast<INDEX_T>(2),
        static_cast<REAL_T>(0.5)
    );

    CHECK_EQ(workspace[0], static_cast<REAL_T>(2.0));
    CHECK_EQ(workspace[1], static_cast<REAL_T>(4.0));
    CHECK_EQ(workspace[2], static_cast<REAL_T>(1.0));
    CHECK_EQ(workspace[3], static_cast<REAL_T>(2.0));
    CHECK_EQ(workspace[4], static_cast<REAL_T>(4.5));
    CHECK_EQ(workspace[5], static_cast<REAL_T>(26.0));
    CHECK_EQ(workspace[6], static_cast<REAL_T>(2.5));
    CHECK_EQ(workspace[7], static_cast<REAL_T>(4.0));
    CHECK_EQ(workspace[8], static_cast<REAL_T>(508.5));

    while (optimizer.step()) {}

    CHECK_EQ(workspace[0], static_cast<REAL_T>(1.0));
    CHECK_EQ(workspace[1], static_cast<REAL_T>(1.0));
    CHECK_EQ(workspace[2], static_cast<REAL_T>(0.0));
    CHECK_EQ(workspace[3], static_cast<REAL_T>(1.0));
    CHECK_EQ(workspace[4], static_cast<REAL_T>(1.0));
    CHECK_EQ(workspace[5], static_cast<REAL_T>(0.0));
    CHECK_EQ(workspace[6], static_cast<REAL_T>(1.0));
    CHECK_EQ(workspace[7], static_cast<REAL_T>(1.0));
    CHECK_EQ(workspace[8], static_cast<REAL_T>(0.0));
}


TEST_CASE("NelderMeadOptimizer (float)") {
    test_nelder_mead_optimizer<float, signed char>();
    test_nelder_mead_optimizer<float, unsigned char>();
    test_nelder_mead_optimizer<float, int>();
    test_nelder_mead_optimizer<float, unsigned>();
    test_nelder_mead_optimizer<float, long long>();
    test_nelder_mead_optimizer<float, unsigned long long>();
}


TEST_CASE("NelderMeadOptimizer (double)") {
    test_nelder_mead_optimizer<double, signed char>();
    test_nelder_mead_optimizer<double, unsigned char>();
    test_nelder_mead_optimizer<double, int>();
    test_nelder_mead_optimizer<double, unsigned>();
    test_nelder_mead_optimizer<double, long long>();
    test_nelder_mead_optimizer<double, unsigned long long>();
}


TEST_CASE("NelderMeadOptimizer (long double)") {
    test_nelder_mead_optimizer<long double, signed char>();
    test_nelder_mead_optimizer<long double, unsigned char>();
    test_nelder_mead_optimizer<long double, int>();
    test_nelder_mead_optimizer<long double, unsigned>();
    test_nelder_mead_optimizer<long double, long long>();
    test_nelder_mead_optimizer<long double, unsigned long long>();
}

#ifdef DZNL_HAS_DECIMAL

TEST_CASE("NelderMeadOptimizer (decimal32)") {
    test_nelder_mead_optimizer<dznl::d32, signed char>();
    test_nelder_mead_optimizer<dznl::d32, unsigned char>();
    test_nelder_mead_optimizer<dznl::d32, int>();
    test_nelder_mead_optimizer<dznl::d32, unsigned>();
    test_nelder_mead_optimizer<dznl::d32, long long>();
    test_nelder_mead_optimizer<dznl::d32, unsigned long long>();
}

// TEST_CASE("NelderMeadOptimizer (decimal64)") {
//     test_nelder_mead_optimizer<dznl::d64, signed char>();
//     test_nelder_mead_optimizer<dznl::d64, unsigned char>();
//     test_nelder_mead_optimizer<dznl::d64, int>();
//     test_nelder_mead_optimizer<dznl::d64, unsigned>();
//     test_nelder_mead_optimizer<dznl::d64, long long>();
//     test_nelder_mead_optimizer<dznl::d64, unsigned long long>();
// }

TEST_CASE("NelderMeadOptimizer (decimal128)") {
    test_nelder_mead_optimizer<dznl::d128, signed char>();
    test_nelder_mead_optimizer<dznl::d128, unsigned char>();
    test_nelder_mead_optimizer<dznl::d128, int>();
    test_nelder_mead_optimizer<dznl::d128, unsigned>();
    test_nelder_mead_optimizer<dznl::d128, long long>();
    test_nelder_mead_optimizer<dznl::d128, unsigned long long>();
}

#endif // DZNL_HAS_DECIMAL


TEST_CASE("NelderMeadOptimizer (user-defined types)") {

    constexpr my_index workspace_size =
        dznl::nelder_mead_workspace_size(my_index::test_only_construct(2));

    void *workspace_memory = operator new(
        sizeof(my_real) * workspace_size.test_only_get_value()
    );
    my_real *workspace = reinterpret_cast<my_real *>(workspace_memory);
    DZNL_CONST my_real initial_x = my_real::test_only_construct(2.0);
    DZNL_CONST my_real initial_y = my_real::test_only_construct(4.0);
    workspace[0] = initial_x;
    workspace[1] = initial_y;

    auto optimizer = dznl::make_nelder_mead_optimizer(
        my_rosenbrock_function,
        my_accessor::test_only_construct(workspace),
        my_index::test_only_construct(2),
        my_real::test_only_construct(0.5)
    );

    CHECK_EQ(workspace[0].test_only_get_value(), 2.0);
    CHECK_EQ(workspace[1].test_only_get_value(), 4.0);
    CHECK_EQ(workspace[2].test_only_get_value(), 1.0);
    CHECK_EQ(workspace[3].test_only_get_value(), 2.0);
    CHECK_EQ(workspace[4].test_only_get_value(), 4.5);
    CHECK_EQ(workspace[5].test_only_get_value(), 26.0);
    CHECK_EQ(workspace[6].test_only_get_value(), 2.5);
    CHECK_EQ(workspace[7].test_only_get_value(), 4.0);
    CHECK_EQ(workspace[8].test_only_get_value(), 508.5);

    while (optimizer.step()) {}

    CHECK_EQ(workspace[0].test_only_get_value(), 1.0);
    CHECK_EQ(workspace[1].test_only_get_value(), 1.0);
    CHECK_EQ(workspace[2].test_only_get_value(), 0.0);
    CHECK_EQ(workspace[3].test_only_get_value(), 1.0);
    CHECK_EQ(workspace[4].test_only_get_value(), 1.0);
    CHECK_EQ(workspace[5].test_only_get_value(), 0.0);
    CHECK_EQ(workspace[6].test_only_get_value(), 1.0);
    CHECK_EQ(workspace[7].test_only_get_value(), 1.0);
    CHECK_EQ(workspace[8].test_only_get_value(), 0.0);

    operator delete(workspace_memory);
}
