#include <dznl/NumericFunctions.hpp>

#include <catch2/catch_template_test_macros.hpp>
#include <catch2/catch_test_macros.hpp>

#include <iomanip>
#include <iostream>
#include <vector>

#include "TestTypes.hpp"

#include "OptimizationTestFunctions.hpp"

#include <dznl/NelderMeadOptimizer.hpp>

TEMPLATE_TEST_CASE(
    "NelderMeadOptimizer (intrinsic types)",
    "",
    signed char,
    unsigned char,
    short,
    unsigned short,
    int,
    unsigned int,
    long,
    unsigned long,
    long long,
    unsigned long long,
    __int128_t,
    __uint128_t
) {
    using Optimizer = dznl::NelderMeadOptimizer<
        double,
        TestType,
        decltype(dznl::rosenbrock_function),
        decltype(dznl::null_constraint),
        double * DZNL_RESTRICT>;

    std::vector<double> initial_point = {2.0, 4.0};
    std::vector<double> workspace(Optimizer::workspace_size(2));
    auto initial_point_accessor = initial_point.data();
    auto workspace_accessor = workspace.data();
    TestType dimension = 2;
    double step_size = 0.5;
    Optimizer optimizer(
        dznl::rosenbrock_function,
        dznl::null_constraint,
        initial_point_accessor,
        dimension,
        step_size,
        workspace_accessor
    );
    REQUIRE(workspace[0] == 2.0);
    REQUIRE(workspace[1] == 4.0);
    REQUIRE(workspace[2] == 1.0);
    REQUIRE(workspace[3] == 2.0);
    REQUIRE(workspace[4] == 4.5);
    REQUIRE(workspace[5] == 26.0);
    REQUIRE(workspace[6] == 2.5);
    REQUIRE(workspace[7] == 4.0);
    REQUIRE(workspace[8] == 508.5);
}


TEST_CASE("NelderMeadOptimizer (user-provided types)") {

    using Optimizer = dznl::NelderMeadOptimizer<
        dznl::my_real,
        dznl::my_index,
        decltype(dznl::my_rosenbrock_function),
        decltype(dznl::my_null_constraint),
        dznl::my_accessor>;

    void *initial_memory = operator new(sizeof(dznl::my_real) * 2);
    dznl::my_real *initial_point =
        reinterpret_cast<dznl::my_real *>(initial_memory);
    dznl::my_real initial_x = dznl::my_real::test_only_construct(2.0);
    dznl::my_real initial_y = dznl::my_real::test_only_construct(4.0);
    initial_point[0] = initial_x;
    initial_point[1] = initial_y;

    dznl::my_index workspace_size =
        Optimizer::workspace_size(dznl::my_index::test_only_construct(2));
    void *workspace_memory = operator new(
        sizeof(dznl::my_real) * workspace_size.test_only_get_value()
    );
    dznl::my_real *workspace =
        reinterpret_cast<dznl::my_real *>(workspace_memory);

    dznl::my_accessor initial_point_accessor =
        dznl::my_accessor::test_only_construct(initial_point);
    dznl::my_accessor workspace_accessor =
        dznl::my_accessor::test_only_construct(workspace);
    dznl::my_index dimension = dznl::my_index::test_only_construct(2);
    dznl::my_real initial_step_size = dznl::my_real::test_only_construct(0.5);

    Optimizer optimizer(
        dznl::my_rosenbrock_function,
        dznl::my_null_constraint,
        initial_point_accessor,
        dimension,
        initial_step_size,
        workspace_accessor
    );

    REQUIRE(workspace[0].test_only_get_value() == 2.0);
    REQUIRE(workspace[1].test_only_get_value() == 4.0);
    REQUIRE(workspace[2].test_only_get_value() == 1.0);
    REQUIRE(workspace[3].test_only_get_value() == 2.0);
    REQUIRE(workspace[4].test_only_get_value() == 4.5);
    REQUIRE(workspace[5].test_only_get_value() == 26.0);
    REQUIRE(workspace[6].test_only_get_value() == 2.5);
    REQUIRE(workspace[7].test_only_get_value() == 4.0);
    REQUIRE(workspace[8].test_only_get_value() == 508.5);

    operator delete(initial_memory);
    operator delete(workspace_memory);
}
