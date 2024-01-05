#include "OptimizationTestFunctions.hpp"
#include "TestTypes.hpp"

#include <dznl/NelderMeadOptimizer.hpp>
#include <dznl/NumericFunctions.hpp>

#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#define DOCTEST_CONFIG_SUPER_FAST_ASSERTS
#include <doctest/doctest.h>

#include <vector>


TEST_CASE("NelderMeadOptimizer (float, intrinsic index types)") {
    using TestType = unsigned long;
    using OptimizerType = dznl::NelderMeadOptimizer<
        float,
        TestType,
        decltype(rosenbrock_function_float)>;

    TestType dimension = 2;
    std::vector<float> initial_point = {2.0F, 4.0F};
    std::vector<float> workspace(
        static_cast<unsigned>(OptimizerType::workspace_size(dimension))
    );
    auto initial_point_accessor = initial_point.data();
    auto workspace_accessor = workspace.data();
    float step_size = 0.5F;
    OptimizerType optimizer(
        rosenbrock_function_float,
        initial_point_accessor,
        dimension,
        step_size,
        workspace_accessor
    );
    REQUIRE(workspace[0] == 2.0F);
    REQUIRE(workspace[1] == 4.0F);
    REQUIRE(workspace[2] == 1.0F);
    REQUIRE(workspace[3] == 2.0F);
    REQUIRE(workspace[4] == 4.5F);
    REQUIRE(workspace[5] == 26.0F);
    REQUIRE(workspace[6] == 2.5F);
    REQUIRE(workspace[7] == 4.0F);
    REQUIRE(workspace[8] == 508.5f);

    while (!(optimizer.has_terminated())) { optimizer.step(); }

    REQUIRE(workspace[0] == 1.0F);
    REQUIRE(workspace[1] == 1.0F);
    REQUIRE(workspace[2] == 0.0F);
    REQUIRE(workspace[3] == 1.0F);
    REQUIRE(workspace[4] == 1.0F);
    REQUIRE(workspace[5] == 0.0F);
    REQUIRE(workspace[6] == 1.0F);
    REQUIRE(workspace[7] == 1.0F);
    REQUIRE(workspace[8] == 0.0F);
}


TEST_CASE("NelderMeadOptimizer (float, intrinsic index types)") {
    using TestType = unsigned long;
    using OptimizerType = dznl::
        NelderMeadOptimizer<double, TestType, decltype(rosenbrock_function)>;

    TestType dimension = 2;
    std::vector<double> initial_point = {2.0, 4.0};
    std::vector<double> workspace(
        static_cast<unsigned>(OptimizerType::workspace_size(dimension))
    );
    auto initial_point_accessor = initial_point.data();
    auto workspace_accessor = workspace.data();
    double step_size = 0.5;
    OptimizerType optimizer(
        rosenbrock_function,
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

    while (!(optimizer.has_terminated())) { optimizer.step(); }

    REQUIRE(workspace[0] == 1.0);
    REQUIRE(workspace[1] == 1.0);
    REQUIRE(workspace[2] == 0.0);
    REQUIRE(workspace[3] == 1.0);
    REQUIRE(workspace[4] == 1.0);
    REQUIRE(workspace[5] == 0.0);
    REQUIRE(workspace[6] == 1.0);
    REQUIRE(workspace[7] == 1.0);
    REQUIRE(workspace[8] == 0.0);
}


TEST_CASE("NelderMeadOptimizer (long double, intrinsic index types)") {
    using TestType = unsigned long;
    using OptimizerType = dznl::NelderMeadOptimizer<
        long double,
        TestType,
        decltype(rosenbrock_function_ldbl)>;

    TestType dimension = 2;
    std::vector<long double> initial_point = {2.0L, 4.0L};
    std::vector<long double> workspace(
        static_cast<unsigned>(OptimizerType::workspace_size(dimension))
    );
    auto initial_point_accessor = initial_point.data();
    auto workspace_accessor = workspace.data();
    long double step_size = 0.5L;
    OptimizerType optimizer(
        rosenbrock_function_ldbl,
        initial_point_accessor,
        dimension,
        step_size,
        workspace_accessor
    );
    REQUIRE(workspace[0] == 2.0L);
    REQUIRE(workspace[1] == 4.0L);
    REQUIRE(workspace[2] == 1.0L);
    REQUIRE(workspace[3] == 2.0L);
    REQUIRE(workspace[4] == 4.5L);
    REQUIRE(workspace[5] == 26.0L);
    REQUIRE(workspace[6] == 2.5L);
    REQUIRE(workspace[7] == 4.0L);
    REQUIRE(workspace[8] == 508.5L);

    while (!(optimizer.has_terminated())) { optimizer.step(); }

    REQUIRE(workspace[0] == 1.0L);
    REQUIRE(workspace[1] == 1.0L);
    REQUIRE(workspace[2] == 0.0L);
    REQUIRE(workspace[3] == 1.0L);
    REQUIRE(workspace[4] == 1.0L);
    REQUIRE(workspace[5] == 0.0L);
    REQUIRE(workspace[6] == 1.0L);
    REQUIRE(workspace[7] == 1.0L);
    REQUIRE(workspace[8] == 0.0L);
}


TEST_CASE("NelderMeadOptimizer (user-provided types)") {

    using Optimizer = dznl::NelderMeadOptimizer<
        my_real,
        my_index,
        decltype(my_rosenbrock_function),
        void,
        my_accessor>;

    void *initial_memory = operator new(sizeof(my_real) * 2);
    my_real *initial_point = reinterpret_cast<my_real *>(initial_memory);
    my_real initial_x = my_real::test_only_construct(2.0);
    my_real initial_y = my_real::test_only_construct(4.0);
    initial_point[0] = initial_x;
    initial_point[1] = initial_y;

    my_index dimension = my_index::test_only_construct(2);
    my_index workspace_size = Optimizer::workspace_size(dimension);
    void *workspace_memory = operator new(
        sizeof(my_real) * workspace_size.test_only_get_value()
    );
    my_real *workspace = reinterpret_cast<my_real *>(workspace_memory);

    my_accessor initial_point_accessor =
        my_accessor::test_only_construct(initial_point);
    my_accessor workspace_accessor =
        my_accessor::test_only_construct(workspace);
    my_real initial_step_size = my_real::test_only_construct(0.5);

    Optimizer optimizer(
        my_rosenbrock_function,
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

    while (!(optimizer.has_terminated())) { optimizer.step(); }

    REQUIRE(workspace[0].test_only_get_value() == 1.0);
    REQUIRE(workspace[1].test_only_get_value() == 1.0);
    REQUIRE(workspace[2].test_only_get_value() == 0.0);
    REQUIRE(workspace[3].test_only_get_value() == 1.0);
    REQUIRE(workspace[4].test_only_get_value() == 1.0);
    REQUIRE(workspace[5].test_only_get_value() == 0.0);
    REQUIRE(workspace[6].test_only_get_value() == 1.0);
    REQUIRE(workspace[7].test_only_get_value() == 1.0);
    REQUIRE(workspace[8].test_only_get_value() == 0.0);

    operator delete(initial_memory);
    operator delete(workspace_memory);
}
