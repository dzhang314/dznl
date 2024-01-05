#include <dznl/NelderMeadOptimizer.hpp>
#include <dznl/NumericFunctions.hpp>

#include <catch2/catch_template_test_macros.hpp>
#include <catch2/catch_test_macros.hpp>

#include <iomanip>
#include <iostream>
#include <vector>

#include "OptimizationTestFunctions.hpp"
#include "TestTypes.hpp"


TEMPLATE_TEST_CASE(
    "NelderMeadOptimizer",
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


// TEST_CASE("NelderMeadOptimizer mut_index_t") {
//     using Optimizer = dznl::NelderMeadOptimizer<
//         double,
//         mut_index_t,
//         decltype(mut_rosenbrock_objective),
//         decltype(mut_null_constraint),
//         mut_accessor_t>;
//     std::vector<double> initial_point = {2.0, 4.0};
//     std::vector<double> workspace;
//     auto workspace_size =
//         Optimizer::workspace_size(mut_index_t(2, test_only_t()))
//             .test_only_get_value();
//     while (workspace_size) {
//         workspace.push_back(0.0);
//         --workspace_size;
//     }
//     mut_accessor_t initial_point_accessor(initial_point.data(),
//     test_only_t()); mut_accessor_t workspace_accessor(workspace.data(),
//     test_only_t()); mut_index_t dimension(2, test_only_t()); double
//     initial_step_size = 0.5; Optimizer optimizer(
//         mut_rosenbrock_objective,
//         mut_null_constraint,
//         initial_point_accessor,
//         dimension,
//         initial_step_size,
//         workspace_accessor
//     );
//     REQUIRE(workspace[0] == 2.0);
//     REQUIRE(workspace[1] == 4.0);
//     REQUIRE(workspace[2] == 1.0);
//     REQUIRE(workspace[3] == 2.0);
//     REQUIRE(workspace[4] == 4.5);
//     REQUIRE(workspace[5] == 26.0);
//     REQUIRE(workspace[6] == 2.5);
//     REQUIRE(workspace[7] == 4.0);
//     REQUIRE(workspace[8] == 508.5);
// }
