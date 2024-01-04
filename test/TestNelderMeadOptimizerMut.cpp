#define DZNL_REMOVE_CONST
#include <dznl/NelderMeadOptimizer.hpp>
#include <dznl/NumericFunctions.hpp>

#include <catch2/catch_template_test_macros.hpp>
#include <catch2/catch_test_macros.hpp>

#include <iomanip>
#include <iostream>
#include <vector>


static constexpr double rosenbrock_objective(double *x) {
    double a = x[0] - 1.0;
    double b = dznl::square(a);
    double c = dznl::square(x[0]);
    double d = x[1] - c;
    double e = dznl::square(d);
    return b + 100.0 * e;
}


static constexpr bool null_constraint(double *) { return true; }


class test_only_t {};


class mut_index_t { // clang-format off
    unsigned int m_value;
    mut_index_t(mut_index_t &&) = delete;
    mut_index_t &operator=(const mut_index_t &) = delete;
    mut_index_t &operator=(mut_index_t &&) = delete;
public: // test-only interface
    explicit constexpr mut_index_t(unsigned int value, test_only_t) noexcept : m_value(value) {}
    constexpr unsigned int test_only_get_value() noexcept { return m_value; }
public: // public interface
    constexpr mut_index_t(mut_index_t &) noexcept                               = default;
    constexpr bool operator<(mut_index_t &other) noexcept                       { return m_value < other.m_value; }
    constexpr bool operator==(mut_index_t &other) noexcept                      { return m_value == other.m_value; }
    constexpr mut_index_t &operator++() noexcept                                { ++m_value; return *this; }
    constexpr mut_index_t &operator--() noexcept                                { --m_value; return *this; }
    constexpr mut_index_t operator+(mut_index_t &other) noexcept                { return mut_index_t(m_value + other.m_value, test_only_t()); }
    constexpr mut_index_t operator*(mut_index_t &other) noexcept                { return mut_index_t(m_value * other.m_value, test_only_t()); }
}; // clang-format on


namespace dznl {

template <>
constexpr mut_index_t zero<mut_index_t>() noexcept {
    return mut_index_t(0, test_only_t());
}

} // namespace dznl


class mut_accessor_t { // clang-format off
    double *m_data;
    mut_accessor_t(mut_accessor_t &&) = delete;
    mut_accessor_t &operator=(const mut_accessor_t &) = delete;
    mut_accessor_t &operator=(mut_accessor_t &&) = delete;
public: // test-only interface
    explicit constexpr mut_accessor_t(double *data, test_only_t) noexcept : m_data(data) {}
    constexpr double *test_only_get_data() noexcept { return m_data; }
public: // public interface
    constexpr mut_accessor_t(mut_accessor_t &) noexcept                         = default;
    constexpr double &operator[](mut_index_t &index) noexcept                   { return m_data[index.test_only_get_value()]; }
    constexpr mut_accessor_t operator+(mut_index_t &index) noexcept             { return mut_accessor_t(m_data + index.test_only_get_value(), test_only_t()); }
}; // clang-format on


static constexpr double mut_rosenbrock_objective(mut_accessor_t &x) {
    return rosenbrock_objective(x.test_only_get_data());
}


static constexpr bool mut_null_constraint(mut_accessor_t &) { return true; }


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
        decltype(rosenbrock_objective),
        decltype(null_constraint),
        double * DZNL_RESTRICT>;
    std::vector<double> initial_point = {2.0, 4.0};
    std::vector<double> workspace(Optimizer::workspace_size(2));
    auto initial_point_accessor = initial_point.data();
    auto workspace_accessor = workspace.data();
    TestType dimension = 2;
    double step_size = 0.5;
    Optimizer optimizer(
        rosenbrock_objective,
        null_constraint,
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


TEST_CASE("NelderMeadOptimizer mut_index_t") {
    using Optimizer = dznl::NelderMeadOptimizer<
        double,
        mut_index_t,
        decltype(mut_rosenbrock_objective),
        decltype(mut_null_constraint),
        mut_accessor_t>;
    std::vector<double> initial_point = {2.0, 4.0};
    std::vector<double> workspace;
    auto workspace_size =
        Optimizer::workspace_size(mut_index_t(2, test_only_t()))
            .test_only_get_value();
    while (workspace_size) {
        workspace.push_back(0.0);
        --workspace_size;
    }
    mut_accessor_t initial_point_accessor(initial_point.data(), test_only_t());
    mut_accessor_t workspace_accessor(workspace.data(), test_only_t());
    mut_index_t dimension(2, test_only_t());
    double initial_step_size = 0.5;
    Optimizer optimizer(
        mut_rosenbrock_objective,
        mut_null_constraint,
        initial_point_accessor,
        dimension,
        initial_step_size,
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
