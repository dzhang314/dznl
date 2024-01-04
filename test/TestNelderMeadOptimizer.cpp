#include <dznl/NelderMeadOptimizer.hpp>
#include <dznl/NumericFunctions.hpp>

#include <catch2/catch_template_test_macros.hpp>
#include <catch2/catch_test_macros.hpp>

#include <iomanip>
#include <iostream>
#include <vector>


static constexpr double rosenbrock_objective(double *x) {
    return dznl::square(x[0] - 1.0) +
           100.0 * dznl::square(x[1] - dznl::square(x[0]));
}


static constexpr bool null_constraint(double *) { return true; }


class test_only_t {};


class my_real_t { // clang-format off
    double m_value;
    // my_real_t(my_real_t &&) = delete;
    // my_real_t &operator=(my_real_t &&) = delete;
public: // test-only interface
    explicit constexpr my_real_t(double value, test_only_t) noexcept : m_value(value) {}
    constexpr double test_only_get_value() const noexcept { return m_value; }
public: // public interface
    constexpr my_real_t(const my_real_t &) noexcept                             = default;
    my_real_t &operator=(const my_real_t &) noexcept                            = default;
    constexpr bool operator<(const my_real_t &other) const noexcept             { return m_value < other.m_value; }
    constexpr bool operator==(const my_real_t &other) const noexcept            { return m_value == other.m_value; }
    constexpr my_real_t operator+(const my_real_t &other) const noexcept        { return my_real_t(m_value + other.m_value, test_only_t()); }
    constexpr my_real_t operator-(const my_real_t &other) const noexcept        { return my_real_t(m_value - other.m_value, test_only_t()); }
    constexpr my_real_t operator*(const my_real_t &other) const noexcept        { return my_real_t(m_value * other.m_value, test_only_t()); }
    constexpr my_real_t operator/(const my_real_t &other) const noexcept        { return my_real_t(m_value / other.m_value, test_only_t()); }
}; // clang-format on


class my_index_t { // clang-format off
    unsigned int m_value;
    my_index_t(my_index_t &&) = delete;
    my_index_t &operator=(const my_index_t &) = delete;
    my_index_t &operator=(my_index_t &&) = delete;
public: // test-only interface
    explicit constexpr my_index_t(unsigned int value, test_only_t) noexcept : m_value(value) {}
    constexpr unsigned int test_only_get_value() const noexcept { return m_value; }
public: // public interface
    constexpr my_index_t(const my_index_t &) noexcept                           = default;
    constexpr bool operator<(const my_index_t &other) const noexcept            { return m_value < other.m_value; }
    constexpr bool operator==(const my_index_t &other) const noexcept           { return m_value == other.m_value; }
    constexpr my_index_t &operator++() noexcept                                 { ++m_value; return *this; }
    constexpr my_index_t &operator--() noexcept                                 { --m_value; return *this; }
    constexpr my_index_t operator+(const my_index_t &other) const noexcept      { return my_index_t(m_value + other.m_value, test_only_t()); }
    constexpr my_index_t operator*(const my_index_t &other) const noexcept      { return my_index_t(m_value * other.m_value, test_only_t()); }
}; // clang-format on


namespace dznl {

template <>
constexpr my_real_t zero<my_real_t>() noexcept {
    return my_real_t(0.0, test_only_t());
}

template <>
constexpr my_real_t one<my_real_t>() noexcept {
    return my_real_t(1.0, test_only_t());
}

template <>
constexpr my_index_t zero<my_index_t>() noexcept {
    return my_index_t(0, test_only_t());
}

} // namespace dznl


class my_accessor_t { // clang-format off
    my_real_t *m_data;
    my_accessor_t(my_accessor_t &&) = delete;
    my_accessor_t &operator=(const my_accessor_t &) = delete;
    my_accessor_t &operator=(my_accessor_t &&) = delete;
public: // test-only interface
    explicit constexpr my_accessor_t(my_real_t *data, test_only_t) noexcept : m_data(data) {}
    constexpr my_real_t *test_only_get_data() const noexcept { return m_data; }
public: // public interface
    constexpr my_accessor_t(const my_accessor_t &) noexcept                     = default;
    constexpr my_real_t &operator[](const my_index_t &index) const noexcept     { return m_data[index.test_only_get_value()]; }
    constexpr my_accessor_t operator+(const my_index_t &index) const noexcept   { return my_accessor_t(m_data + index.test_only_get_value(), test_only_t()); }
}; // clang-format on


static constexpr my_real_t my_rosenbrock_objective(const my_accessor_t &x) {
    double y[2] = {
        x[my_index_t(0, test_only_t())].test_only_get_value(),
        x[my_index_t(1, test_only_t())].test_only_get_value(),
    };
    return my_real_t(rosenbrock_objective(y), test_only_t());
}


static constexpr bool my_null_constraint(const my_accessor_t &) { return true; }


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
    Optimizer optimizer(
        rosenbrock_objective,
        null_constraint,
        initial_point.data(),
        2,
        0.5,
        workspace.data()
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


TEST_CASE("NelderMeadOptimizer my_index_t") {
    using Optimizer = dznl::NelderMeadOptimizer<
        my_real_t,
        my_index_t,
        decltype(my_rosenbrock_objective),
        decltype(my_null_constraint),
        my_accessor_t>;
    std::vector<my_real_t> initial_point = {
        my_real_t(2.0, test_only_t()), my_real_t(4.0, test_only_t())
    };
    std::vector<my_real_t> workspace;
    auto workspace_size =
        Optimizer::workspace_size(my_index_t(2, test_only_t()))
            .test_only_get_value();
    while (workspace_size) {
        workspace.emplace_back(my_real_t(0.0, test_only_t()));
        workspace_size--;
    }
    Optimizer optimizer(
        my_rosenbrock_objective,
        my_null_constraint,
        my_accessor_t(initial_point.data(), test_only_t()),
        my_index_t(2, test_only_t()),
        my_real_t(0.5, test_only_t()),
        my_accessor_t(workspace.data(), test_only_t())
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

    std::cout << std::setprecision(17);
    for (unsigned i = 0; i < 9; ++i) {
        std::cout << " " << workspace[i].test_only_get_value();
    }
    std::cout << std::endl;
    for (int j = 0; j < 200; ++j) {
        optimizer.step();
        for (unsigned i = 0; i < 9; ++i) {
            std::cout << " " << workspace[i].test_only_get_value();
        }
        std::cout << std::endl;
    }
}
