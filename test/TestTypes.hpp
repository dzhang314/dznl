#ifndef DZNL_TEST_TYPES_HPP_INCLUDED
#define DZNL_TEST_TYPES_HPP_INCLUDED

#include <dznl/Macros.hpp>

namespace dznl {


class my_real { // clang-format off

public: // public interface

    constexpr my_real(DZNL_CONST my_real &) noexcept                            = default;
    constexpr my_real &operator=(DZNL_CONST my_real &) noexcept                 = default;
    constexpr bool operator<(DZNL_CONST my_real &rhs) DZNL_CONST noexcept       { return m_value < rhs.m_value; }
    constexpr bool operator==(DZNL_CONST my_real &rhs) DZNL_CONST noexcept      { return m_value == rhs.m_value; }
    constexpr my_real operator+(DZNL_CONST my_real &rhs) DZNL_CONST noexcept    { return my_real(m_value + rhs.m_value); }
    constexpr my_real operator-(DZNL_CONST my_real &rhs) DZNL_CONST noexcept    { return my_real(m_value - rhs.m_value); }
    constexpr my_real operator*(DZNL_CONST my_real &rhs) DZNL_CONST noexcept    { return my_real(m_value * rhs.m_value); }
    constexpr my_real operator/(DZNL_CONST my_real &rhs) DZNL_CONST noexcept    { return my_real(m_value / rhs.m_value); }
    constexpr my_real &operator+=(DZNL_CONST my_real &rhs) noexcept             { m_value += rhs.m_value; return *this; }
    constexpr my_real &operator-=(DZNL_CONST my_real &rhs) noexcept             { m_value -= rhs.m_value; return *this; }
    constexpr my_real &operator*=(DZNL_CONST my_real &rhs) noexcept             { m_value *= rhs.m_value; return *this; }
    constexpr my_real &operator/=(DZNL_CONST my_real &rhs) noexcept             { m_value /= rhs.m_value; return *this; }

public: // test-only interface

    static constexpr my_real test_only_construct(double value) noexcept         { return my_real(value); }
    constexpr double test_only_get_value() const noexcept                       { return m_value; }

private: // clang-format on

    double m_value;
    explicit constexpr my_real(double value) noexcept
        : m_value(value) {}

    my_real(my_real &&) = delete;
    my_real &operator=(my_real &&) = delete;

}; // class my_real

// clang-format off
template <> constexpr my_real zero<my_real>() noexcept                          { return my_real::test_only_construct(0.0); }
template <> constexpr my_real one<my_real>()  noexcept                          { return my_real::test_only_construct(1.0); }
constexpr my_real inv(DZNL_CONST my_real &x) noexcept                           { return my_real::test_only_construct(inv(x.test_only_get_value())); }
constexpr my_real square(DZNL_CONST my_real &x) noexcept                        { return x * x; }
// clang-format on


class my_index { // clang-format off

public: // public interface

    constexpr my_index(DZNL_CONST my_index &) noexcept                          = default;
    constexpr bool operator<(DZNL_CONST my_index &rhs) DZNL_CONST noexcept      { return m_value < rhs.m_value; }
    constexpr bool operator==(DZNL_CONST my_index &rhs) DZNL_CONST noexcept     { return m_value == rhs.m_value; }
    constexpr my_index &operator++() noexcept                                   { ++m_value; return *this; }
    constexpr my_index &operator--() noexcept                                   { --m_value; return *this; }
    constexpr my_index operator+(DZNL_CONST my_index &rhs) DZNL_CONST noexcept  { return my_index(m_value + rhs.m_value); }
    constexpr my_index operator*(DZNL_CONST my_index &rhs) DZNL_CONST noexcept  { return my_index(m_value * rhs.m_value); }

public: // test-only interface

    static constexpr my_index test_only_construct(unsigned value) noexcept      { return my_index(value); }
    constexpr unsigned test_only_get_value() const noexcept                     { return m_value; }

private: // clang-format on

    unsigned m_value;
    explicit constexpr my_index(unsigned value) noexcept
        : m_value(value) {}

    my_index(my_index &&) = delete;
    my_index &operator=(const my_index &) = delete;
    my_index &operator=(my_index &&) = delete;

}; // class my_index

// clang-format off
template <> constexpr my_index zero<my_index>() noexcept                        { return my_index::test_only_construct(0); }
// clang-format on


class my_accessor { // clang-format off

public: // public interface

    constexpr my_accessor(DZNL_CONST my_accessor &) noexcept                    = default;
    constexpr my_real &operator[](DZNL_CONST my_index &i) DZNL_CONST noexcept   { return m_data[i.test_only_get_value()]; }
    constexpr my_accessor operator+(DZNL_CONST my_index &i) DZNL_CONST noexcept { return my_accessor(m_data + i.test_only_get_value()); }

public: // test-only interface

    static constexpr my_accessor test_only_construct(my_real *data) noexcept    { return my_accessor(data); }
    constexpr my_real *test_only_get_data() const noexcept                      { return m_data; }

private: // clang-format on

    my_real *m_data;
    explicit constexpr my_accessor(my_real *data) noexcept
        : m_data(data) {}

    my_accessor(my_accessor &&) = delete;
    my_accessor &operator=(const my_accessor &) = delete;
    my_accessor &operator=(my_accessor &&) = delete;

}; // class my_accessor


} // namespace dznl

#endif // DZNL_TEST_TYPES_HPP_INCLUDED
