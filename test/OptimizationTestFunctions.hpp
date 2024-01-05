#ifndef DZNL_OPTIMIZATION_TEST_FUNCTIONS_HPP_INCLUDED
#define DZNL_OPTIMIZATION_TEST_FUNCTIONS_HPP_INCLUDED

#include <dznl/Macros.hpp>
#include <dznl/NumericFunctions.hpp>

#include "TestTypes.hpp"

namespace dznl {


constexpr double rosenbrock_function(double *x) noexcept {
    DZNL_CONST double err_0 = x[0] - 1.0;
    DZNL_CONST double err_1 = x[1] - dznl::square(x[0]);
    const double s = dznl::square(err_0);
    const double t = dznl::square(err_1);
    return s + 100.0 * t;
}


constexpr my_real my_rosenbrock_function(DZNL_CONST my_accessor &x) noexcept {
    DZNL_CONST my_index INDEX_ZERO = my_index::test_only_construct(0);
    DZNL_CONST my_index INDEX_ONE = my_index::test_only_construct(1);
    DZNL_CONST my_real ONE = my_real::test_only_construct(1.0);
    DZNL_CONST my_real HUNDRED = my_real::test_only_construct(100.0);
    DZNL_CONST my_real &a = x[INDEX_ZERO];
    DZNL_CONST my_real &b = x[INDEX_ONE];
    my_real a2 = dznl::square(a);
    my_real err_0 = a - ONE;
    my_real err_1 = b - a2;
    my_real s = dznl::square(err_0);
    my_real t = dznl::square(err_1);
    my_real u = HUNDRED * t;
    return s + u;
}


constexpr bool null_constraint(double *) noexcept { return true; }


constexpr bool my_null_constraint(DZNL_CONST my_accessor &) noexcept {
    return true;
}


} // namespace dznl

#endif // DZNL_OPTIMIZATION_TEST_FUNCTIONS_HPP_INCLUDED
