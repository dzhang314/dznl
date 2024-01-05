#ifndef DZNL_OPTIMIZATION_TEST_FUNCTIONS_HPP_INCLUDED
#define DZNL_OPTIMIZATION_TEST_FUNCTIONS_HPP_INCLUDED

#include <dznl/Macros.hpp>
#include <dznl/NumericFunctions.hpp>

#include "TestTypes.hpp"

constexpr float rosenbrock_function_float(float *x) noexcept {
    return dznl::square(x[0] - 1.0F) +
           100.0F * dznl::square(x[1] - dznl::square(x[0]));
}

constexpr double rosenbrock_function(double *x) noexcept {
    return dznl::square(x[0] - 1.0) +
           100.0 * dznl::square(x[1] - dznl::square(x[0]));
}


constexpr long double rosenbrock_function_ldbl(long double *x) noexcept {
    return dznl::square(x[0] - 1.0L) +
           100.0L * dznl::square(x[1] - dznl::square(x[0]));
}


constexpr my_real my_rosenbrock_function(DZNL_CONST my_accessor &x) noexcept {
    using dznl::square;
    DZNL_CONST my_index INDEX_ZERO = my_index::test_only_construct(0);
    DZNL_CONST my_index INDEX_ONE = my_index::test_only_construct(1);
    DZNL_CONST my_real ONE = my_real::test_only_construct(1.0);
    DZNL_CONST my_real HUNDRED = my_real::test_only_construct(100.0);
    DZNL_CONST my_real &a = x[INDEX_ZERO];
    DZNL_CONST my_real &b = x[INDEX_ONE];
    my_real a2 = square(a);
    my_real err_0 = a - ONE;
    my_real err_1 = b - a2;
    my_real s = square(err_0);
    my_real t = square(err_1);
    my_real u = HUNDRED * t;
    return s + u;
}


constexpr bool null_constraint_float(float *) noexcept { return true; }


constexpr bool null_constraint(double *) noexcept { return true; }


constexpr bool null_constraint_ldbl(long double *) noexcept { return true; }


constexpr bool my_null_constraint(DZNL_CONST my_accessor &) noexcept {
    return true;
}


#endif // DZNL_OPTIMIZATION_TEST_FUNCTIONS_HPP_INCLUDED
