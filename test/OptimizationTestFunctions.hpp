#ifndef DZNL_OPTIMIZATION_TEST_FUNCTIONS_HPP_INCLUDED
#define DZNL_OPTIMIZATION_TEST_FUNCTIONS_HPP_INCLUDED

#include <dznl/DecimalTypes.hpp>
#include <dznl/Macros.hpp>
#include <dznl/NumericFunctions.hpp>

#include "TestTypes.hpp"


template <typename REAL_T>
constexpr REAL_T rosenbrock_function(const REAL_T *x) noexcept {
    using dznl::square;
    DZNL_CONST REAL_T ONE = dznl::one<REAL_T>();
    DZNL_CONST REAL_T TWO = ONE + ONE;
    DZNL_CONST REAL_T FOUR = TWO + TWO;
    DZNL_CONST REAL_T EIGHT = FOUR + FOUR;
    DZNL_CONST REAL_T SIXTEEN = EIGHT + EIGHT;
    DZNL_CONST REAL_T THIRTY_TWO = SIXTEEN + SIXTEEN;
    DZNL_CONST REAL_T SIXTY_FOUR = THIRTY_TWO + THIRTY_TWO;
    DZNL_CONST REAL_T NINETY_SIX = SIXTY_FOUR + THIRTY_TWO;
    DZNL_CONST REAL_T ONE_HUNDRED = NINETY_SIX + FOUR;
    DZNL_CONST REAL_T x_squared = square(x[0]);
    DZNL_CONST REAL_T err_0 = x[0] - ONE;
    DZNL_CONST REAL_T err_1 = x[1] - x_squared;
    DZNL_CONST REAL_T err_0_squared = square(err_0);
    DZNL_CONST REAL_T err_1_squared = square(err_1);
    DZNL_CONST REAL_T err_1_scaled = ONE_HUNDRED * err_1_squared;
    return err_0_squared + err_1_scaled;
}


constexpr my_real my_rosenbrock_function(DZNL_CONST my_accessor &x) noexcept {
    using dznl::square;
    DZNL_CONST my_real ONE = my_real::test_only_construct(1.0);
    DZNL_CONST my_real ONE_HUNDRED = my_real::test_only_construct(100.0);
    DZNL_CONST my_index INDEX_ZERO = my_index::test_only_construct(0);
    DZNL_CONST my_index INDEX_ONE = my_index::test_only_construct(1);
    DZNL_CONST my_real x_squared = square(x[INDEX_ZERO]);
    DZNL_CONST my_real err_0 = x[INDEX_ZERO] - ONE;
    DZNL_CONST my_real err_1 = x[INDEX_ONE] - x_squared;
    DZNL_CONST my_real err_0_squared = square(err_0);
    DZNL_CONST my_real err_1_squared = square(err_1);
    DZNL_CONST my_real err_1_scaled = ONE_HUNDRED * err_1_squared;
    return err_0_squared + err_1_scaled;
}


#endif // DZNL_OPTIMIZATION_TEST_FUNCTIONS_HPP_INCLUDED
