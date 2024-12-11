#ifndef DZNL_FLOATING_POINT_HPP_INCLUDED
#define DZNL_FLOATING_POINT_HPP_INCLUDED

#include "NumericConstants.hpp"
#include "Tuple.hpp"

namespace dznl {


template <typename FLOAT_T, typename INTEGER_T = int>
constexpr Tuple<FLOAT_T, INTEGER_T> compute_radix() {

    // The radix of a floating-point type is the smallest value of ulp(x) that
    // exceeds 1. For example, a binary floating-point type has possible ulp
    // values ..., 0.125, 0.25, 0.5, 1, **2**, 4, 8, ...; the radix is 2.
    // Similarly, a decimal floating-point type has possible ulp values
    // ..., 0.001, 0.01, 0.1, 1, **10**, 100, 1000, ...; the radix is 10.
    const FLOAT_T FLOAT_ONE = one<FLOAT_T>();

    // Step 1: Find a minimal floating-point number x such that ulp(x) > 1.
    // It suffices to consider powers of two, because for any radix r >= 2,
    // a power of two always lies between r^k and r^(k + 1) for any power k.
    FLOAT_T x = FLOAT_ONE;
    while (true) {
        const FLOAT_T y = x + FLOAT_ONE;
        const FLOAT_T z = y - x;
        if (!(z == FLOAT_ONE)) { break; }
        x += x;
    }

    // Step 2: Determine ulp(x). This is the radix.
    FLOAT_T float_radix = FLOAT_ONE;
    INTEGER_T integer_radix = one<INTEGER_T>();
    while (true) {
        const FLOAT_T y = x + float_radix;
        const FLOAT_T z = y - x;
        if (z == float_radix) { break; }
        float_radix += FLOAT_ONE;
        ++integer_radix;
    }
    return {float_radix, integer_radix};
}


template <typename FLOAT_T, typename INTEGER_T = int>
constexpr int compute_precision() {

    // Step 1: Compute the radix r as a floating-point number.
    const FLOAT_T float_radix = compute_radix<FLOAT_T, INTEGER_T>().first;

    // Step 2: Find the first power k such that ulp(r^k) > 1.
    const FLOAT_T FLOAT_ONE = one<FLOAT_T>();
    FLOAT_T power = FLOAT_ONE;
    INTEGER_T precision = 0;
    while (true) {
        const FLOAT_T y = power + FLOAT_ONE;
        const FLOAT_T z = y - power;
        if (!(z == FLOAT_ONE)) { break; }
        power *= float_radix;
        ++precision;
    }
    return precision;
}


} // namespace dznl

#endif // DZNL_FLOATING_POINT_HPP_INCLUDED
