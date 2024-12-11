#ifndef DZNL_FLOATING_POINT_HPP_INCLUDED
#define DZNL_FLOATING_POINT_HPP_INCLUDED

#include "NumericConstants.hpp"

namespace dznl {


template <typename FLOAT_T>
constexpr int compute_radix() {

    // The radix of a floating-point type is the smallest value of ulp(x) that
    // exceeds 1. For example, a binary floating-point type has possible ulp
    // values ..., 0.125, 0.25, 0.5, 1, **2**, 4, 8, ...; the radix is 2.
    // Similarly, a decimal floating-point type has possible ulp values
    // ..., 0.001, 0.01, 0.1, 1, **10**, 100, 1000, ...; the radix is 10.
    const FLOAT_T ONE = one<FLOAT_T>();

    // Step 1: Find a minimal floating-point number x such that ulp(x) > 1.
    // It suffices to consider powers of two, because for any radix r >= 2,
    // a power of two always lies between r^k and r^(k + 1) for any power k.
    FLOAT_T x = ONE;
    while (true) {
        const FLOAT_T y = x + ONE;
        const FLOAT_T z = y - x;
        if (!(z == ONE)) { break; }
        x += x;
    }

    // Step 2: Determine ulp(x). This is the radix.
    FLOAT_T radix = ONE;
    int result = 1;
    while (true) {
        const FLOAT_T y = x + radix;
        const FLOAT_T z = y - x;
        if (z == radix) { break; }
        radix += ONE;
        ++result;
    }
    return result;
}


template <typename FLOAT_T>
constexpr int compute_precision() {

    // Step 1: Compute the radix r as a floating-point number.
    const FLOAT_T ONE = one<FLOAT_T>();
    const int radix = compute_radix<FLOAT_T>();
    FLOAT_T float_radix = ONE;
    for (int i = 1; i < radix; ++i) { float_radix += ONE; }

    // Step 2: Find the first power k such that ulp(r^k) > 1.
    FLOAT_T power = ONE;
    int result = 0;
    while (true) {
        const FLOAT_T y = power + ONE;
        const FLOAT_T z = y - power;
        if (!(z == ONE)) { break; }
        power *= float_radix;
        ++result;
    }
    return result;
}


} // namespace dznl

#endif // DZNL_FLOATING_POINT_HPP_INCLUDED
