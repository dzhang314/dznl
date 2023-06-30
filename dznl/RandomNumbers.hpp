#ifndef DZNL_RANDOM_NUMBERS_HPP
#define DZNL_RANDOM_NUMBERS_HPP

#include "MathematicalFunctions.hpp"
#include "NumericTypes.hpp"

namespace dznl {


constexpr f64 random_advance(u64 &seed) noexcept {
    constexpr u64 multiplier = 6364136223846793005ULL;
    constexpr u64 increment = 1442695040888963407ULL;
    constexpr f64 denominator = 1.0 / 18446744073709551616.0;
    seed *= multiplier;
    seed += increment;
    return static_cast<f64>(seed) * denominator;
}


template <typename T, typename I>
void random_fill(T *__restrict__ result, I length, u64 seed) noexcept {
    for (; length > 0; --length) {
        *result++ = static_cast<T>(random_advance(seed));
    }
}


template <int dimension, typename T, typename I>
void random_fill_sphere(
    T *__restrict__ result, I num_points, u64 seed
) noexcept {
    for (; num_points > 0; --num_points) {
        T point[dimension];
        while (true) {
            f64 norm_squared = 0.0;
            for (int j = 0; j < dimension; ++j) {
                const f64 random_value =
                    double_value(random_advance(seed)) - one<f64>();
                point[j] = static_cast<T>(random_value);
                norm_squared += square(random_value);
            }
            if (norm_squared < 1.0) { break; }
        }
        T norm = zero<T>();
        for (int j = 0; j < dimension; ++j) {
            const T x = point[j];
            norm += square(x);
        }
        norm = sqrt(norm);
        for (int j = 0; j < dimension; ++j) { *result++ = point[j] / norm; }
    }
}


} // namespace dznl

#endif // DZNL_RANDOM_NUMBERS_HPP
