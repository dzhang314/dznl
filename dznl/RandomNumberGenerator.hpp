#ifndef DZNL_RANDOM_NUMBER_GENERATOR_HPP_INCLUDED
#define DZNL_RANDOM_NUMBER_GENERATOR_HPP_INCLUDED

#include "FixedSizeArray.hpp"
#include "NumericFunctions.hpp"
#include "NumericTypes.hpp"

namespace dznl {


class RandomNumberGenerator {

    static constexpr u64 MULTIPLIER = 6364136223846793005ULL;
    static constexpr u64 INCREMENT = 1442695040888963407ULL;
    static constexpr f64 DENOMINATOR = 1.0 / 18446744073709551616.0;

    u64 state;

public:

    explicit constexpr RandomNumberGenerator(u64 seed) noexcept
        : state(seed) {}

    constexpr u64 random_integer() noexcept {
        state *= MULTIPLIER;
        state += INCREMENT;
        return state;
    }

    constexpr f64 random_real() noexcept {
        state *= MULTIPLIER;
        state += INCREMENT;
        return static_cast<f64>(state) * DENOMINATOR;
    }

    template <typename REAL_T, typename INDEX_T, INDEX_T DIMENSION>
    constexpr FixedSizeArray<REAL_T, INDEX_T, DIMENSION>
    random_sphere_point() noexcept {
        FixedSizeArray<REAL_T, INDEX_T, DIMENSION> result;
        while (true) {
            f64 norm_squared = zero<f64>();
            for (INDEX_T i = zero<INDEX_T>(); i < DIMENSION; ++i) {
                const f64 x = twice(random_real()) - one<f64>();
                result[i] = static_cast<REAL_T>(x);
                norm_squared += square(x);
            }
            if (norm_squared <= one<f64>()) { break; }
        }
        REAL_T norm_squared = zero<REAL_T>();
        for (INDEX_T i = zero<INDEX_T>(); i < DIMENSION; ++i) {
            norm_squared += square(result[i]);
        }
        const REAL_T norm = sqrt(norm_squared);
        for (INDEX_T i = zero<INDEX_T>(); i < DIMENSION; ++i) {
            result[i] /= norm;
        }
        return result;
    }

}; // class RandomNumberGenerator


} // namespace dznl

#endif // DZNL_RANDOM_NUMBER_GENERATOR_HPP_INCLUDED
