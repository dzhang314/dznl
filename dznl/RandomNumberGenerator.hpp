#ifndef DZNL_RANDOM_NUMBER_GENERATOR_HPP_INCLUDED
#define DZNL_RANDOM_NUMBER_GENERATOR_HPP_INCLUDED

#include "FixedSizeArray.hpp"
#include "NumericFunctions.hpp"
#include "NumericTypes.hpp"

namespace dznl {


struct RandomNumberGenerator {

    static constexpr u64 MULTIPLIER = 6364136223846793005ULL;
    static constexpr u64 INCREMENT = 1442695040888963407ULL;
    static constexpr f32 F32_DENOMINATOR = 1.0f / 4294967296.0f;
    static constexpr f64 F64_DENOMINATOR = 1.0 / 4294967296.0;

    u64 state;

    explicit constexpr RandomNumberGenerator(u64 seed) noexcept
        : state(0) {
        random_u32();
        state += seed;
        random_u32();
    }

    constexpr u32 random_u32() noexcept {
        const u64 last = state;
        state = MULTIPLIER * last + INCREMENT;
        const u32 xorshift = static_cast<u32>(((last >> 18) ^ last) >> 27);
        const u32 rotation = static_cast<u32>(last >> 59);
        return (xorshift >> rotation) | (xorshift << ((-rotation) & 31));
    }

    constexpr f32 random_f32() noexcept {
        return static_cast<f32>(random_u32()) * F32_DENOMINATOR;
    }

    constexpr f64 random_f64() noexcept {
        return static_cast<f64>(random_u32()) * F64_DENOMINATOR;
    }

    template <typename REAL_T, typename INDEX_T, INDEX_T DIMENSION>
    constexpr FixedSizeArray<REAL_T, INDEX_T, DIMENSION>
    random_sphere_point() noexcept {
        FixedSizeArray<REAL_T, INDEX_T, DIMENSION> result;
        while (true) {
            f64 norm_squared = 0.0;
            for (INDEX_T i = zero<INDEX_T>(); i < DIMENSION; ++i) {
                const f64 x = twice(random_f64()) - 1.0;
                result[i] = static_cast<REAL_T>(x);
                norm_squared += square(x);
            }
            if (norm_squared <= 1.0) { break; }
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

}; // struct RandomNumberGenerator


} // namespace dznl

#endif // DZNL_RANDOM_NUMBER_GENERATOR_HPP_INCLUDED
