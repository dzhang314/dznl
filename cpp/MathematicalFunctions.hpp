#ifndef DZNL_MATHEMATICAL_FUNCTIONS_HPP_INCLUDED
#define DZNL_MATHEMATICAL_FUNCTIONS_HPP_INCLUDED

#include "FloatingPointTypes.hpp"
#include "NumericTypeInterface.hpp"

#define DZNL_DECLARE_UNARY_F32_FUNCTION(NAME, BUILTIN)                         \
    static inline __attribute__((always_inline)) f32 NAME(f32 x) noexcept {    \
        return BUILTIN(x);                                                     \
    }

#define DZNL_DECLARE_UNARY_F64_FUNCTION(NAME, BUILTIN)                         \
    static inline __attribute__((always_inline)) f64 NAME(f64 x) noexcept {    \
        return BUILTIN(x);                                                     \
    }

#define DZNL_DECLARE_BINARY_F32_FUNCTION(NAME, BUILTIN)                        \
    static inline __attribute__((always_inline)) f32 NAME(                     \
        f32 x, f32 y                                                           \
    ) noexcept {                                                               \
        return BUILTIN(x, y);                                                  \
    }

#define DZNL_DECLARE_BINARY_F64_FUNCTION(NAME, BUILTIN)                        \
    static inline __attribute__((always_inline)) f64 NAME(                     \
        f64 x, f64 y                                                           \
    ) noexcept {                                                               \
        return BUILTIN(x, y);                                                  \
    }

namespace dznl {


// TODO: For some reason, these primitives don't map to the corresponding
// WebAssembly instructions (f32.min, f64.min, f32.max, f64.max).
// DZNL_DECLARE_BINARY_F32_FUNCTION(min, __builtin_fminf);
// DZNL_DECLARE_BINARY_F64_FUNCTION(min, __builtin_fmin);
// DZNL_DECLARE_BINARY_F32_FUNCTION(max, __builtin_fmaxf);
// DZNL_DECLARE_BINARY_F64_FUNCTION(max, __builtin_fmax);


DZNL_DECLARE_UNARY_F32_FUNCTION(round, __builtin_roundevenf)
DZNL_DECLARE_UNARY_F64_FUNCTION(round, __builtin_roundeven)
DZNL_DECLARE_UNARY_F32_FUNCTION(ceil, __builtin_ceilf)
DZNL_DECLARE_UNARY_F64_FUNCTION(ceil, __builtin_ceil)
DZNL_DECLARE_UNARY_F32_FUNCTION(floor, __builtin_floorf)
DZNL_DECLARE_UNARY_F64_FUNCTION(floor, __builtin_floor)
DZNL_DECLARE_UNARY_F32_FUNCTION(trunc, __builtin_truncf)
DZNL_DECLARE_UNARY_F64_FUNCTION(trunc, __builtin_trunc)
DZNL_DECLARE_UNARY_F32_FUNCTION(abs, __builtin_fabsf)
DZNL_DECLARE_UNARY_F64_FUNCTION(abs, __builtin_fabs)
DZNL_DECLARE_UNARY_F32_FUNCTION(sqrt, __builtin_sqrtf)
DZNL_DECLARE_UNARY_F64_FUNCTION(sqrt, __builtin_sqrt)
DZNL_DECLARE_BINARY_F32_FUNCTION(copysign, __builtin_copysignf);
DZNL_DECLARE_BINARY_F64_FUNCTION(copysign, __builtin_copysign);


/**
 * @brief Given a number x (of any type T, integer or floating-point) and a
 * natural number n, compute and return x^n.
 *
 * This function does NOT use the exponentiation-by-squaring optimization, so
 * it performs fully-left-associated multiplications (e.g., ((x * x) * x) * x)
 * in the computation of x^n.
 */
template <typename T, typename U>
constexpr T pow_slow(T base, U exponent) {
    constexpr U ZERO = zero<U>();
    T result = one<T>();
    for (; exponent > ZERO; --exponent) { result *= base; }
    return result;
}


/**
 * @brief Given a number x (of any type T, integer or floating-point) and a
 * natural number n, compute and return x^n.
 *
 * This function uses the exponentiation-by-squaring optimization, so it may
 * reassociate multiplications in the computation of x^n.
 */
template <typename T, typename U>
constexpr T pow(T base, U exponent) {
    constexpr U ZERO = zero<U>();
    constexpr U ONE = one<U>();
    T accum = base;
    T result = one<T>();
    for (; exponent > ZERO; exponent >>= ONE) {
        if (exponent & ONE) { result *= accum; }
        accum *= accum;
    }
    return result;
}


} // namespace dznl

#undef DZNL_DECLARE_UNARY_F32_FUNCTION
#undef DZNL_DECLARE_UNARY_F64_FUNCTION
#undef DZNL_DECLARE_BINARY_F32_FUNCTION
#undef DZNL_DECLARE_BINARY_F64_FUNCTION

#endif // DZNL_MATHEMATICAL_FUNCTIONS_HPP_INCLUDED
