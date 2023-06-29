#ifndef DZNL_MATHEMATICAL_FUNCTIONS_HPP_INCLUDED
#define DZNL_MATHEMATICAL_FUNCTIONS_HPP_INCLUDED

#include "FloatingPointTypes.hpp"
#include "NumericTypeInterface.hpp"

namespace dznl {


/**
 * @brief Given an element x of a numeric type T and a nonnegative integer n,
 *        compute and return x raised to the nth power.
 *
 * This function does NOT perform exponentiation by squaring. It computes x^n
 * using fully left-associated multiplications (e.g., ((x * x) * x) * x).
 */
template <typename T, typename U>
constexpr T pow_slow(T base, U exponent) noexcept {
    constexpr U ZERO = zero<U>();
    T result = one<T>();
    for (; exponent > ZERO; --exponent) { result *= base; }
    return result;
}


/**
 * @brief Given an element x of a numeric type T and a nonnegative integer n,
 *        compute and return x raised to the nth power.
 *
 * This function performs exponentiation by squaring.
 * It may reassociate multiplications in the computation of x^n.
 */
template <typename T, typename U>
constexpr T pow(T base, U exponent) noexcept {
    constexpr U ZERO = zero<U>();
    constexpr U ONE = one<U>();
    T result = one<T>();
    T accum = base;
    for (; exponent > ZERO; exponent >>= ONE) {
        if (exponent & ONE) { result *= accum; }
        accum *= accum;
    }
    return result;
}


#define DZNL_DECLARE_INLINE_UNARY_FUNCTION(NAME, TYPE, FUNCTION)               \
    static inline __attribute__((always_inline)) TYPE NAME(TYPE x) noexcept {  \
        return FUNCTION(x);                                                    \
    }

#define DZNL_DECLARE_INLINE_BINARY_FUNCTION(NAME, TYPE, FUNCTION)              \
    static inline __attribute__((always_inline)) TYPE NAME(                    \
        TYPE x, TYPE y                                                         \
    ) noexcept {                                                               \
        return FUNCTION(x, y);                                                 \
    }


#if __has_builtin(__builtin_wasm_min_f32)
DZNL_DECLARE_INLINE_BINARY_FUNCTION(min, f32, __builtin_wasm_min_f32)
#else
DZNL_DECLARE_INLINE_BINARY_FUNCTION(min, f32, __builtin_fminf)
#endif

#if __has_builtin(__builtin_wasm_min_f64)
DZNL_DECLARE_INLINE_BINARY_FUNCTION(min, f64, __builtin_wasm_min_f64)
#else
DZNL_DECLARE_INLINE_BINARY_FUNCTION(min, f64, __builtin_fmin)
#endif


#if __has_builtin(__builtin_wasm_max_f32)
DZNL_DECLARE_INLINE_BINARY_FUNCTION(max, f32, __builtin_wasm_max_f32)
#else
DZNL_DECLARE_INLINE_BINARY_FUNCTION(max, f32, __builtin_fmaxf)
#endif

#if __has_builtin(__builtin_wasm_max_f64)
DZNL_DECLARE_INLINE_BINARY_FUNCTION(max, f64, __builtin_wasm_max_f64)
#else
DZNL_DECLARE_INLINE_BINARY_FUNCTION(max, f64, __builtin_fmax)
#endif


#if __has_builtin(__builtin_roundevenf)
DZNL_DECLARE_INLINE_UNARY_FUNCTION(round, f32, __builtin_roundevenf)
#else
DZNL_DECLARE_INLINE_UNARY_FUNCTION(round, f32, __builtin_roundf)
#endif

#if __has_builtin(__builtin_roundeven)
DZNL_DECLARE_INLINE_UNARY_FUNCTION(round, f64, __builtin_roundeven)
#else
DZNL_DECLARE_INLINE_UNARY_FUNCTION(round, f64, __builtin_round)
#endif


DZNL_DECLARE_INLINE_UNARY_FUNCTION(ceil, f32, __builtin_ceilf)
DZNL_DECLARE_INLINE_UNARY_FUNCTION(ceil, f64, __builtin_ceil)
DZNL_DECLARE_INLINE_UNARY_FUNCTION(floor, f32, __builtin_floorf)
DZNL_DECLARE_INLINE_UNARY_FUNCTION(floor, f64, __builtin_floor)
DZNL_DECLARE_INLINE_UNARY_FUNCTION(trunc, f32, __builtin_truncf)
DZNL_DECLARE_INLINE_UNARY_FUNCTION(trunc, f64, __builtin_trunc)
DZNL_DECLARE_INLINE_UNARY_FUNCTION(abs, f32, __builtin_fabsf)
DZNL_DECLARE_INLINE_UNARY_FUNCTION(abs, f64, __builtin_fabs)
DZNL_DECLARE_INLINE_UNARY_FUNCTION(sqrt, f32, __builtin_sqrtf)
DZNL_DECLARE_INLINE_UNARY_FUNCTION(sqrt, f64, __builtin_sqrt)
DZNL_DECLARE_INLINE_BINARY_FUNCTION(copysign, f32, __builtin_copysignf)
DZNL_DECLARE_INLINE_BINARY_FUNCTION(copysign, f64, __builtin_copysign)


#undef DZNL_DECLARE_INLINE_UNARY_FUNCTION
#undef DZNL_DECLARE_INLINE_BINARY_FUNCTION


} // namespace dznl

#endif // DZNL_MATHEMATICAL_FUNCTIONS_HPP_INCLUDED
