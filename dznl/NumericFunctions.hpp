#ifndef DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED
#define DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED

#include "Macros.hpp"
#include "Memory.hpp"
#include "NumericTypes.hpp"

namespace dznl {


template <typename T>
struct NumTraits {};


/**
 * @brief Construct and return an additive identity element
 *        of a numeric type `T`.
 */
template <typename T>
constexpr T zero() noexcept {
    return NumTraits<T>::zero_impl();
}


/**
 * @brief Construct and return a multiplicative identity element
 *        of a numeric type `T`.
 */
template <typename T>
constexpr T one() noexcept {
    return NumTraits<T>::one_impl();
}


template <typename T>
constexpr bool is_zero(const T &x) noexcept {
    return NumTraits<T>::is_zero_impl(x);
}


template <typename T>
constexpr bool is_one(const T &x) noexcept {
    return NumTraits<T>::is_one_impl(x);
}


template <typename T>
constexpr bool sign_bit(const T &x) noexcept {
    return NumTraits<T>::sign_bit_impl(x);
}


template <typename T>
constexpr bool is_nan(const T &x) noexcept {
    return NumTraits<T>::is_nan_impl(x);
}


template <typename T>
constexpr bool is_inf(const T &x) noexcept {
    return NumTraits<T>::is_inf_impl(x);
}


template <typename T>
constexpr bool is_finite(const T &x) noexcept {
    return NumTraits<T>::is_finite_impl(x);
}


template <typename T>
constexpr T twice(const T &x) noexcept {
    return NumTraits<T>::twice_impl(x);
}


template <typename T>
constexpr T square(const T &x) noexcept {
    return NumTraits<T>::square_impl(x);
}


template <typename T>
constexpr T fma(const T &x, const T &y, const T &z) noexcept {
    return NumTraits<T>::fma_impl(x, y, z);
}


template <typename T>
constexpr T inv(const T &x) {
    return NumTraits<T>::inv_impl(x);
}


template <typename T>
constexpr T halve(const T &x) {
    return NumTraits<T>::halve_impl(x);
}


template <typename T>
constexpr T sqrt(const T &x) {
    return NumTraits<T>::sqrt_impl(x);
}


template <typename T>
constexpr T rsqrt(const T &x) {
    return NumTraits<T>::rsqrt_impl(x);
}


////////////////////////////////////////////////////// FUNDAMENTAL INTEGER TYPES


template <>
struct NumTraits<char> {
    static constexpr char ZERO_CONST = '\0';
    static constexpr char zero_impl() noexcept { return ZERO_CONST; }
    static constexpr bool is_zero_impl(const char &x) noexcept {
        return x == ZERO_CONST;
    }
}; // struct NumTraits<char>


template <>
struct NumTraits<signed char> {
    static constexpr signed char ZERO_CONST = '\0';
    static constexpr signed char ONE_CONST = '\1';
    static constexpr signed char zero_impl() noexcept { return ZERO_CONST; }
    static constexpr signed char one_impl() noexcept { return ONE_CONST; }
    static constexpr bool is_zero_impl(const signed char &x) noexcept {
        return x == ZERO_CONST;
    }
    static constexpr bool is_one_impl(const signed char &x) noexcept {
        return x == ONE_CONST;
    }
    static constexpr bool sign_bit_impl(const signed char &x) noexcept {
        return x < ZERO_CONST;
    }
    static constexpr bool is_nan_impl(const signed char &) noexcept {
        return false;
    }
    static constexpr bool is_inf_impl(const signed char &) noexcept {
        return false;
    }
    static constexpr bool is_finite_impl(const signed char &) noexcept {
        return true;
    }
    static constexpr signed char twice_impl(const signed char &x) noexcept {
        return static_cast<signed char>(x + x);
    }
    static constexpr signed char square_impl(const signed char &x) noexcept {
        return static_cast<signed char>(x * x);
    }
}; // struct NumTraits<signed char>


template <>
struct NumTraits<unsigned char> {
    static constexpr unsigned char ZERO_CONST = '\0';
    static constexpr unsigned char ONE_CONST = '\1';
    static constexpr unsigned char zero_impl() noexcept { return ZERO_CONST; }
    static constexpr unsigned char one_impl() noexcept { return ONE_CONST; }
    static constexpr bool is_zero_impl(const unsigned char &x) noexcept {
        return x == ZERO_CONST;
    }
    static constexpr bool is_one_impl(const unsigned char &x) noexcept {
        return x == ONE_CONST;
    }
    static constexpr bool sign_bit_impl(const unsigned char &) noexcept {
        return false;
    }
    static constexpr bool is_nan_impl(const unsigned char &) noexcept {
        return false;
    }
    static constexpr bool is_inf_impl(const unsigned char &) noexcept {
        return false;
    }
    static constexpr bool is_finite_impl(const unsigned char &) noexcept {
        return true;
    }
    static constexpr unsigned char twice_impl(const unsigned char &x) noexcept {
        return static_cast<unsigned char>(x + x);
    }
    static constexpr unsigned char square_impl(const unsigned char &x
    ) noexcept {
        return static_cast<unsigned char>(x * x);
    }
}; // struct NumTraits<unsigned char>


template <>
struct NumTraits<short> {
    static constexpr short ZERO_CONST = 0;
    static constexpr short ONE_CONST = 1;
    static constexpr short zero_impl() noexcept { return ZERO_CONST; }
    static constexpr short one_impl() noexcept { return ONE_CONST; }
    static constexpr bool is_zero_impl(const short &x) noexcept {
        return x == ZERO_CONST;
    }
    static constexpr bool is_one_impl(const short &x) noexcept {
        return x == ONE_CONST;
    }
    static constexpr bool sign_bit_impl(const short &x) noexcept {
        return x < ZERO_CONST;
    }
    static constexpr bool is_nan_impl(const short &) noexcept { return false; }
    static constexpr bool is_inf_impl(const short &) noexcept { return false; }
    static constexpr bool is_finite_impl(const short &) noexcept {
        return true;
    }
    static constexpr short twice_impl(const short &x) noexcept {
        return static_cast<short>(x + x);
    }
    static constexpr short square_impl(const short &x) noexcept {
        return static_cast<short>(x * x);
    }
}; // struct NumTraits<short>


template <>
struct NumTraits<unsigned short> {
    static constexpr unsigned short ZERO_CONST = 0U;
    static constexpr unsigned short ONE_CONST = 1U;
    static constexpr unsigned short zero_impl() noexcept { return ZERO_CONST; }
    static constexpr unsigned short one_impl() noexcept { return ONE_CONST; }
    static constexpr bool is_zero_impl(const unsigned short &x) noexcept {
        return x == ZERO_CONST;
    }
    static constexpr bool is_one_impl(const unsigned short &x) noexcept {
        return x == ONE_CONST;
    }
    static constexpr bool sign_bit_impl(const unsigned short &) noexcept {
        return false;
    }
    static constexpr bool is_nan_impl(const unsigned short &) noexcept {
        return false;
    }
    static constexpr bool is_inf_impl(const unsigned short &) noexcept {
        return false;
    }
    static constexpr bool is_finite_impl(const unsigned short &) noexcept {
        return true;
    }
    static constexpr unsigned short twice_impl(const unsigned short &x
    ) noexcept {
        return static_cast<unsigned short>(x + x);
    }
    static constexpr unsigned short square_impl(const unsigned short &x
    ) noexcept {
        return static_cast<unsigned short>(x * x);
    }
}; // struct NumTraits<unsigned short>


template <>
struct NumTraits<int> {
    static constexpr int ZERO_CONST = 0;
    static constexpr int ONE_CONST = 1;
    static constexpr int zero_impl() noexcept { return ZERO_CONST; }
    static constexpr int one_impl() noexcept { return ONE_CONST; }
    static constexpr bool is_zero_impl(const int &x) noexcept {
        return x == ZERO_CONST;
    }
    static constexpr bool is_one_impl(const int &x) noexcept {
        return x == ONE_CONST;
    }
    static constexpr bool sign_bit_impl(const int &x) noexcept {
        return x < ZERO_CONST;
    }
    static constexpr bool is_nan_impl(const int &) noexcept { return false; }
    static constexpr bool is_inf_impl(const int &) noexcept { return false; }
    static constexpr bool is_finite_impl(const int &) noexcept { return true; }
    static constexpr int twice_impl(const int &x) noexcept { return x + x; }
    static constexpr int square_impl(const int &x) noexcept { return x * x; }
}; // struct NumTraits<int>


template <>
struct NumTraits<unsigned> {
    static constexpr unsigned ZERO_CONST = 0U;
    static constexpr unsigned ONE_CONST = 1U;
    static constexpr unsigned zero_impl() noexcept { return ZERO_CONST; }
    static constexpr unsigned one_impl() noexcept { return ONE_CONST; }
    static constexpr bool is_zero_impl(const unsigned &x) noexcept {
        return x == ZERO_CONST;
    }
    static constexpr bool is_one_impl(const unsigned &x) noexcept {
        return x == ONE_CONST;
    }
    static constexpr bool sign_bit_impl(const unsigned &) noexcept {
        return false;
    }
    static constexpr bool is_nan_impl(const unsigned &) noexcept {
        return false;
    }
    static constexpr bool is_inf_impl(const unsigned &) noexcept {
        return false;
    }
    static constexpr bool is_finite_impl(const unsigned &) noexcept {
        return true;
    }
    static constexpr unsigned twice_impl(const unsigned &x) noexcept {
        return x + x;
    }
    static constexpr unsigned square_impl(const unsigned &x) noexcept {
        return x * x;
    }
}; // struct NumTraits<unsigned>


template <>
struct NumTraits<long> {
    static constexpr long ZERO_CONST = 0L;
    static constexpr long ONE_CONST = 1L;
    static constexpr long zero_impl() noexcept { return ZERO_CONST; }
    static constexpr long one_impl() noexcept { return ONE_CONST; }
    static constexpr bool is_zero_impl(const long &x) noexcept {
        return x == ZERO_CONST;
    }
    static constexpr bool is_one_impl(const long &x) noexcept {
        return x == ONE_CONST;
    }
    static constexpr bool sign_bit_impl(const long &x) noexcept {
        return x < ZERO_CONST;
    }
    static constexpr bool is_nan_impl(const long &) noexcept { return false; }
    static constexpr bool is_inf_impl(const long &) noexcept { return false; }
    static constexpr bool is_finite_impl(const long &) noexcept { return true; }
    static constexpr long twice_impl(const long &x) noexcept { return x + x; }
    static constexpr long square_impl(const long &x) noexcept { return x * x; }
}; // struct NumTraits<long>


template <>
struct NumTraits<unsigned long> {
    static constexpr unsigned long ZERO_CONST = 0UL;
    static constexpr unsigned long ONE_CONST = 1UL;
    static constexpr unsigned long zero_impl() noexcept { return ZERO_CONST; }
    static constexpr unsigned long one_impl() noexcept { return ONE_CONST; }
    static constexpr bool is_zero_impl(const unsigned long &x) noexcept {
        return x == ZERO_CONST;
    }
    static constexpr bool is_one_impl(const unsigned long &x) noexcept {
        return x == ONE_CONST;
    }
    static constexpr bool sign_bit_impl(const unsigned long &) noexcept {
        return false;
    }
    static constexpr bool is_nan_impl(const unsigned long &) noexcept {
        return false;
    }
    static constexpr bool is_inf_impl(const unsigned long &) noexcept {
        return false;
    }
    static constexpr bool is_finite_impl(const unsigned long &) noexcept {
        return true;
    }
    static constexpr unsigned long twice_impl(const unsigned long &x) noexcept {
        return x + x;
    }
    static constexpr unsigned long square_impl(const unsigned long &x
    ) noexcept {
        return x * x;
    }
}; // struct NumTraits<unsigned long>


template <>
struct NumTraits<long long> {
    static constexpr long long ZERO_CONST = 0LL;
    static constexpr long long ONE_CONST = 1LL;
    static constexpr long long zero_impl() noexcept { return ZERO_CONST; }
    static constexpr long long one_impl() noexcept { return ONE_CONST; }
    static constexpr bool is_zero_impl(const long long &x) noexcept {
        return x == ZERO_CONST;
    }
    static constexpr bool is_one_impl(const long long &x) noexcept {
        return x == ONE_CONST;
    }
    static constexpr bool sign_bit_impl(const long long &x) noexcept {
        return x < ZERO_CONST;
    }
    static constexpr bool is_nan_impl(const long long &) noexcept {
        return false;
    }
    static constexpr bool is_inf_impl(const long long &) noexcept {
        return false;
    }
    static constexpr bool is_finite_impl(const long long &) noexcept {
        return true;
    }
    static constexpr long long twice_impl(const long long &x) noexcept {
        return x + x;
    }
    static constexpr long long square_impl(const long long &x) noexcept {
        return x * x;
    }
}; // struct NumTraits<long long>


template <>
struct NumTraits<unsigned long long> {
    static constexpr unsigned long long ZERO_CONST = 0ULL;
    static constexpr unsigned long long ONE_CONST = 1ULL;
    static constexpr unsigned long long zero_impl() noexcept {
        return ZERO_CONST;
    }
    static constexpr unsigned long long one_impl() noexcept {
        return ONE_CONST;
    }
    static constexpr bool is_zero_impl(const unsigned long long &x) noexcept {
        return x == ZERO_CONST;
    }
    static constexpr bool is_one_impl(const unsigned long long &x) noexcept {
        return x == ONE_CONST;
    }
    static constexpr bool sign_bit_impl(const unsigned long long &) noexcept {
        return false;
    }
    static constexpr bool is_nan_impl(const unsigned long long &) noexcept {
        return false;
    }
    static constexpr bool is_inf_impl(const unsigned long long &) noexcept {
        return false;
    }
    static constexpr bool is_finite_impl(const unsigned long long &) noexcept {
        return true;
    }
    static constexpr unsigned long long twice_impl(const unsigned long long &x
    ) noexcept {
        return x + x;
    }
    static constexpr unsigned long long square_impl(const unsigned long long &x
    ) noexcept {
        return x * x;
    }
}; // struct NumTraits<unsigned long long>


///////////////////////////////////////////////////////// EXTENDED INTEGER TYPES


#ifdef DZNL_REQUEST_I128
template <>
struct NumTraits<i128> {
    static constexpr i128 zero_impl() noexcept { return 0LL; }
    static constexpr i128 one_impl() noexcept { return 1LL; }
    static constexpr bool is_zero_impl(const i128 &x) noexcept {
        return x == 0LL;
    }
    static constexpr bool is_one_impl(const i128 &x) noexcept {
        return x == 1LL;
    }
    static constexpr bool sign_bit_impl(const i128 &x) noexcept {
        return x < 0LL;
    }
    static constexpr bool is_nan_impl(const i128 &) noexcept { return false; }
    static constexpr bool is_inf_impl(const i128 &) noexcept { return false; }
    static constexpr bool is_finite_impl(const i128 &) noexcept { return true; }
    static constexpr i128 twice_impl(const i128 &x) noexcept { return x + x; }
    static constexpr i128 square_impl(const i128 &x) noexcept { return x * x; }
}; // struct NumTraits<i128>
#endif // DZNL_REQUEST_I128


#ifdef DZNL_REQUEST_U128
template <>
struct NumTraits<u128> {
    static constexpr u128 zero_impl() noexcept { return 0ULL; }
    static constexpr u128 one_impl() noexcept { return 1ULL; }
    static constexpr bool is_zero_impl(const u128 &x) noexcept {
        return x == 0ULL;
    }
    static constexpr bool is_one_impl(const u128 &x) noexcept {
        return x == 1ULL;
    }
    static constexpr bool sign_bit_impl(const u128 &) noexcept { return false; }
    static constexpr bool is_nan_impl(const u128 &) noexcept { return false; }
    static constexpr bool is_inf_impl(const u128 &) noexcept { return false; }
    static constexpr bool is_finite_impl(const u128 &) noexcept { return true; }
    static constexpr u128 twice_impl(const u128 &x) noexcept { return x + x; }
    static constexpr u128 square_impl(const u128 &x) noexcept { return x * x; }
}; // struct NumTraits<u128>
#endif // DZNL_REQUEST_U128


/////////////////////////////////////////////// FUNDAMENTAL FLOATING-POINT TYPES


template <>
struct NumTraits<f32> {
    static constexpr f32 zero_impl() noexcept { return 0.0F; }
    static constexpr f32 one_impl() noexcept { return 1.0F; }
    static constexpr bool is_zero_impl(const f32 &x) noexcept {
        return x == 0.0F;
    }
    static constexpr bool is_one_impl(const f32 &x) noexcept {
        return x == 1.0F;
    }
    static constexpr bool sign_bit_impl(const f32 &x) noexcept {
        return sign_bit(bit_cast<i32>(x));
    }
    static constexpr bool is_nan_impl(const f32 &x) noexcept {
        return !(x == x);
    }
    static constexpr bool is_inf_impl(const f32 &x) noexcept {
        return (!is_nan_impl(x)) && is_nan_impl(x - x);
    }
    static constexpr bool is_finite_impl(const f32 &x) noexcept {
        return (!is_nan_impl(x)) && (!is_nan_impl(x - x));
    }
    static constexpr f32 twice_impl(const f32 &x) noexcept { return x + x; }
    static constexpr f32 square_impl(const f32 &x) noexcept { return x * x; }
#if DZNL_HAS_BUILTIN(__builtin_fmaf)
    static inline f32
    fma_impl(const f32 &x, const f32 &y, const f32 &z) noexcept {
        return __builtin_fmaf(x, y, z);
    }
#endif
    static constexpr f32 inv_impl(const f32 &x) noexcept { return 1.0F / x; }
    static constexpr f32 halve_impl(const f32 &x) noexcept { return 0.5F * x; }
#if DZNL_HAS_BUILTIN(__builtin_sqrtf)
    static inline f32 sqrt_impl(const f32 &x) noexcept {
        return __builtin_sqrtf(x);
    }
    static inline f32 rsqrt_impl(const f32 &x) noexcept {
        return 1.0F / __builtin_sqrtf(x);
    }
#endif
}; // struct NumTraits<f32>


template <>
struct NumTraits<f64> {
    static constexpr f64 zero_impl() noexcept { return 0.0; }
    static constexpr f64 one_impl() noexcept { return 1.0; }
    static constexpr bool is_zero_impl(const f64 &x) noexcept {
        return x == 0.0;
    }
    static constexpr bool is_one_impl(const f64 &x) noexcept {
        return x == 1.0;
    }
    static constexpr bool sign_bit_impl(const f64 &x) noexcept {
        return sign_bit(bit_cast<i64>(x));
    }
    static constexpr bool is_nan_impl(const f64 &x) noexcept {
        return !(x == x);
    }
    static constexpr bool is_inf_impl(const f64 &x) noexcept {
        return (!is_nan_impl(x)) && is_nan_impl(x - x);
    }
    static constexpr bool is_finite_impl(const f64 &x) noexcept {
        return (!is_nan_impl(x)) && (!is_nan_impl(x - x));
    }
    static constexpr f64 twice_impl(const f64 &x) noexcept { return x + x; }
    static constexpr f64 square_impl(const f64 &x) noexcept { return x * x; }
#if DZNL_HAS_BUILTIN(__builtin_fma)
    static inline f64
    fma_impl(const f64 &x, const f64 &y, const f64 &z) noexcept {
        return __builtin_fma(x, y, z);
    }
#endif
    static constexpr f64 inv_impl(const f64 &x) noexcept { return 1.0 / x; }
    static constexpr f64 halve_impl(const f64 &x) noexcept { return 0.5 * x; }
#if DZNL_HAS_BUILTIN(__builtin_sqrt)
    static inline f64 sqrt_impl(const f64 &x) noexcept {
        return __builtin_sqrt(x);
    }
    static inline f64 rsqrt_impl(const f64 &x) noexcept {
        return 1.0 / __builtin_sqrt(x);
    }
#endif
}; // struct NumTraits<f64>


////////////////////////////////////////////////// EXTENDED FLOATING-POINT TYPES


#ifdef DZNL_REQUEST_F16
template <>
struct NumTraits<f16> {
    static constexpr f16 zero_impl() noexcept { return static_cast<f16>(0); }
    static constexpr f16 one_impl() noexcept { return static_cast<f16>(1); }
    static constexpr bool is_zero_impl(const f16 &x) noexcept {
        return x == static_cast<f16>(0);
    }
    static constexpr bool is_one_impl(const f16 &x) noexcept {
        return x == static_cast<f16>(1);
    }
    static constexpr bool sign_bit_impl(const f16 &x) noexcept {
        return sign_bit(bit_cast<i16>(x));
    }
    static constexpr bool is_nan_impl(const f16 &x) noexcept {
        return !(x == x);
    }
    static constexpr bool is_inf_impl(const f16 &x) noexcept {
        return (!is_nan_impl(x)) && is_nan_impl(x - x);
    }
    static constexpr bool is_finite_impl(const f16 &x) noexcept {
        return (!is_nan_impl(x)) && (!is_nan_impl(x - x));
    }
}; // struct NumTraits<f16>
#endif // DZNL_REQUEST_F16


#ifdef DZNL_REQUEST_BF16
template <>
struct NumTraits<bf16> {
    static constexpr bf16 zero_impl() noexcept { return static_cast<bf16>(0); }
    static constexpr bf16 one_impl() noexcept { return static_cast<bf16>(1); }
    static constexpr bool is_zero_impl(const bf16 &x) noexcept {
        return x == static_cast<bf16>(0);
    }
    static constexpr bool is_one_impl(const bf16 &x) noexcept {
        return x == static_cast<bf16>(1);
    }
    static constexpr bool sign_bit_impl(const bf16 &x) noexcept {
        return sign_bit(bit_cast<i16>(x));
    }
    static constexpr bool is_nan_impl(const bf16 &x) noexcept {
        return !(x == x);
    }
    static constexpr bool is_inf_impl(const bf16 &x) noexcept {
        return (!is_nan_impl(x)) && is_nan_impl(x - x);
    }
    static constexpr bool is_finite_impl(const bf16 &x) noexcept {
        return (!is_nan_impl(x)) && (!is_nan_impl(x - x));
    }
}; // struct NumTraits<bf16>
#endif // DZNL_REQUEST_BF16


#ifdef DZNL_REQUEST_F128
template <>
struct NumTraits<f128> {
    static constexpr f128 zero_impl() noexcept { return static_cast<f128>(0); }
    static constexpr f128 one_impl() noexcept { return static_cast<f128>(1); }
    static constexpr bool is_zero_impl(const f128 &x) noexcept {
        return x == static_cast<f128>(0);
    }
    static constexpr bool is_one_impl(const f128 &x) noexcept {
        return x == static_cast<f128>(1);
    }
    static constexpr bool sign_bit_impl(const f128 &x) noexcept {
        return sign_bit(bit_cast<i128>(x));
    }
    static constexpr bool is_nan_impl(const f128 &x) noexcept {
        return !(x == x);
    }
    static constexpr bool is_inf_impl(const f128 &x) noexcept {
        return (!is_nan_impl(x)) && is_nan_impl(x - x);
    }
    static constexpr bool is_finite_impl(const f128 &x) noexcept {
        return (!is_nan_impl(x)) && (!is_nan_impl(x - x));
    }
}; // struct NumTraits<f128>
#endif // DZNL_REQUEST_F128


#ifdef DZNL_REQUEST_D32
template <>
struct NumTraits<d32> {
    static constexpr d32 zero_impl() noexcept { return static_cast<d32>(0); }
    static constexpr d32 one_impl() noexcept { return static_cast<d32>(1); }
    static constexpr bool is_zero_impl(const d32 &x) noexcept {
        return x == static_cast<d32>(0);
    }
    static constexpr bool is_one_impl(const d32 &x) noexcept {
        return x == static_cast<d32>(1);
    }
    static constexpr bool sign_bit_impl(const d32 &x) noexcept {
        return sign_bit(bit_cast<i32>(x));
    }
    static constexpr bool is_nan_impl(const d32 &x) noexcept {
        return !(x == x);
    }
    static constexpr bool is_inf_impl(const d32 &x) noexcept {
        return (!is_nan_impl(x)) && is_nan_impl(x - x);
    }
    static constexpr bool is_finite_impl(const d32 &x) noexcept {
        return (!is_nan_impl(x)) && (!is_nan_impl(x - x));
    }
}; // struct NumTraits<d32>
#endif // DZNL_REQUEST_D32


#ifdef DZNL_REQUEST_D64
template <>
struct NumTraits<d64> {
    static constexpr d64 zero_impl() noexcept { return static_cast<d64>(0); }
    static constexpr d64 one_impl() noexcept { return static_cast<d64>(1); }
    static constexpr bool is_zero_impl(const d64 &x) noexcept {
        return x == static_cast<d64>(0);
    }
    static constexpr bool is_one_impl(const d64 &x) noexcept {
        return x == static_cast<d64>(1);
    }
    static constexpr bool sign_bit_impl(const d64 &x) noexcept {
        return sign_bit(bit_cast<i64>(x));
    }
    static constexpr bool is_nan_impl(const d64 &x) noexcept {
        return !(x == x);
    }
    static constexpr bool is_inf_impl(const d64 &x) noexcept {
        return (!is_nan_impl(x)) && is_nan_impl(x - x);
    }
    static constexpr bool is_finite_impl(const d64 &x) noexcept {
        return (!is_nan_impl(x)) && (!is_nan_impl(x - x));
    }
}; // struct NumTraits<d64>
#endif // DZNL_REQUEST_D64


#ifdef DZNL_REQUEST_D128
template <>
struct NumTraits<d128> {
    static constexpr d128 zero_impl() noexcept { return static_cast<d128>(0); }
    static constexpr d128 one_impl() noexcept { return static_cast<d128>(1); }
    static constexpr bool is_zero_impl(const d128 &x) noexcept {
        return x == static_cast<d128>(0);
    }
    static constexpr bool is_one_impl(const d128 &x) noexcept {
        return x == static_cast<d128>(1);
    }
    static constexpr bool sign_bit_impl(const d128 &x) noexcept {
        return sign_bit(bit_cast<i128>(x));
    }
    static constexpr bool is_nan_impl(const d128 &x) noexcept {
        return !(x == x);
    }
    static constexpr bool is_inf_impl(const d128 &x) noexcept {
        return (!is_nan_impl(x)) && is_nan_impl(x - x);
    }
    static constexpr bool is_finite_impl(const d128 &x) noexcept {
        return (!is_nan_impl(x)) && (!is_nan_impl(x - x));
    }
}; // struct NumTraits<d128>
#endif // DZNL_REQUEST_D128


/////////////////////////////////////////////////// LIBRARY FLOATING-POINT TYPES


#ifdef DZNL_REQUEST_BOOST_MULTIPRECISION_INTEROP
template <
    typename Backend,
    ::boost::multiprecision::expression_template_option ExpressionTemplates>
struct NumTraits<
    ::boost::multiprecision::number<Backend, ExpressionTemplates>> {
    static constexpr ::boost::multiprecision::
        number<Backend, ExpressionTemplates>
        zero_impl() noexcept {
        return static_cast<
            ::boost::multiprecision::number<Backend, ExpressionTemplates>>(0);
    }
    static constexpr ::boost::multiprecision::
        number<Backend, ExpressionTemplates>
        one_impl() noexcept {
        return static_cast<
            ::boost::multiprecision::number<Backend, ExpressionTemplates>>(1);
    }
    static constexpr bool is_zero_impl(
        const ::boost::multiprecision::number<Backend, ExpressionTemplates> &x
    ) noexcept {
        return x == 0;
    }
    static constexpr bool is_one_impl(
        const ::boost::multiprecision::number<Backend, ExpressionTemplates> &x
    ) noexcept {
        return x == 1;
    }
    static constexpr bool sign_bit_impl(
        const ::boost::multiprecision::number<Backend, ExpressionTemplates> &x
    ) noexcept {
        return x < 0;
    }
    static constexpr bool is_nan_impl(
        const ::boost::multiprecision::number<Backend, ExpressionTemplates> &x
    ) noexcept {
        return !(x == x);
    }
    static constexpr bool is_inf_impl(
        const ::boost::multiprecision::number<Backend, ExpressionTemplates> &x
    ) noexcept {
        return (!is_nan_impl(x)) && is_nan_impl(x - x);
    }
    static constexpr bool is_finite_impl(
        const ::boost::multiprecision::number<Backend, ExpressionTemplates> &x
    ) noexcept {
        return (!is_nan_impl(x)) && (!is_nan_impl(x - x));
    }
};
#endif // DZNL_REQUEST_BOOST_MULTIPRECISION_INTEROP


////////////////////////////////////////////////////////////////////////////////


template <typename UNSIGNED_T>
constexpr int leading_zeros(UNSIGNED_T x) noexcept {
    constexpr int BIT_SIZE = DZNL_CHAR_BIT * sizeof(UNSIGNED_T);
#if DZNL_HAS_BUILTIN(__builtin_clzg)
    return is_zero(x) ? BIT_SIZE : __builtin_clzg(x);
#else
    constexpr UNSIGNED_T BIT_MASK = one<UNSIGNED_T>() << (BIT_SIZE - 1);
    for (int i = 0; i < BIT_SIZE; ++i) {
        if (!is_zero(x & BIT_MASK)) {
            return i;
        } else {
            x <<= 1;
        }
    }
    return BIT_SIZE;
#endif
}


namespace internal {


template <typename T, typename INTEGER_T>
constexpr T mul_by_doubling(const T &x, const INTEGER_T &n) {
    if (is_zero(n)) {
        return zero<T>();
    } else if (is_one(n)) {
        return x;
    } else {
        constexpr INTEGER_T ONE = one<INTEGER_T>();
        const T y = mul_by_doubling(x, n >> ONE);
        const T z = y + y;
        return is_zero(n & ONE) ? z : (z + x);
    }
}


template <typename T, typename INTEGER_T>
constexpr T pow_by_squaring(const T &x, const INTEGER_T &n) {
    if (is_zero(n)) {
        return one<T>();
    } else if (is_one(n)) {
        return x;
    } else {
        constexpr INTEGER_T ONE = one<INTEGER_T>();
        const T y = pow_by_squaring(x, n >> ONE);
        const T z = y * y;
        return is_zero(n & ONE) ? z : (z * x);
    }
}


template <typename T, typename INTEGER_T>
constexpr T bbp_pi_term(
    const INTEGER_T &n,
    const T &K1,
    const T &K3,
    const T &K5,
    const T &K47,
    const T &K120,
    const T &K151
) {
    const T KN = mul_by_doubling(K1, n);
    const T K2N = KN + KN;
    const T K4N = K2N + K2N;
    const T K8N = K4N + K4N;
    const T num = (K120 * KN + K151) * KN + K47;
    const T den = (K2N + K1) * (K4N + K3) * (K8N + K1) * (K8N + K5);
    return num / den;
}


template <typename T, typename INTEGER_T>
constexpr T bbp_pi_partial_sum(
    const INTEGER_T &n,
    const T &K0,
    const T &K1,
    const T &K3,
    const T &K5,
    const T &K16,
    const T &K47,
    const T &K120,
    const T &K151
) {
    T result = K0;
    for (INTEGER_T i = n; !is_zero(i); --i) {
        result = bbp_pi_term<T>(i, K1, K3, K5, K47, K120, K151) + result / K16;
    }
    result = bbp_pi_term<T>(0, K1, K3, K5, K47, K120, K151) + result / K16;
    return result;
}


template <typename T, typename INTEGER_T>
constexpr T e_partial_sum(const INTEGER_T &n) {
    const T ONE = one<T>();
    T result = ONE;
    for (INTEGER_T i = n; !is_zero(i); --i) {
        result = ONE + result / mul_by_doubling(ONE, i);
    }
    return result;
}


} // namespace internal


template <typename T>
constexpr T compute_pi() {
    const T K0 = zero<T>();
    const T K1 = one<T>();
    const T K2 = twice(K1);
    const T K3 = K2 + K1;
    const T K4 = twice(K2);
    const T K5 = K4 + K1;
    const T K7 = K4 + K3;
    const T K8 = twice(K4);
    const T K15 = K8 + K7;
    const T K16 = twice(K8);
    const T K23 = K16 + K7;
    const T K24 = K16 + K8;
    const T K32 = twice(K16);
    const T K47 = K32 + K15;
    const T K56 = K32 + K24;
    const T K64 = twice(K32);
    const T K120 = K64 + K56;
    const T K128 = twice(K64);
    const T K151 = K128 + K23;
    T current = internal::bbp_pi_partial_sum<T>(
        0, K0, K1, K3, K5, K16, K47, K120, K151
    );
    for (int n = 1;; ++n) {
        const T next = internal::bbp_pi_partial_sum<T>(
            n, K0, K1, K3, K5, K16, K47, K120, K151
        );
        if (current == next) { return current; }
        current = next;
    }
}


template <typename T>
constexpr T compute_e() {
    T current = internal::e_partial_sum<T>(0);
    for (int n = 1;; ++n) {
        const T next = internal::e_partial_sum<T>(n);
        if (current == next) { return current; }
        current = next;
    }
}


} // namespace dznl

#endif // DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED
