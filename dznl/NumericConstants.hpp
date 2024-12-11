#ifndef DZNL_NUMERIC_CONSTANTS_HPP_INCLUDED
#define DZNL_NUMERIC_CONSTANTS_HPP_INCLUDED

#ifdef DZNL_REQUEST_BOOST_MULTIPRECISION_INTEROP
#include <boost/multiprecision/number.hpp>
#endif // DZNL_REQUEST_BOOST_MULTIPRECISION_INTEROP

namespace dznl {


template <typename T>
struct constants {

    [[deprecated("WARNING: You are using the default placeholder implementation"
                 " of dznl::zero<T>(). Please specialize dznl::constants<T> for"
                 " for this specific type T.")]]
    static constexpr T zero() noexcept {
        return static_cast<T>(0);
    }

    [[deprecated("WARNING: You are using the default placeholder implementation"
                 " of dznl::one<T>(). Please specialize dznl::constants<T> for"
                 " for this specific type T.")]]
    static constexpr T one() noexcept {
        return static_cast<T>(1);
    }

}; // struct constants<T>


/**
 * @brief Construct and return an additive identity element
 *        of a numeric type `T`.
 */
template <typename T>
constexpr T zero() noexcept {
    return constants<T>::zero();
}


/**
 * @brief Construct and return a multiplicative identity element
 *        of a numeric type `T`.
 */
template <typename T>
constexpr T one() noexcept {
    return constants<T>::one();
}


#define DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(TYPE, ZERO, ONE)                \
    template <>                                                                \
    struct constants<TYPE> {                                                   \
        static constexpr TYPE zero() noexcept { return ZERO; }                 \
        static constexpr TYPE one() noexcept { return ONE; }                   \
    }

DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(signed char, '\0', '\1');
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(unsigned char, '\0', '\1');
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(signed short, 0, 1);
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(unsigned short, 0U, 1U);
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(signed int, 0, 1);
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(unsigned int, 0U, 1U);
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(signed long, 0L, 1L);
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(unsigned long, 0UL, 1UL);
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(signed long long, 0LL, 1LL);
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(unsigned long long, 0ULL, 1ULL);
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(float, 0.0F, 1.0F);
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(double, 0.0, 1.0);
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(long double, 0.0L, 1.0L);

#ifdef __SIZEOF_INT128__
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(__int128_t, 0LL, 1LL);
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(__uint128_t, 0ULL, 1ULL);
#endif // __SIZEOF_INT128__

#ifdef DZNL_REQUEST_F16
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(f16, 0, 1);
#endif // DZNL_REQUEST_F16

#ifdef DZNL_REQUEST_BF16
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(bf16, 0, 1);
#endif // DZNL_REQUEST_BF16

#ifdef DZNL_REQUEST_F128
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(f128, 0, 1);
#endif // DZNL_REQUEST_F128

#ifdef DZNL_REQUEST_D32
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(d32, 0, 1);
#endif // DZNL_REQUEST_D32

#ifdef DZNL_REQUEST_D64
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(d64, 0, 1);
#endif // DZNL_REQUEST_D64

#ifdef DZNL_REQUEST_D128
DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS(d128, 0, 1);
#endif // DZNL_REQUEST_D128

#undef DZNL_INTERNAL_DEFINE_NUMERIC_CONSTANTS


#ifdef DZNL_REQUEST_BOOST_MULTIPRECISION_INTEROP
// clang-format off
template <typename Backend, ::boost::multiprecision::expression_template_option ExpressionTemplates>
struct constants<::boost::multiprecision::number<Backend, ExpressionTemplates>> {
    static constexpr ::boost::multiprecision::number<Backend, ExpressionTemplates> zero() noexcept { return 0; }
    static constexpr ::boost::multiprecision::number<Backend, ExpressionTemplates> one() noexcept { return 1; }
};
// clang-format on
#endif // DZNL_REQUEST_BOOST_MULTIPRECISION_INTEROP


} // namespace dznl

#endif // DZNL_NUMERIC_CONSTANTS_HPP_INCLUDED
