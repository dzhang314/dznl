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


#ifdef DZNL_REQUEST_D32
template <>
struct constants<d32> {
    static constexpr d32 zero() noexcept { return 0; }
    static constexpr d32 one() noexcept { return 1; }
}; // struct constants<d32>
#endif // DZNL_REQUEST_D32


#ifdef DZNL_REQUEST_D64
template <>
struct constants<d64> {
    static constexpr d64 zero() noexcept { return 0; }
    static constexpr d64 one() noexcept { return 1; }
}; // struct constants<d64>
#endif // DZNL_REQUEST_D64


#ifdef DZNL_REQUEST_D128
template <>
struct constants<d128> {
    static constexpr d128 zero() noexcept { return 0; }
    static constexpr d128 one() noexcept { return 1; }
}; // struct constants<d128>
#endif // DZNL_REQUEST_D128


#ifdef DZNL_REQUEST_BOOST_MULTIPRECISION_INTEROP
// clang-format off
template <typename Backend, ::boost::multiprecision::expression_template_option ExpressionTemplates>
struct constants<::boost::multiprecision::number<Backend, ExpressionTemplates>> {
    static constexpr ::boost::multiprecision::number<Backend, ExpressionTemplates> zero() noexcept { return 0; }
    static constexpr ::boost::multiprecision::number<Backend, ExpressionTemplates> one() noexcept { return 1; }
};
// clang-format on
#endif // DZNL_REQUEST_BOOST_MULTIPRECISION_INTEROP


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


#define DZNL_DEFINE_NUMERIC_CONSTANT(TYPE, NAME, VALUE)                        \
    template <>                                                                \
    constexpr TYPE NAME<TYPE>() noexcept {                                     \
        return VALUE;                                                          \
    }

DZNL_DEFINE_NUMERIC_CONSTANT(signed char, zero, '\0')
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned char, zero, '\0')
DZNL_DEFINE_NUMERIC_CONSTANT(signed short, zero, 0)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned short, zero, 0U)
DZNL_DEFINE_NUMERIC_CONSTANT(signed int, zero, 0)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned int, zero, 0U)
DZNL_DEFINE_NUMERIC_CONSTANT(signed long, zero, 0L)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned long, zero, 0UL)
DZNL_DEFINE_NUMERIC_CONSTANT(signed long long, zero, 0LL)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned long long, zero, 0ULL)
DZNL_DEFINE_NUMERIC_CONSTANT(float, zero, 0.0F)
DZNL_DEFINE_NUMERIC_CONSTANT(double, zero, 0.0)
DZNL_DEFINE_NUMERIC_CONSTANT(long double, zero, 0.0L)

DZNL_DEFINE_NUMERIC_CONSTANT(signed char, one, '\1')
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned char, one, '\1')
DZNL_DEFINE_NUMERIC_CONSTANT(signed short, one, 1)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned short, one, 1U)
DZNL_DEFINE_NUMERIC_CONSTANT(signed int, one, 1)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned int, one, 1U)
DZNL_DEFINE_NUMERIC_CONSTANT(signed long, one, 1L)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned long, one, 1UL)
DZNL_DEFINE_NUMERIC_CONSTANT(signed long long, one, 1LL)
DZNL_DEFINE_NUMERIC_CONSTANT(unsigned long long, one, 1ULL)
DZNL_DEFINE_NUMERIC_CONSTANT(float, one, 1.0F)
DZNL_DEFINE_NUMERIC_CONSTANT(double, one, 1.0)
DZNL_DEFINE_NUMERIC_CONSTANT(long double, one, 1.0L)

#ifdef __SIZEOF_INT128__
DZNL_DEFINE_NUMERIC_CONSTANT(__int128_t, zero, 0LL)
DZNL_DEFINE_NUMERIC_CONSTANT(__uint128_t, zero, 0ULL)
DZNL_DEFINE_NUMERIC_CONSTANT(__int128_t, one, 1LL)
DZNL_DEFINE_NUMERIC_CONSTANT(__uint128_t, one, 1ULL)
#endif // __SIZEOF_INT128__

#undef DZNL_DEFINE_NUMERIC_CONSTANT


} // namespace dznl

#endif // DZNL_NUMERIC_CONSTANTS_HPP_INCLUDED
