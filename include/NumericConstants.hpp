#ifndef DZNL_NUMERIC_CONSTANTS_HPP_INCLUDED
#define DZNL_NUMERIC_CONSTANTS_HPP_INCLUDED

#ifdef DZNL_REQUEST_BOOST_MULTIPRECISION_INTEROP
#include <boost/multiprecision/number.hpp>
#endif // DZNL_REQUEST_BOOST_MULTIPRECISION_INTEROP

#ifdef BOOST_MP_NUMBER_HPP
#define DZNL_REQUEST_BOOST_MULTIPRECISION_INTEROP
#endif // BOOST_MP_NUMBER_HPP

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


#ifdef DZNL_REQUEST_BOOST_MULTIPRECISION_INTEROP

template <typename B, ::boost::multiprecision::expression_template_option ET>
struct constants<::boost::multiprecision::number<B, ET>> {

    static constexpr ::boost::multiprecision::number<B, ET> zero() noexcept {
        return 0;
    }

    static constexpr ::boost::multiprecision::number<B, ET> one() noexcept {
        return 1;
    }
};

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
