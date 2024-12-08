#ifndef DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED
#define DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED

namespace dznl {


namespace internal {


template <typename T>
[[deprecated("WARNING: You are using the default placeholder implementation of"
             " dznl::zero<T>(). Please provide a template specialization of"
             " dznl::zero<T>() optimized for this type T.")]] constexpr T
zero_default_impl() noexcept {
    return static_cast<T>(0);
}


template <typename T>
[[deprecated("WARNING: You are using the default placeholder implementation of"
             " dznl::one<T>(). Please provide a template specialization of"
             " dznl::one<T>() optimized for this type T.")]] constexpr T
one_default_impl() noexcept {
    return static_cast<T>(1);
}


} // namespace internal


/**
 * @brief Construct and return an additive identity element
 *        of a numeric type `T`.
 */
template <typename T>
constexpr T zero() noexcept {
    return internal::zero_default_impl<T>();
}


/**
 * @brief Construct and return a multiplicative identity element
 *        of a numeric type `T`.
 */
template <typename T>
constexpr T one() noexcept {
    return internal::one_default_impl<T>();
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

#endif // DZNL_NUMERIC_FUNCTIONS_HPP_INCLUDED
