#ifndef DZNL_MACROS_HPP_INCLUDED
#define DZNL_MACROS_HPP_INCLUDED

namespace dznl {


#ifndef DZNL_RESTRICT
#ifdef __GNUC__
#define DZNL_RESTRICT __restrict__
#elif defined(_MSC_VER)
#define DZNL_RESTRICT __restrict
#else
#define DZNL_RESTRICT
#endif
#endif // DZNL_RESTRICT


#ifndef DZNL_CONST
#ifdef DZNL_REMOVE_CONST
#define DZNL_CONST
#else
#define DZNL_CONST const
#endif // DZNL_REMOVE_CONST
#endif // DZNL_CONST


#ifndef DZNL_HAS_BUILTIN
#ifdef __has_builtin
#define DZNL_HAS_BUILTIN(x) __has_builtin(x)
#else
#define DZNL_HAS_BUILTIN(x) 0
#endif // __has_builtin
#endif // DZNL_HAS_BUILTIN


#define DZNL_LOOP_OVER_FUNDAMENTAL_INTEGER_TYPES                               \
    DZNL_LOOP_BODY(signed char)                                                \
    DZNL_LOOP_BODY(unsigned char)                                              \
    DZNL_LOOP_BODY(signed short)                                               \
    DZNL_LOOP_BODY(unsigned short)                                             \
    DZNL_LOOP_BODY(signed int)                                                 \
    DZNL_LOOP_BODY(unsigned int)                                               \
    DZNL_LOOP_BODY(signed long)                                                \
    DZNL_LOOP_BODY(unsigned long)                                              \
    DZNL_LOOP_BODY(signed long long)                                           \
    DZNL_LOOP_BODY(unsigned long long)


#ifdef __SIZEOF_INT128__
#define DZNL_LOOP_OVER_EXTENDED_INTEGER_TYPES                                  \
    DZNL_LOOP_BODY(__int128_t)                                                 \
    DZNL_LOOP_BODY(__uint128_t)
#else
#define DZNL_LOOP_OVER_EXTENDED_INTEGER_TYPES
#endif // __SIZEOF_INT128__


#define DZNL_LOOP_OVER_FUNDAMENTAL_FLOATING_POINT_TYPES                        \
    DZNL_LOOP_BODY(float)                                                      \
    DZNL_LOOP_BODY(double)                                                     \
    DZNL_LOOP_BODY(long double)


#define DZNL_LOOP_OVER_INTRINSIC_NUMERIC_TYPES                                 \
    DZNL_LOOP_OVER_FUNDAMENTAL_INTEGER_TYPES                                   \
    DZNL_LOOP_OVER_EXTENDED_INTEGER_TYPES                                      \
    DZNL_LOOP_OVER_FUNDAMENTAL_FLOATING_POINT_TYPES


} // namespace dznl

#endif // DZNL_MACROS_HPP_INCLUDED
