#ifdef DZNL_REQUEST_128_BIT_FLOATS
#define DZNL_REQUEST_F128
#endif // DZNL_REQUEST_128_BIT_FLOATS


#if defined(DZNL_REQUEST_F128) && defined(DZNL_REQUEST_FLOAT_TO_STRING)
#define DZNL_REQUEST_128_BIT_INTEGERS
#endif // defined(DZNL_REQUEST_F128) && defined(DZNL_REQUEST_FLOAT_TO_STRING)


#ifdef DZNL_REQUEST_128_BIT_INTEGERS
#define DZNL_REQUEST_I128
#define DZNL_REQUEST_U128
#endif // DZNL_REQUEST_128_BIT_INTEGERS


#ifdef DZNL_REQUEST_16_BIT_FLOATS
#define DZNL_REQUEST_F16
#define DZNL_REQUEST_BF16
#endif // DZNL_REQUEST_16_BIT_FLOATS


#ifdef DZNL_REQUEST_DECIMAL_FLOATS
#define DZNL_REQUEST_D32
#define DZNL_REQUEST_D64
#define DZNL_REQUEST_D128
#endif // DZNL_REQUEST_DECIMAL_FLOATS


#ifdef BOOST_MP_NUMBER_HPP
#define DZNL_REQUEST_BOOST_MULTIPRECISION_INTEROP
#endif // BOOST_MP_NUMBER_HPP


// IWYU pragma: begin_exports
#include "FloatingPoint.hpp"
#include "Macros.hpp"
#include "Memory.hpp"
#include "MultiFloat.hpp"
#include "NumericConstants.hpp"
#include "NumericFunctions.hpp"
#include "NumericTypes.hpp"
#include "StaticString.hpp"
#include "Tuple.hpp"
// IWYU pragma: end_exports
