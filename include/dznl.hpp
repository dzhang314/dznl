#ifdef DZNL_REQUEST_DECIMAL_FLOATS
#define DZNL_REQUEST_D32
#define DZNL_REQUEST_D64
#define DZNL_REQUEST_D128
#endif // DZNL_REQUEST_DECIMAL_FLOATS


#ifdef DZNL_REQUEST_128_BIT_INTEGERS
#define DZNL_REQUEST_I128
#define DZNL_REQUEST_U128
#endif // DZNL_REQUEST_128_BIT_INTEGERS


#ifdef BOOST_MP_NUMBER_HPP
#define DZNL_REQUEST_BOOST_MULTIPRECISION_INTEROP
#endif // BOOST_MP_NUMBER_HPP


// clang-format off
#include "Macros.hpp"
#include "NumericTypes.hpp"
#include "NumericConstants.hpp"
#include "Tuple.hpp"
#include "MultiFloat.hpp"
// clang-format on
