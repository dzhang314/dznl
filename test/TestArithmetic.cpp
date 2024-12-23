#include <cstdlib>

#include <boost/multiprecision/cpp_bin_float.hpp>
#include <boost/multiprecision/cpp_dec_float.hpp>

#ifndef _MSC_VER
#define DZNL_REQUEST_128_BIT_INTEGERS
#define DZNL_REQUEST_16_BIT_FLOATS
#endif // _MSC_VER

#if defined(__GNUC__) && !defined(__clang__)
#define DZNL_REQUEST_128_BIT_FLOATS
#define DZNL_REQUEST_DECIMAL_FLOATS
#endif // defined(__GNUC__) && !defined(__clang__)

#include <dznl/dznl.hpp>


template <typename T>
constexpr bool test_signed() {

    const T zero = dznl::zero<T>();
    const T one = dznl::one<T>();
    const T two = one + one;
    const T neg_one = -one;
    const T neg_two = -two;

    bool result = true;

    result &= !dznl::is_zero(neg_two);
    result &= !dznl::is_zero(neg_one);
    result &= dznl::is_zero(zero);
    result &= !dznl::is_zero(one);
    result &= !dznl::is_zero(two);

    result &= !dznl::is_one(neg_two);
    result &= !dznl::is_one(neg_one);
    result &= !dznl::is_one(zero);
    result &= dznl::is_one(one);
    result &= !dznl::is_one(two);

    result &= dznl::sign_bit(neg_two);
    result &= dznl::sign_bit(neg_one);
    result &= !dznl::sign_bit(zero);
    result &= !dznl::sign_bit(one);
    result &= !dznl::sign_bit(two);

    result &= (neg_two + zero == neg_two);
    result &= (neg_two + one == neg_one);
    result &= (neg_two + two == zero);
    result &= (neg_one + neg_one == neg_two);
    result &= (neg_one + zero == neg_one);
    result &= (neg_one + one == zero);
    result &= (neg_one + two == one);
    result &= (zero + neg_two == neg_two);
    result &= (zero + neg_one == neg_one);
    result &= (zero + zero == zero);
    result &= (zero + one == one);
    result &= (zero + two == two);
    result &= (one + neg_two == neg_one);
    result &= (one + neg_one == zero);
    result &= (one + zero == one);
    result &= (one + one == two);
    result &= (two + neg_two == zero);
    result &= (two + neg_one == one);
    result &= (two + zero == two);

    result &= (neg_two - neg_two == zero);
    result &= (neg_two - neg_one == neg_one);
    result &= (neg_two - zero == neg_two);
    result &= (neg_one - neg_two == one);
    result &= (neg_one - neg_one == zero);
    result &= (neg_one - zero == neg_one);
    result &= (neg_one - one == neg_two);
    result &= (zero - neg_two == two);
    result &= (zero - neg_one == one);
    result &= (zero - zero == zero);
    result &= (zero - one == neg_one);
    result &= (zero - two == neg_two);
    result &= (one - neg_one == two);
    result &= (one - zero == one);
    result &= (one - one == zero);
    result &= (one - two == neg_one);
    result &= (two - zero == two);
    result &= (two - one == one);
    result &= (two - two == zero);

    result &= (neg_two * neg_one == two);
    result &= (neg_two * zero == zero);
    result &= (neg_two * one == neg_two);
    result &= (neg_one * neg_two == two);
    result &= (neg_one * neg_one == one);
    result &= (neg_one * zero == zero);
    result &= (neg_one * one == neg_one);
    result &= (neg_one * two == neg_two);
    result &= (zero * neg_two == zero);
    result &= (zero * neg_one == zero);
    result &= (zero * zero == zero);
    result &= (zero * one == zero);
    result &= (zero * two == zero);
    result &= (one * neg_two == neg_two);
    result &= (one * neg_one == neg_one);
    result &= (one * zero == zero);
    result &= (one * one == one);
    result &= (one * two == two);
    result &= (two * neg_one == neg_two);
    result &= (two * zero == zero);
    result &= (two * one == two);

    result &= (neg_two / neg_two == one);
    result &= (neg_two / neg_one == two);
    result &= (neg_two / one == neg_two);
    result &= (neg_two / two == neg_one);
    result &= (neg_one / neg_one == one);
    result &= (neg_one / one == neg_one);
    result &= (zero / neg_two == zero);
    result &= (zero / neg_one == zero);
    result &= (zero / one == zero);
    result &= (zero / two == zero);
    result &= (one / neg_one == neg_one);
    result &= (one / one == one);
    result &= (two / neg_two == neg_one);
    result &= (two / neg_one == neg_two);
    result &= (two / one == two);
    result &= (two / two == one);

    return result;
}


template <typename T>
constexpr bool test_unsigned() {

    constexpr T zero = dznl::zero<T>();
    constexpr T one = dznl::one<T>();
    constexpr T two = one + one;

    bool result = true;

    result &= dznl::is_zero(zero);
    result &= !dznl::is_zero(one);
    result &= !dznl::is_zero(two);

    result &= !dznl::is_one(zero);
    result &= dznl::is_one(one);
    result &= !dznl::is_one(two);

    result &= !dznl::sign_bit(zero);
    result &= !dznl::sign_bit(one);
    result &= !dznl::sign_bit(two);

    result &= (zero + zero == zero);
    result &= (zero + one == one);
    result &= (zero + two == two);
    result &= (one + zero == one);
    result &= (one + one == two);
    result &= (two + zero == two);

    result &= (zero - zero == zero);
    result &= (one - zero == one);
    result &= (one - one == zero);
    result &= (two - zero == two);
    result &= (two - one == one);
    result &= (two - two == zero);

    result &= (zero * zero == zero);
    result &= (zero * one == zero);
    result &= (zero * two == zero);
    result &= (one * zero == zero);
    result &= (one * one == one);
    result &= (one * two == two);
    result &= (two * zero == zero);
    result &= (two * one == two);

    result &= (zero / one == zero);
    result &= (zero / two == zero);
    result &= (one / one == one);
    result &= (two / one == two);
    result &= (two / two == one);

    return result;
}


int main() {

    static_assert(test_signed<dznl::i8>());
    static_assert(test_signed<dznl::i16>());
    static_assert(test_signed<dznl::i32>());
    static_assert(test_signed<dznl::i64>());
    static_assert(test_unsigned<dznl::u8>());
    static_assert(test_unsigned<dznl::u16>());
    static_assert(test_unsigned<dznl::u32>());
    static_assert(test_unsigned<dznl::u64>());
    static_assert(test_signed<dznl::f32>());
    static_assert(test_signed<dznl::f64>());

#ifndef _MSC_VER
    static_assert(test_signed<dznl::i128>());
    static_assert(test_unsigned<dznl::u128>());
    static_assert(test_signed<dznl::f16>());
    static_assert(test_signed<dznl::bf16>());
#endif // _MSC_VER

#if defined(__GNUC__) && !defined(__clang__)
    static_assert(test_signed<dznl::f128>());
    static_assert(test_signed<dznl::d32>());
    static_assert(test_signed<dznl::d64>());
    static_assert(test_signed<dznl::d128>());
#endif // defined(__GNUC__) && !defined(__clang__)

    using namespace boost::multiprecision;

    if (!test_signed<cpp_bin_float_single>()) { return EXIT_FAILURE; }
    if (!test_signed<cpp_bin_float_double>()) { return EXIT_FAILURE; }
    if (!test_signed<cpp_bin_float_double_extended>()) { return EXIT_FAILURE; }
    if (!test_signed<cpp_bin_float_quad>()) { return EXIT_FAILURE; }
    if (!test_signed<cpp_bin_float_oct>()) { return EXIT_FAILURE; }
    if (!test_signed<cpp_bin_float_50>()) { return EXIT_FAILURE; }
    if (!test_signed<cpp_bin_float_100>()) { return EXIT_FAILURE; }
    if (!test_signed<cpp_dec_float_50>()) { return EXIT_FAILURE; }
    if (!test_signed<cpp_dec_float_100>()) { return EXIT_FAILURE; }

    return EXIT_SUCCESS;
}
