#include "NumericFunctions.hpp"
#include "NumericTypes.hpp"


template <typename T>
constexpr bool test_signed_zero_one_two() {

    constexpr T zero = dznl::zero<T>();
    constexpr T one = dznl::one<T>();
    constexpr T two = one + one;
    constexpr T neg_one = -one;
    constexpr T neg_two = -two;

    bool result = true;

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
constexpr bool test_unsigned_zero_one_two() {

    constexpr T zero = dznl::zero<T>();
    constexpr T one = dznl::one<T>();
    constexpr T two = one + one;

    bool result = true;

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
    static_assert(test_signed_zero_one_two<dznl::i8>());
    static_assert(test_signed_zero_one_two<dznl::i16>());
    static_assert(test_signed_zero_one_two<dznl::i32>());
    static_assert(test_signed_zero_one_two<dznl::i64>());
    static_assert(test_unsigned_zero_one_two<dznl::u8>());
    static_assert(test_unsigned_zero_one_two<dznl::u16>());
    static_assert(test_unsigned_zero_one_two<dznl::u32>());
    static_assert(test_unsigned_zero_one_two<dznl::u64>());
    static_assert(test_signed_zero_one_two<dznl::f32>());
    static_assert(test_signed_zero_one_two<dznl::f64>());
    return 0;
}
