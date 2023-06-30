#ifndef DZNL_NUMERIC_TYPES_HPP_INCLUDED
#define DZNL_NUMERIC_TYPES_HPP_INCLUDED

namespace dznl {


/**
 * @brief Return the additive identity element of a given numeric type T.
 */
template <typename T>
constexpr T zero() noexcept;


/**
 * @brief Return the multiplicative identity element of a given numeric type T.
 */
template <typename T>
constexpr T one() noexcept;


/**
 * @brief Test whether a given element of a numeric type T
 *        is an additive identity element.
 */
template <typename T>
constexpr bool is_zero(const T &) noexcept;


/**
 * @brief Test whether a given element of a numeric type T
 *        is a multiplicative identity element.
 */
template <typename T>
constexpr bool is_one(const T &) noexcept;


/**
 * @brief Return the sum of a given element of a numeric type T with itself.
 *
 * The expressions double_value(x) and x + x should always be equivalent, but
 * double_value(x) can be computed more efficiently than x + x for some types T.
 */
template <typename T>
constexpr T double_value(const T &) noexcept;


/**
 * @brief Return the product of a given element of a numeric type T with itself.
 *
 * The expressions square(x) and x * x should always be equivalent, but
 * square(x) can be computed more efficiently than x * x for some types T.
 */
template <typename T>
constexpr T square(const T &) noexcept;


/**
 * @brief Return the additive inverse of a given element of a numeric type T.
 */
template <typename T>
constexpr T negate(const T &) noexcept;


/**
 * @brief Return the multiplicative inverse of a given element
 *        of a numeric type T.
 */
template <typename T>
constexpr T inv(const T &) noexcept;


#define DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(TYPE)              \
    template <>                                                                \
    constexpr bool is_zero(const TYPE &x) noexcept {                           \
        return x == zero<TYPE>();                                              \
    }                                                                          \
    template <>                                                                \
    constexpr bool is_one(const TYPE &x) noexcept {                            \
        return x == one<TYPE>();                                               \
    }                                                                          \
    template <>                                                                \
    constexpr TYPE double_value(const TYPE &x) noexcept {                      \
        return x + x;                                                          \
    }                                                                          \
    template <>                                                                \
    constexpr TYPE square(const TYPE &x) noexcept {                            \
        return x * x;                                                          \
    }                                                                          \
    template <>                                                                \
    constexpr TYPE negate(const TYPE &x) noexcept {                            \
        return -x;                                                             \
    }


#define DZNL_DEFAULT_INV_IMPLEMENTATION(TYPE)                                  \
    template <>                                                                \
    constexpr TYPE inv(const TYPE &x) noexcept {                               \
        return one<TYPE>() / x;                                                \
    }


using i8 = signed char;
using i16 = signed short int;
using i32 = signed int;
using i64 = signed long long int;
using u8 = unsigned char;
using u16 = unsigned short int;
using u32 = unsigned int;
using u64 = unsigned long long int;
using f32 = float;
using f64 = double;


static_assert(sizeof(i8) == 1);
static_assert(sizeof(i16) == 2);
static_assert(sizeof(i32) == 4);
static_assert(sizeof(i64) == 8);
static_assert(sizeof(u8) == 1);
static_assert(sizeof(u16) == 2);
static_assert(sizeof(u32) == 4);
static_assert(sizeof(u64) == 8);
static_assert(sizeof(f32) == 4);
static_assert(sizeof(f64) == 8);


// clang-format off
template <> constexpr  i8 zero< i8>() noexcept { return '\0'; }
template <> constexpr i16 zero<i16>() noexcept { return 0;    }
template <> constexpr i32 zero<i32>() noexcept { return 0;    }
template <> constexpr i64 zero<i64>() noexcept { return 0LL;  }
template <> constexpr  u8 zero< u8>() noexcept { return '\0'; }
template <> constexpr u16 zero<u16>() noexcept { return 0U;   }
template <> constexpr u32 zero<u32>() noexcept { return 0U;   }
template <> constexpr u64 zero<u64>() noexcept { return 0ULL; }
template <> constexpr f32 zero<f32>() noexcept { return 0.0f; }
template <> constexpr f64 zero<f64>() noexcept { return 0.0;  }
template <> constexpr  i8 one< i8>() noexcept { return '\1'; }
template <> constexpr i16 one<i16>() noexcept { return 1;    }
template <> constexpr i32 one<i32>() noexcept { return 1;    }
template <> constexpr i64 one<i64>() noexcept { return 1LL;  }
template <> constexpr  u8 one< u8>() noexcept { return '\1'; }
template <> constexpr u16 one<u16>() noexcept { return 1U;   }
template <> constexpr u32 one<u32>() noexcept { return 1U;   }
template <> constexpr u64 one<u64>() noexcept { return 1ULL; }
template <> constexpr f32 one<f32>() noexcept { return 1.0f; }
template <> constexpr f64 one<f64>() noexcept { return 1.0;  }
// clang-format on


DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(i8)
DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(i16)
DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(i32)
DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(i64)
DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(u8)
DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(u16)
DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(u32)
DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(u64)
DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(f32)
DZNL_DEFAULT_NUMERIC_TYPE_INTERFACE_IMPLEMENTATIONS(f64)
DZNL_DEFAULT_INV_IMPLEMENTATION(f32)
DZNL_DEFAULT_INV_IMPLEMENTATION(f64)


} // namespace dznl

#endif // DZNL_NUMERIC_TYPES_HPP_INCLUDED
