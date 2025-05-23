#include <cstdlib>

#ifndef __NVCOMPILER
#include <boost/multiprecision/cpp_bin_float.hpp>
#endif

#if (defined(__GNUC__) && (!defined(__clang__)) && (!defined(__NVCOMPILER)) && \
     (__GNUC__ >= 12)) ||                                                      \
    (defined(__clang__) &&                                                     \
     (defined(__apple_build_version__) || (__clang_major__ >= 15)))
#define DZNL_REQUEST_F16
#endif

#if (defined(__GNUC__) && (!defined(__clang__)) && (!defined(__NVCOMPILER)) && \
     (__GNUC__ >= 13)) ||                                                      \
    (defined(__clang__) &&                                                     \
     (defined(__apple_build_version__) || (__clang_major__ >= 17)))
#define DZNL_REQUEST_BF16
#endif

#if defined(__GNUC__) && (!defined(__clang__))
#define DZNL_REQUEST_128_BIT_FLOATS
#endif

#if defined(__GNUC__) && (!defined(__clang__)) && (!defined(__NVCOMPILER))
#define DZNL_REQUEST_DECIMAL_FLOATS
#endif

#include <dznl/dznl.hpp>


int main() {

    static_assert(dznl::compute_radix<dznl::f32>().second == 2);
    static_assert(dznl::compute_precision<dznl::f32>() == 24);
    static_assert(dznl::compute_radix<dznl::f64>().second == 2);
    static_assert(dznl::compute_precision<dznl::f64>() == 53);

#if (defined(__GNUC__) && (!defined(__clang__)) && (!defined(__NVCOMPILER)) && \
     (__GNUC__ >= 12)) ||                                                      \
    (defined(__clang__) &&                                                     \
     (defined(__apple_build_version__) || (__clang_major__ >= 15)))
    static_assert(dznl::compute_radix<dznl::f16>().second == 2);
    static_assert(dznl::compute_precision<dznl::f16>() == 11);
#endif

#if (defined(__GNUC__) && (!defined(__clang__)) && (!defined(__NVCOMPILER)) && \
     (__GNUC__ >= 13)) ||                                                      \
    (defined(__clang__) &&                                                     \
     (defined(__apple_build_version__) || (__clang_major__ >= 17)))
    static_assert(dznl::compute_radix<dznl::bf16>().second == 2);
    static_assert(dznl::compute_precision<dznl::bf16>() == 8);
#endif

#if defined(__GNUC__) && (!defined(__clang__))
    static_assert(dznl::compute_radix<dznl::f128>().second == 2);
    static_assert(dznl::compute_precision<dznl::f128>() == 113);
#endif

#if defined(__GNUC__) && (!defined(__clang__)) && (!defined(__NVCOMPILER))
    static_assert(dznl::compute_radix<dznl::d32>().second == 10);
    static_assert(dznl::compute_precision<dznl::d32>() == 7);
    static_assert(dznl::compute_radix<dznl::d64>().second == 10);
    static_assert(dznl::compute_precision<dznl::d64>() == 16);
    static_assert(dznl::compute_radix<dznl::d128>().second == 10);
    static_assert(dznl::compute_precision<dznl::d128>() == 34);
#endif

#ifndef __NVCOMPILER
    using namespace boost::multiprecision;
    // clang-format off
    if (dznl::compute_radix<cpp_bin_float_single>().second != 2) { return EXIT_FAILURE; }
    if (dznl::compute_precision<cpp_bin_float_single>() != 24) { return EXIT_FAILURE; }
    if (dznl::compute_radix<cpp_bin_float_double>().second != 2) { return EXIT_FAILURE; }
    if (dznl::compute_precision<cpp_bin_float_double>() != 53) { return EXIT_FAILURE; }
    if (dznl::compute_radix<cpp_bin_float_double_extended>().second != 2) { return EXIT_FAILURE; }
    if (dznl::compute_precision<cpp_bin_float_double_extended>() != 64) { return EXIT_FAILURE; }
    if (dznl::compute_radix<cpp_bin_float_quad>().second != 2) { return EXIT_FAILURE; }
    if (dznl::compute_precision<cpp_bin_float_quad>() != 113) { return EXIT_FAILURE; }
    if (dznl::compute_radix<cpp_bin_float_oct>().second != 2) { return EXIT_FAILURE; }
    if (dznl::compute_precision<cpp_bin_float_oct>() != 237) { return EXIT_FAILURE; }
    if (dznl::compute_radix<cpp_bin_float_50>().second != 2) { return EXIT_FAILURE; }
    if (dznl::compute_precision<cpp_bin_float_50>() != 168) { return EXIT_FAILURE; }
    if (dznl::compute_radix<cpp_bin_float_100>().second != 2) { return EXIT_FAILURE; }
    if (dznl::compute_precision<cpp_bin_float_100>() != 334) { return EXIT_FAILURE; }
    // clang-format on
#endif

    return EXIT_SUCCESS;
}
