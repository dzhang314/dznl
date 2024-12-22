#include <cstdlib>

#include <boost/multiprecision/cpp_bin_float.hpp>

#ifndef _MSC_VER
#define DZNL_REQUEST_16_BIT_FLOATS
#endif // _MSC_VER

#if defined(__GNUC__) && !defined(__clang__)
#define DZNL_REQUEST_128_BIT_FLOATS
#define DZNL_REQUEST_DECIMAL_FLOATS
#endif // defined(__GNUC__) && !defined(__clang__)

#include <dznl/dznl.hpp>

int main() {

    static_assert(dznl::compute_radix<dznl::f32>().second == 2);
    static_assert(dznl::compute_precision<dznl::f32>() == 24);
    static_assert(dznl::compute_radix<dznl::f64>().second == 2);
    static_assert(dznl::compute_precision<dznl::f64>() == 53);

#ifndef _MSC_VER
    static_assert(dznl::compute_radix<dznl::f16>().second == 2);
    static_assert(dznl::compute_precision<dznl::f16>() == 11);
    static_assert(dznl::compute_radix<dznl::bf16>().second == 2);
    static_assert(dznl::compute_precision<dznl::bf16>() == 8);
#endif // _MSC_VER

#if defined(__GNUC__) && !defined(__clang__)
    static_assert(dznl::compute_radix<dznl::f128>().second == 2);
    static_assert(dznl::compute_precision<dznl::f128>() == 113);
    static_assert(dznl::compute_radix<dznl::d32>().second == 10);
    static_assert(dznl::compute_precision<dznl::d32>() == 7);
    static_assert(dznl::compute_radix<dznl::d64>().second == 10);
    static_assert(dznl::compute_precision<dznl::d64>() == 16);
    static_assert(dznl::compute_radix<dznl::d128>().second == 10);
    static_assert(dznl::compute_precision<dznl::d128>() == 34);
#endif // defined(__GNUC__) && !defined(__clang__)

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

    return EXIT_SUCCESS;
}
