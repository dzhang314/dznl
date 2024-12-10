#include <cstdlib>

#include <boost/multiprecision/cpp_bin_float.hpp>

#if defined(__GNUC__) && !defined(__clang__)
#define DZNL_REQUEST_DECIMAL_FLOATS
#endif // defined(__GNUC__) && !defined(__clang__)
#include <dznl/dznl.hpp>

int main() {

    static_assert(dznl::compute_radix<dznl::f32>() == 2);
    static_assert(dznl::compute_precision<dznl::f32>() == 24);
    static_assert(dznl::compute_radix<dznl::f64>() == 2);
    static_assert(dznl::compute_precision<dznl::f64>() == 53);

#if defined(__GNUC__) && !defined(__clang__)
    static_assert(dznl::compute_radix<dznl::d32>() == 10);
    static_assert(dznl::compute_precision<dznl::d32>() == 7);
    static_assert(dznl::compute_radix<dznl::d64>() == 10);
    static_assert(dznl::compute_precision<dznl::d64>() == 16);
    static_assert(dznl::compute_radix<dznl::d128>() == 10);
    static_assert(dznl::compute_precision<dznl::d128>() == 34);
#endif // defined(__GNUC__) && !defined(__clang__)

    using namespace boost::multiprecision;

    // clang-format off
    if (dznl::compute_radix<cpp_bin_float_single>() != 2) { return EXIT_FAILURE; }
    if (dznl::compute_precision<cpp_bin_float_single>() != 24) { return EXIT_FAILURE; }
    if (dznl::compute_radix<cpp_bin_float_double>() != 2) { return EXIT_FAILURE; }
    if (dznl::compute_precision<cpp_bin_float_double>() != 53) { return EXIT_FAILURE; }
    if (dznl::compute_radix<cpp_bin_float_double_extended>() != 2) { return EXIT_FAILURE; }
    if (dznl::compute_precision<cpp_bin_float_double_extended>() != 64) { return EXIT_FAILURE; }
    if (dznl::compute_radix<cpp_bin_float_quad>() != 2) { return EXIT_FAILURE; }
    if (dznl::compute_precision<cpp_bin_float_quad>() != 113) { return EXIT_FAILURE; }
    if (dznl::compute_radix<cpp_bin_float_oct>() != 2) { return EXIT_FAILURE; }
    if (dznl::compute_precision<cpp_bin_float_oct>() != 237) { return EXIT_FAILURE; }
    if (dznl::compute_radix<cpp_bin_float_50>() != 2) { return EXIT_FAILURE; }
    if (dznl::compute_precision<cpp_bin_float_50>() != 168) { return EXIT_FAILURE; }
    if (dznl::compute_radix<cpp_bin_float_100>() != 2) { return EXIT_FAILURE; }
    if (dznl::compute_precision<cpp_bin_float_100>() != 334) { return EXIT_FAILURE; }
    // clang-format on
}
