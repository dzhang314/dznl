#include <iostream>

#define DZNL_REQUEST_16_BIT_FLOATS
#if defined(__GNUC__) && !defined(__clang__)
#define DZNL_REQUEST_128_BIT_FLOATS
#endif // defined(__GNUC__) && !defined(__clang__)
#define DZNL_REQUEST_FLOAT_TO_STRING
#define DZNL_REQUEST_BOOST_MULTIPRECISION_INTEROP
#include <dznl/dznl.hpp>

#include <boost/multiprecision/cpp_bin_float.hpp>


int main() {

    constexpr dznl::f16 pi_f16 = dznl::compute_pi<dznl::f16>();
    constexpr dznl::bf16 pi_bf16 = dznl::compute_pi<dznl::bf16>();
    constexpr dznl::f32 pi_f32 = dznl::compute_pi<dznl::f32>();
    constexpr dznl::f64 pi_f64 = dznl::compute_pi<dznl::f64>();
#if defined(__GNUC__) && !defined(__clang__)
    constexpr dznl::f128 pi_f128 = dznl::compute_pi<dznl::f128>();
#endif // defined(__GNUC__) && !defined(__clang__)

    std::cout << dznl::to_string(pi_f16) << std::endl;
    std::cout << dznl::to_string(pi_bf16) << std::endl;
    std::cout << dznl::to_string(pi_f32) << std::endl;
    std::cout << dznl::to_string(pi_f64) << std::endl;
#if defined(__GNUC__) && !defined(__clang__)
    std::cout << dznl::to_string(pi_f128) << std::endl;
#endif // defined(__GNUC__) && !defined(__clang__)

    constexpr dznl::f16 e_f16 = dznl::compute_e<dznl::f16>();
    constexpr dznl::bf16 e_bf16 = dznl::compute_e<dznl::bf16>();
    constexpr dznl::f32 e_f32 = dznl::compute_e<dznl::f32>();
    constexpr dznl::f64 e_f64 = dznl::compute_e<dznl::f64>();
#if defined(__GNUC__) && !defined(__clang__)
    constexpr dznl::f128 e_f128 = dznl::compute_e<dznl::f128>();
#endif // defined(__GNUC__) && !defined(__clang__)

    std::cout << dznl::to_string(e_f16) << std::endl;
    std::cout << dznl::to_string(e_bf16) << std::endl;
    std::cout << dznl::to_string(e_f32) << std::endl;
    std::cout << dznl::to_string(e_f64) << std::endl;
#if defined(__GNUC__) && !defined(__clang__)
    std::cout << dznl::to_string(e_f128) << std::endl;
#endif // defined(__GNUC__) && !defined(__clang__)

    using namespace boost::multiprecision;

    const cpp_bin_float_single pi_single =
        dznl::compute_pi<cpp_bin_float_single>();
    const cpp_bin_float_double pi_double =
        dznl::compute_pi<cpp_bin_float_double>();
    const cpp_bin_float_double_extended pi_extended =
        dznl::compute_pi<cpp_bin_float_double_extended>();
    const cpp_bin_float_quad pi_quad = dznl::compute_pi<cpp_bin_float_quad>();
    const cpp_bin_float_oct pi_oct = dznl::compute_pi<cpp_bin_float_oct>();
    const cpp_bin_float_50 pi_50 = dznl::compute_pi<cpp_bin_float_50>();
    const cpp_bin_float_100 pi_100 = dznl::compute_pi<cpp_bin_float_100>();

    std::cout << dznl::to_string(pi_single) << std::endl;
    std::cout << dznl::to_string(pi_double) << std::endl;
    std::cout << dznl::to_string(pi_extended) << std::endl;
    std::cout << dznl::to_string(pi_quad) << std::endl;
    std::cout << dznl::to_string(pi_oct) << std::endl;
    std::cout << dznl::to_string(pi_50) << std::endl;
    std::cout << dznl::to_string(pi_100) << std::endl;

    const cpp_bin_float_single e_single =
        dznl::compute_e<cpp_bin_float_single>();
    const cpp_bin_float_double e_double =
        dznl::compute_e<cpp_bin_float_double>();
    const cpp_bin_float_double_extended e_extended =
        dznl::compute_e<cpp_bin_float_double_extended>();
    const cpp_bin_float_quad e_quad = dznl::compute_e<cpp_bin_float_quad>();
    const cpp_bin_float_oct e_oct = dznl::compute_e<cpp_bin_float_oct>();
    const cpp_bin_float_50 e_50 = dznl::compute_e<cpp_bin_float_50>();
    const cpp_bin_float_100 e_100 = dznl::compute_e<cpp_bin_float_100>();

    std::cout << dznl::to_string(e_single) << std::endl;
    std::cout << dznl::to_string(e_double) << std::endl;
    std::cout << dznl::to_string(e_extended) << std::endl;
    std::cout << dznl::to_string(e_quad) << std::endl;
    std::cout << dznl::to_string(e_oct) << std::endl;
    std::cout << dznl::to_string(e_50) << std::endl;
    std::cout << dznl::to_string(e_100) << std::endl;
}
