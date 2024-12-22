#include <cstdlib>
#include <string>

#ifndef _MSC_VER
#define DZNL_REQUEST_16_BIT_FLOATS
#endif // _MSC_VER

#if defined(__GNUC__) && !defined(__clang__)
#define DZNL_REQUEST_128_BIT_FLOATS
#endif // defined(__GNUC__) && !defined(__clang__)

#define DZNL_REQUEST_FLOAT_TO_STRING

#include <dznl/dznl.hpp>


template <typename FLOAT_T>
bool test_to_string() {

    bool result = true;

    {
        constexpr FLOAT_T a = static_cast<FLOAT_T>(3);
        constexpr FLOAT_T b = static_cast<FLOAT_T>(10);
        constexpr FLOAT_T c = a / b;
        result &= (dznl::to_string(c) == "0.3");
    }

    {
        constexpr FLOAT_T a = static_cast<FLOAT_T>(-3);
        constexpr FLOAT_T b = static_cast<FLOAT_T>(10);
        constexpr FLOAT_T c = a / b;
        result &= (dznl::to_string(c) == "-0.3");
    }

    {
        constexpr FLOAT_T a = static_cast<FLOAT_T>(3);
        constexpr FLOAT_T b = static_cast<FLOAT_T>(10);
        constexpr FLOAT_T c = a / b;
        result &= (dznl::to_string(c, true) == "+0.3");
    }

    {
        constexpr FLOAT_T a = static_cast<FLOAT_T>(40);
        constexpr FLOAT_T b = static_cast<FLOAT_T>(25);
        constexpr FLOAT_T c = a / b;
        result &= (dznl::to_string(c) == "1.6");
    }

    {
        constexpr FLOAT_T a = static_cast<FLOAT_T>(-50);
        constexpr FLOAT_T b = static_cast<FLOAT_T>(50);
        constexpr FLOAT_T c = a * b;
        result &= (dznl::to_string(c) == "-2.5e3");
    }

    return result;
}


int main() {

    if (!test_to_string<dznl::f32>()) { return EXIT_FAILURE; }
    if (!test_to_string<dznl::f64>()) { return EXIT_FAILURE; }

#ifndef _MSC_VER
    if (!test_to_string<dznl::f16>()) { return EXIT_FAILURE; }
    if (!test_to_string<dznl::bf16>()) { return EXIT_FAILURE; }
#endif // _MSC_VER

#if defined(__GNUC__) && !defined(__clang__)
    if (!test_to_string<dznl::f128>()) { return EXIT_FAILURE; }
#endif // defined(__GNUC__) && !defined(__clang__)

    return EXIT_SUCCESS;
}
