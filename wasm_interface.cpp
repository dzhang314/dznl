#include "FloatingPoint.hpp"
#include "Types.hpp"


__attribute__((export_name("compute_float_radix"))) dznl::f32
compute_float_radix() {
    return dznl::compute_radix<dznl::f32, dznl::u32>();
}


__attribute__((export_name("compute_double_radix"))) dznl::f64
compute_double_radix() {
    return dznl::compute_radix<dznl::f64, dznl::u32>();
}


__attribute__((export_name("compute_float_precision"))) dznl::u32
compute_float_precision() {
    return dznl::compute_precision<dznl::f32, dznl::u32>();
}


__attribute__((export_name("compute_double_precision"))) dznl::u32
compute_double_precision() {
    return dznl::compute_precision<dznl::f64, dznl::u32>();
}


__attribute__((export_name("random_fill"))) void
random_fill(double *__restrict__ result, unsigned int length,
            unsigned long long seed) {
    constexpr unsigned long long multiplier = 6364136223846793005ULL;
    constexpr unsigned long long increment = 1442695040888963407ULL;
    constexpr double denominator = 18446744073709551616.0;
    unsigned long long value = seed;
    for (unsigned int i = 0; i < length; ++i) {
        value *= multiplier;
        value += increment;
        result[i] = static_cast<double>(value) / denominator;
    }
}
