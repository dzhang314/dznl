#include "FloatingPoint.hpp"
#include "Random.hpp"
#include "Types.hpp"


__attribute__((export_name("compute_f32_radix"))) dznl::f32
compute_f32_radix() {
    return dznl::compute_radix<dznl::f32, dznl::u32>();
}


__attribute__((export_name("compute_f64_radix"))) dznl::f64
compute_f64_radix() {
    return dznl::compute_radix<dznl::f64, dznl::u32>();
}


__attribute__((export_name("compute_f32_precision"))) dznl::u32
compute_f32_precision() {
    return dznl::compute_precision<dznl::f32, dznl::u32>();
}


__attribute__((export_name("compute_f64_precision"))) dznl::u32
compute_f64_precision() {
    return dznl::compute_precision<dznl::f64, dznl::u32>();
}


__attribute__((export_name("random_fill_f32"))) void
random_fill_f32(dznl::f32 *__restrict__ result, dznl::u32 length,
                dznl::u64 seed) {
    dznl::random_fill(result, length, seed);
}


__attribute__((export_name("random_fill_f64"))) void
random_fill_f64(dznl::f64 *__restrict__ result, dznl::u32 length,
                dznl::u64 seed) {
    dznl::random_fill(result, length, seed);
}


__attribute__((export_name("random_fill_sphere_f32"))) void
random_fill_sphere_f32(dznl::f32 *__restrict__ result, dznl::u32 num_points,
                       dznl::u64 seed) {
    dznl::random_fill_sphere<3>(result, num_points, seed);
}


__attribute__((export_name("random_fill_sphere_f64"))) void
random_fill_sphere_f64(dznl::f64 *__restrict__ result, dznl::u32 num_points,
                       dznl::u64 seed) {
    dznl::random_fill_sphere<3>(result, num_points, seed);
}
