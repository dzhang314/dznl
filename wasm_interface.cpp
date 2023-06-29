#include "MathematicalFunctions.hpp"


__attribute__((export_name("min_f32"))) dznl::f32 min_f32(dznl::f32, dznl::f32);
__attribute__((export_name("min_f64"))) dznl::f64 min_f64(dznl::f64, dznl::f64);
dznl::f32 min_f32(dznl::f32 x, dznl::f32 y) { return dznl::min(x, y); }
dznl::f64 min_f64(dznl::f64 x, dznl::f64 y) { return dznl::min(x, y); }


__attribute__((export_name("max_f32"))) dznl::f32 max_f32(dznl::f32, dznl::f32);
__attribute__((export_name("max_f64"))) dznl::f64 max_f64(dznl::f64, dznl::f64);
dznl::f32 max_f32(dznl::f32 x, dznl::f32 y) { return dznl::max(x, y); }
dznl::f64 max_f64(dznl::f64 x, dznl::f64 y) { return dznl::max(x, y); }


__attribute__((export_name("round_f32"))) dznl::f32 round_f32(dznl::f32);
__attribute__((export_name("round_f64"))) dznl::f64 round_f64(dznl::f64);
dznl::f32 round_f32(dznl::f32 x) { return dznl::round(x); }
dznl::f64 round_f64(dznl::f64 x) { return dznl::round(x); }


__attribute__((export_name("ceil_f32"))) dznl::f32 ceil_f32(dznl::f32);
__attribute__((export_name("ceil_f64"))) dznl::f64 ceil_f64(dznl::f64);
dznl::f32 ceil_f32(dznl::f32 x) { return dznl::ceil(x); }
dznl::f64 ceil_f64(dznl::f64 x) { return dznl::ceil(x); }


__attribute__((export_name("floor_f32"))) dznl::f32 floor_f32(dznl::f32);
__attribute__((export_name("floor_f64"))) dznl::f64 floor_f64(dznl::f64);
dznl::f32 floor_f32(dznl::f32 x) { return dznl::floor(x); }
dznl::f64 floor_f64(dznl::f64 x) { return dznl::floor(x); }


__attribute__((export_name("trunc_f32"))) dznl::f32 trunc_f32(dznl::f32);
__attribute__((export_name("trunc_f64"))) dznl::f64 trunc_f64(dznl::f64);
dznl::f32 trunc_f32(dznl::f32 x) { return dznl::trunc(x); }
dznl::f64 trunc_f64(dznl::f64 x) { return dznl::trunc(x); }


__attribute__((export_name("abs_f32"))) dznl::f32 abs_f32(dznl::f32);
__attribute__((export_name("abs_f64"))) dznl::f64 abs_f64(dznl::f64);
dznl::f32 abs_f32(dznl::f32 x) { return dznl::abs(x); }
dznl::f64 abs_f64(dznl::f64 x) { return dznl::abs(x); }


__attribute__((export_name("sqrt_f32"))) dznl::f32 sqrt_f32(dznl::f32);
__attribute__((export_name("sqrt_f64"))) dznl::f64 sqrt_f64(dznl::f64);
dznl::f32 sqrt_f32(dznl::f32 x) { return dznl::sqrt(x); }
dznl::f64 sqrt_f64(dznl::f64 x) { return dznl::sqrt(x); }


__attribute__((export_name("copysign_f32")))
dznl::f32 copysign_f32(dznl::f32, dznl::f32);
__attribute__((export_name("copysign_f64")))
dznl::f64 copysign_f64(dznl::f64, dznl::f64);
dznl::f32 copysign_f32(dznl::f32 x, dznl::f32 y) {
    return dznl::copysign(x, y);
}
dznl::f64 copysign_f64(dznl::f64 x, dznl::f64 y) {
    return dznl::copysign(x, y);
}


// __attribute__((export_name("compute_f32_radix"))) dznl::f32
// compute_f32_radix() {
//     return dznl::compute_radix<dznl::f32, dznl::u32>();
// }


// __attribute__((export_name("compute_f64_radix"))) dznl::f64
// compute_f64_radix() {
//     return dznl::compute_radix<dznl::f64, dznl::u32>();
// }


// __attribute__((export_name("compute_f32_precision"))) dznl::u32
// compute_f32_precision() {
//     return dznl::compute_precision<dznl::f32, dznl::u32>();
// }


// __attribute__((export_name("compute_f64_precision"))) dznl::u32
// compute_f64_precision() {
//     return dznl::compute_precision<dznl::f64, dznl::u32>();
// }


// __attribute__((export_name("fast_two_sum_f32")))
// dznl::Pair<dznl::f32, dznl::f32>
// fast_two_sum_f32(dznl::f32 a, dznl::f32 b) {
//     return dznl::fast_two_sum(a, b);
// }


// __attribute__((export_name("fast_two_sum_f64")))
// dznl::Pair<dznl::f64, dznl::f64>
// fast_two_sum_f64(dznl::f64 a, dznl::f64 b) {
//     return dznl::fast_two_sum(a, b);
// }


// __attribute__((export_name("two_sum_f32"))) dznl::Pair<dznl::f32, dznl::f32>
// two_sum_f32(dznl::f32 a, dznl::f32 b) {
//     return dznl::two_sum(a, b);
// }


// __attribute__((export_name("two_sum_f64"))) dznl::Pair<dznl::f64, dznl::f64>
// two_sum_f64(dznl::f64 a, dznl::f64 b) {
//     return dznl::two_sum(a, b);
// }


// __attribute__((export_name("two_prod_f32"))) dznl::Pair<dznl::f32, dznl::f32>
// two_prod_f32(dznl::f32 a, dznl::f32 b) {
//     return dznl::two_prod(a, b);
// }


// __attribute__((export_name("two_prod_f64"))) dznl::Pair<dznl::f64, dznl::f64>
// two_prod_f64(dznl::f64 a, dznl::f64 b) {
//     return dznl::two_prod(a, b);
// }


// __attribute__((export_name("random_fill_f32"))) void random_fill_f32(
//     dznl::f32 *__restrict__ result, dznl::u32 length, dznl::u64 seed
// ) {
//     dznl::random_fill(result, length, seed);
// }


// __attribute__((export_name("random_fill_f64"))) void random_fill_f64(
//     dznl::f64 *__restrict__ result, dznl::u32 length, dznl::u64 seed
// ) {
//     dznl::random_fill(result, length, seed);
// }


// __attribute__((export_name("random_fill_sphere_f32"))) void
// random_fill_sphere_f32(
//     dznl::f32 *__restrict__ result, dznl::u32 num_points, dznl::u64 seed
// ) {
//     dznl::random_fill_sphere<3>(result, num_points, seed);
// }


// __attribute__((export_name("random_fill_sphere_f64"))) void
// random_fill_sphere_f64(
//     dznl::f64 *__restrict__ result, dznl::u32 num_points, dznl::u64 seed
// ) {
//     dznl::random_fill_sphere<3>(result, num_points, seed);
// }
