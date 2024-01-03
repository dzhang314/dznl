/*
#include <dznl/ErrorFreeTransformations.hpp>
#include <dznl/FloatingPointProperties.hpp>
#include <dznl/MathematicalFunctions.hpp>
#include <dznl/NumericTypes.hpp>
#include <dznl/RandomNumbers.hpp>


#define DZNL_WASM_EXPORT(NAME) __attribute__((export_name(NAME)))


using dznl::f32;
using dznl::f64;
using dznl::u64;


DZNL_WASM_EXPORT("min_f32") f32 min_f32(f32, f32);
DZNL_WASM_EXPORT("min_f64") f64 min_f64(f64, f64);
DZNL_WASM_EXPORT("max_f32") f32 max_f32(f32, f32);
DZNL_WASM_EXPORT("max_f64") f64 max_f64(f64, f64);
DZNL_WASM_EXPORT("round_f32") f32 round_f32(f32);
DZNL_WASM_EXPORT("round_f64") f64 round_f64(f64);
DZNL_WASM_EXPORT("ceil_f32") f32 ceil_f32(f32);
DZNL_WASM_EXPORT("ceil_f64") f64 ceil_f64(f64);
DZNL_WASM_EXPORT("floor_f32") f32 floor_f32(f32);
DZNL_WASM_EXPORT("floor_f64") f64 floor_f64(f64);
DZNL_WASM_EXPORT("trunc_f32") f32 trunc_f32(f32);
DZNL_WASM_EXPORT("trunc_f64") f64 trunc_f64(f64);
DZNL_WASM_EXPORT("abs_f32") f32 abs_f32(f32);
DZNL_WASM_EXPORT("abs_f64") f64 abs_f64(f64);
DZNL_WASM_EXPORT("sqrt_f32") f32 sqrt_f32(f32);
DZNL_WASM_EXPORT("sqrt_f64") f64 sqrt_f64(f64);
DZNL_WASM_EXPORT("copysign_f32") f32 copysign_f32(f32, f32);
DZNL_WASM_EXPORT("copysign_f64") f64 copysign_f64(f64, f64);


f32 min_f32(f32 x, f32 y) { return dznl::min(x, y); }
f64 min_f64(f64 x, f64 y) { return dznl::min(x, y); }
f32 max_f32(f32 x, f32 y) { return dznl::max(x, y); }
f64 max_f64(f64 x, f64 y) { return dznl::max(x, y); }
f32 round_f32(f32 x) { return dznl::round(x); }
f64 round_f64(f64 x) { return dznl::round(x); }
f32 ceil_f32(f32 x) { return dznl::ceil(x); }
f64 ceil_f64(f64 x) { return dznl::ceil(x); }
f32 floor_f32(f32 x) { return dznl::floor(x); }
f64 floor_f64(f64 x) { return dznl::floor(x); }
f32 trunc_f32(f32 x) { return dznl::trunc(x); }
f64 trunc_f64(f64 x) { return dznl::trunc(x); }
f32 abs_f32(f32 x) { return dznl::abs(x); }
f64 abs_f64(f64 x) { return dznl::abs(x); }
f32 sqrt_f32(f32 x) { return dznl::sqrt(x); }
f64 sqrt_f64(f64 x) { return dznl::sqrt(x); }
f32 copysign_f32(f32 x, f32 y) { return dznl::copysign(x, y); }
f64 copysign_f64(f64 x, f64 y) { return dznl::copysign(x, y); }


DZNL_WASM_EXPORT("compute_radix_f32") f32 compute_radix_f32();
DZNL_WASM_EXPORT("compute_radix_f64") f64 compute_radix_f64();
DZNL_WASM_EXPORT("compute_precision_f32") u64 compute_precision_f32();
DZNL_WASM_EXPORT("compute_precision_f64") u64 compute_precision_f64();


f32 compute_radix_f32() { return dznl::compute_radix<f32, u64>(); }
f64 compute_radix_f64() { return dznl::compute_radix<f64, u64>(); }
u64 compute_precision_f32() { return dznl::compute_precision<f32, u64>(); }
u64 compute_precision_f64() { return dznl::compute_precision<f64, u64>(); }


DZNL_WASM_EXPORT("fast_two_sum_f32")
dznl::Tuple<f32, f32> fast_two_sum_f32(f32, f32);
DZNL_WASM_EXPORT("fast_two_sum_f64")
dznl::Tuple<f64, f64> fast_two_sum_f64(f64, f64);
DZNL_WASM_EXPORT("two_sum_f32") dznl::Tuple<f32, f32> two_sum_f32(f32, f32);
DZNL_WASM_EXPORT("two_sum_f64") dznl::Tuple<f64, f64> two_sum_f64(f64, f64);
DZNL_WASM_EXPORT("two_prod_f32") dznl::Tuple<f32, f32> two_prod_f32(f32, f32);
DZNL_WASM_EXPORT("two_prod_f64") dznl::Tuple<f64, f64> two_prod_f64(f64, f64);


dznl::Tuple<f32, f32> fast_two_sum_f32(f32 a, f32 b) {
    return dznl::fast_two_sum(a, b);
}
dznl::Tuple<f64, f64> fast_two_sum_f64(f64 a, f64 b) {
    return dznl::fast_two_sum(a, b);
}
dznl::Tuple<f32, f32> two_sum_f32(f32 a, f32 b) { return dznl::two_sum(a, b); }
dznl::Tuple<f64, f64> two_sum_f64(f64 a, f64 b) { return dznl::two_sum(a, b); }
dznl::Tuple<f32, f32> two_prod_f32(f32 a, f32 b) {
    return dznl::two_prod(a, b);
}
dznl::Tuple<f64, f64> two_prod_f64(f64 a, f64 b) {
    return dznl::two_prod(a, b);
}


// DZNL_WASM_EXPORT("random_fill_f32") void random_fill_f32(
//     f32 *__restrict__ result, dznl::u32 length, dznl::u64 seed
// ) {
//     dznl::random_fill(result, length, seed);
// }


// DZNL_WASM_EXPORT("random_fill_f64") void random_fill_f64(
//     f64 *__restrict__ result, dznl::u32 length, dznl::u64 seed
// ) {
//     dznl::random_fill(result, length, seed);
// }


// DZNL_WASM_EXPORT("random_fill_sphere_f32") void
// random_fill_sphere_f32(
//     f32 *__restrict__ result, dznl::u32 num_points, dznl::u64 seed
// ) {
//     dznl::random_fill_sphere<3>(result, num_points, seed);
// }


// DZNL_WASM_EXPORT("random_fill_sphere_f64") void
// random_fill_sphere_f64(
//     f64 *__restrict__ result, dznl::u32 num_points, dznl::u64 seed
// ) {
//     dznl::random_fill_sphere<3>(result, num_points, seed);
// }
*/
