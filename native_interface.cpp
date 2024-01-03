#include <dznl/FloatingPointProperties.hpp>
#include <dznl/NumericTypes.hpp>


// dznl::f32 min_f32(dznl::f32, dznl::f32);
// dznl::f64 min_f64(dznl::f64, dznl::f64);
// dznl::f32 min_f32(dznl::f32 x, dznl::f32 y) { return dznl::min(x, y); }
// dznl::f64 min_f64(dznl::f64 x, dznl::f64 y) { return dznl::min(x, y); }


// dznl::f32 max_f32(dznl::f32, dznl::f32);
// dznl::f64 max_f64(dznl::f64, dznl::f64);
// dznl::f32 max_f32(dznl::f32 x, dznl::f32 y) { return dznl::max(x, y); }
// dznl::f64 max_f64(dznl::f64 x, dznl::f64 y) { return dznl::max(x, y); }


// dznl::f32 round_f32(dznl::f32);
// dznl::f64 round_f64(dznl::f64);
// dznl::f32 round_f32(dznl::f32 x) { return dznl::round(x); }
// dznl::f64 round_f64(dznl::f64 x) { return dznl::round(x); }


// dznl::f32 ceil_f32(dznl::f32);
// dznl::f64 ceil_f64(dznl::f64);
// dznl::f32 ceil_f32(dznl::f32 x) { return dznl::ceil(x); }
// dznl::f64 ceil_f64(dznl::f64 x) { return dznl::ceil(x); }


// dznl::f32 floor_f32(dznl::f32);
// dznl::f64 floor_f64(dznl::f64);
// dznl::f32 floor_f32(dznl::f32 x) { return dznl::floor(x); }
// dznl::f64 floor_f64(dznl::f64 x) { return dznl::floor(x); }


// dznl::f32 trunc_f32(dznl::f32);
// dznl::f64 trunc_f64(dznl::f64);
// dznl::f32 trunc_f32(dznl::f32 x) { return dznl::trunc(x); }
// dznl::f64 trunc_f64(dznl::f64 x) { return dznl::trunc(x); }


// dznl::f32 abs_f32(dznl::f32);
// dznl::f64 abs_f64(dznl::f64);
// dznl::f32 abs_f32(dznl::f32 x) { return dznl::abs(x); }
// dznl::f64 abs_f64(dznl::f64 x) { return dznl::abs(x); }


// dznl::f32 sqrt_f32(dznl::f32);
// dznl::f64 sqrt_f64(dznl::f64);
// dznl::f32 sqrt_f32(dznl::f32 x) { return dznl::sqrt(x); }
// dznl::f64 sqrt_f64(dznl::f64 x) { return dznl::sqrt(x); }


// dznl::f32 copysign_f32(dznl::f32, dznl::f32);
// dznl::f64 copysign_f64(dznl::f64, dznl::f64);
// dznl::f32 copysign_f32(dznl::f32 x, dznl::f32 y) {
//     return dznl::copysign(x, y);
// }
// dznl::f64 copysign_f64(dznl::f64 x, dznl::f64 y) {
//     return dznl::copysign(x, y);
// }


dznl::f32 compute_float_radix_f32();
dznl::f64 compute_float_radix_f64();
dznl::f32 compute_float_radix_f32() {
    return dznl::compute_float_radix<dznl::f32, int>().first;
}
dznl::f64 compute_float_radix_f64() {
    return dznl::compute_float_radix<dznl::f64, int>().first;
}


dznl::f32 compute_float_precision_f32();
dznl::f64 compute_float_precision_f64();
dznl::f32 compute_float_precision_f32() {
    return dznl::compute_float_precision<dznl::f32, int>();
}
dznl::f64 compute_precision_f64() {
    return dznl::compute_float_precision<dznl::f64, int>();
}
