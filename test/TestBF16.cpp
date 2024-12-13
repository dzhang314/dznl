#define DZNL_REQUEST_BF16
#include <dznl/dznl.hpp>


int main() {
    constexpr dznl::bf16 zero = dznl::zero<dznl::bf16>();
    constexpr dznl::bf16 one = dznl::one<dznl::bf16>();
    constexpr dznl::bf16 two = one + one;
    return !((zero * two == zero) && (one * two == two) && (two - two == zero));
}
