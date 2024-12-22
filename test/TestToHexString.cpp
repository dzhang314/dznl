#include <dznl/dznl.hpp>


int main() {
    static_assert(dznl::to_hex_string(dznl::zero<dznl::u8>()) == "0x00");
    static_assert(dznl::to_hex_string(dznl::one<dznl::u8>()) == "0x01");

    static_assert(dznl::to_hex_string(dznl::zero<dznl::u16>()) == "0x0000");
    static_assert(dznl::to_hex_string(dznl::one<dznl::u16>()) == "0x0001");

    static_assert(dznl::to_hex_string(dznl::zero<dznl::u32>()) == "0x00000000");
    static_assert(dznl::to_hex_string(dznl::one<dznl::u32>()) == "0x00000001");

    static_assert(
        dznl::to_hex_string(dznl::zero<dznl::u64>()) == "0x0000000000000000"
    );
    static_assert(
        dznl::to_hex_string(dznl::one<dznl::u64>()) == "0x0000000000000001"
    );

    static_assert(dznl::to_hex_string(1.0) == "+0x1.0000000000000p+0000");
    static_assert(dznl::to_hex_string(1.5) == "+0x1.8000000000000p+0000");
    static_assert(dznl::to_hex_string(1.75) == "+0x1.C000000000000p+0000");
    static_assert(dznl::to_hex_string(-100.0) == "-0x1.9000000000000p+0006");
    static_assert(dznl::to_hex_string(273.15) == "+0x1.1126666666666p+0008");
    static_assert(dznl::to_hex_string(0.0001) == "+0x1.A36E2EB1C432Dp-0014");
}
