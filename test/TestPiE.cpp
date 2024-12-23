#include <cstdlib>
#include <iostream>

#include <dznl/dznl.hpp>


template <int N>
bool test_pi_f32() {

    constexpr dznl::f32 PI_LIMBS[6] = {
        +0x1.921FB6p+001,
        -0x1.777A5Cp-024,
        -0x1.EE59DAp-049,
        +0x1.98A2E0p-076,
        +0x1.B839A2p-103,
        +0x1.481270p-129,
    };

    using f32xN = dznl::MultiFloat<dznl::f32, N>;
    const f32xN pi = dznl::compute_pi<f32xN>();

    bool result = true;
    for (int i = 0; i + 1 < N; ++i) { result &= (pi.limbs[i] == PI_LIMBS[i]); }

    std::cout << "pi f32x" << N << ": "
              << static_cast<dznl::i32>(
                     dznl::bit_cast<dznl::u32>(pi.limbs[N - 1]) -
                     dznl::bit_cast<dznl::u32>(PI_LIMBS[N - 1])
                 )
              << " ULPs (" << (pi.limbs[N - 1] - PI_LIMBS[N - 1]) << ")"
              << std::endl;

    return result;
}


template <int N>
bool test_pi_f64() {

    constexpr dznl::f64 PI_LIMBS[20] = {
        +0x1.921FB54442D18p+0001, +0x1.1A62633145C07p-0053,
        -0x1.F1976B7ED8FBCp-0109, +0x1.4CF98E804177Dp-0163,
        +0x1.31D89CD9128A5p-0217, +0x1.0F31C6809BBDFp-0275,
        +0x1.519B3CD3A431Bp-0330, +0x1.8158536F92F8Ap-0385,
        +0x1.BA7F09AB6B6A9p-0441, -0x1.EDD0DBD2544CFp-0497,
        +0x1.79FB1BD1310BAp-0552, +0x1.A637ED6B0BFF6p-0606,
        -0x1.A485FCA40908Ep-0661, -0x1.E501295D98169p-0716,
        -0x1.160DBEE83B4E0p-0770, -0x1.9B6D799AE131Cp-0826,
        +0x1.6CF70801F2E28p-0880, +0x1.63BF0598DA483p-0934,
        +0x1.871574E69A459p-0988, -0x1.5C0B6CC000000p-1048,
    };

    using f64xN = dznl::MultiFloat<dznl::f64, N>;
    const f64xN pi = dznl::compute_pi<f64xN>();

    bool result = true;
    for (int i = 0; i + 1 < N; ++i) { result &= (pi.limbs[i] == PI_LIMBS[i]); }

    std::cout << "pi f64x" << N << ": "
              << static_cast<dznl::i64>(
                     dznl::bit_cast<dznl::u64>(pi.limbs[N - 1]) -
                     dznl::bit_cast<dznl::u64>(PI_LIMBS[N - 1])
                 )
              << " ULPs (" << (pi.limbs[N - 1] - PI_LIMBS[N - 1]) << ")"
              << std::endl;

    return result;
}


template <int N>
bool test_e_f32() {

    constexpr dznl::f32 E_LIMBS[6] = {
        +0x1.5BF0A8p+001,
        +0x1.628AEEp-024,
        -0x1.AB2A82p-049,
        +0x1.C56202p-074,
        +0x1.CF4F3Cp-100,
        +0x1.D8B9C6p-126,
    };

    using f32xN = dznl::MultiFloat<dznl::f32, N>;
    const f32xN e = dznl::compute_e<f32xN>();

    bool result = true;
    for (int i = 0; i + 1 < N; ++i) { result &= (e.limbs[i] == E_LIMBS[i]); }

    std::cout << "e f32x" << N << ": "
              << static_cast<dznl::i32>(
                     dznl::bit_cast<dznl::u32>(e.limbs[N - 1]) -
                     dznl::bit_cast<dznl::u32>(E_LIMBS[N - 1])
                 )
              << " ULPs (" << (e.limbs[N - 1] - E_LIMBS[N - 1]) << ")"
              << std::endl;

    return result;
}


template <int N>
bool test_e_f64() {

    constexpr double E_LIMBS[20] = {
        +0x1.5BF0A8B145769p+0001, +0x1.4D57EE2B1013Ap-0053,
        -0x1.618713A31D3E2p-0109, +0x1.C5A6D2B53C26Dp-0163,
        -0x1.F75CDE60219B6p-0217, -0x1.88C76D93041A1p-0272,
        +0x1.2FE363630C75Ep-0326, -0x1.C25F937F544EEp-0380,
        -0x1.E852C20E12A2Ap-0434, -0x1.4D4F6DE605705p-0493,
        -0x1.F3225EF539355p-0551, -0x1.6109728625547p-0605,
        -0x1.94301506D94CFp-0659, -0x1.879C78F8CBA44p-0713,
        -0x1.D5976250C1018p-0770, +0x1.C877C56284DABp-0824,
        +0x1.E73530ACCA4F5p-0878, -0x1.F161A150FD53Ap-0932,
        +0x1.59927DB0E8845p-0989, +0x1.2976591C00000p-1043,
    };

    using f64xN = dznl::MultiFloat<dznl::f64, N>;
    const f64xN e = dznl::compute_e<f64xN>();

    bool result = true;
    for (int i = 0; i + 1 < N; ++i) { result &= (e.limbs[i] == E_LIMBS[i]); }

    std::cout << "pi f32x" << N << ": "
              << static_cast<dznl::i64>(
                     dznl::bit_cast<dznl::u64>(e.limbs[N - 1]) -
                     dznl::bit_cast<dznl::u64>(E_LIMBS[N - 1])
                 )
              << " ULPs (" << (e.limbs[N - 1] - E_LIMBS[N - 1]) << ")"
              << std::endl;

    return result;
}


int main() {

    if (!test_pi_f32<1>()) { return EXIT_FAILURE; }
    if (!test_pi_f32<2>()) { return EXIT_FAILURE; }
    if (!test_pi_f32<3>()) { return EXIT_FAILURE; }
    if (!test_pi_f32<4>()) { return EXIT_FAILURE; }
    if (!test_pi_f32<5>()) { return EXIT_FAILURE; }
    if (!test_pi_f32<6>()) { return EXIT_FAILURE; }

    if (!test_pi_f64<1>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<2>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<3>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<4>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<5>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<6>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<7>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<8>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<9>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<10>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<11>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<12>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<13>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<14>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<15>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<16>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<17>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<18>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<19>()) { return EXIT_FAILURE; }
    if (!test_pi_f64<20>()) { return EXIT_FAILURE; }

    if (!test_e_f32<1>()) { return EXIT_FAILURE; }
    if (!test_e_f32<2>()) { return EXIT_FAILURE; }
    if (!test_e_f32<3>()) { return EXIT_FAILURE; }
    if (!test_e_f32<4>()) { return EXIT_FAILURE; }
    if (!test_e_f32<5>()) { return EXIT_FAILURE; }
    if (!test_e_f32<6>()) { return EXIT_FAILURE; }

    if (!test_e_f64<1>()) { return EXIT_FAILURE; }
    if (!test_e_f64<2>()) { return EXIT_FAILURE; }
    if (!test_e_f64<3>()) { return EXIT_FAILURE; }
    if (!test_e_f64<4>()) { return EXIT_FAILURE; }
    if (!test_e_f64<5>()) { return EXIT_FAILURE; }
    if (!test_e_f64<6>()) { return EXIT_FAILURE; }
    if (!test_e_f64<7>()) { return EXIT_FAILURE; }
    if (!test_e_f64<8>()) { return EXIT_FAILURE; }
    if (!test_e_f64<9>()) { return EXIT_FAILURE; }
    if (!test_e_f64<10>()) { return EXIT_FAILURE; }
    if (!test_e_f64<11>()) { return EXIT_FAILURE; }
    if (!test_e_f64<12>()) { return EXIT_FAILURE; }
    if (!test_e_f64<13>()) { return EXIT_FAILURE; }
    if (!test_e_f64<14>()) { return EXIT_FAILURE; }
    if (!test_e_f64<15>()) { return EXIT_FAILURE; }
    if (!test_e_f64<16>()) { return EXIT_FAILURE; }
    if (!test_e_f64<17>()) { return EXIT_FAILURE; }
    if (!test_e_f64<18>()) { return EXIT_FAILURE; }
    if (!test_e_f64<19>()) { return EXIT_FAILURE; }
    if (!test_e_f64<20>()) { return EXIT_FAILURE; }

    return EXIT_SUCCESS;
}
