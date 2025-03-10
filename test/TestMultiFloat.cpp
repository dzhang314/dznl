#include <cstdlib>
#include <iostream>

#include <dznl/dznl.hpp>


template <int N>
bool test_sqrt_2_f32() {

    constexpr dznl::f32 SQRT_2_LIMBS[6] = {
        +0x1.6A09E6p+000F, +0x1.9FCEF4p-026F, -0x1.B7BA68p-051F,
        -0x1.3B2646p-078F, +0x1.4ABEA0p-103F, -0x1.C52140p-128F,
    };

    using f32xN = dznl::MultiFloat<dznl::f32, N>;
    const f32xN sqrt_2 = dznl::sqrt(f32xN(2.0f));

    bool result = true;
    for (int i = 0; i + 1 < N; ++i) {
        result &= (sqrt_2.limbs[i] == SQRT_2_LIMBS[i]);
    }

    std::cout << "sqrt(2) f32x" << N << ": "
              << static_cast<dznl::i32>(
                     dznl::bit_cast<dznl::u32>(sqrt_2.limbs[N - 1]) -
                     dznl::bit_cast<dznl::u32>(SQRT_2_LIMBS[N - 1])
                 )
              << " ULPs (" << (sqrt_2.limbs[N - 1] - SQRT_2_LIMBS[N - 1]) << ")"
              << std::endl;

    return result;
}


template <int N>
bool test_sqrt_2_f64() {

    constexpr dznl::f64 SQRT_2_LIMBS[20] = {
        +0x1.6A09E667F3BCDp+0000, -0x1.BDD3413B26456p-0054,
        +0x1.57D3E3ADEC175p-0108, +0x1.2775099DA2F59p-0164,
        +0x1.60CCE64552BF2p-0221, +0x1.821D5C5161D46p-0278,
        -0x1.C032046F8498Ep-0332, +0x1.EE950BC8738F7p-0388,
        -0x1.AC3FDBC64E103p-0442, +0x1.3B469101743A1p-0498,
        +0x1.5E3E9CA60B38Cp-0552, +0x1.1BC337BCAB1BDp-0611,
        -0x1.BBA5DEE9D6E7Dp-0665, -0x1.438DD083B1CC4p-0719,
        +0x1.B56A28E2EDFA7p-0773, +0x1.CCB2A634331F4p-0827,
        -0x1.BD9056876F83Ep-0882, -0x1.234FA22AB6BEFp-0936,
        +0x1.9040CA4A81395p-0991, -0x1.5249C0C000000p-1045,
    };

    using f64xN = dznl::MultiFloat<dznl::f64, N>;
    const f64xN sqrt_2 = dznl::sqrt(f64xN(2.0));

    bool result = true;
    for (int i = 0; i + 1 < N; ++i) {
        result &= (sqrt_2.limbs[i] == SQRT_2_LIMBS[i]);
    }

    std::cout << "sqrt(2) f64x" << N << ": "
              << static_cast<dznl::i64>(
                     dznl::bit_cast<dznl::u64>(sqrt_2.limbs[N - 1]) -
                     dznl::bit_cast<dznl::u64>(SQRT_2_LIMBS[N - 1])
                 )
              << " ULPs (" << (sqrt_2.limbs[N - 1] - SQRT_2_LIMBS[N - 1]) << ")"
              << std::endl;

    return result;
}


template <int N>
bool test_fourth_root_2_f32() {

    constexpr dznl::f32 FOURTH_ROOT_2_LIMBS[7] = {
        +0x1.306FE0p+000F, +0x1.4636E2p-025F, +0x1.4B7A36p-050F,
        -0x1.2DCE7Ep-075F, +0x1.C85EDEp-100F, +0x1.9784E6p-125F,
        +0x1.000000p-149F,
    };

    using f32xN = dznl::MultiFloat<dznl::f32, N>;
    const f32xN fourth_root_2 = dznl::sqrt(dznl::sqrt(f32xN(2.0f)));

    bool result = true;
    for (int i = 0; i + 1 < N; ++i) {
        result &= (fourth_root_2.limbs[i] == FOURTH_ROOT_2_LIMBS[i]);
    }

    std::cout << "sqrt(sqrt(2)) f32x" << N << ": "
              << static_cast<dznl::i32>(
                     dznl::bit_cast<dznl::u32>(fourth_root_2.limbs[N - 1]) -
                     dznl::bit_cast<dznl::u32>(FOURTH_ROOT_2_LIMBS[N - 1])
                 )
              << " ULPs ("
              << (fourth_root_2.limbs[N - 1] - FOURTH_ROOT_2_LIMBS[N - 1])
              << ")" << std::endl;

    return result;
}


template <int N>
bool test_fourth_root_2_f64() {

    constexpr dznl::f64 FOURTH_ROOT_2_LIMBS[20] = {
        +0x1.306FE0A31B715p+0000, +0x1.6F46AD23182E4p-0055,
        +0x1.7B7B2F09CD0D9p-0110, -0x1.60AFD0E50E934p-0164,
        -0x1.A082C224820DCp-0218, -0x1.E5963FED7ABD9p-0274,
        +0x1.3F29DC1921B78p-0328, -0x1.4D99426DFC16Bp-0382,
        -0x1.4768615F30643p-0437, +0x1.5EB7FD1156903p-0493,
        +0x1.6868A4B889C83p-0547, -0x1.DD21C4D803F86p-0601,
        +0x1.EC6BED52DF946p-0657, +0x1.A2E1A27E241F4p-0711,
        +0x1.284B29DB93DB8p-0772, +0x1.9ADE11F9E687Ep-0828,
        -0x1.AD1EA8DD82EB4p-0882, +0x1.36DEBD6E73EA3p-0937,
        -0x1.997CEEE28F144p-0991, -0x1.36C60B6000000p-1047,
    };

    using f64xN = dznl::MultiFloat<dznl::f64, N>;
    const f64xN fourth_root_2 = dznl::sqrt(dznl::sqrt(f64xN(2.0)));

    bool result = true;
    for (int i = 0; i + 1 < N; ++i) {
        result &= (fourth_root_2.limbs[i] == FOURTH_ROOT_2_LIMBS[i]);
    }

    std::cout << "sqrt(sqrt(2)) f64x" << N << ": "
              << static_cast<dznl::i64>(
                     dznl::bit_cast<dznl::u64>(fourth_root_2.limbs[N - 1]) -
                     dznl::bit_cast<dznl::u64>(FOURTH_ROOT_2_LIMBS[N - 1])
                 )
              << " ULPs ("
              << (fourth_root_2.limbs[N - 1] - FOURTH_ROOT_2_LIMBS[N - 1])
              << ")" << std::endl;

    return result;
}


template <int N>
bool test_inv_fourth_root_2_f32() {

    constexpr dznl::f32 INV_FOURTH_ROOT_2_LIMBS[6] = {
        +0x1.AE89FAp-001F, -0x1.A94B14p-027F, -0x1.50BC66p-052F,
        +0x1.A2EE64p-078F, +0x1.69FEF0p-107F, +0x1.D73380p-132F,
    };

    using f32xN = dznl::MultiFloat<dznl::f32, N>;
    const f32xN inv_fourth_root_2 = dznl::rsqrt(dznl::sqrt(f32xN(2.0f)));

    bool result = true;
    for (int i = 0; i + 1 < N; ++i) {
        result &= (inv_fourth_root_2.limbs[i] == INV_FOURTH_ROOT_2_LIMBS[i]);
    }

    std::cout << "rsqrt(sqrt(2)) f32x" << N << ": "
              << static_cast<dznl::i32>(
                     dznl::bit_cast<dznl::u32>(inv_fourth_root_2.limbs[N - 1]) -
                     dznl::bit_cast<dznl::u32>(INV_FOURTH_ROOT_2_LIMBS[N - 1])
                 )
              << " ULPs ("
              << (inv_fourth_root_2.limbs[N - 1] -
                  INV_FOURTH_ROOT_2_LIMBS[N - 1])
              << ")" << std::endl;

    return result;
}


template <int N>
bool test_inv_fourth_root_2_f64() {

    constexpr dznl::f64 INV_FOURTH_ROOT_2_LIMBS[20] = {
        +0x1.AE89F995AD3ADp-0001, +0x1.7A1CD345DCC81p-0055,
        +0x1.A7FBC3AE675EAp-0109, +0x1.102C58B5AE09Dp-0163,
        +0x1.B41CEF0533DF6p-0217, +0x1.FDA334BCA9A81p-0276,
        +0x1.23A2C7DB0F2BBp-0331, +0x1.C6C15E91EB1B3p-0386,
        +0x1.083FEEC2C4B5Fp-0441, +0x1.01ABE5769650Ap-0495,
        -0x1.CF82902D196E8p-0550, +0x1.F091F5D490F3Cp-0605,
        -0x1.DE65197045E82p-0660, +0x1.10B9F19227482p-0714,
        +0x1.8D61F8DAED297p-0768, +0x1.B8A9A38E50AB6p-0825,
        +0x1.5FA511C50364Ep-0879, -0x1.72D5F5EA6D7D5p-0933,
        +0x1.CFC383A4997D5p-0987, +0x1.FCE6886400000p-1044,
    };

    using f64xN = dznl::MultiFloat<dznl::f64, N>;
    const f64xN inv_fourth_root_2 = dznl::rsqrt(dznl::sqrt(f64xN(2.0)));

    bool result = true;
    for (int i = 0; i + 1 < N; ++i) {
        result &= (inv_fourth_root_2.limbs[i] == INV_FOURTH_ROOT_2_LIMBS[i]);
    }

    std::cout << "rsqrt(sqrt(2)) f64x" << N << ": "
              << static_cast<dznl::i64>(
                     dznl::bit_cast<dznl::u64>(inv_fourth_root_2.limbs[N - 1]) -
                     dznl::bit_cast<dznl::u64>(INV_FOURTH_ROOT_2_LIMBS[N - 1])
                 )
              << " ULPs ("
              << (inv_fourth_root_2.limbs[N - 1] -
                  INV_FOURTH_ROOT_2_LIMBS[N - 1])
              << ")" << std::endl;

    return result;
}


template <int N>
bool test_pi_f32() {

    constexpr dznl::f32 PI_LIMBS[6] = {
        +0x1.921FB6p+001F, -0x1.777A5Cp-024F, -0x1.EE59DAp-049F,
        +0x1.98A2E0p-076F, +0x1.B839A2p-103F, +0x1.481270p-129F,
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
        +0x1.5BF0A8p+001F, +0x1.628AEEp-024F, -0x1.AB2A82p-049F,
        +0x1.C56202p-074F, +0x1.CF4F3Cp-100F, +0x1.D8B9C6p-126F,
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

    std::cout << "e f64x" << N << ": "
              << static_cast<dznl::i64>(
                     dznl::bit_cast<dznl::u64>(e.limbs[N - 1]) -
                     dznl::bit_cast<dznl::u64>(E_LIMBS[N - 1])
                 )
              << " ULPs (" << (e.limbs[N - 1] - E_LIMBS[N - 1]) << ")"
              << std::endl;

    return result;
}


int main() {

    if (!test_sqrt_2_f32<1>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f32<2>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f32<3>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f32<4>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f32<5>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f32<6>()) { return EXIT_FAILURE; }

    if (!test_sqrt_2_f64<1>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<2>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<3>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<4>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<5>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<6>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<7>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<8>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<9>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<10>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<11>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<12>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<13>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<14>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<15>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<16>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<17>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<18>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<19>()) { return EXIT_FAILURE; }
    if (!test_sqrt_2_f64<20>()) { return EXIT_FAILURE; }

    if (!test_fourth_root_2_f32<1>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f32<2>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f32<3>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f32<4>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f32<5>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f32<6>()) { return EXIT_FAILURE; }

    if (!test_fourth_root_2_f64<1>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<2>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<3>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<4>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<5>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<6>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<7>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<8>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<9>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<10>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<11>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<12>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<13>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<14>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<15>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<16>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<17>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<18>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<19>()) { return EXIT_FAILURE; }
    if (!test_fourth_root_2_f64<20>()) { return EXIT_FAILURE; }

    if (!test_inv_fourth_root_2_f32<1>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f32<2>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f32<3>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f32<4>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f32<5>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f32<6>()) { return EXIT_FAILURE; }

    if (!test_inv_fourth_root_2_f64<1>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<2>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<3>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<4>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<5>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<6>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<7>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<8>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<9>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<10>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<11>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<12>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<13>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<14>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<15>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<16>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<17>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<18>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<19>()) { return EXIT_FAILURE; }
    if (!test_inv_fourth_root_2_f64<20>()) { return EXIT_FAILURE; }

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
