import time
import z3


PRECISION: int = 53
ZERO_EXPONENT: int = -1


class FPVariable(object):

    def __init__(self, solver: z3.Solver, name: str):
        self.name: str = name

        # We explicitly model five attributes of a floating-point number:
        # (1) the sign bit;
        # (2) the exponent;
        # (3) the number of leading zero bits in the mantissa;
        # (4) the number of leading one bits in the mantissa; and
        # (5) the index of the last nonzero bit in the mantissa.
        self.sign_bit: z3.BoolRef = z3.Bool(name + "_sign_bit")
        self.exponent: z3.ArithRef = z3.Int(name + "_exponent")
        self.num_leading_zeroes: z3.ArithRef = z3.Int(name + "_num_leading_zeroes")
        self.num_leading_ones: z3.ArithRef = z3.Int(name + "_num_leading_ones")
        self.last_nonzero_bit: z3.ArithRef = z3.Int(name + "_last_nonzero_bit")

        e = self.exponent
        z = self.num_leading_zeroes
        o = self.num_leading_ones
        n = self.last_nonzero_bit

        solver.add(z >= 0)  # G-LBZ
        solver.add(z < PRECISION)  # G-UBZ
        solver.add(o >= 0)  # G-LBO
        solver.add(o < PRECISION)  # G-UBO
        solver.add(n >= 0)  # G-LBN
        solver.add(n < PRECISION)  # G-UBN
        solver.add(z3.Xor(z == 0, o == 0))  # G-RZO
        solver.add(z3.Implies(z < PRECISION - 1, z < n))  # G-RZN-G
        solver.add(z3.Implies(z == PRECISION - 1, n == 0))  # G-RZN-S
        solver.add(o <= n)  # G-RON

        # We model a hypothetical floating-point datatype with infinite
        # exponent range, eliminating the possibility of overflow or underflow.
        # This means that all results proven in this model assume that no
        # overflow or underflow occurs when performing the actual computation.

        # When analyzing floating-point addition and subtraction circuits, only
        # relative values of the exponents matter, not absolute values. This
        # means we can arbitrarily set the zero point anywhere without loss of
        # generality. In this model, we consider 0.0 to have exponent -1 and
        # assume all nonzero floating-point numbers have nonnegative exponents.
        solver.add(e >= ZERO_EXPONENT)

        # We do not consider infinities or NaNs in this model, so all
        # floating-point numbers are either positive, negative, or zero.
        self.is_zero: z3.BoolRef = e == ZERO_EXPONENT
        self.is_positive: z3.BoolRef = z3.And(e > ZERO_EXPONENT, z3.Not(self.sign_bit))
        self.is_negative: z3.BoolRef = z3.And(e > ZERO_EXPONENT, self.sign_bit)
        solver.add(z3.Implies(self.is_zero, z == PRECISION - 1))
        solver.add(z3.Implies(self.is_zero, o == 0))
        solver.add(z3.Implies(self.is_zero, n == 0))

    def maybe_equal(self, other: "FPVariable") -> z3.BoolRef:
        return z3.Or(
            z3.And(self.is_zero, other.is_zero),
            z3.And(
                self.sign_bit == other.sign_bit,
                self.exponent == other.exponent,
                self.num_leading_zeroes == other.num_leading_zeroes,
                self.num_leading_ones == other.num_leading_ones,
                self.last_nonzero_bit == other.last_nonzero_bit,
            ),
        )

    def has_same_sign(self, other: "FPVariable") -> z3.BoolRef:
        return z3.Or(
            z3.And(self.is_zero, other.is_zero),
            z3.And(self.is_positive, other.is_positive),
            z3.And(self.is_negative, other.is_negative),
        )


def print_model(model: z3.ModelRef, variable_ordering: list[str]) -> None:
    float_vars: dict[tuple[str, str], z3.FuncDeclRef] = {}
    non_float_vars: dict[str, z3.FuncDeclRef] = {}
    for var in model:
        var_name = str(var)
        if var_name.endswith("_sign_bit"):
            float_vars[(var_name[:-9], "sign_bit")] = var
        elif var_name.endswith("_exponent"):
            float_vars[(var_name[:-9], "exponent")] = var
        elif var_name.endswith("_num_leading_zeroes"):
            float_vars[(var_name[:-19], "num_leading_zeroes")] = var
        elif var_name.endswith("_num_leading_ones"):
            float_vars[(var_name[:-17], "num_leading_ones")] = var
        elif var_name.endswith("_last_nonzero_bit"):
            float_vars[(var_name[:-17], "last_nonzero_bit")] = var
        else:
            non_float_vars[var_name] = var
    float_names = {name for name, _ in float_vars}
    max_name_length = max(len(name) for name in float_names)
    max_exponent_length = 0
    for name in float_names:
        if (name, "exponent") in float_vars:
            exponent_var = model[float_vars[(name, "exponent")]]
            assert isinstance(exponent_var, z3.IntNumRef)
            max_exponent_length = max(
                max_exponent_length, len(str(exponent_var.as_long()))
            )
    for name in variable_ordering + list(float_names - set(variable_ordering)):
        if (name, "sign_bit") in float_vars:
            sign_value = model[float_vars[(name, "sign_bit")]]
            assert isinstance(sign_value, z3.BoolRef)
            sign_str = "-" if sign_value else "+"
        else:
            sign_str = "±"
        if (name, "exponent") in float_vars:
            exponent_var = model[float_vars[(name, "exponent")]]
            assert isinstance(exponent_var, z3.IntNumRef)
            exponent_value = exponent_var.as_long()
            exponent_str = str(exponent_value)
            if exponent_value == ZERO_EXPONENT:
                leading_bit = "0"
            else:
                leading_bit = "1"
        else:
            exponent_str = "?"
            leading_bit = "?"
        mantissa = ["?" for _ in range(PRECISION - 1)]
        if (name, "num_leading_zeroes") in float_vars:
            num_leading_zeroes_var = model[float_vars[(name, "num_leading_zeroes")]]
            assert isinstance(num_leading_zeroes_var, z3.IntNumRef)
            num_leading_zeroes = num_leading_zeroes_var.as_long()
            for i in range(num_leading_zeroes):
                mantissa[i] = "0"
            if num_leading_zeroes < PRECISION - 1:
                mantissa[num_leading_zeroes] = "1"
        if (name, "num_leading_ones") in float_vars:
            num_leading_ones_var = model[float_vars[(name, "num_leading_ones")]]
            assert isinstance(num_leading_ones_var, z3.IntNumRef)
            num_leading_ones = num_leading_ones_var.as_long()
            for i in range(num_leading_ones):
                mantissa[i] = "1"
            if num_leading_ones < PRECISION - 1:
                mantissa[num_leading_ones] = "0"
        if (name, "last_nonzero_bit") in float_vars:
            last_nonzero_bit_var = model[float_vars[(name, "last_nonzero_bit")]]
            assert isinstance(last_nonzero_bit_var, z3.IntNumRef)
            last_nonzero_bit = last_nonzero_bit_var.as_long()
            mantissa[last_nonzero_bit - 1] = "1"
            for i in range(last_nonzero_bit, PRECISION - 1):
                mantissa[i] = "0"
        mantissa_str = "".join(mantissa)
        name = name.rjust(max_name_length)
        exponent_str = exponent_str.ljust(max_exponent_length)
        print(f"{name} = {sign_str}2^{exponent_str} * {leading_bit}.{mantissa_str}")
    for name, var in non_float_vars.items():
        print(name, model[var])
    return None


def prove(
    solver: z3.Solver,
    claim: z3.BoolRef,
    name: str,
    variable_ordering: list[str],
    *,
    verbose: bool = True,
) -> bool:
    start = time.perf_counter_ns()
    result = solver.check(z3.Not(claim))
    stop = time.perf_counter_ns()
    if result == z3.unsat:
        if verbose:
            print(f"Verified {name} in {(stop - start) / 1e9:.6f} seconds.")
        return True
    else:
        assert result == z3.sat
        if verbose:
            print(f"Refuted {name} in {(stop - start) / 1e9:.6f} seconds.")
            print_model(solver.model(), variable_ordering)
        return False


def is_ulp_nonoverlapping(x: FPVariable, y: FPVariable) -> z3.BoolRef:
    """
    Construct a Z3 formula that determines whether two FPVariables are
    ulp-nonoverlapping and sorted in descending order by magnitude.
    """
    return z3.Or(
        y.is_zero,
        y.exponent < x.exponent - PRECISION,
        z3.And(y.exponent == x.exponent - PRECISION, y.last_nonzero_bit == 0),
    )


def fp_two_sum(
    solver: z3.Solver,
    x: FPVariable,
    y: FPVariable,
    sum_name: str,
    err_name: str,
) -> tuple[FPVariable, FPVariable]:
    """
    Create two new FPVariables that represent the floating-point sum and
    error computed by the 2Sum algorithm applied to two existing FPVariables.
    """
    s = FPVariable(solver, sum_name)
    e = FPVariable(solver, err_name)

    s_x = x.sign_bit
    s_y = y.sign_bit
    s_s = s.sign_bit
    s_e = e.sign_bit

    e_x = x.exponent
    e_y = y.exponent
    e_s = s.exponent
    e_e = e.exponent

    z_x = x.num_leading_zeroes
    z_y = y.num_leading_zeroes
    z_s = s.num_leading_zeroes
    z_e = e.num_leading_zeroes

    o_x = x.num_leading_ones
    o_y = y.num_leading_ones
    o_s = s.num_leading_ones
    o_e = e.num_leading_ones

    n_x = x.last_nonzero_bit
    n_y = y.last_nonzero_bit
    n_s = s.last_nonzero_bit
    n_e = e.last_nonzero_bit

    solver.add(
        z3.Or(s.is_zero, e_s - n_s >= e_x - n_x, e_s - n_s >= e_y - n_y)
    )  # G-LBES

    solver.add(z3.Or(e_s <= e_x + 1, e_s <= e_y + 1))  # G-UBES

    solver.add(
        z3.Or(e.is_zero, e_e - n_e >= e_x - n_x, e_e - n_e >= e_y - n_y)
    )  # G-LBEE

    solver.add(
        z3.Or(
            e.is_zero,
            e_e < e_s - PRECISION,
            z3.And(e_e == e_s - PRECISION, n_e == 0),
        )
    )  # G-UBEE

    solver.add(
        z3.Implies(
            z3.Or(
                z3.And(e_x - n_x > e_y, e_x - PRECISION < e_y - n_y),
                z3.And(e_x - (o_x + 1) > e_y, e_x - PRECISION < e_y - n_y),
                z3.And(e_x < e_y - n_y, e_x - n_x > e_y - PRECISION),
                z3.And(e_x < e_y - (o_y + 1), e_x - n_x > e_y - PRECISION),
            ),
            e.is_zero,
        )
    )  # G-NOC-E

    case_0a = y.is_zero
    case_0b = x.is_zero
    case_1a = e_x - (PRECISION + 1) > e_y
    case_1b = e_x < e_y - (PRECISION + 1)
    case_2as = z3.And(e_x - (PRECISION + 1) == e_y, s_x == s_y)
    case_2bs = z3.And(e_x == e_y - (PRECISION + 1), s_x == s_y)
    case_2ad_n = z3.And(e_x - (PRECISION + 1) == e_y, s_x != s_y, n_x != 0)
    case_2bd_n = z3.And(e_x == e_y - (PRECISION + 1), s_x != s_y, n_y != 0)
    case_2ad_zz = z3.And(e_x - (PRECISION + 1) == e_y, s_x != s_y, n_x == 0, n_y == 0)
    case_2bd_zz = z3.And(e_x == e_y - (PRECISION + 1), s_x != s_y, n_x == 0, n_y == 0)
    case_2ad_zn = z3.And(e_x - (PRECISION + 1) == e_y, s_x != s_y, n_x == 0, n_y != 0)
    case_2bd_zn = z3.And(e_x == e_y - (PRECISION + 1), s_x != s_y, n_x != 0, n_y == 0)
    case_3as = z3.And(e_x - PRECISION == e_y, s_x == s_y)
    case_3bs = z3.And(e_x == e_y - PRECISION, s_x == s_y)
    case_3ad = z3.And(e_x - PRECISION == e_y, s_x != s_y)
    case_3bd = z3.And(e_x == e_y - PRECISION, s_x != s_y)
    case_4as = z3.And(e_x - PRECISION < e_y, e_x - 1 > e_y, s_x == s_y)
    case_4as_n = z3.And(case_4as, e_x - (o_x + 1) > e_y)
    case_4bs = z3.And(e_x > e_y - PRECISION, e_x < e_y - 1, s_x == s_y)
    case_4bs_n = z3.And(case_4bs, e_x < e_y - (o_y + 1))
    case_4ad = z3.And(e_x - PRECISION < e_y, e_x - 1 > e_y, s_x != s_y)
    case_4bd = z3.And(e_x > e_y - PRECISION, e_x < e_y - 1, s_x != s_y)
    case_6s_x = z3.And(
        e_x == e_y,
        s_x == s_y,
        z3.Xor(n_x == PRECISION - 1, n_y == PRECISION - 1),
    )
    case_6s_n = z3.And(
        e_x == e_y,
        s_x == s_y,
        z3.Not(z3.Xor(n_x == PRECISION - 1, n_y == PRECISION - 1)),
    )
    case_6d = z3.And(e_x == e_y, s_x != s_y)

    solver.add(z3.Implies(case_0a, s.maybe_equal(x)))  # 0A-S
    solver.add(z3.Implies(case_0a, e.is_zero))  # 0A-E
    solver.add(z3.Implies(case_0b, s.maybe_equal(y)))  # 0B-S
    solver.add(z3.Implies(case_0b, e.is_zero))  # 0B-E

    solver.add(z3.Implies(case_1a, s.maybe_equal(x)))  # 1A-S
    solver.add(z3.Implies(case_1a, e.maybe_equal(y)))  # 1A-E
    solver.add(z3.Implies(case_1b, s.maybe_equal(y)))  # 1B-S
    solver.add(z3.Implies(case_1b, e.maybe_equal(x)))  # 1B-E

    solver.add(z3.Implies(case_2as, s.maybe_equal(x)))  # 2AS-S
    solver.add(z3.Implies(case_2as, e.maybe_equal(y)))  # 2AS-E
    solver.add(z3.Implies(case_2bs, s.maybe_equal(y)))  # 2BS-S
    solver.add(z3.Implies(case_2bs, e.maybe_equal(x)))  # 2BS-E
    solver.add(z3.Implies(case_2ad_n, s.maybe_equal(x)))  # 2AD-N-S
    solver.add(z3.Implies(case_2ad_n, e.maybe_equal(y)))  # 2AD-N-E
    solver.add(z3.Implies(case_2bd_n, s.maybe_equal(y)))  # 2BD-N-S
    solver.add(z3.Implies(case_2bd_n, e.maybe_equal(x)))  # 2BD-N-E
    solver.add(z3.Implies(case_2ad_zz, s.maybe_equal(x)))  # 2AD-ZZ-S
    solver.add(z3.Implies(case_2ad_zz, e.maybe_equal(y)))  # 2AD-ZZ-E
    solver.add(z3.Implies(case_2bd_zz, s.maybe_equal(y)))  # 2BD-ZZ-S
    solver.add(z3.Implies(case_2bd_zz, e.maybe_equal(x)))  # 2BD-ZZ-E
    solver.add(
        z3.Implies(
            case_2ad_zn,
            z3.And(
                s_s == s_x,
                e_s == e_x - 1,
                z_s == 0,
                o_s == PRECISION - 1,
                n_s == PRECISION - 1,
            ),
        )
    )  # 2AD-ZN-S
    solver.add(z3.Implies(case_2ad_zn, s_e == s_x))  # 2AD-ZN-SE
    solver.add(z3.Implies(case_2ad_zn, e_e < e_y))  # 2AD-ZN-UBEE
    solver.add(
        z3.Implies(
            case_2bd_zn,
            z3.And(
                s_s == s_y,
                e_s == e_y - 1,
                z_s == 0,
                o_s == PRECISION - 1,
                n_s == PRECISION - 1,
            ),
        )
    )  # 2BD-ZN-S
    solver.add(z3.Implies(case_2bd_zn, s_e == s_y))  # 2BD-ZN-SE
    solver.add(z3.Implies(case_2bd_zn, e_e < e_x))  # 2BD-ZN-UBEE

    solver.add(z3.Implies(case_3as, s_s == s_x))  # 3AS-SS
    solver.add(z3.Implies(case_3as, z3.Or(e_s == e_x, e_s == e_x + 1)))  # 3AS-ES
    solver.add(z3.Implies(case_3bs, s_s == s_y))  # 3BS-SS
    solver.add(z3.Implies(case_3bs, z3.Or(e_s == e_y, e_s == e_y + 1)))  # 3BS-ES
    solver.add(z3.Implies(case_3ad, s_s == s_x))  # 3AD-SS
    solver.add(z3.Implies(case_3ad, z3.Or(e_s == e_x, e_s == e_x - 1)))  # 3AD-ES
    solver.add(z3.Implies(case_3bd, s_s == s_y))  # 3BD-SS
    solver.add(z3.Implies(case_3bd, z3.Or(e_s == e_y, e_s == e_y - 1)))  # 3BD-ES

    solver.add(z3.Implies(case_4as, s_s == s_x))  # 4AS-SS
    solver.add(z3.Implies(case_4as, z3.Or(e_s == e_x, e_s == e_x + 1)))  # 4AS-ES
    solver.add(z3.Implies(case_4as_n, e_s == e_x))  # 4AS-N-ES
    solver.add(z3.Implies(case_4bs, s_s == s_y))  # 4BS-SS
    solver.add(z3.Implies(case_4bs, z3.Or(e_s == e_y, e_s == e_y + 1)))  # 4BS-ES
    solver.add(z3.Implies(case_4bs_n, e_s == e_y))  # 4BS-N-ES
    solver.add(z3.Implies(case_4ad, s_s == s_x))  # 4AD-SS
    solver.add(z3.Implies(case_4ad, z3.Or(e_s == e_x, e_s == e_x - 1)))  # 4AD-ES
    solver.add(z3.Implies(case_4bd, s_s == s_y))  # 4BD-SS
    solver.add(z3.Implies(case_4bd, z3.Or(e_s == e_y, e_s == e_y - 1)))  # 4BD-ES

    solver.add(z3.Implies(case_6s_x, z3.And(s_s == s_x, s_s == s_y)))  # 6S-X-SS
    solver.add(z3.Implies(case_6s_x, z3.And(e_s == e_x + 1, e_s == e_y + 1)))  # 6S-X-ES
    solver.add(
        z3.Implies(
            case_6s_x,
            z3.And(
                e_e == e_x - (PRECISION - 1),
                e_e == e_y - (PRECISION - 1),
                z_e == PRECISION - 1,
                o_e == 0,
                n_e == 0,
            ),
        )
    )  # 6S-X-E
    solver.add(z3.Implies(case_6s_x, n_e == 0))  # 6S-X-NE
    solver.add(z3.Implies(case_6s_n, z3.And(s_s == s_x, s_s == s_y)))  # 6S-N-SS
    solver.add(
        z3.Implies(case_6s_n, z3.Or(s.is_zero, z3.And(e_s == e_x + 1, e_s == e_y + 1)))
    )  # 6S-N-ES
    solver.add(z3.Implies(case_6s_n, e.is_zero))  # 6S-N-E
    solver.add(
        z3.Implies(
            case_6d,
            z3.And(
                z3.Or(s.is_zero, e_s < e_x - z_x, e_s < e_y - z_y),
                z3.Or(s.is_zero, e_s < e_x - o_x, e_s < e_y - o_y),
            ),
        )
    )  # 6D-UBES
    solver.add(z3.Implies(case_6d, e.is_zero))  # 6D-E

    # case_3as_g = z3.And(e_x - PRECISION == e_y, s_x == s_y, o_x != PRECISION - 1)
    # case_3as_s = z3.And(
    #     e_x - PRECISION == e_y,
    #     s_x == s_y,
    #     o_x == PRECISION - 1,
    #     z3.Not(y.is_zero),
    # )
    # case_3bs_g = z3.And(e_x == e_y - PRECISION, s_x == s_y, o_y != PRECISION - 1)
    # case_3bs_s = z3.And(
    #     e_x == e_y - PRECISION,
    #     s_x == s_y,
    #     o_y == PRECISION - 1,
    #     z3.Not(x.is_zero),
    # )

    # solver.add(
    #     z3.Implies(
    #         case_3as_g,
    #         z3.And(
    #             s_s == s_x,
    #             e_s == e_x,
    #             z3.Or(
    #                 z3.And(s.maybe_equal(x), e.maybe_equal(y)),
    #                 z3.And(
    #                     s_e != s_x,
    #                     e_e < e_y,
    #                 ),
    #                 z3.And(
    #                     s_e != s_x,
    #                     e_e == e_y,
    #                     n_y == 0,
    #                     n_e == 0,
    #                 ),
    #             ),
    #         ),
    #     )
    # )

    # solver.add(
    #     z3.Implies(
    #         case_3bs_g,
    #         z3.And(
    #             s_s == s_y,
    #             e_s == e_y,
    #             z3.Or(
    #                 z3.And(s.maybe_equal(y), e.maybe_equal(x)),
    #                 z3.And(
    #                     s_e != s_y,
    #                     e_e < e_x,
    #                 ),
    #                 z3.And(
    #                     s_e != s_y,
    #                     e_e == e_x,
    #                     n_x == 0,
    #                     n_e == 0,
    #                 ),
    #             ),
    #         ),
    #     )
    # )

    # solver.add(
    #     z3.Implies(
    #         case_3as_s,
    #         z3.And(
    #             s_s == s_x,
    #             e_s == e_x + 1,
    #             s_e != s_x,
    #             z3.Or(
    #                 e_e < e_y,
    #                 z3.And(
    #                     e_e == e_y,
    #                     n_y == 0,
    #                     n_e == 0,
    #                 ),
    #             ),
    #         ),
    #     )
    # )

    # solver.add(
    #     z3.Implies(
    #         case_3bs_s,
    #         z3.And(
    #             s_s == s_y,
    #             e_s == e_y + 1,
    #             s_e != s_y,
    #             z3.Or(
    #                 e_e < e_x,
    #                 z3.And(
    #                     e_e == e_x,
    #                     n_x == 0,
    #                     n_e == 0,
    #                 ),
    #             ),
    #         ),
    #     )
    # )

    # solver.add(
    #     z3.Implies(
    #         case_4as,
    #         z3.And(
    #             s_s == s_x,
    #             z3.Or(e_s == e_x, e_s == e_x + 1),
    #             z3.Or(
    #                 e.is_zero,
    #                 e_e <= e_s - PRECISION,
    #                 z3.And(e_e == e_s - (PRECISION - 1), n_e == 0),
    #             ),
    #         ),
    #     )
    # )

    # solver.add(
    #     z3.Implies(
    #         z3.And(case_4as, e_x - n_x > e_y, e_x - PRECISION < e_y - n_y),
    #         e.is_zero,
    #     )
    # )

    # solver.add(
    #     z3.Implies(
    #         z3.And(case_4as, e_x - (o_x + 1) > e_y, e_x - PRECISION < e_y - n_y),
    #         e.is_zero,
    #     )
    # )

    # solver.add(
    #     z3.Implies(
    #         case_4bs,
    #         z3.And(
    #             s_s == s_y,
    #             z3.Or(e_s == e_y, e_s == e_y + 1),
    #             z3.Or(
    #                 e.is_zero,
    #                 e_e <= e_s - PRECISION,
    #                 z3.And(e_e == e_s - (PRECISION - 1), n_e == 0),
    #             ),
    #         ),
    #     )
    # )

    # solver.add(
    #     z3.Implies(
    #         z3.And(case_4bs, e_x < e_y - n_y, e_x - n_x < e_y - PRECISION),
    #         e.is_zero,
    #     )
    # )

    # solver.add(
    #     z3.Implies(
    #         z3.And(case_4bs, e_x < e_y - (o_y + 1), e_x - n_x < e_y - PRECISION),
    #         e.is_zero,
    #     )
    # )

    # solver.add(
    #     z3.Implies(
    #         case_5as,
    #         z3.And(
    #             s_s == s_x,
    #             z3.Or(e_s == e_x, e_s == e_x + 1),
    #             z3.Or(
    #                 e.is_zero,
    #                 e_e <= e_s - PRECISION,
    #                 z3.And(e_e == e_s - (PRECISION - 1), n_e == 0),
    #             ),
    #         ),
    #     )
    # )

    # solver.add(
    #     z3.Implies(
    #         z3.And(case_5as, e_x - n_x > e_y, e_x - PRECISION < e_y - n_y),
    #         e.is_zero,
    #     )
    # )

    # solver.add(
    #     z3.Implies(
    #         z3.And(case_5as, e_x - (o_x + 1) > e_y, e_x - PRECISION < e_y - n_y),
    #         e.is_zero,
    #     )
    # )

    # solver.add(
    #     z3.Implies(
    #         case_5bs,
    #         z3.And(
    #             s_s == s_y,
    #             z3.Or(e_s == e_y, e_s == e_y + 1),
    #             z3.Or(
    #                 e.is_zero,
    #                 e_e <= e_s - PRECISION,
    #                 z3.And(e_e == e_s - (PRECISION - 1), n_e == 0),
    #             ),
    #         ),
    #     )
    # )

    # solver.add(
    #     z3.Implies(
    #         z3.And(case_5bs, e_x < e_y - n_y, e_x - n_x < e_y - PRECISION),
    #         e.is_zero,
    #     )
    # )

    # solver.add(
    #     z3.Implies(
    #         z3.And(case_5bs, e_x < e_y - (o_y + 1), e_x - n_x < e_y - PRECISION),
    #         e.is_zero,
    #     )
    # )

    # solver.add(
    #     z3.Implies(
    #         case_5ad,
    #         z3.And(
    #             s_s == s_x,
    #             e_s <= e_x,
    #             e_s >= e_x - PRECISION,
    #             z3.Or(e.is_zero, e_e <= e_s - PRECISION),
    #         ),
    #     )
    # )

    # solver.add(
    #     z3.Implies(
    #         case_5bd,
    #         z3.And(
    #             s_s == s_y,
    #             e_s <= e_y,
    #             e_s >= e_y - PRECISION,
    #             z3.Or(e.is_zero, e_e <= e_s - PRECISION),
    #         ),
    #     )
    # )

    return (s, e)


def fast_two_sum_preconditions(
    x: FPVariable,
    y: FPVariable,
) -> z3.BoolRef:
    """
    Construct a Z3 formula that determines whether the
    preconditions of the Fast2Sum algorithm are satisfied.
    """
    return z3.Or(x.is_zero, y.is_zero, x.exponent >= y.exponent)


def fp_fast_two_sum(
    solver: z3.Solver,
    x: FPVariable,
    y: FPVariable,
    sum_name: str,
    err_name: str,
    *,
    verbose: bool = True,
) -> tuple[FPVariable, FPVariable]:
    """
    Create two new FPVariables that represent the floating-point sum and error
    computed by the Fast2Sum algorithm applied to two existing FPVariables.
    Raise an exception if the preconditions of the algorithm are not satisfied.
    """
    # assert prove(
    #     solver,
    #     fast_two_sum_preconditions(x, y),
    #     f"Fast2Sum preconditions for {x.name} and {y.name}",
    #     [x.name, y.name, sum_name, err_name],
    #     verbose=verbose,
    # )
    return fp_two_sum(solver, x, y, sum_name, err_name)


def verify_joldes_2017_algorithm_4():
    solver = z3.Solver()
    x0 = FPVariable(solver, "x0")
    x1 = FPVariable(solver, "x1")
    solver.add(is_ulp_nonoverlapping(x0, x1))
    y = FPVariable(solver, "y")

    s0, s1 = fp_two_sum(solver, x0, y, "s0", "s1")
    v, err_v = fp_two_sum(solver, x1, s1, "v", "err_v")
    z0, z1 = fp_fast_two_sum(solver, s0, v, "z0", "z1")

    prove(
        solver,
        is_ulp_nonoverlapping(z0, z1),
        "nonoverlapping",
        ["x0", "y", "s0", "s1", "x1", "s1", "v", "err_v", "s0", "v", "z0", "z1"],
    )
    prove(
        solver,
        z3.Or(err_v.is_zero, err_v.exponent <= z0.exponent - 105),
        "error bound",
        ["x0", "y", "s0", "s1", "x1", "s1", "v", "err_v", "s0", "v", "z0", "z1"],
    )


def refute_joldes_2017_algorithm_5():
    solver = z3.Solver()
    x0 = FPVariable(solver, "x0")
    x1 = FPVariable(solver, "x1")
    solver.add(is_ulp_nonoverlapping(x0, x1))
    y0 = FPVariable(solver, "y0")
    y1 = FPVariable(solver, "y1")
    solver.add(is_ulp_nonoverlapping(y0, y1))

    s0, s1 = fp_two_sum(solver, x0, y0, "s0", "s1")
    v, err_v = fp_two_sum(solver, x1, y1, "v", "err_v")
    w, err_w = fp_two_sum(solver, s1, v, "w", "err_w")
    z0, z1 = fp_fast_two_sum(solver, s0, w, "z0", "z1")

    prove(
        solver,
        is_ulp_nonoverlapping(z0, z1),
        "nonoverlapping",
        [],
    )
    assert not prove(
        solver,
        z3.Or(err_v.is_zero, err_v.exponent <= z0.exponent + 1940),
        "error bound on v",
        [],
        verbose=False,
    )
    prove(
        solver,
        z3.Or(err_w.is_zero, err_w.exponent <= z0.exponent - 103),
        "error bound on w",
        [],
    )


def verify_joldes_2017_algorithm_6():
    solver = z3.Solver()
    x0 = FPVariable(solver, "x0")
    x1 = FPVariable(solver, "x1")
    solver.add(is_ulp_nonoverlapping(x0, x1))
    y0 = FPVariable(solver, "y0")
    y1 = FPVariable(solver, "y1")
    solver.add(is_ulp_nonoverlapping(y0, y1))

    s0, s1 = fp_two_sum(solver, x0, y0, "s0", "s1")
    t0, t1 = fp_two_sum(solver, x1, y1, "t0", "t1")
    c, err_c = fp_two_sum(solver, s1, t0, "c", "err_c")
    v0, v1 = fp_fast_two_sum(solver, s0, c, "v0", "v1")
    w, err_w = fp_two_sum(solver, t1, v1, "w", "err_w")
    z0, z1 = fp_fast_two_sum(solver, v0, w, "z0", "z1")

    prove(
        solver,
        is_ulp_nonoverlapping(z0, z1),
        "nonoverlapping",
        [],
    )
    prove(
        solver,
        z3.Or(err_c.is_zero, err_c.exponent <= z0.exponent - 102),
        "error bound on c",
        [],
    )
    prove(
        solver,
        z3.Or(err_w.is_zero, err_w.exponent <= z0.exponent - 105),
        "error bound on w",
        [],
    )
    pass


if __name__ == "__main__":
    verify_joldes_2017_algorithm_4()
    refute_joldes_2017_algorithm_5()
    verify_joldes_2017_algorithm_6()
