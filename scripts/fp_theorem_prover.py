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

        solver.add(0 <= self.num_leading_ones)
        solver.add(self.num_leading_ones <= self.last_nonzero_bit)
        solver.add(self.last_nonzero_bit < PRECISION)

        solver.add(0 <= self.num_leading_zeroes)
        solver.add(self.num_leading_zeroes < PRECISION)

        # The leading digit of the mantissa is either a 0 or a 1, not both.
        solver.add(z3.Xor(self.num_leading_zeroes == 0, self.num_leading_ones == 0))

        solver.add(
            z3.Implies(
                self.num_leading_zeroes < PRECISION - 1,
                self.num_leading_zeroes < self.last_nonzero_bit,
            )
        )

        solver.add(
            z3.Implies(
                self.num_leading_zeroes == PRECISION - 1,
                self.last_nonzero_bit == 0,
            )
        )

        # We model a hypothetical floating-point datatype with infinite
        # exponent range, eliminating the possibility of overflow or underflow.
        # This means that all results proven in this model assume that no
        # overflow or underflow occurs when performing the actual computation.

        # When analyzing floating-point addition and subtraction circuits, only
        # relative values of the exponents matter, not absolute values. This
        # means we can arbitrarily set the zero point anywhere without loss of
        # generality. In this model, we consider 0.0 to have exponent -1 and
        # assume all nonzero floating-point numbers have nonnegative exponents.
        solver.add(self.exponent >= ZERO_EXPONENT)

        # We do not consider infinities or NaNs in this model, so all
        # floating-point numbers are either positive, negative, or zero.
        self.is_zero: z3.BoolRef = self.exponent == ZERO_EXPONENT
        solver.add(z3.Implies(self.is_zero, self.num_leading_zeroes == PRECISION - 1))
        solver.add(z3.Implies(self.is_zero, self.num_leading_ones == 0))
        solver.add(z3.Implies(self.is_zero, self.last_nonzero_bit == 0))

        self.is_positive: z3.BoolRef = z3.And(
            self.exponent > ZERO_EXPONENT,
            z3.Not(self.sign_bit),
        )

        self.is_negative: z3.BoolRef = z3.And(
            self.exponent > ZERO_EXPONENT,
            self.sign_bit,
        )

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


def print_model(model: z3.ModelRef) -> None:
    float_vars: dict[tuple[str, str], z3.FuncDeclRef] = {}
    non_float_vars: dict[str, z3.FuncDeclRef] = {}
    for var in model:
        var_name = str(var)
        if var_name.endswith("_sign_bit"):
            float_vars[(var_name[:-9], "sign_bit")] = var
        elif var_name.endswith("_exponent"):
            float_vars[(var_name[:-9], "exponent")] = var
        elif var_name.endswith("_nnzb"):
            float_vars[(var_name[:-5], "nnzb")] = var
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
    for name in float_names:
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
        else:
            exponent_str = "?"
        if (name, "nnzb") in float_vars:
            nnzb_var = model[float_vars[(name, "nnzb")]]
            assert isinstance(nnzb_var, z3.IntNumRef)
            nnzb_value = nnzb_var.as_long()
            mantissa_str = nnzb_value * "?" + (PRECISION - nnzb_value - 1) * "0"
        else:
            mantissa_str = "?" * (PRECISION - 1)
        name = name.rjust(max_name_length)
        exponent_str = exponent_str.ljust(max_exponent_length)
        print(f"{name} = {sign_str}2^{exponent_str} * 1.{mantissa_str}")
    for name, var in non_float_vars.items():
        print(name, model[var])
    return None


def prove(
    solver: z3.Solver,
    claim: z3.BoolRef,
    name: str,
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

    case_0a = y.is_zero
    case_0b = x.is_zero
    case_1a = e_x - (PRECISION + 2) >= e_y
    case_1b = e_x <= e_y - (PRECISION + 2)
    case_2as = z3.And(e_x - (PRECISION + 1) == e_y, s_x == s_y)
    case_2bs = z3.And(e_x == e_y - (PRECISION + 1), s_x == s_y)
    case_2ad_n = z3.And(e_x - (PRECISION + 1) == e_y, s_x != s_y, n_x != 0)
    case_2bd_n = z3.And(e_x == e_y - (PRECISION + 1), s_x != s_y, n_y != 0)
    case_2ad_zz = z3.And(e_x - (PRECISION + 1) == e_y, s_x != s_y, n_x == 0, n_y == 0)
    case_2bd_zz = z3.And(e_x == e_y - (PRECISION + 1), s_x != s_y, n_x == 0, n_y == 0)
    case_2ad_zn = z3.And(e_x - (PRECISION + 1) == e_y, s_x != s_y, n_x == 0, n_y != 0)
    case_2bd_zn = z3.And(e_x == e_y - (PRECISION + 1), s_x != s_y, n_x != 0, n_y == 0)
    case_3as_g = z3.And(e_x - PRECISION == e_y, s_x == s_y, o_x != PRECISION - 1)
    case_3as_s = z3.And(
        e_x - PRECISION == e_y,
        s_x == s_y,
        o_x == PRECISION - 1,
        z3.Not(y.is_zero),
    )
    case_3ad = z3.And(e_x - PRECISION == e_y, s_x != s_y)
    case_3bs_g = z3.And(e_x == e_y - PRECISION, s_x == s_y, o_y != PRECISION - 1)
    case_3bs_s = z3.And(
        e_x == e_y - PRECISION,
        s_x == s_y,
        o_y == PRECISION - 1,
        z3.Not(x.is_zero),
    )
    case_3bd = z3.And(e_x == e_y - PRECISION, s_x != s_y)
    case_4as = z3.And(e_x - PRECISION < e_y, e_x > e_y, s_x == s_y)
    case_4ad = z3.And(e_x - PRECISION < e_y, e_x > e_y, s_x != s_y)
    case_4bs = z3.And(e_x > e_y - PRECISION, e_x < e_y, s_x == s_y)
    case_4bd = z3.And(e_x > e_y - PRECISION, e_x < e_y, s_x != s_y)
    case_5s_x = z3.And(
        e_x == e_y,
        s_x == s_y,
        z3.Not(x.is_zero),
        z3.Not(y.is_zero),
        z3.Xor(n_x == PRECISION - 1, n_y == PRECISION - 1),
    )
    case_5s_n = z3.And(
        e_x == e_y,
        s_x == s_y,
        z3.Not(x.is_zero),
        z3.Not(y.is_zero),
        z3.Not(z3.Xor(n_x == PRECISION - 1, n_y == PRECISION - 1)),
    )
    case_5d = z3.And(e_x == e_y, s_x != s_y, z3.Not(x.is_zero), z3.Not(y.is_zero))

    prove(
        solver,
        z3.Or(
            case_0a,
            case_0b,
            case_1a,
            case_1b,
            case_2as,
            case_2ad_n,
            case_2ad_zz,
            case_2ad_zn,
            case_2bs,
            case_2bd_n,
            case_2bd_zz,
            case_2bd_zn,
            case_3as_g,
            case_3as_s,
            case_3ad,
            case_3bs_g,
            case_3bs_s,
            case_3bd,
            case_4as,
            case_4ad,
            case_4bs,
            case_4bd,
            case_5s_x,
            case_5s_n,
            case_5d,
        ),
        "TwoSum cases are exhaustive",
    )

    solver.add(z3.Implies(case_0a, z3.And(s.maybe_equal(x), e.is_zero)))
    solver.add(z3.Implies(case_0b, z3.And(s.maybe_equal(y), e.is_zero)))
    solver.add(z3.Implies(case_1a, z3.And(s.maybe_equal(x), e.maybe_equal(y))))
    solver.add(z3.Implies(case_1b, z3.And(s.maybe_equal(y), e.maybe_equal(x))))
    solver.add(z3.Implies(case_2as, z3.And(s.maybe_equal(x), e.maybe_equal(y))))
    solver.add(z3.Implies(case_2bs, z3.And(s.maybe_equal(y), e.maybe_equal(x))))
    solver.add(z3.Implies(case_2ad_n, z3.And(s.maybe_equal(x), e.maybe_equal(y))))
    solver.add(z3.Implies(case_2bd_n, z3.And(s.maybe_equal(y), e.maybe_equal(x))))
    solver.add(z3.Implies(case_2ad_zz, z3.And(s.maybe_equal(x), e.maybe_equal(y))))
    solver.add(z3.Implies(case_2bd_zz, z3.And(s.maybe_equal(y), e.maybe_equal(x))))

    solver.add(
        z3.Implies(
            case_2ad_zn,
            z3.And(
                s_s == s_x,
                e_s == e_x - 1,
                o_s == PRECISION - 1,
                s_e == s_x,
                e_e < e_y,
            ),
        )
    )

    solver.add(
        z3.Implies(
            case_2bd_zn,
            z3.And(
                s_s == s_y,
                e_s == e_y - 1,
                o_s == PRECISION - 1,
                s_e == s_y,
                e_e < e_x,
            ),
        )
    )

    solver.add(
        z3.Implies(
            case_3as_g,
            z3.And(
                s_s == s_x,
                e_s == e_x,
                z3.Or(
                    z3.And(s.maybe_equal(x), e.maybe_equal(y)),
                    z3.And(
                        s_e != s_x,
                        e_e < e_y,
                    ),
                    z3.And(
                        s_e != s_x,
                        e_e == e_y,
                        n_y == 0,
                        n_e == 0,
                    ),
                ),
            ),
        )
    )

    solver.add(
        z3.Implies(
            case_3bs_g,
            z3.And(
                s_s == s_y,
                e_s == e_y,
                z3.Or(
                    z3.And(s.maybe_equal(y), e.maybe_equal(x)),
                    z3.And(
                        s_e != s_y,
                        e_e < e_x,
                    ),
                    z3.And(
                        s_e != s_y,
                        e_e == e_x,
                        n_x == 0,
                        n_e == 0,
                    ),
                ),
            ),
        )
    )

    solver.add(
        z3.Implies(
            case_3as_s,
            z3.And(
                s_s == s_x,
                e_s == e_x + 1,
                s_e != s_x,
                z3.Or(
                    e_e < e_y,
                    z3.And(
                        e_e == e_y,
                        n_y == 0,
                        n_e == 0,
                    ),
                ),
            ),
        )
    )

    solver.add(
        z3.Implies(
            case_3bs_s,
            z3.And(
                s_s == s_y,
                e_s == e_y + 1,
                s_e != s_y,
                z3.Or(
                    e_e < e_x,
                    z3.And(
                        e_e == e_x,
                        n_x == 0,
                        n_e == 0,
                    ),
                ),
            ),
        )
    )

    solver.add(
        z3.Implies(
            case_3ad,
            z3.And(
                s_s == s_x,
                z3.Or(
                    e_s == e_x,
                    e_s == e_x - 1,
                ),
            ),
        )
    )

    solver.add(
        z3.Implies(
            case_3bd,
            z3.And(
                s_s == s_y,
                z3.Or(
                    e_s == e_y,
                    e_s == e_y - 1,
                ),
            ),
        )
    )

    solver.add(
        z3.Implies(
            case_4as,
            z3.And(
                s_s == s_x,
                z3.Or(
                    e_s == e_x,
                    e_s == e_x + 1,
                ),
            ),
        )
    )

    solver.add(
        z3.Implies(
            z3.And(case_4as, e_x - n_x > e_y, e_x - PRECISION < e_y - n_y),
            e.is_zero,
        )
    )

    solver.add(
        z3.Implies(
            z3.And(case_4as, e_x - (o_x + 1) > e_y, e_x - PRECISION < e_y - n_y),
            e.is_zero,
        )
    )

    solver.add(
        z3.Implies(
            case_4bs,
            z3.And(
                s_s == s_y,
                z3.Or(
                    e_s == e_y,
                    e_s == e_y + 1,
                ),
            ),
        )
    )

    solver.add(
        z3.Implies(
            z3.And(case_4bs, e_x < e_y - n_y, e_x - n_x < e_y - PRECISION),
            e.is_zero,
        )
    )

    solver.add(
        z3.Implies(
            z3.And(case_4bs, e_x < e_y - (o_y + 1), e_x - n_x < e_y - PRECISION),
            e.is_zero,
        )
    )

    solver.add(
        z3.Implies(
            case_4ad,
            z3.And(
                s_s == s_x,
                e_s <= e_x,
            ),
        )
    )

    solver.add(
        z3.Implies(
            case_4bd,
            z3.And(
                s_s == s_y,
                e_s <= e_y,
            ),
        )
    )

    solver.add(
        z3.Implies(
            case_5s_x,
            z3.And(
                s_s == s_x,
                s_s == s_y,
                e_s == e_x + 1,
                e_s == e_y + 1,
                e_e == e_x - (PRECISION - 1),
                e_e == e_y - (PRECISION - 1),
                n_e == 0,
            ),
        )
    )

    solver.add(
        z3.Implies(
            case_5s_n,
            z3.And(
                s_s == s_x,
                s_s == s_y,
                e_s == e_x + 1,
                e_s == e_y + 1,
                e.is_zero,
            ),
        )
    )

    solver.add(
        z3.Implies(
            case_5d,
            z3.And(
                z3.Or(s.is_zero, e_s < e_x - o_x, e_s < e_y - o_y),
                z3.Or(s.is_zero, e_s < e_x - z_x, e_s < e_y - z_y),
                e.is_zero,
            ),
        )
    )

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
    assert prove(
        solver,
        fast_two_sum_preconditions(x, y),
        f"Fast2Sum preconditions for {x.name} and {y.name}",
        verbose=verbose,
    )
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
    )
    prove(
        solver,
        z3.Or(err_v.is_zero, err_v.exponent <= z0.exponent - 104),
        "error bound",
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
    )
    assert not prove(
        solver,
        z3.Or(err_v.is_zero, err_v.exponent <= z0.exponent + 1940),
        "error bound on v",
        verbose=False,
    )
    prove(
        solver,
        z3.Or(err_w.is_zero, err_w.exponent <= z0.exponent - 103),
        "error bound on w",
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
    )
    prove(
        solver,
        z3.Or(err_c.is_zero, err_c.exponent <= z0.exponent - 102),
        "error bound on c",
    )
    prove(
        solver,
        z3.Or(err_w.is_zero, err_w.exponent <= z0.exponent - 105),
        "error bound on w",
    )
    pass


if __name__ == "__main__":
    verify_joldes_2017_algorithm_4()
    refute_joldes_2017_algorithm_5()
    verify_joldes_2017_algorithm_6()
