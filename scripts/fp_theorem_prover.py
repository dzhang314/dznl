import time
import z3


PRECISION: int = 53
ZERO_EXPONENT: int = -1


class FPVariable(object):

    def __init__(self, solver: z3.Solver, name: str):
        self.name: str = name

        # We explicitly model three attributes of a floating-point number:
        # the sign bit, the exponent, and the number of nonzero bits (nnzb).
        self.sign_bit: z3.BoolRef = z3.Bool(name + "_sign_bit")
        self.exponent: z3.ArithRef = z3.Int(name + "_exponent")
        self.nnzb: z3.ArithRef = z3.Int(name + "_nnzb")

        # The count of nonzero bits does NOT include the implicit leading one.
        solver.add(self.nnzb >= 0)
        solver.add(self.nnzb < PRECISION)

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
                self.nnzb == other.nnzb,
            ),
        )

    def has_same_sign(self, other: "FPVariable") -> z3.BoolRef:
        return z3.Or(
            z3.And(self.is_zero, other.is_zero),
            z3.And(self.is_positive, other.is_positive),
            z3.And(self.is_negative, other.is_negative),
        )


def fp_sum(
    solver: z3.Solver,
    x: FPVariable,
    y: FPVariable,
    name: str,
) -> FPVariable:
    """
    Create a new FPVariable that represents the floating-point sum of two
    existing FPVariables.
    """
    s = FPVariable(solver, name)
    e_x = x.exponent
    e_y = y.exponent
    e_s = s.exponent
    e_min = z3.If(e_x < e_y, e_x, e_y)
    e_max = z3.If(e_x > e_y, e_x, e_y)

    ############################################################ ZERO PROPERTIES

    # Theorem: If x == 0 and y == 0, then s == 0.
    solver.add(z3.Implies(z3.And(x.is_zero, y.is_zero), s.is_zero))

    # Theorem: If x == 0, then s == y or s === y.
    solver.add(z3.Implies(x.is_zero, s.maybe_equal(y)))

    # Theorem: If y == 0, then s == x or s === x.
    solver.add(z3.Implies(y.is_zero, s.maybe_equal(x)))

    ######################################################## EXPONENT PROPERTIES

    # Theorem: If e_x > e_y + p + 1, then s === x.
    solver.add(z3.Implies(e_x > e_y + PRECISION + 1, s.maybe_equal(x)))

    # Theorem: If e_x + p + 1 < e_y, then s === y.
    solver.add(z3.Implies(e_x + PRECISION + 1 < e_y, s.maybe_equal(y)))

    ###################################################### EXPONENT UPPER BOUNDS

    # Theorem: e_s <= e_max + 1.
    solver.add(e_s <= e_max + 1)

    # Theorem: If s_x != s_y, then e_s <= e_max.
    solver.add(z3.Implies(x.sign_bit != y.sign_bit, e_s <= e_max))

    # Theorem: If e_x - nnzb_x > e_y + 1, then e_s <= e_x.
    solver.add(z3.Implies(e_x - x.nnzb > e_y + 1, e_s <= e_x))

    # Theorem: If e_x + 1 < e_y - nnzb_y, then e_s <= e_y.
    solver.add(z3.Implies(e_x + 1 < e_y - y.nnzb, e_s <= e_y))

    # Theorem: If e_x - nnzb_x > e_y and e_x - p < e_y - nnzb_y,
    # then e_s <= e_x.
    solver.add(
        z3.Implies(
            z3.And(
                e_x - x.nnzb > e_y,
                e_x - PRECISION < e_y - y.nnzb,
            ),
            e_s <= e_x,
        )
    )

    # Theorem: If e_x < e_y - nnzb_y and e_x - nnzb_x > e_y - p,
    # then e_s <= e_y.
    solver.add(
        z3.Implies(
            z3.And(
                e_x < e_y - y.nnzb,
                e_x - x.nnzb > e_y - PRECISION,
            ),
            e_s <= e_y,
        )
    )

    ###################################################### EXPONENT LOWER BOUNDS

    # Theorem: s == 0 or e_s >= e_min - (p - 1).
    solver.add(z3.Or(s.is_zero, e_s >= e_min - (PRECISION - 1)))

    # Theorem: s == 0 or e_s >= e_max - p.
    solver.add(z3.Or(s.is_zero, e_s >= e_max - PRECISION))

    # Theorem: If e_x > e_y + nnzb_y, then e_s >= e_y + nnzb_y.
    solver.add(z3.Implies(e_x > e_y + y.nnzb, e_s >= e_y + y.nnzb))

    # Theorem: If e_x + nnzb_x < e_y, then e_s >= e_x + nnzb_x.
    solver.add(z3.Implies(e_x + x.nnzb < e_y, e_s >= e_x + x.nnzb))

    ########################################################## NNZB UPPER BOUNDS

    # Theorem: If s is not zero or subnormal, then e_s - nnzb_s >= e_max - p.
    solver.add(z3.Implies(z3.Not(s.is_zero), e_s - s.nnzb >= e_max - PRECISION))

    return s


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
            print("Counterexample:")
            model = solver.model()
            print_model(model)
        return False


def is_ulp_nonoverlapping(x: FPVariable, y: FPVariable) -> z3.BoolRef:
    """
    Construct a Z3 formula that determines whether two FPVariables are
    ulp-nonoverlapping and sorted in descending order by magnitude.
    """
    return z3.Or(
        y.is_zero,
        y.exponent < x.exponent - PRECISION,
        z3.And(y.exponent == x.exponent - PRECISION, y.nnzb == 0),
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
    s = fp_sum(solver, x, y, sum_name)
    e = FPVariable(solver, err_name)

    # The error term is ulp-nonoverlapping with the sum.
    solver.add(is_ulp_nonoverlapping(s, e))

    # If either addend is zero, the error term is zero.
    solver.add(z3.Implies(x.is_zero, e.is_zero))
    solver.add(z3.Implies(y.is_zero, e.is_zero))

    # If the error term is nonzero, it is larger than
    # the least significant bit of the smaller addend.
    solver.add(
        z3.Or(
            e.is_zero,
            e.exponent > x.exponent - PRECISION,
            e.exponent > y.exponent - PRECISION,
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
