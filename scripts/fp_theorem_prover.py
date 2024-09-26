import time
import z3


PRECISION: int = 53
MAX_EXPONENT: int = 1023
MIN_NORMALIZED_EXPONENT: int = -1022
ZERO_EXPONENT: int = MIN_NORMALIZED_EXPONENT - 1


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
            print(solver.model())
        return False


class FPVariable(object):

    def __init__(self, solver: z3.Solver, name: str):
        self.name: str = name
        self.sign_bit: z3.BoolRef = z3.Bool(name + "_sign_bit")
        self.exponent: z3.ArithRef = z3.Int(name + "_exponent")
        self.is_pow2: z3.BoolRef = z3.Bool(name + "_is_pow2")

        # We consider only computations without overflow or underflow.
        solver.add(self.exponent >= ZERO_EXPONENT)
        solver.add(self.exponent <= MAX_EXPONENT)

        # We assume that zero is the only subnormal number.
        self.is_zero: z3.BoolRef = self.exponent == ZERO_EXPONENT

        self.is_positive: z3.BoolRef = z3.And(
            self.exponent >= MIN_NORMALIZED_EXPONENT,
            z3.Not(self.sign_bit),
        )
        self.is_negative: z3.BoolRef = z3.And(
            self.exponent >= MIN_NORMALIZED_EXPONENT,
            self.sign_bit,
        )

    def is_equal(self, other: "FPVariable") -> z3.BoolRef:
        return z3.Or(
            z3.And(self.is_zero, other.is_zero),
            z3.And(
                self.sign_bit == other.sign_bit,
                self.exponent == other.exponent,
            ),
        )

    def has_same_sign(self, other: "FPVariable") -> z3.BoolRef:
        return z3.Or(
            z3.And(self.is_zero, other.is_zero),
            z3.And(self.is_positive, other.is_positive),
            z3.And(self.is_negative, other.is_negative),
        )

    def interpretation(self, model: z3.ModelRef) -> str:
        exponent = model[self.exponent]
        assert exponent is not None
        if exponent == ZERO_EXPONENT:
            return f"{self.name}: 0"
        sign_bit = model[self.sign_bit]
        sign = "?" if sign_bit is None else "-" if sign_bit else "+"
        return f"{self.name}: {sign}2^{exponent}"


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

    ######################################################## IDENTITY PROPERTIES

    # If both addends are zero, the sum is zero.
    solver.add(z3.Implies(z3.And(x.is_zero, y.is_zero), s.is_zero))

    # If either addend is zero, the sum equals the other one.
    solver.add(z3.Implies(x.is_zero, s.is_equal(y)))
    solver.add(z3.Implies(y.is_zero, s.is_equal(x)))

    ############################################################## SIGN ANALYSIS

    # If both addends have the same sign, the sum has the same sign.
    solver.add(z3.Implies(z3.And(x.is_positive, y.is_positive), s.is_positive))
    solver.add(z3.Implies(z3.And(x.is_negative, y.is_negative), s.is_negative))

    # If the addends have different exponents, the sum is
    # nonzero and has the same sign as the larger addend.
    solver.add(z3.Implies(x.exponent != y.exponent, z3.Not(s.is_zero)))
    solver.add(z3.Implies(x.exponent > y.exponent, s.has_same_sign(x)))
    solver.add(z3.Implies(x.exponent < y.exponent, s.has_same_sign(y)))

    ###################################################### EXPONENT UPPER BOUNDS

    max_exponent = z3.If(x.exponent > y.exponent, x.exponent, y.exponent)

    # Addition can only increase the exponent of the larger addend by one.
    solver.add(s.exponent <= max_exponent + 1)

    # If the addends have different signs, the exponent cannot increase.
    solver.add(z3.Or(x.has_same_sign(y), s.exponent <= max_exponent))

    # If the larger addend is a power of two and its exponent exceeds the
    # smaller addend by at least two, the exponent of the sum cannot increase.
    solver.add(
        z3.Implies(
            z3.Or(
                z3.And(x.exponent > y.exponent + 1, x.is_pow2),
                z3.And(x.exponent + 1 < y.exponent, y.is_pow2),
            ),
            s.exponent <= max_exponent,
        )
    )

    # If both addends are powers of two with the same sign and
    # different exponents, the exponent of the sum cannot increase.
    solver.add(
        z3.Implies(
            z3.And(
                x.is_pow2,
                y.is_pow2,
                x.has_same_sign(y),
                x.exponent != y.exponent,
            ),
            s.exponent <= max_exponent,
        )
    )

    ###################################################### EXPONENT LOWER BOUNDS

    # If the sum is nonzero, it is at least as large
    # as the bit one past the end of the larger addend.
    solver.add(z3.Or(s.is_zero, s.exponent >= max_exponent - PRECISION))

    # Moreover, if both addends have the same exponent, the
    # sum is at least as large as the least significant bit.
    solver.add(
        z3.Implies(
            x.exponent == y.exponent,
            z3.Or(s.is_zero, s.exponent > max_exponent - PRECISION),
        )
    )

    # If the exponent of the larger addend exceeds the smaller addend
    # by at least two, the exponent of the sum can only decrease by one.
    solver.add(
        z3.Implies(
            x.exponent > y.exponent + 1,
            s.exponent >= x.exponent - 1,
        )
    )
    solver.add(
        z3.Implies(
            x.exponent + 1 < y.exponent,
            s.exponent >= y.exponent - 1,
        )
    )

    # If both addends have the same sign, the exponent cannot decrease.
    solver.add(z3.Implies(x.has_same_sign(y), s.exponent >= max_exponent))

    return s


def is_ulp_nonoverlapping(x: FPVariable, y: FPVariable) -> z3.BoolRef:
    """
    Construct a Z3 formula that determines whether two FPVariables are
    ulp-nonoverlapping and sorted in descending order by magnitude.
    """
    return z3.Or(
        y.is_zero,
        y.exponent < x.exponent - PRECISION,
        z3.And(y.exponent == x.exponent - PRECISION, y.is_pow2),
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
