import z3


PRECISION: int = 53
MAX_EXPONENT: int = 1023
MIN_NORMALIZED_EXPONENT: int = -1022
ZERO_EXPONENT: int = MIN_NORMALIZED_EXPONENT - 1


class FPVariable(object):

    def __init__(self, solver: z3.Solver, name: str):
        self.name: str = name
        self.sign_bit: z3.BoolRef = z3.Bool(name + "_sign_bit")
        self.exponent: z3.ArithRef = z3.Int(name + "_exponent")

        # We consider only computations without overflow or underflow.
        solver.add(self.exponent >= ZERO_EXPONENT)
        solver.add(self.exponent <= MAX_EXPONENT)

        # We assume that zero is the only subnormal number.
        self.is_zero: z3.BoolRef = self.exponent == ZERO_EXPONENT

        self.is_positive: z3.BoolRef = z3.And(
            self.exponent >= MIN_NORMALIZED_EXPONENT, z3.Not(self.sign_bit)
        )
        self.is_negative: z3.BoolRef = z3.And(
            self.exponent >= MIN_NORMALIZED_EXPONENT, self.sign_bit
        )

    def is_equal(self, other: "FPVariable") -> z3.BoolRef:
        return z3.Or(
            z3.And(self.is_zero, other.is_zero),
            z3.And(self.sign_bit == other.sign_bit, self.exponent == other.exponent),
        )

    def has_same_sign(self, other: "FPVariable") -> z3.BoolRef:
        return z3.Or(
            z3.And(self.is_zero, other.is_zero),
            z3.And(self.is_positive, other.is_positive),
            z3.And(self.is_negative, other.is_negative),
        )

    def interpretation(self, model: z3.ModelRef) -> str:
        sign_bit = model[self.sign_bit]
        assert sign_bit is not None
        exponent = model[self.exponent]
        assert exponent is not None
        if exponent == ZERO_EXPONENT:
            return f"{self.name}: 0"
        else:
            sign = "-" if sign_bit else "+"
            return f"{self.name}: {sign}2^{exponent}"


def fp_sum(solver: z3.Solver, x: FPVariable, y: FPVariable, name: str) -> FPVariable:
    """
    Create a new FPVariable that represents the floating-point sum of two
    existing FPVariables.
    """
    s = FPVariable(solver, name)

    # If both addends are zero, the sum is zero.
    solver.add(z3.Implies(z3.And(x.is_zero, y.is_zero), s.is_zero))

    # If both addends have the same sign, the sum has the same sign.
    solver.add(z3.Implies(z3.And(x.is_positive, y.is_positive), s.is_positive))
    solver.add(z3.Implies(z3.And(x.is_negative, y.is_negative), s.is_negative))

    # If either addend is zero, the sum equals the other addend.
    solver.add(z3.Implies(x.is_zero, s.is_equal(y)))
    solver.add(z3.Implies(y.is_zero, s.is_equal(x)))

    # If the addends have different exponents, the sum is
    # nonzero and has the same sign as the larger addend.
    solver.add(z3.Implies(x.exponent != y.exponent, z3.Not(s.is_zero)))
    solver.add(z3.Implies(x.exponent > y.exponent, s.has_same_sign(x)))
    solver.add(z3.Implies(x.exponent < y.exponent, s.has_same_sign(y)))

    # The exponent of the sum is at most one
    # plus the exponent of the larger addend.
    solver.add(z3.Or(s.exponent <= x.exponent + 1, s.exponent <= y.exponent + 1))

    # If the addends have the same sign, then the exponent of
    # the sum is at least the exponent of the larger addend.
    solver.add(z3.Implies(x.has_same_sign(y), s.exponent >= x.exponent))
    solver.add(z3.Implies(x.has_same_sign(y), s.exponent >= y.exponent))

    # If the exponents of the addends are non-adjacent, the
    # exponent of the sum is adjacent to the larger addend.
    solver.add(z3.Implies(x.exponent > y.exponent + 1, s.exponent >= x.exponent - 1))
    solver.add(z3.Implies(x.exponent + 1 < y.exponent, s.exponent >= y.exponent - 1))

    # If the sum is nonzero, then it is at least as large
    # as the least significant bit of the larger addend.
    solver.add(z3.Or(s.is_zero, s.exponent >= x.exponent - PRECISION))
    solver.add(z3.Or(s.is_zero, s.exponent >= y.exponent - PRECISION))

    return s


def fp_two_sum(
    solver: z3.Solver, x: FPVariable, y: FPVariable, sum_name: str, err_name: str
) -> tuple[FPVariable, FPVariable]:
    """
    Create two new FPVariables that represent the floating-point sum and error
    term computed by the TwoSum algorithm applied to two existing FPVariables.
    """
    s = fp_sum(solver, x, y, sum_name)
    e = FPVariable(solver, err_name)

    # If the error term is nonzero, it is smaller
    # than the least significant bit of the sum.
    solver.add(z3.Or(e.is_zero, e.exponent <= s.exponent - PRECISION))

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


def is_normalized(xs: list[FPVariable]) -> z3.BoolRef:
    if len(xs) <= 1:
        return z3.BoolVal(True)
    return z3.Or(
        z3.And(*(x.is_zero for x in xs)),
        z3.And(xs[0].exponent >= xs[1].exponent + 53, is_normalized(xs[1:])),
    )
