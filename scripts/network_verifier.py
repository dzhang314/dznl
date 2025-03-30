#!/usr/bin/env python3

import z3

from se_lemmas import two_sum_se_lemmas
from setz_lemmas import two_sum_setz_lemmas
from seltzo_lemmas import two_sum_seltzo_lemmas
from sys import argv
from time import perf_counter_ns


GLOBAL_PRECISION: z3.ArithRef = z3.Int("PRECISION")
GLOBAL_ZERO_EXPONENT: z3.ArithRef = z3.Int("ZERO_EXPONENT")
GLOBAL_MANTISSA_WIDTH: z3.ArithRef = GLOBAL_PRECISION - 1


def decide(
    solver: z3.Solver,
    claim: z3.BoolRef,
    name: str,
) -> z3.ModelRef | None:
    start: int = perf_counter_ns()
    result: z3.CheckSatResult = solver.check(z3.Not(claim))
    stop: int = perf_counter_ns()
    elapsed: float = (stop - start) / 1.0e9
    if result == z3.unsat:
        if name:
            print(f"Verified {name} in {elapsed:.3f} seconds.")
        return None
    elif result == z3.unknown:
        if name:
            print(f"Failed to determine {name} in {elapsed:.3f} seconds.")
        return None
    elif result == z3.sat:
        if name:
            print(f"Refuted {name} in {elapsed:.3f} seconds.")
        return solver.model()
    else:
        raise RuntimeError(f"SMT solver returned unknown result {result}.")


class FPVariable(object):

    def __init__(
        self,
        solver: z3.Solver,
        name: str,
    ) -> None:
        self.name: str = name
        self.sign_bit: z3.BoolRef = z3.Bool(name + "_sign_bit")
        self.leading_bit: z3.BoolRef = z3.Bool(name + "_leading_bit")
        self.trailing_bit: z3.BoolRef = z3.Bool(name + "_trailing_bit")
        self.exponent: z3.ArithRef = z3.Int(name + "_exponent")
        self.num_leading_bits: z3.ArithRef = z3.Int(name + "_num_leading_bits")
        self.num_trailing_bits: z3.ArithRef = z3.Int(name + "_num_trailing_bits")

        # We model a hypothetical floating-point datatype with infinite
        # exponent range, eliminating the possibility of overflow or underflow.
        # This means that all results proven in this model assume that no
        # overflow or underflow occurs when performing the actual computation.

        # We do not consider infinities or NaNs in this model, so all
        # floating-point numbers are either positive, negative, or zero.

        # When analyzing floating-point accumulation networks,
        # only relative exponent values matter, not absolute values.
        # We can set the zero point anywhere without loss of generality.
        solver.add(self.exponent >= GLOBAL_ZERO_EXPONENT)
        self.is_zero: z3.BoolRef = self.exponent == GLOBAL_ZERO_EXPONENT

        solver.add(self.num_leading_bits > 0)
        solver.add(self.num_trailing_bits > 0)
        solver.add(
            z3.Implies(
                self.is_zero,
                z3.And(
                    z3.Not(self.leading_bit),
                    z3.Not(self.trailing_bit),
                    self.num_leading_bits == GLOBAL_MANTISSA_WIDTH,
                    self.num_trailing_bits == GLOBAL_MANTISSA_WIDTH,
                ),
            )
        )
        solver.add(
            z3.Implies(
                self.leading_bit == self.trailing_bit,
                z3.Or(
                    self.num_leading_bits + self.num_trailing_bits
                    < GLOBAL_MANTISSA_WIDTH,
                    z3.And(
                        self.num_leading_bits == GLOBAL_MANTISSA_WIDTH,
                        self.num_trailing_bits == GLOBAL_MANTISSA_WIDTH,
                    ),
                ),
            )
        )
        solver.add(
            z3.Implies(
                self.leading_bit != self.trailing_bit,
                z3.Or(
                    self.num_leading_bits + self.num_trailing_bits
                    < GLOBAL_MANTISSA_WIDTH - 1,
                    self.num_leading_bits + self.num_trailing_bits
                    == GLOBAL_MANTISSA_WIDTH,
                ),
            )
        )

    def maybe_equal(self, other: "FPVariable") -> z3.BoolRef:
        return z3.Or(
            z3.And(self.is_zero, other.is_zero),
            z3.And(
                self.sign_bit == other.sign_bit,
                self.leading_bit == other.leading_bit,
                self.trailing_bit == other.trailing_bit,
                self.exponent == other.exponent,
                self.num_leading_bits == other.num_leading_bits,
                self.num_trailing_bits == other.num_trailing_bits,
            ),
        )

    def is_power_of_two(self) -> z3.BoolRef:
        return z3.And(
            z3.Not(self.is_zero),
            z3.Not(self.leading_bit),
            z3.Not(self.trailing_bit),
            self.num_leading_bits == GLOBAL_MANTISSA_WIDTH,
            self.num_trailing_bits == GLOBAL_MANTISSA_WIDTH,
        )

    def s_dominates(self, other: "FPVariable") -> z3.BoolRef:
        ntz: z3.ArithRef = z3.If(
            self.trailing_bit, z3.IntVal(0), self.num_trailing_bits
        )
        return z3.Or(
            other.is_zero,
            self.exponent >= other.exponent + (GLOBAL_PRECISION - ntz),
        )

    def p_dominates(self, other: "FPVariable") -> z3.BoolRef:
        return z3.Or(
            other.is_zero,
            self.exponent >= other.exponent + GLOBAL_PRECISION,
        )

    def ulp_dominates(self, other: "FPVariable") -> z3.BoolRef:
        return z3.Or(
            other.is_zero,
            self.exponent > other.exponent + (GLOBAL_PRECISION - 1),
            z3.And(
                self.exponent == other.exponent + (GLOBAL_PRECISION - 1),
                other.is_power_of_two(),
            ),
        )

    def qd_dominates(self, other: "FPVariable") -> z3.BoolRef:
        return z3.Or(
            other.is_zero,
            self.exponent > other.exponent + GLOBAL_PRECISION,
            z3.And(
                self.exponent == other.exponent + GLOBAL_PRECISION,
                other.is_power_of_two(),
            ),
        )

    def two_sum_dominates(self, other: "FPVariable") -> z3.BoolRef:
        return z3.Or(
            other.is_zero,
            self.exponent > other.exponent + (GLOBAL_PRECISION + 1),
            z3.And(
                self.exponent == other.exponent + (GLOBAL_PRECISION + 1),
                z3.Or(
                    self.sign_bit == other.sign_bit,
                    z3.Not(self.is_power_of_two()),
                    other.is_power_of_two(),
                ),
            ),
            z3.And(
                self.exponent == other.exponent + GLOBAL_PRECISION,
                other.is_power_of_two(),
                z3.Not(self.trailing_bit),
                z3.Or(self.sign_bit == other.sign_bit, z3.Not(self.is_power_of_two())),
            ),
        )

    def is_smaller_than(
        self, other: "FPVariable", magnitude: int | z3.ArithRef
    ) -> z3.BoolRef:
        return z3.Or(self.is_zero, self.exponent + magnitude < other.exponent)


def two_sum(
    solver: z3.Solver,
    x: FPVariable,
    y: FPVariable,
    sum_name: str,
    err_name: str,
) -> tuple[FPVariable, FPVariable]:
    """
    Create two new FPVariables that represent the floating-point sum and error
    computed by the TwoSum algorithm applied to two existing FPVariables.
    """
    s = FPVariable(solver, sum_name)
    e = FPVariable(solver, err_name)

    if "--se" in argv:
        lemmas: dict[str, z3.BoolRef] = two_sum_se_lemmas(
            x,
            y,
            s,
            e,
            x.sign_bit,
            y.sign_bit,
            s.sign_bit,
            e.sign_bit,
            x.exponent,
            y.exponent,
            s.exponent,
            e.exponent,
            lambda v: v.is_zero,
            lambda v: z3.Not(v.sign_bit),
            lambda v: v.sign_bit,
            lambda v, w: v.maybe_equal(w),
            GLOBAL_PRECISION,
            z3.IntVal(1),
            z3.IntVal(2),
        )
    else:
        lemmas: dict[str, z3.BoolRef] = two_sum_setz_lemmas(
            x,
            y,
            s,
            e,
            x.sign_bit,
            y.sign_bit,
            s.sign_bit,
            e.sign_bit,
            x.exponent,
            y.exponent,
            s.exponent,
            e.exponent,
            z3.If(x.trailing_bit, z3.IntVal(0), x.num_trailing_bits),
            z3.If(y.trailing_bit, z3.IntVal(0), y.num_trailing_bits),
            z3.If(s.trailing_bit, z3.IntVal(0), s.num_trailing_bits),
            z3.If(e.trailing_bit, z3.IntVal(0), e.num_trailing_bits),
            lambda v: v.is_zero,
            lambda v: z3.Not(v.sign_bit),
            lambda v: v.sign_bit,
            lambda v, w: v.maybe_equal(w),
            GLOBAL_PRECISION,
            z3.IntVal(1),
            z3.IntVal(2),
            z3.IntVal(3),
        )
        if "--setz" not in argv:
            lemmas |= two_sum_seltzo_lemmas(
                x,
                y,
                s,
                e,
                x.sign_bit,
                y.sign_bit,
                s.sign_bit,
                e.sign_bit,
                x.leading_bit,
                y.leading_bit,
                s.leading_bit,
                e.leading_bit,
                x.trailing_bit,
                y.trailing_bit,
                s.trailing_bit,
                e.trailing_bit,
                x.exponent,
                y.exponent,
                s.exponent,
                e.exponent,
                x.num_leading_bits,
                y.num_leading_bits,
                s.num_leading_bits,
                e.num_leading_bits,
                x.num_trailing_bits,
                y.num_trailing_bits,
                s.num_trailing_bits,
                e.num_trailing_bits,
                lambda v: v.is_zero,
                lambda v: z3.Not(v.sign_bit),
                lambda v: v.sign_bit,
                lambda v, w: v.maybe_equal(w),
                GLOBAL_PRECISION,
                z3.IntVal(1),
                z3.IntVal(2),
                z3.IntVal(3),
            )

    for claim in lemmas.values():
        solver.add(claim)

    return (s, e)


CHECK_FAST_TWO_SUM: bool = "--check-fast-two-sum" in argv


def fast_two_sum(
    solver: z3.Solver,
    x: FPVariable,
    y: FPVariable,
    sum_name: str,
    err_name: str,
) -> tuple[FPVariable, FPVariable]:
    if CHECK_FAST_TWO_SUM:
        decide(
            solver,
            z3.Or(x.is_zero, y.is_zero, x.exponent >= y.exponent),
            f"FastTwoSum({x.name}, {y.name})",
        )
    return two_sum(solver, x, y, sum_name, err_name)


def bool_value(var: z3.BoolRef) -> bool:
    if z3.is_true(var):
        return True
    elif z3.is_false(var):
        return False
    else:
        raise RuntimeError(f"{var} does not have a concrete Boolean value.")


def float_str(
    model: z3.ModelRef,
    var: FPVariable,
    *,
    exponent_delta: int = 0,
    head_length: int = 0,
) -> str:
    sign_str: str = "-" if bool_value(model[var.sign_bit]) else "+"
    exponent: int = model[var.exponent].as_long()
    zero_exponent: int = model[GLOBAL_ZERO_EXPONENT].as_long()
    if exponent == zero_exponent:
        return f"{sign_str}0"

    exponent += exponent_delta
    precision: int = model[GLOBAL_PRECISION].as_long()
    mantissa: list[str] = ["?" for _ in range(precision - 1)]

    leading_bit: bool = bool_value(model[var.leading_bit])
    leading_char: str = "1" if leading_bit else "0"
    terminator: str = "0" if leading_bit else "1"
    num_leading_bits: int = model[var.num_leading_bits].as_long()
    for i in range(num_leading_bits):
        assert mantissa[i] in {"?", leading_char}
        mantissa[i] = leading_char
    if num_leading_bits < precision - 1:
        assert mantissa[num_leading_bits] in {"?", terminator}
        mantissa[num_leading_bits] = terminator

    trailing_bit: bool = bool_value(model[var.trailing_bit])
    trailing_char: str = "1" if trailing_bit else "0"
    terminator: str = "0" if trailing_bit else "1"
    num_trailing_bits: int = model[var.num_trailing_bits].as_long()
    for i in range(1, num_trailing_bits + 1):
        assert mantissa[-i] == "?" or mantissa[-i] == trailing_char
        mantissa[-i] = trailing_char
    if num_trailing_bits < precision - 1:
        assert mantissa[-num_trailing_bits - 1] in {"?", terminator}
        mantissa[-num_trailing_bits - 1] = terminator

    head_str: str = f"{sign_str}2^{exponent}".ljust(head_length)
    mantissa_str: str = "1." + "".join(mantissa)
    return f"{head_str} * {mantissa_str}"


def print_model(model: z3.ModelRef, variables: list[list[FPVariable]]) -> None:
    # TODO: Handle the case where every variable is zero.
    zero_exponent: int = model[GLOBAL_ZERO_EXPONENT].as_long()
    min_exponent: int = min(
        model[var.exponent].as_long()
        for row in variables
        for var in row
        if model[var.exponent].as_long() != zero_exponent
    )
    head_length: int = 3 + max(
        len(str(model[var.exponent].as_long() - min_exponent))
        for row in variables
        for var in row
    )
    for row in variables:
        for var in row:
            s: str = float_str(
                model, var, exponent_delta=-min_exponent, head_length=head_length
            )
            print(f"    {var.name}: {s}")
        print()
    return None


def prove(
    solver: z3.Solver,
    claim: z3.BoolRef,
    name: str,
    variables: list[list[FPVariable]],
) -> None:
    counterexample: z3.ModelRef | None = decide(solver, claim, name)
    if counterexample is not None:
        print_model(counterexample, variables)


def verify_joldes_2017_algorithm_4() -> None:
    solver: z3.Solver = z3.SolverFor("QF_LIA")

    a0 = FPVariable(solver, "a0")
    b0 = FPVariable(solver, "b0")
    c0 = FPVariable(solver, "c0")

    solver.add(a0.two_sum_dominates(c0))

    a1, b1 = two_sum(solver, a0, b0, "a1", "b1")
    b2, c2 = two_sum(solver, b1, c0, "b2", "c2")
    a3, b3 = fast_two_sum(solver, a1, b2, "a3", "b3")

    variables = [
        [a0, b0, a1, b1],
        [b1, c0, b2, c2],
        [a1, b2, a3, b3],
    ]

    # SE: 2p - 4
    # SETZ: 2p - 3
    prove(solver, a3.two_sum_dominates(b3), "A4N", variables)
    prove(
        solver,
        c2.is_smaller_than(a3, GLOBAL_PRECISION + GLOBAL_PRECISION - 2),
        "A4E",
        variables,
    )


def verify_joldes_2017_algorithm_6() -> None:
    solver: z3.Solver = z3.SolverFor("QF_LIA")

    a0 = FPVariable(solver, "a0")
    b0 = FPVariable(solver, "b0")
    c0 = FPVariable(solver, "c0")
    d0 = FPVariable(solver, "d0")

    solver.add(a0.two_sum_dominates(c0))
    solver.add(b0.two_sum_dominates(d0))

    a1, b1 = two_sum(solver, a0, b0, "a1", "b1")
    c1, d1 = two_sum(solver, c0, d0, "c1", "d1")
    b2, c2 = two_sum(solver, b1, c1, "b2", "c2")
    a3, b3 = fast_two_sum(solver, a1, b2, "a3", "b3")
    b4, d4 = fast_two_sum(solver, b3, d1, "b4", "d4")
    a5, b5 = fast_two_sum(solver, a3, b4, "a5", "b5")
    c5, d5 = fast_two_sum(solver, c2, d4, "c5", "d5")

    variables = [
        [a0, b0, a1, b1],
        [c0, d0, c1, d1],
        [b1, c1, b2, c2],
        [a1, b2, a3, b3],
        [b3, d1, b4, d4],
        [a3, b4, a5, b5],
        [c2, d4, c5, d5],
    ]

    # SE: 2p - 7
    # SETZ: 2p - 4
    prove(solver, a5.two_sum_dominates(b5), "A6N", variables)
    prove(
        solver,
        c5.is_smaller_than(a5, GLOBAL_PRECISION + GLOBAL_PRECISION - 3),
        "A6E",
        variables,
    )


def verify_zhang_addition() -> None:
    solver: z3.Solver = z3.SolverFor("QF_LIA")

    a0 = FPVariable(solver, "a0")
    b0 = FPVariable(solver, "b0")
    c0 = FPVariable(solver, "c0")
    d0 = FPVariable(solver, "d0")

    solver.add(a0.two_sum_dominates(c0))
    solver.add(b0.two_sum_dominates(d0))

    a1, b1 = two_sum(solver, a0, b0, "a1", "b1")
    c1, d1 = two_sum(solver, c0, d0, "c1", "d1")
    a2, c2 = fast_two_sum(solver, a1, c1, "a2", "c2")
    b2, d2 = fast_two_sum(solver, b1, d1, "b2", "d2")
    b3, c3 = two_sum(solver, b2, c2, "b3", "c3")
    a4, b4 = fast_two_sum(solver, a2, b3, "a4", "b4")
    c4, d4 = fast_two_sum(solver, c3, d2, "c4", "d4")

    variables = [
        [a0, b0, a1, b1],
        [c0, d0, c1, d1],
        [a1, c1, a2, c2],
        [b1, d1, b2, d2],
        [b2, c2, b3, c3],
        [a2, b3, a4, b4],
        [c3, d2, c4, d4],
    ]

    # SE: 2p - 6
    # SETZ: 2p - 3
    prove(solver, a4.two_sum_dominates(b4), "ZAN", variables)
    prove(
        solver,
        c4.is_smaller_than(a4, GLOBAL_PRECISION + GLOBAL_PRECISION - 2),
        "ZAE",
        variables,
    )


if __name__ == "__main__":
    verify_joldes_2017_algorithm_4()
    verify_joldes_2017_algorithm_6()
    verify_zhang_addition()
