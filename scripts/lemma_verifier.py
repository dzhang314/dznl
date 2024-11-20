#!/usr/bin/env python3

import operator
import os
import random
import subprocess
import time
import z3

from fp_lemmas import (
    count_leading_zeros,
    count_leading_ones,
    count_trailing_zeros,
    count_trailing_ones,
    two_sum_lemmas,
)


ONE: z3.BitVecNumRef = z3.BitVecVal(1, 1)
RNE: z3.FPRMRef = z3.RoundNearestTiesToEven()


def is_pos_zero(x: z3.FPRef) -> z3.BoolRef:
    return z3.And(z3.fpIsZero(x), z3.fpIsPositive(x))


def is_neg_zero(x: z3.FPRef) -> z3.BoolRef:
    return z3.And(z3.fpIsZero(x), z3.fpIsNegative(x))


def prove(solver: z3.Solver, name: str, claim: z3.BoolRef) -> bool:

    # Write current solver state and claim to SMT-LIB2 file.
    solver.push()
    solver.add(z3.Not(claim))
    os.makedirs("smt2", exist_ok=True)
    filename: str = os.path.join("smt2", name + ".smt2")
    with open(filename, "w") as f:
        f.write("(set-logic QF_BVFP)\n")
        f.write(solver.to_smt2())
    solver.pop()

    # Invoke external solvers to prove or refute the claim.
    external_solvers: list[str] = ["bitwuzla", "cvc5", "mathsat", "z3"]
    random.shuffle(external_solvers)
    external_processes: list[tuple[str, int, subprocess.Popen[str]]] = []
    for external_solver in external_solvers:
        start: int = time.perf_counter_ns()
        process = subprocess.Popen(
            [external_solver, filename], stdout=subprocess.PIPE, text=True
        )
        external_processes.append((external_solver, start, process))

    # Wait for the first solver to finish and check its result.
    while True:
        for external_solver, start, process in external_processes:
            if process.poll() is not None:
                stop: int = time.perf_counter_ns()
                elapsed: float = (stop - start) / 1.0e9
                assert process.returncode == 0
                stdout: str
                stderr: str
                stdout, stderr = process.communicate()
                assert stderr is None
                for _, _, other_process in external_processes:
                    other_process.kill()
                solver_len: int = max(map(len, external_solvers))
                solver_name: str = external_solver.rjust(solver_len)
                if stdout == "unsat\n":
                    print(f"{solver_name} proved {name} in {elapsed} seconds.")
                    return True
                elif stdout == "sat\n":
                    print(f"{solver_name} refuted {name} in {elapsed} seconds.")
                    return False
                else:
                    print(
                        f"When attempting to prove {name}, {external_solver}",
                        f"returned {stdout} in {elapsed} seconds.",
                    )
                    assert False
        # Sleep for a short time to avoid busy waiting. (Even the fastest SMT
        # solvers take a few milliseconds, so 0.1ms is a reasonable interval.)
        time.sleep(0.0001)


def main(
    exponent_width: int,
    promoted_exponent_width: int,
    precision: int,
    suffix: str = "",
) -> None:

    mantissa_width: int = precision - 1
    exponent_padding: z3.BitVecNumRef = z3.BitVecVal(
        0, promoted_exponent_width - exponent_width
    )
    exponent_bias: z3.BitVecNumRef = z3.BitVecVal(
        2 ** (exponent_width - 1) - 1, promoted_exponent_width
    )

    x_sign_bit: z3.BitVecRef = z3.BitVec("x_sign_bit", 1)
    x_exponent: z3.BitVecRef = z3.BitVec("x_exponent", exponent_width)
    x_mantissa: z3.BitVecRef = z3.BitVec("x_mantissa", mantissa_width)
    x: z3.FPRef = z3.fpFP(x_sign_bit, x_exponent, x_mantissa)

    y_sign_bit: z3.BitVecRef = z3.BitVec("y_sign_bit", 1)
    y_exponent: z3.BitVecRef = z3.BitVec("y_exponent", exponent_width)
    y_mantissa: z3.BitVecRef = z3.BitVec("y_mantissa", mantissa_width)
    y: z3.FPRef = z3.fpFP(y_sign_bit, y_exponent, y_mantissa)

    s_sign_bit: z3.BitVecRef = z3.BitVec("s_sign_bit", 1)
    s_exponent: z3.BitVecRef = z3.BitVec("s_exponent", exponent_width)
    s_mantissa: z3.BitVecRef = z3.BitVec("s_mantissa", mantissa_width)
    s: z3.FPRef = z3.fpFP(s_sign_bit, s_exponent, s_mantissa)

    e_sign_bit: z3.BitVecRef = z3.BitVec("e_sign_bit", 1)
    e_exponent: z3.BitVecRef = z3.BitVec("e_exponent", exponent_width)
    e_mantissa: z3.BitVecRef = z3.BitVec("e_mantissa", mantissa_width)
    e: z3.FPRef = z3.fpFP(e_sign_bit, e_exponent, e_mantissa)

    solver: z3.Solver = z3.SolverFor("QF_BVFP")

    solver.add(z3.Not(z3.fpIsInf(x)))
    solver.add(z3.Not(z3.fpIsNaN(x)))
    solver.add(z3.Not(z3.fpIsSubnormal(x)))

    solver.add(z3.Not(z3.fpIsInf(y)))
    solver.add(z3.Not(z3.fpIsNaN(y)))
    solver.add(z3.Not(z3.fpIsSubnormal(y)))

    solver.add(z3.Not(z3.fpIsInf(s)))
    solver.add(z3.Not(z3.fpIsNaN(s)))
    solver.add(z3.Not(z3.fpIsSubnormal(s)))

    solver.add(z3.Not(z3.fpIsInf(e)))
    solver.add(z3.Not(z3.fpIsNaN(e)))
    solver.add(z3.Not(z3.fpIsSubnormal(e)))

    solver.add(s == z3.fpAdd(RNE, x, y))
    x_prime: z3.FPRef = z3.fpSub(RNE, s, y)
    y_prime: z3.FPRef = z3.fpSub(RNE, s, x_prime)
    x_err: z3.FPRef = z3.fpSub(RNE, x, x_prime)
    y_err: z3.FPRef = z3.fpSub(RNE, y, y_prime)
    solver.add(e == z3.fpAdd(RNE, x_err, y_err))

    max_idx: int = mantissa_width - 1
    x_leading_bit: z3.BoolRef = z3.Extract(max_idx, max_idx, x_mantissa) == ONE
    y_leading_bit: z3.BoolRef = z3.Extract(max_idx, max_idx, y_mantissa) == ONE
    s_leading_bit: z3.BoolRef = z3.Extract(max_idx, max_idx, s_mantissa) == ONE
    e_leading_bit: z3.BoolRef = z3.Extract(max_idx, max_idx, e_mantissa) == ONE

    x_trailing_bit: z3.BoolRef = z3.Extract(0, 0, x_mantissa) == ONE
    y_trailing_bit: z3.BoolRef = z3.Extract(0, 0, y_mantissa) == ONE
    s_trailing_bit: z3.BoolRef = z3.Extract(0, 0, s_mantissa) == ONE
    e_trailing_bit: z3.BoolRef = z3.Extract(0, 0, e_mantissa) == ONE

    lemmas: dict[str, z3.BoolRef] = two_sum_lemmas(
        x,
        y,
        s,
        e,
        x_sign_bit,
        y_sign_bit,
        s_sign_bit,
        e_sign_bit,
        x_leading_bit,
        y_leading_bit,
        s_leading_bit,
        e_leading_bit,
        x_trailing_bit,
        y_trailing_bit,
        s_trailing_bit,
        e_trailing_bit,
        z3.Concat(exponent_padding, x_exponent) - exponent_bias,
        z3.Concat(exponent_padding, y_exponent) - exponent_bias,
        z3.Concat(exponent_padding, s_exponent) - exponent_bias,
        z3.Concat(exponent_padding, e_exponent) - exponent_bias,
        z3.If(
            x_leading_bit,
            count_leading_ones(x_mantissa, promoted_exponent_width),
            count_leading_zeros(x_mantissa, promoted_exponent_width),
        ),
        z3.If(
            y_leading_bit,
            count_leading_ones(y_mantissa, promoted_exponent_width),
            count_leading_zeros(y_mantissa, promoted_exponent_width),
        ),
        z3.If(
            s_leading_bit,
            count_leading_ones(s_mantissa, promoted_exponent_width),
            count_leading_zeros(s_mantissa, promoted_exponent_width),
        ),
        z3.If(
            e_leading_bit,
            count_leading_ones(e_mantissa, promoted_exponent_width),
            count_leading_zeros(e_mantissa, promoted_exponent_width),
        ),
        z3.If(
            x_trailing_bit,
            count_trailing_ones(x_mantissa, promoted_exponent_width),
            count_trailing_zeros(x_mantissa, promoted_exponent_width),
        ),
        z3.If(
            y_trailing_bit,
            count_trailing_ones(y_mantissa, promoted_exponent_width),
            count_trailing_zeros(y_mantissa, promoted_exponent_width),
        ),
        z3.If(
            s_trailing_bit,
            count_trailing_ones(s_mantissa, promoted_exponent_width),
            count_trailing_zeros(s_mantissa, promoted_exponent_width),
        ),
        z3.If(
            e_trailing_bit,
            count_trailing_ones(e_mantissa, promoted_exponent_width),
            count_trailing_zeros(e_mantissa, promoted_exponent_width),
        ),
        z3.fpIsZero,
        z3.fpIsPositive,
        z3.fpIsNegative,
        operator.eq,
        z3.BitVecVal(precision, promoted_exponent_width),
        z3.BitVecVal(1, promoted_exponent_width),
        z3.BitVecVal(2, promoted_exponent_width),
        z3.BitVecVal(3, promoted_exponent_width),
    )

    for name, lemma in lemmas.items():
        assert prove(solver, name + suffix, lemma)


if __name__ == "__main__":
    main(8, 16, 24, "-F32")
    main(11, 16, 53, "-F64")


"""
lemmas["G-LBZ"] = z_x >= ZERO_BV
lemmas["G-UBZ"] = z_x < PRECISION_BV
lemmas["G-LBO"] = o_x >= ZERO_BV
lemmas["G-UBO"] = o_x < PRECISION_BV
lemmas["G-LBN"] = n_x >= ZERO_BV
lemmas["G-UBN"] = n_x < PRECISION_BV
lemmas["G-RZO"] = z3.Xor(z_x == ZERO_BV, o_x == ZERO_BV)
lemmas["G-RZN-G"] = z3.Implies(z_x < PRECISION_MINUS_ONE_BV, z_x < n_x)
lemmas["G-RZN-S"] = z3.Implies(z_x == PRECISION_MINUS_ONE_BV, n_x == ZERO_BV)
lemmas["G-RON"] = o_x <= n_x

lemmas["G-LBES"] = z3.Or(
    z3.fpIsZero(s),
    e_s - n_s >= e_x - n_x,
    e_s - n_s >= e_y - n_y,
)

lemmas["G-UBES"] = z3.Or(e_s <= e_x + ONE_BV, e_s <= e_y + ONE_BV)

lemmas["G-LBEE"] = z3.Or(
    z3.fpIsZero(e),
    e_e - n_e >= e_x - n_x,
    e_e - n_e >= e_y - n_y,
)

lemmas["G-UBEE"] = z3.Or(
    z3.fpIsZero(e),
    e_e < e_s - PRECISION_BV,
    z3.And(e_e == e_s - PRECISION_BV, n_e == ZERO_BV),
)

lemmas["GA-NO-S"] = z3.Implies(
    z3.And(
        e_x - (z_x + ONE_BV) > e_y,
        z3.Or(s_x != s_y, z_x >= ONE_BV),
        z_x < PRECISION_MINUS_ONE_BV,
    ),
    z3.And(s_s == s_x, e_s == e_x, z_s >= z_x - ONE_BV),
)  # likely cannot be strengthened

lemmas["GB-NO-S"] = z3.Implies(
    z3.And(
        e_x < e_y - (z_y + ONE_BV),
        z3.Or(s_x != s_y, z_y >= ONE_BV),
        z_y < PRECISION_MINUS_ONE_BV,
    ),
    z3.And(s_s == s_y, e_s == e_y, z_s >= z_y - ONE_BV),
)  # likely cannot be strengthened

lemmas["G-NOC-E"] = z3.Implies(
    z3.Or(  # None of the following strict inequalities can be weakened.
        z3.And(e_x - n_x > e_y, e_x - PRECISION_BV < e_y - n_y),
        z3.And(e_x - (o_x + ONE_BV) > e_y, e_x - PRECISION_BV < e_y - n_y),
        z3.And(e_x < e_y - n_y, e_x - n_x > e_y - PRECISION_BV),
        z3.And(e_x < e_y - (o_y + ONE_BV), e_x - n_x > e_y - PRECISION_BV),
    ),
    z3.fpIsZero(e),
)

case_2ad_zn = z3.And(
    e_x - PRECISION_PLUS_ONE_BV == e_y, s_x != s_y, n_x == ZERO_BV, n_y != ZERO_BV
)
case_2bd_zn = z3.And(
    e_x == e_y - PRECISION_PLUS_ONE_BV, s_x != s_y, n_x != ZERO_BV, n_y == ZERO_BV
)
case_6s_x = z3.And(
    e_x == e_y,
    s_x == s_y,
    z3.Xor(n_x == PRECISION_MINUS_ONE_BV, n_y == PRECISION_MINUS_ONE_BV),
)
case_6d = z3.And(e_x == e_y, s_x != s_y)

lemmas["2AD-ZN-S"] = z3.Implies(
    case_2ad_zn,
    z3.And(
        s_s == s_x,
        e_s == e_x - ONE_BV,
        z_s == ZERO_BV,
        o_s == PRECISION_MINUS_ONE_BV,
        n_s == PRECISION_MINUS_ONE_BV,
    ),
)  # cannot be strengthened
lemmas["2BD-ZN-S"] = z3.Implies(
    case_2bd_zn,
    z3.And(
        s_s == s_y,
        e_s == e_y - ONE_BV,
        z_s == ZERO_BV,
        o_s == PRECISION_MINUS_ONE_BV,
        n_s == PRECISION_MINUS_ONE_BV,
    ),
)  # cannot be strengthened

lemmas["6S-X-E"] = z3.Implies(
    case_6s_x,
    z3.And(
        e_e == e_x - PRECISION_MINUS_ONE_BV,
        e_e == e_y - PRECISION_MINUS_ONE_BV,
        z_e == PRECISION_MINUS_ONE_BV,
        o_e == ZERO_BV,
        n_e == ZERO_BV,
    ),
)  # likely cannot be strengthened
lemmas["6D-UBES"] = z3.Implies(
    case_6d,
    z3.And(
        z3.Or(z3.fpIsZero(s), e_s < e_x - z_x, e_s < e_y - z_y),
        z3.Or(z3.fpIsZero(s), e_s < e_x - o_x, e_s < e_y - o_y),
    ),
)  # cannot be strengthened by a constant
"""
