#!/usr/bin/env python3

import os
import random
import subprocess
import time
import z3


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

    sx: z3.BitVecRef = x_sign_bit
    sy: z3.BitVecRef = y_sign_bit
    ss: z3.BitVecRef = s_sign_bit
    se: z3.BitVecRef = e_sign_bit

    ex: z3.BitVecRef = z3.Concat(exponent_padding, x_exponent) - exponent_bias
    ey: z3.BitVecRef = z3.Concat(exponent_padding, y_exponent) - exponent_bias
    es: z3.BitVecRef = z3.Concat(exponent_padding, s_exponent) - exponent_bias
    ee: z3.BitVecRef = z3.Concat(exponent_padding, e_exponent) - exponent_bias

    p: z3.BitVecRef = z3.BitVecVal(precision, promoted_exponent_width)
    one: z3.BitVecRef = z3.BitVecVal(1, promoted_exponent_width)
    two: z3.BitVecRef = z3.BitVecVal(2, promoted_exponent_width)
    three: z3.BitVecRef = z3.BitVecVal(3, promoted_exponent_width)

    lemmas: dict[str, z3.BoolRef] = {}

    ############################################################################

    case_0pp: z3.BoolRef = z3.And(is_pos_zero(x), is_pos_zero(y))
    lemmas["0PP"] = z3.Implies(case_0pp, z3.And(is_pos_zero(s), is_pos_zero(e)))

    case_0pp: z3.BoolRef = z3.And(is_pos_zero(x), is_neg_zero(y))
    lemmas["0PN"] = z3.Implies(case_0pp, z3.And(is_pos_zero(s), is_pos_zero(e)))

    case_0pp: z3.BoolRef = z3.And(is_neg_zero(x), is_pos_zero(y))
    lemmas["0NP"] = z3.Implies(case_0pp, z3.And(is_pos_zero(s), is_pos_zero(e)))

    case_0pp: z3.BoolRef = z3.And(is_neg_zero(x), is_neg_zero(y))
    lemmas["0NN"] = z3.Implies(case_0pp, z3.And(is_neg_zero(s), is_pos_zero(e)))

    case_0x: z3.BoolRef = z3.And(z3.Not(z3.fpIsZero(x)), z3.fpIsZero(y))
    lemmas["0X"] = z3.Implies(case_0x, z3.And(s == x, is_pos_zero(e)))

    case_0y: z3.BoolRef = z3.And(z3.fpIsZero(x), z3.Not(z3.fpIsZero(y)))
    lemmas["0Y"] = z3.Implies(case_0y, z3.And(s == y, is_pos_zero(e)))

    ############################################################################

    case_1x: z3.BoolRef = z3.And(ex > ey + (p + one), z3.Not(z3.fpIsZero(y)))
    lemmas["1X"] = z3.Implies(case_1x, z3.And(s == x, e == y))

    case_1y: z3.BoolRef = z3.And(ex + (p + one) < ey, z3.Not(z3.fpIsZero(x)))
    lemmas["1Y"] = z3.Implies(case_1y, z3.And(s == y, e == x))

    ############################################################################

    case_2xs: z3.BoolRef = z3.And(
        ex == ey + (p + one), sx == sy, z3.Not(z3.fpIsZero(y))
    )
    lemmas["2XS"] = z3.Implies(case_2xs, z3.And(s == x, e == y))

    case_2ys: z3.BoolRef = z3.And(
        ex + (p + one) == ey, sx == sy, z3.Not(z3.fpIsZero(x))
    )
    lemmas["2YS"] = z3.Implies(case_2ys, z3.And(s == y, e == x))

    case_2xd: z3.BoolRef = z3.And(
        ex == ey + (p + one), sx != sy, z3.Not(z3.fpIsZero(y))
    )
    lemmas["2XD"] = z3.Implies(
        case_2xd,
        z3.Or(
            z3.And(
                ss == sx,
                es == ex - one,
                se != sy,
                ee >= ey - (p - one),
                ee <= ey - one,
            ),
            z3.And(s == x, e == y),
        ),
    )

    case_2yd: z3.BoolRef = z3.And(
        ex + (p + one) == ey, sx != sy, z3.Not(z3.fpIsZero(x))
    )
    lemmas["2YD"] = z3.Implies(
        case_2yd,
        z3.Or(
            z3.And(
                ss == sy,
                es == ey - one,
                se != sx,
                ee >= ex - (p - one),
                ee <= ex - one,
            ),
            z3.And(s == y, e == x),
        ),
    )

    ############################################################################

    case_3xs: z3.BoolRef = z3.And(ex == ey + p, sx == sy, z3.Not(z3.fpIsZero(y)))
    lemmas["3XS"] = z3.Implies(
        case_3xs,
        z3.Or(
            z3.And(s == x, e == y),
            z3.And(
                ss == sx,
                es >= ex,
                es <= ex + one,
                se != sy,
                ee >= ey - (p - one),
                ee <= ey,
            ),
        ),
    )

    case_3ys: z3.BoolRef = z3.And(ex + p == ey, sx == sy, z3.Not(z3.fpIsZero(x)))
    lemmas["3YS"] = z3.Implies(
        case_3ys,
        z3.Or(
            z3.And(s == y, e == x),
            z3.And(
                ss == sy,
                es >= ey,
                es <= ey + one,
                se != sx,
                ee >= ex - (p - one),
                ee <= ex,
            ),
        ),
    )

    case_3xd: z3.BoolRef = z3.And(ex == ey + p, sx != sy, z3.Not(z3.fpIsZero(y)))
    lemmas["3XD"] = z3.Implies(
        case_3xd,
        z3.Or(
            z3.And(s == x, e == y),
            z3.And(
                ss == sx,
                es == ex - one,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sx,
                es == ex - one,
                se == sy,
                ee >= ey - (p - one),
                ee <= ey - two,
            ),
            z3.And(
                ss == sx,
                es == ex - one,
                se != sy,
                ee >= ey - (p - one),
                ee <= ey - one,
            ),
            z3.And(
                ss == sx,
                es == ex,
                se != sy,
                ee >= ey - (p - one),
                ee <= ey,
            ),
        ),
    )

    case_3yd: z3.BoolRef = z3.And(ex + p == ey, sx != sy, z3.Not(z3.fpIsZero(x)))
    lemmas["3YD"] = z3.Implies(
        case_3yd,
        z3.Or(
            z3.And(s == y, e == x),
            z3.And(
                ss == sy,
                es == ey - one,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sy,
                es == ey - one,
                se == sx,
                ee >= ex - (p - one),
                ee <= ex - two,
            ),
            z3.And(
                ss == sy,
                es == ey - one,
                se != sx,
                ee >= ex - (p - one),
                ee <= ex - one,
            ),
            z3.And(
                ss == sy,
                es == ey,
                se != sx,
                ee >= ex - (p - one),
                ee <= ex,
            ),
        ),
    )

    ############################################################################

    case_4xs: z3.BoolRef = z3.And(
        ex == ey + (p - one), sx == sy, z3.Not(z3.fpIsZero(y))
    )
    lemmas["4XS"] = z3.Implies(
        case_4xs,
        z3.Or(
            z3.And(
                ss == sx,
                es >= ex,
                es <= ex + one,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sx,
                es >= ex,
                es <= ex + one,
                ee >= ey - (p - one),
                ee <= ey - one,
            ),
        ),
    )

    case_4ys: z3.BoolRef = z3.And(
        ex + (p - one) == ey, sx == sy, z3.Not(z3.fpIsZero(x))
    )
    lemmas["4YS"] = z3.Implies(
        case_4ys,
        z3.Or(
            z3.And(
                ss == sy,
                es >= ey,
                es <= ey + one,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sy,
                es >= ey,
                es <= ey + one,
                ee >= ex - (p - one),
                ee <= ex - one,
            ),
        ),
    )

    case_4xd: z3.BoolRef = z3.And(
        ex == ey + (p - one), sx != sy, z3.Not(z3.fpIsZero(y))
    )
    lemmas["4XD"] = z3.Implies(
        case_4xd,
        z3.Or(
            z3.And(
                ss == sx,
                es >= ex - one,
                es <= ex,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sx,
                es == ex - one,
                ee >= ey - (p - one),
                ee <= ey - two,
            ),
            z3.And(
                ss == sx,
                es == ex,
                ee >= ey - (p - one),
                ee <= ey - one,
            ),
        ),
    )

    case_4yd: z3.BoolRef = z3.And(
        ex + (p - one) == ey, sx != sy, z3.Not(z3.fpIsZero(x))
    )
    lemmas["4YD"] = z3.Implies(
        case_4yd,
        z3.Or(
            z3.And(
                ss == sy,
                es >= ey - one,
                es <= ey,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sy,
                es == ey - one,
                ee >= ex - (p - one),
                ee <= ex - two,
            ),
            z3.And(
                ss == sy,
                es == ey,
                ee >= ex - (p - one),
                ee <= ex - one,
            ),
        ),
    )

    ############################################################################

    case_5xs: z3.BoolRef = z3.And(
        ex == ey + (p - two), sx == sy, z3.Not(z3.fpIsZero(y))
    )
    lemmas["5XS"] = z3.Implies(
        case_5xs,
        z3.Or(
            z3.And(
                ss == sx,
                es >= ex,
                es <= ex + one,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sx,
                es == ex,
                se == sy,
                ee >= ey - (p - one),
                ee <= ey - two,
            ),
            z3.And(
                ss == sx,
                es == ex + one,
                se == sy,
                ee >= ey - (p - one),
                ee <= ey - one,
            ),
            z3.And(
                ss == sx,
                es >= ex,
                es <= ex + one,
                se != sy,
                ee >= ey - (p - one),
                ee <= ey - two,
            ),
        ),
    )

    case_5ys: z3.BoolRef = z3.And(
        ex + (p - two) == ey, sx == sy, z3.Not(z3.fpIsZero(x))
    )
    lemmas["5YS"] = z3.Implies(
        case_5ys,
        z3.Or(
            z3.And(
                ss == sy,
                es >= ey,
                es <= ey + one,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sy,
                es == ey,
                se == sx,
                ee >= ex - (p - one),
                ee <= ex - two,
            ),
            z3.And(
                ss == sy,
                es == ey + one,
                se == sx,
                ee >= ex - (p - one),
                ee <= ex - one,
            ),
            z3.And(
                ss == sy,
                es >= ey,
                es <= ey + one,
                se != sx,
                ee >= ex - (p - one),
                ee <= ex - two,
            ),
        ),
    )

    case_5xd: z3.BoolRef = z3.And(
        ex == ey + (p - two), sx != sy, z3.Not(z3.fpIsZero(y))
    )
    lemmas["5XD"] = z3.Implies(
        case_5xd,
        z3.Or(
            z3.And(
                ss == sx,
                es >= ex - one,
                es <= ex,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sx,
                es == ex - one,
                ee >= ey - (p - one),
                ee <= ey - three,
            ),
            z3.And(
                ss == sx,
                es == ex,
                ee >= ey - (p - one),
                ee <= ey - two,
            ),
        ),
    )

    case_5yd: z3.BoolRef = z3.And(
        ex + (p - two) == ey, sx != sy, z3.Not(z3.fpIsZero(x))
    )
    lemmas["5YD"] = z3.Implies(
        case_5yd,
        z3.Or(
            z3.And(
                ss == sy,
                es >= ey - one,
                es <= ey,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sy,
                es == ey - one,
                ee >= ex - (p - one),
                ee <= ex - three,
            ),
            z3.And(
                ss == sy,
                es == ey,
                ee >= ex - (p - one),
                ee <= ex - two,
            ),
        ),
    )

    ############################################################################

    case_6xs: z3.BoolRef = z3.And(two <= ex - ey, ex - ey <= p - three, sx == sy)
    lemmas["6XS"] = z3.Implies(
        case_6xs,
        z3.Or(
            z3.And(
                ss == sx,
                es >= ex,
                es <= ex + one,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sx,
                es == ex,
                ee >= ey - (p - one),
                ee <= ey - (p - (ex - ey)),
            ),
            z3.And(
                ss == sx,
                es == ex + one,
                ee >= ey - (p - one),
                ee <= ey - (p - ((ex - ey) + one)),
            ),
        ),
    )

    case_6ys: z3.BoolRef = z3.And(two <= ey - ex, ey - ex <= p - three, sx == sy)
    lemmas["6YS"] = z3.Implies(
        case_6ys,
        z3.Or(
            z3.And(
                ss == sy,
                es >= ey,
                es <= ey + one,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sy,
                es == ey,
                ee >= ex - (p - one),
                ee <= ex - (p - (ey - ex)),
            ),
            z3.And(
                ss == sy,
                es == ey + one,
                ee >= ex - (p - one),
                ee <= ex - (p - ((ey - ex) + one)),
            ),
        ),
    )

    case_6xd: z3.BoolRef = z3.And(two <= ex - ey, ex - ey <= p - three, sx != sy)
    lemmas["6XD"] = z3.Implies(
        case_6xd,
        z3.Or(
            z3.And(
                ss == sx,
                es >= ex - one,
                es <= ex,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sx,
                es == ex - one,
                ee >= ey - (p - one),
                ee <= ey - (p - ((ex - ey) - one)),
            ),
            z3.And(
                ss == sx,
                es == ex,
                ee >= ey - (p - one),
                ee <= ey - (p - (ex - ey)),
            ),
        ),
    )

    case_6yd: z3.BoolRef = z3.And(two <= ey - ex, ey - ex <= p - three, sx != sy)
    lemmas["6YD"] = z3.Implies(
        case_6yd,
        z3.Or(
            z3.And(
                ss == sy,
                es >= ey - one,
                es <= ey,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sy,
                es == ey - one,
                ee >= ex - (p - one),
                ee <= ex - (p - ((ey - ex) - one)),
            ),
            z3.And(
                ss == sy,
                es == ey,
                ee >= ex - (p - one),
                ee <= ex - (p - (ey - ex)),
            ),
        ),
    )

    ############################################################################

    case_7xs: z3.BoolRef = z3.And(ex == ey + one, sx == sy)
    lemmas["7XS"] = z3.Implies(
        case_7xs,
        z3.Or(
            z3.And(
                ss == sx,
                es >= ex,
                es <= ex + one,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sx,
                es == ex,
                ee == ey - (p - one),
            ),
            z3.And(
                ss == sx,
                es == ex + one,
                ee >= ey - (p - one),
                ee <= ey - (p - two),
            ),
        ),
    )

    case_7ys: z3.BoolRef = z3.And(ex + one == ey, sx == sy)
    lemmas["7YS"] = z3.Implies(
        case_7ys,
        z3.Or(
            z3.And(
                ss == sy,
                es >= ey,
                es <= ey + one,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sy,
                es == ey,
                ee == ex - (p - one),
            ),
            z3.And(
                ss == sy,
                es == ey + one,
                ee >= ex - (p - one),
                ee <= ex - (p - two),
            ),
        ),
    )

    case_7xd: z3.BoolRef = z3.And(ex == ey + one, sx != sy)
    lemmas["7XD"] = z3.Implies(
        case_7xd,
        z3.Or(
            z3.And(
                ss == sx,
                es >= ex - p,
                es <= ex,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sx,
                es == ex,
                ee == ey - (p - one),
            ),
        ),
    )

    case_7yd: z3.BoolRef = z3.And(ex + one == ey, sx != sy)
    lemmas["7YD"] = z3.Implies(
        case_7yd,
        z3.Or(
            z3.And(
                ss == sy,
                es >= ey - p,
                es <= ey,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sy,
                es == ey,
                ee == ex - (p - one),
            ),
        ),
    )

    ############################################################################

    case_8s: z3.BoolRef = z3.And(
        ex == ey, sx == sy, z3.Not(z3.fpIsZero(x)), z3.Not(z3.fpIsZero(y))
    )
    lemmas["8S"] = z3.Implies(
        case_8s,
        z3.Or(
            z3.And(
                ss == sx,
                es == ex + one,
                is_pos_zero(e),
            ),
            z3.And(
                ss == sx,
                es == ex + one,
                ee == ex - (p - one),
            ),
        ),
    )

    case_8d: z3.BoolRef = z3.And(
        ex == ey, sx != sy, z3.Not(z3.fpIsZero(x)), z3.Not(z3.fpIsZero(y))
    )
    lemmas["8D"] = z3.Implies(
        case_8d,
        z3.Or(
            z3.And(
                is_pos_zero(s),
                is_pos_zero(e),
            ),
            z3.And(
                es >= ex - (p - one),
                es <= ex - one,
                is_pos_zero(e),
            ),
        ),
    )

    ############################################################################

    for name, lemma in lemmas.items():
        assert prove(solver, name + suffix, lemma)


if __name__ == "__main__":
    main(8, 16, 24, "-F32")
    main(11, 16, 53, "-F64")


"""
def num_leading_zeroes(b: z3.BitVecRef, result_width: int) -> z3.BitVecRef:
    result = z3.BitVecVal(0, result_width)
    for i in range(b.size()):
        zeros = z3.BitVecVal(0, i + 1)
        result = z3.If(
            z3.Extract(b.size() - 1, b.size() - (i + 1), b) == zeros,
            z3.BitVecVal(i + 1, result_width),
            result,
        )
    return result


def num_leading_ones(b: z3.BitVecRef, result_width: int) -> z3.BitVecRef:
    result = z3.BitVecVal(0, result_width)
    for i in range(b.size()):
        ones = z3.BitVecVal(2 ** (i + 1) - 1, i + 1)
        result = z3.If(
            z3.Extract(b.size() - 1, b.size() - (i + 1), b) == ones,
            z3.BitVecVal(i + 1, result_width),
            result,
        )
    return result


def final_zero_index(b: z3.BitVecRef, result_width: int) -> z3.BitVecRef:
    result = z3.BitVecVal(b.size(), result_width)
    for i in range(b.size()):
        ones = z3.BitVecVal(2 ** (i + 1) - 1, i + 1)
        result = z3.If(
            z3.Extract(i, 0, b) == ones,
            z3.BitVecVal(b.size() - (i + 1), result_width),
            result,
        )
    return result


def final_one_index(b: z3.BitVecRef, result_width: int) -> z3.BitVecRef:
    result = z3.BitVecVal(b.size(), result_width)
    for i in range(b.size()):
        zeros = z3.BitVecVal(0, i + 1)
        result = z3.If(
            z3.Extract(i, 0, b) == zeros,
            z3.BitVecVal(b.size() - (i + 1), result_width),
            result,
        )
    return result





ZERO_BV: z3.BitVecRef = z3.BitVecVal(0, PROMOTED_EXPONENT_WIDTH)
ONE_BV: z3.BitVecRef = z3.BitVecVal(1, PROMOTED_EXPONENT_WIDTH)
PRECISION_BV: z3.BitVecRef = z3.BitVecVal(PRECISION, PROMOTED_EXPONENT_WIDTH)
PRECISION_MINUS_ONE_BV: z3.BitVecRef = z3.BitVecVal(
    PRECISION - 1, PROMOTED_EXPONENT_WIDTH
)
PRECISION_PLUS_ONE_BV: z3.BitVecRef = z3.BitVecVal(
    PRECISION + 1, PROMOTED_EXPONENT_WIDTH
)

z_x = num_leading_zeroes(x_mantissa, PROMOTED_EXPONENT_WIDTH)
z_y = num_leading_zeroes(y_mantissa, PROMOTED_EXPONENT_WIDTH)
z_s = num_leading_zeroes(s_mantissa, PROMOTED_EXPONENT_WIDTH)
z_e = num_leading_zeroes(e_mantissa, PROMOTED_EXPONENT_WIDTH)

o_x = num_leading_ones(x_mantissa, PROMOTED_EXPONENT_WIDTH)
o_y = num_leading_ones(y_mantissa, PROMOTED_EXPONENT_WIDTH)
o_s = num_leading_ones(s_mantissa, PROMOTED_EXPONENT_WIDTH)
o_e = num_leading_ones(e_mantissa, PROMOTED_EXPONENT_WIDTH)

m_x = final_zero_index(x_mantissa, PROMOTED_EXPONENT_WIDTH)
m_y = final_zero_index(y_mantissa, PROMOTED_EXPONENT_WIDTH)
m_s = final_zero_index(s_mantissa, PROMOTED_EXPONENT_WIDTH)
m_e = final_zero_index(e_mantissa, PROMOTED_EXPONENT_WIDTH)

n_x = final_one_index(x_mantissa, PROMOTED_EXPONENT_WIDTH)
n_y = final_one_index(y_mantissa, PROMOTED_EXPONENT_WIDTH)
n_s = final_one_index(s_mantissa, PROMOTED_EXPONENT_WIDTH)
n_e = final_one_index(e_mantissa, PROMOTED_EXPONENT_WIDTH)


lemmas: dict[str, z3.BoolRef] = {}

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


case_0a = z3.fpIsZero(y)
case_0b = z3.fpIsZero(x)
case_1a = e_x - PRECISION_PLUS_ONE_BV > e_y
case_1b = e_x < e_y - PRECISION_PLUS_ONE_BV
case_2as = z3.And(e_x - PRECISION_PLUS_ONE_BV == e_y, s_x == s_y)
case_2bs = z3.And(e_x == e_y - PRECISION_PLUS_ONE_BV, s_x == s_y)
case_2ad_n = z3.And(e_x - PRECISION_PLUS_ONE_BV == e_y, s_x != s_y, n_x != ZERO_BV)
case_2bd_n = z3.And(e_x == e_y - PRECISION_PLUS_ONE_BV, s_x != s_y, n_y != ZERO_BV)
case_2ad_zz = z3.And(
    e_x - PRECISION_PLUS_ONE_BV == e_y, s_x != s_y, n_x == ZERO_BV, n_y == ZERO_BV
)
case_2bd_zz = z3.And(
    e_x == e_y - PRECISION_PLUS_ONE_BV, s_x != s_y, n_x == ZERO_BV, n_y == ZERO_BV
)
case_2ad_zn = z3.And(
    e_x - PRECISION_PLUS_ONE_BV == e_y, s_x != s_y, n_x == ZERO_BV, n_y != ZERO_BV
)
case_2bd_zn = z3.And(
    e_x == e_y - PRECISION_PLUS_ONE_BV, s_x != s_y, n_x != ZERO_BV, n_y == ZERO_BV
)
case_3as_g = z3.And(
    e_x - PRECISION_BV == e_y, s_x == s_y, o_x != PRECISION_MINUS_ONE_BV
)
case_3as_s = z3.And(
    e_x - PRECISION_BV == e_y,
    s_x == s_y,
    o_x == PRECISION_MINUS_ONE_BV,
    z3.Not(z3.fpIsZero(y)),
)
case_3bs_g = z3.And(
    e_x == e_y - PRECISION_BV, s_x == s_y, o_y != PRECISION_MINUS_ONE_BV
)
case_3bs_s = z3.And(
    e_x == e_y - PRECISION_BV,
    s_x == s_y,
    o_y == PRECISION_MINUS_ONE_BV,
    z3.Not(z3.fpIsZero(x)),
)
case_3ad = z3.And(e_x - PRECISION_BV == e_y, s_x != s_y)
case_3bd = z3.And(e_x == e_y - PRECISION_BV, s_x != s_y)
case_4as = z3.And(e_x - PRECISION_BV < e_y, e_x - ONE_BV > e_y, s_x == s_y)
case_4as_n = z3.And(case_4as, e_x - (o_x + ONE_BV) > e_y)
case_4bs = z3.And(e_x > e_y - PRECISION_BV, e_x < e_y - ONE_BV, s_x == s_y)
case_4bs_n = z3.And(case_4bs, e_x < e_y - (o_y + ONE_BV))
case_4ad = z3.And(e_x - PRECISION_BV < e_y, e_x - ONE_BV > e_y, s_x != s_y)
case_4bd = z3.And(e_x > e_y - PRECISION_BV, e_x < e_y - ONE_BV, s_x != s_y)
case_5as = z3.And(e_x - ONE_BV == e_y, s_x == s_y)
case_5bs = z3.And(e_x == e_y - ONE_BV, s_x == s_y)
case_5ad = z3.And(e_x - ONE_BV == e_y, s_x != s_y)
case_5bd = z3.And(e_x == e_y - ONE_BV, s_x != s_y)
case_6s_x = z3.And(
    e_x == e_y,
    s_x == s_y,
    z3.Xor(n_x == PRECISION_MINUS_ONE_BV, n_y == PRECISION_MINUS_ONE_BV),
)
case_6s_n = z3.And(
    e_x == e_y,
    s_x == s_y,
    z3.Not(z3.Xor(n_x == PRECISION_MINUS_ONE_BV, n_y == PRECISION_MINUS_ONE_BV)),
)
case_6d = z3.And(e_x == e_y, s_x != s_y)


lemmas["0A-S"] = z3.Implies(case_0a, z3.fpEQ(s, x))  # cannot be strengthened
lemmas["0A-E"] = z3.Implies(case_0a, z3.fpIsZero(e))  # cannot be strengthened
lemmas["0B-S"] = z3.Implies(case_0b, z3.fpEQ(s, y))  # cannot be strengthened
lemmas["0B-E"] = z3.Implies(case_0b, z3.fpIsZero(e))  # cannot be strengthened

lemmas["1A-S"] = z3.Implies(case_1a, s == x)  # cannot be strengthened
lemmas["1A-E"] = z3.Implies(case_1a, z3.fpEQ(e, y))  # cannot be strengthened
lemmas["1B-S"] = z3.Implies(case_1b, s == y)  # cannot be strengthened
lemmas["1B-E"] = z3.Implies(case_1b, z3.fpEQ(e, x))  # cannot be strengthened

lemmas["2AS-S"] = z3.Implies(case_1a, s == x)  # cannot be strengthened
lemmas["2AS-E"] = z3.Implies(case_1a, z3.fpEQ(e, y))  # cannot be strengthened
lemmas["2BS-S"] = z3.Implies(case_1b, s == y)  # cannot be strengthened
lemmas["2BS-E"] = z3.Implies(case_1b, z3.fpEQ(e, x))  # cannot be strengthened
lemmas["2AD-N-S"] = z3.Implies(case_2ad_n, s == x)  # cannot be strengthened
lemmas["2AD-N-E"] = z3.Implies(case_2ad_n, z3.fpEQ(e, y))  # cannot be strengthened
lemmas["2BD-N-S"] = z3.Implies(case_2bd_n, s == y)  # cannot be strengthened
lemmas["2BD-N-E"] = z3.Implies(case_2bd_n, z3.fpEQ(e, x))  # cannot be strengthened
lemmas["2AD-ZZ-S"] = z3.Implies(case_2ad_zz, s == x)  # cannot be strengthened
lemmas["2AD-ZZ-E"] = z3.Implies(case_2ad_zz, z3.fpEQ(e, y))  # cannot be strengthened
lemmas["2BD-ZZ-S"] = z3.Implies(case_2bd_zz, s == y)  # cannot be strengthened
lemmas["2BD-ZZ-E"] = z3.Implies(case_2bd_zz, z3.fpEQ(e, x))  # cannot be strengthened
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
lemmas["2AD-ZN-SE"] = z3.Implies(case_2ad_zn, s_e == s_x)
lemmas["2AD-ZN-UBEE"] = z3.Implies(
    case_2ad_zn, e_e < e_y
)  # cannot be strengthened by a constant
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
lemmas["2BD-ZN-SE"] = z3.Implies(case_2bd_zn, s_e == s_y)
lemmas["2BD-ZN-UBEE"] = z3.Implies(
    case_2bd_zn, e_e < e_x
)  # cannot be strengthened by a constant

lemmas["3AS-G-SS"] = z3.Implies(case_3as_g, s_s == s_x)  # cannot be strengthened
lemmas["3AS-G-ES"] = z3.Implies(case_3as_g, e_s == e_x)
lemmas["3AS-S-SS"] = z3.Implies(case_3as_s, s_s == s_x)  # cannot be strengthened
lemmas["3AS-S-ES"] = z3.Implies(case_3as_s, e_s == e_x + ONE_BV)
lemmas["3BS-G-SS"] = z3.Implies(case_3bs_g, s_s == s_y)  # cannot be strengthened
lemmas["3BS-G-ES"] = z3.Implies(case_3bs_g, e_s == e_y)
lemmas["3BS-S-SS"] = z3.Implies(case_3bs_s, s_s == s_y)  # cannot be strengthened
lemmas["3BS-S-ES"] = z3.Implies(case_3bs_s, e_s == e_y + ONE_BV)
lemmas["3AD-SS"] = z3.Implies(case_3ad, s_s == s_x)  # cannot be strengthened
lemmas["3AD-ES"] = z3.Implies(case_3ad, z3.Or(e_s == e_x, e_s == e_x - ONE_BV))
lemmas["3BD-SS"] = z3.Implies(case_3bd, s_s == s_y)  # cannot be strengthened
lemmas["3BD-ES"] = z3.Implies(case_3bd, z3.Or(e_s == e_y, e_s == e_y - ONE_BV))

lemmas["4AS-SS"] = z3.Implies(case_4as, s_s == s_x)  # cannot be strengthened
lemmas["4AS-ES"] = z3.Implies(case_4as, z3.Or(e_s == e_x, e_s == e_x + ONE_BV))
lemmas["4AS-N-ES"] = z3.Implies(case_4as_n, e_s == e_x)
lemmas["4BS-SS"] = z3.Implies(case_4bs, s_s == s_y)  # cannot be strengthened
lemmas["4BS-ES"] = z3.Implies(case_4bs, z3.Or(e_s == e_y, e_s == e_y + ONE_BV))
lemmas["4BS-N-ES"] = z3.Implies(case_4bs_n, e_s == e_y)
lemmas["4AD-SS"] = z3.Implies(case_4ad, s_s == s_x)  # cannot be strengthened
lemmas["4AD-ES"] = z3.Implies(case_4ad, z3.Or(e_s == e_x, e_s == e_x - ONE_BV))
lemmas["4BD-SS"] = z3.Implies(case_4bd, s_s == s_y)  # cannot be strengthened
lemmas["4BD-ES"] = z3.Implies(case_4bd, z3.Or(e_s == e_y, e_s == e_y - ONE_BV))

lemmas["5AS-SS"] = z3.Implies(case_5as, s_s == s_x)  # cannot be strengthened
lemmas["5AS-ES"] = z3.Implies(case_5as, z3.Or(e_s == e_x, e_s == e_x + ONE_BV))
lemmas["5BS-SS"] = z3.Implies(case_5bs, s_s == s_y)  # cannot be strengthened
lemmas["5BS-ES"] = z3.Implies(case_5bs, z3.Or(e_s == e_y, e_s == e_y + ONE_BV))
lemmas["5AD-SS"] = z3.Implies(case_5ad, s_s == s_x)  # cannot be strengthened
lemmas["5AD-ES"] = z3.Implies(case_5ad, z3.And(e_s <= e_x, e_s >= e_x - PRECISION_BV))
lemmas["5BD-SS"] = z3.Implies(case_5bd, s_s == s_y)  # cannot be strengthened
lemmas["5BD-ES"] = z3.Implies(case_5bd, z3.And(e_s <= e_y, e_s >= e_y - PRECISION_BV))

lemmas["6S-X-SS"] = z3.Implies(case_6s_x, z3.And(s_s == s_x, s_s == s_y))
lemmas["6S-X-ES"] = z3.Implies(
    case_6s_x, z3.And(e_s == e_x + ONE_BV, e_s == e_y + ONE_BV)
)
# In case 6S-X, s_e is difficult to determine a priori
# because it depends on round-to-nearest-even tie breaking.
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
lemmas["6S-N-SS"] = z3.Implies(case_6s_n, z3.And(s_s == s_x, s_s == s_y))
lemmas["6S-N-ES"] = z3.Implies(
    case_6s_n, z3.Or(z3.fpIsZero(s), z3.And(e_s == e_x + ONE_BV, e_s == e_y + ONE_BV))
)
lemmas["6S-N-E"] = z3.Implies(case_6s_n, z3.fpIsZero(e))  # cannot be strengthened
lemmas["6D-UBES"] = z3.Implies(
    case_6d,
    z3.And(
        z3.Or(z3.fpIsZero(s), e_s < e_x - z_x, e_s < e_y - z_y),
        z3.Or(z3.fpIsZero(s), e_s < e_x - o_x, e_s < e_y - o_y),
    ),
)  # cannot be strengthened by a constant
lemmas["6D-E"] = z3.Implies(case_6d, z3.fpIsZero(e))  # cannot be strengthened


expensive_lemmas: set[str] = {
    "G-LBES",
    "G-LBEE",
    "G-UBEE",
    "G-NOC-E",
    "6S-X-E",
    "6S-N-E",
    "6D-E",
}

for name, lemma in lemmas.items():
    if name not in expensive_lemmas:
        assert prove(solver, name, lemma)
"""
