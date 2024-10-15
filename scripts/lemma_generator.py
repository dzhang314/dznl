import os
import time
import z3


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


def last_nonzero_bit(b: z3.BitVecRef, result_width: int) -> z3.BitVecRef:
    result = z3.BitVecVal(b.size(), result_width)
    for i in range(b.size()):
        zeros = z3.BitVecVal(0, i + 1)
        result = z3.If(
            z3.Extract(i, 0, b) == zeros,
            z3.BitVecVal(b.size() - (i + 1), result_width),
            result,
        )
    return result


def prove(solver: z3.Solver, name: str, claim: z3.BoolRef):
    solver.push()
    solver.add(z3.Not(claim))
    os.makedirs("smt2", exist_ok=True)
    with open(os.path.join("smt2", name + ".smt2"), "w") as f:
        f.write("(set-logic QF_BVFP)\n")
        f.write(solver.to_smt2())
    solver.pop()
    # start = time.perf_counter_ns()
    # result = solver.check(z3.Not(claim))
    # stop = time.perf_counter_ns()
    # if result == z3.unsat:
    #     print(f"Verified {name} in {(stop - start) / 1e9:.6f} seconds.")
    #     return True
    # else:
    #     assert result == z3.sat
    #     print(f"Refuted {name} in {(stop - start) / 1e9:.6f} seconds.")
    #     return False


EXPONENT_WIDTH: int = 8
PROMOTED_EXPONENT_WIDTH: int = 16
EXPONENT_PADDING: z3.BitVecRef = z3.BitVecVal(
    0, PROMOTED_EXPONENT_WIDTH - EXPONENT_WIDTH
)
EXPONENT_BIAS: z3.BitVecRef = z3.BitVecVal(
    2 ** (EXPONENT_WIDTH - 1) - 1, PROMOTED_EXPONENT_WIDTH
)

PRECISION: int = 24
MANTISSA_WIDTH: int = PRECISION - 1
ZERO_BV: z3.BitVecRef = z3.BitVecVal(0, PROMOTED_EXPONENT_WIDTH)
PRECISION_BV: z3.BitVecRef = z3.BitVecVal(PRECISION, PROMOTED_EXPONENT_WIDTH)
PRECISION_MINUS_ONE_BV: z3.BitVecRef = z3.BitVecVal(
    PRECISION - 1, PROMOTED_EXPONENT_WIDTH
)

solver = z3.SolverFor("QF_BVFP")

x_sign_bit = z3.BitVec("x_sign_bit", 1)
x_exponent = z3.BitVec("x_exponent", EXPONENT_WIDTH)
x_mantissa = z3.BitVec("x_mantissa", MANTISSA_WIDTH)
x = z3.fpFP(x_sign_bit, x_exponent, x_mantissa)
solver.add(z3.Not(z3.fpIsInf(x)))
solver.add(z3.Not(z3.fpIsNaN(x)))
solver.add(z3.Not(z3.fpIsSubnormal(x)))

y_sign_bit = z3.BitVec("y_sign_bit", 1)
y_exponent = z3.BitVec("y_exponent", EXPONENT_WIDTH)
y_mantissa = z3.BitVec("y_mantissa", MANTISSA_WIDTH)
y = z3.fpFP(y_sign_bit, y_exponent, y_mantissa)
solver.add(z3.Not(z3.fpIsInf(y)))
solver.add(z3.Not(z3.fpIsNaN(y)))
solver.add(z3.Not(z3.fpIsSubnormal(y)))

s_sign_bit = z3.BitVec("s_sign_bit", 1)
s_exponent = z3.BitVec("s_exponent", EXPONENT_WIDTH)
s_mantissa = z3.BitVec("s_mantissa", MANTISSA_WIDTH)
s = z3.fpFP(s_sign_bit, s_exponent, s_mantissa)
solver.add(z3.Not(z3.fpIsInf(s)))
solver.add(z3.Not(z3.fpIsNaN(s)))
solver.add(z3.Not(z3.fpIsSubnormal(s)))

e_sign_bit = z3.BitVec("e_sign_bit", 1)
e_exponent = z3.BitVec("e_exponent", EXPONENT_WIDTH)
e_mantissa = z3.BitVec("e_mantissa", MANTISSA_WIDTH)
e = z3.fpFP(e_sign_bit, e_exponent, e_mantissa)
solver.add(z3.Not(z3.fpIsInf(e)))
solver.add(z3.Not(z3.fpIsNaN(e)))
solver.add(z3.Not(z3.fpIsSubnormal(e)))

solver.add(s == x + y)
x_prime = s - y
y_prime = s - x_prime
x_err = x - x_prime
y_err = y - y_prime
solver.add(e == x_err + y_err)

e_x = z3.Concat(EXPONENT_PADDING, x_exponent) - EXPONENT_BIAS
e_y = z3.Concat(EXPONENT_PADDING, y_exponent) - EXPONENT_BIAS
e_s = z3.Concat(EXPONENT_PADDING, s_exponent) - EXPONENT_BIAS
e_e = z3.Concat(EXPONENT_PADDING, e_exponent) - EXPONENT_BIAS

z_x = num_leading_zeroes(x_mantissa, PROMOTED_EXPONENT_WIDTH)
z_y = num_leading_zeroes(y_mantissa, PROMOTED_EXPONENT_WIDTH)
z_s = num_leading_zeroes(s_mantissa, PROMOTED_EXPONENT_WIDTH)
z_e = num_leading_zeroes(e_mantissa, PROMOTED_EXPONENT_WIDTH)

o_x = num_leading_ones(x_mantissa, PROMOTED_EXPONENT_WIDTH)
o_y = num_leading_ones(y_mantissa, PROMOTED_EXPONENT_WIDTH)
o_s = num_leading_ones(s_mantissa, PROMOTED_EXPONENT_WIDTH)
o_e = num_leading_ones(e_mantissa, PROMOTED_EXPONENT_WIDTH)

n_x = last_nonzero_bit(x_mantissa, PROMOTED_EXPONENT_WIDTH)
n_y = last_nonzero_bit(y_mantissa, PROMOTED_EXPONENT_WIDTH)
n_s = last_nonzero_bit(s_mantissa, PROMOTED_EXPONENT_WIDTH)
n_e = last_nonzero_bit(e_mantissa, PROMOTED_EXPONENT_WIDTH)


prove(solver, "G-LZ", ZERO_BV <= z_x)
prove(solver, "G-UZ", z_x < PRECISION_BV)
prove(solver, "G-LO", ZERO_BV <= o_x)
prove(solver, "G-UO", o_x < PRECISION_BV)
prove(solver, "G-LN", ZERO_BV <= n_x)
prove(solver, "G-UN", n_x < PRECISION_BV)
prove(solver, "G-ZO", z3.Xor(z_x == ZERO_BV, o_x == ZERO_BV))
prove(solver, "G-ZN-G", z3.Implies(z_x < PRECISION_MINUS_ONE_BV, z_x < n_x))
prove(solver, "G-ZN-S", z3.Implies(z_x == PRECISION_MINUS_ONE_BV, n_x == ZERO_BV))
prove(solver, "G-ON", o_x <= n_x)

prove(
    solver,
    "G-LEE",
    z3.Or(
        z3.fpIsZero(e),
        e_e - n_e > e_x - PRECISION_BV,
        e_e - n_e > e_y - PRECISION_BV,
    ),
)

prove(
    solver,
    "G-UEE",
    z3.Or(
        z3.fpIsZero(e),
        e_e < e_s - PRECISION_BV,
        z3.And(e_e == e_s - PRECISION_BV, n_e == ZERO_BV),
    ),
)
