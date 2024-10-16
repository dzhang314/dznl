import os
import random
import subprocess
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

    # Write current solver state and claim to SMT-LIB2 file.
    solver.push()
    solver.add(z3.Not(claim))
    os.makedirs("smt2", exist_ok=True)
    filename = os.path.join("smt2", name + ".smt2")
    with open(filename, "w") as f:
        f.write("(set-logic QF_BVFP)\n")
        f.write(solver.to_smt2())
    solver.pop()

    # Invoke external solvers to prove or refute the claim.
    external_solvers = ["bitwuzla", "cvc5", "mathsat", "z3"]
    random.shuffle(external_solvers)
    external_processes: list[tuple[str, int, subprocess.Popen[str]]] = []
    for external_solver in external_solvers:
        start = time.perf_counter_ns()
        process = subprocess.Popen(
            [external_solver, filename], stdout=subprocess.PIPE, text=True
        )
        external_processes.append((external_solver, start, process))

    # Wait for the first solver to finish and check its result.
    while True:
        for external_solver, start, process in external_processes:
            if process.poll() is not None:
                stop = time.perf_counter_ns()
                elapsed = (stop - start) / 1.0e9
                assert process.returncode == 0
                stdout, stderr = process.communicate()
                assert stderr is None
                for _, _, other_process in external_processes:
                    other_process.kill()
                if stdout == "unsat\n":
                    print(f"{external_solver} proved {name} in {elapsed} seconds.")
                    return True
                elif stdout == "sat\n":
                    print(f"{external_solver} refuted {name} in {elapsed} seconds.")
                    return False
                else:
                    print(
                        f"When attempting to prove {name}, {external_solver}",
                        f"returned {stdout} in {elapsed} seconds.",
                    )
                    assert False
        # Sleep for a short time to avoid busy waiting. (Even the fastest SMT
        # solvers take a few milliseconds, so 0.1ms is a reasonable interval.)
        time.sleep(1.0e-4)


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
ONE_BV: z3.BitVecRef = z3.BitVecVal(1, PROMOTED_EXPONENT_WIDTH)
PRECISION_BV: z3.BitVecRef = z3.BitVecVal(PRECISION, PROMOTED_EXPONENT_WIDTH)
PRECISION_MINUS_ONE_BV: z3.BitVecRef = z3.BitVecVal(
    PRECISION - 1, PROMOTED_EXPONENT_WIDTH
)
PRECISION_PLUS_ONE_BV: z3.BitVecRef = z3.BitVecVal(
    PRECISION + 1, PROMOTED_EXPONENT_WIDTH
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

RNE = z3.RoundNearestTiesToEven()
solver.add(s == z3.fpAdd(RNE, x, y))
x_prime = z3.fpSub(RNE, s, y)
y_prime = z3.fpSub(RNE, s, x_prime)
x_err = z3.fpSub(RNE, x, x_prime)
y_err = z3.fpSub(RNE, y, y_prime)
solver.add(e == z3.fpAdd(RNE, x_err, y_err))

s_x = x_sign_bit
s_y = y_sign_bit
s_s = s_sign_bit
s_e = e_sign_bit

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
    e_s - n_s > e_x - PRECISION_BV,
    e_s - n_s > e_y - PRECISION_BV,
)

lemmas["G-UBES"] = z3.Or(e_s <= e_x + ONE_BV, e_s <= e_y + ONE_BV)

lemmas["G-LBEE"] = z3.Or(
    z3.fpIsZero(e),
    e_e - n_e > e_x - PRECISION_BV,
    e_e - n_e > e_y - PRECISION_BV,
)

lemmas["G-UBEE"] = z3.Or(
    z3.fpIsZero(e),
    e_e < e_s - PRECISION_BV,
    z3.And(e_e == e_s - PRECISION_BV, n_e == ZERO_BV),
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
case_3as = z3.And(e_x - PRECISION_BV == e_y, s_x == s_y)
case_3bs = z3.And(e_x == e_y - PRECISION_BV, s_x == s_y)
case_3ad = z3.And(e_x - PRECISION_BV == e_y, s_x != s_y)
case_3bd = z3.And(e_x == e_y - PRECISION_BV, s_x != s_y)
case_4as = z3.And(e_x - PRECISION_BV < e_y, e_x - ONE_BV > e_y, s_x == s_y)
case_4bs = z3.And(e_x > e_y - PRECISION_BV, e_x < e_y - ONE_BV, s_x == s_y)
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


expensive_lemmas: set[str] = {"G-LBEE", "G-UBEE", "6D-E"}

for name, lemma in lemmas.items():
    if name not in expensive_lemmas:
        assert prove(solver, name, lemma)
