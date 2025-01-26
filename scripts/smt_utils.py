import os
import subprocess
import z3

from random import shuffle
from sys import argv
from time import perf_counter_ns
from typing import TypeVar


def count_leading_zeros(b: z3.BitVecRef, result_width: int) -> z3.BitVecRef:
    result: z3.BitVecRef = z3.BitVecVal(0, result_width)
    for i in range(1, b.size() + 1):
        substr: z3.BitVecRef = z3.Extract(b.size() - 1, b.size() - i, b)
        zeros: z3.BitVecRef = z3.BitVecVal(0, i)
        result = z3.If(substr == zeros, z3.BitVecVal(i, result_width), result)
    return result


def count_leading_ones(b: z3.BitVecRef, result_width: int) -> z3.BitVecRef:
    result: z3.BitVecRef = z3.BitVecVal(0, result_width)
    for i in range(1, b.size() + 1):
        substr: z3.BitVecRef = z3.Extract(b.size() - 1, b.size() - i, b)
        ones: z3.BitVecRef = z3.BitVecVal(2**i - 1, i)
        result = z3.If(substr == ones, z3.BitVecVal(i, result_width), result)
    return result


def count_trailing_zeros(b: z3.BitVecRef, result_width: int) -> z3.BitVecRef:
    result: z3.BitVecRef = z3.BitVecVal(0, result_width)
    for i in range(1, b.size() + 1):
        substr: z3.BitVecRef = z3.Extract(i - 1, 0, b)
        zeros: z3.BitVecRef = z3.BitVecVal(0, i)
        result = z3.If(substr == zeros, z3.BitVecVal(i, result_width), result)
    return result


def count_trailing_ones(b: z3.BitVecRef, result_width: int) -> z3.BitVecRef:
    result: z3.BitVecRef = z3.BitVecVal(0, result_width)
    for i in range(1, b.size() + 1):
        substr: z3.BitVecRef = z3.Extract(i - 1, 0, b)
        ones: z3.BitVecRef = z3.BitVecVal(2**i - 1, i)
        result = z3.If(substr == ones, z3.BitVecVal(i, result_width), result)
    return result


BoolVar = TypeVar("BoolVar", z3.BoolRef, z3.BitVecRef)
IntVar = TypeVar("IntVar", z3.ArithRef, z3.BitVecRef)
FloatVar = TypeVar("FloatVar")


# This wrapper function works around Python type checkers
# being unable to resolve overloads through type variables.
def z3_If(c: z3.BoolRef, a: IntVar, b: IntVar) -> IntVar:
    return z3.If(c, a, b)  # type: ignore


def detect_smt_solvers() -> list[str]:
    result: list[str] = []

    if "--no-bitwuzla" not in argv:
        try:
            v: str = subprocess.check_output(["bitwuzla", "--version"], text=True)
            print("Found Bitwuzla:", v.strip())
            result.append("bitwuzla")
        except FileNotFoundError:
            print("Bitwuzla not found.")

    if "--no-cvc5" not in argv:
        try:
            v: str = subprocess.check_output(["cvc5", "--version"], text=True)
            print("Found CVC5:", v.splitlines()[0].strip())
            result.append("cvc5")
        except FileNotFoundError:
            print("CVC5 not found.")

    if "--no-mathsat" not in argv:
        try:
            v: str = subprocess.check_output(["mathsat", "-version"], text=True)
            print("Found MathSAT:", v.strip())
            result.append("mathsat")
        except FileNotFoundError:
            print("MathSAT not found.")

    if "--no-z3" not in argv:
        try:
            v: str = subprocess.check_output(["z3", "--version"], text=True)
            print("Found Z3:", v.strip())
            result.append("z3")
        except FileNotFoundError:
            print("Z3 not found.")

    print()
    return result


SMT_SOLVERS: list[str] = detect_smt_solvers()


class SMTJob(object):
    def __init__(self, filename: str) -> None:
        assert os.path.isfile(filename)
        self.filename: str = filename
        self.processes: dict[str, tuple[int, subprocess.Popen[str]]] = {}
        self.result: tuple[float, z3.CheckSatResult] | None = None

    def start(self) -> None:
        assert not self.processes
        assert self.result is None
        shuffle(SMT_SOLVERS)
        for smt_solver in SMT_SOLVERS:
            command: list[str] = [smt_solver]
            if smt_solver == "cvc5":
                command.append("--fp-exp")
            command.append(self.filename)
            self.processes[smt_solver] = (
                perf_counter_ns(),
                subprocess.Popen(
                    command,
                    stdout=subprocess.PIPE,
                    text=True,
                ),
            )

    def poll(self) -> bool:
        assert self.processes

        if self.result is not None:
            return True

        finished_solver: str | None = None
        for smt_solver, (start, process) in self.processes.items():
            if process.poll() is not None:

                # Measure elapsed time.
                stop: int = perf_counter_ns()
                elapsed: float = (stop - start) / 1.0e9

                # Verify successful termination.
                assert process.returncode == 0
                stdout: str
                stderr: str
                stdout, stderr = process.communicate()
                assert stderr is None

                # Parse SMT solver output.
                if stdout == "unsat\n":
                    self.result = (elapsed, z3.unsat)
                elif stdout == "sat\n":
                    self.result = (elapsed, z3.sat)
                elif stdout == "unknown\n":
                    self.result = (elapsed, z3.unknown)
                else:
                    raise RuntimeError(
                        f"Unexpected output from {smt_solver} on {self.filename}:\n"
                        + stdout
                    )

                finished_solver = smt_solver
                break

        # If an SMT solver has terminated, kill all other solvers.
        if finished_solver is not None:
            for other_solver in self.processes.keys() - {finished_solver}:
                self.processes[other_solver][1].kill()
                del self.processes[other_solver]

        return self.result is not None


def create_smt_job(
    solver: z3.Solver, logic: str, name: str, claim: z3.BoolRef
) -> SMTJob:

    # Obtain current solver state and claim in SMT-LIB 2 format.
    solver.push()
    solver.add(z3.Not(claim))
    contents: str = f"(set-logic {logic})\n" + solver.to_smt2()
    solver.pop()

    # Write SMT-LIB 2 file in smt2 subdirectory.
    os.makedirs("smt2", exist_ok=True)
    filename: str = os.path.join("smt2", name + ".smt2")
    with open(filename, "w") as f:
        f.write(contents)

    return SMTJob(filename)
