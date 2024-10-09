from typing import overload

class BoolRef(object):
    def __eq__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: BoolRef
    ) -> BoolRef: ...
    def __ne__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: BoolRef
    ) -> BoolRef: ...

def Bool(name: str) -> BoolRef: ...
def BoolVal(value: bool) -> BoolRef: ...
def Not(arg: BoolRef) -> BoolRef: ...
def And(*args: BoolRef) -> BoolRef: ...
def Or(*args: BoolRef) -> BoolRef: ...
def Implies(a: BoolRef, b: BoolRef) -> BoolRef: ...

class ArithRef(object):
    def __eq__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: int | ArithRef
    ) -> BoolRef: ...
    def __ne__(  # pyright: ignore[reportIncompatibleMethodOverride]
        self, other: int | ArithRef
    ) -> BoolRef: ...
    def __lt__(self, other: int | ArithRef) -> BoolRef: ...
    def __le__(self, other: int | ArithRef) -> BoolRef: ...
    def __gt__(self, other: int | ArithRef) -> BoolRef: ...
    def __ge__(self, other: int | ArithRef) -> BoolRef: ...
    def __add__(self, other: int | ArithRef) -> ArithRef: ...
    def __sub__(self, other: int | ArithRef) -> ArithRef: ...

class CheckSatResult(object): ...

sat: CheckSatResult
unsat: CheckSatResult
unknown: CheckSatResult

class FuncDeclRef(object): ...

class IntNumRef(object):
    def as_long(self) -> int: ...

class ModelRef(object):
    @overload
    def __getitem__(self, key: int) -> FuncDeclRef: ...
    @overload
    def __getitem__(self, key: BoolRef) -> bool | None: ...
    @overload
    def __getitem__(self, key: ArithRef) -> int | None: ...
    @overload
    def __getitem__(self, key: FuncDeclRef) -> BoolRef | IntNumRef | None: ...

class Solver(object):
    def add(self, expr: BoolRef) -> None: ...
    def check(self, *args: BoolRef) -> CheckSatResult: ...
    def model(self) -> ModelRef: ...

def Int(name: str) -> ArithRef: ...
def Abs(x: ArithRef) -> ArithRef: ...
def If(c: BoolRef, a: int | ArithRef, b: int | ArithRef) -> ArithRef: ...
