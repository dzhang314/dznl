# `dznl`

**`dznl`** is a C++ header-only template library for computational mathematics, with a focus on numerical optimization and high-precision arithmetic.

## Design Goals

* **Zero dependencies** &mdash; ***not even the C++ standard library!*** This makes **`dznl`** perfect for environments like WebAssembly where a standard library implementation may not be available.
* **Zero dynamic allocation** &mdash; **`dznl`** does not contain a single call to `malloc` or `operator new` (except in unit tests). This makes **`dznl`** especially suitable for resource-constrained environments where memory must be carefully managed.
* **No recursion or exceptions** &mdash; **`dznl`** is designed to have completely predictable static resource allocation with no possibility of stack unwinding or overflow.
* **Arbitrary precision** &mdash; **`dznl`** works equally well with all numeric types, including nonstandard and user-defined types, with no baked-in assumptions about 32/64-bit precision or tolerance. Want to run the Nelder-Mead algorithm using `bfloat16`? How about gradient descent with `_Decimal128`? Or L-BFGS with `boost::multiprecision`? **`dznl`** makes all of this just as easy as using `float` or `double`.
* **Supreme flexibility** &mdash; **`dznl`** does not limit the user to a fixed set of baked-in constraints and stopping criteria. Its optimization algorithms are designed to adaptively handle any feasible set geometry and provide the user full control over the optimization loop.
* **Clean code** &mdash; **`dznl`** is written in standards-conforming C++17 that throws zero warnings, even on the most aggressive compiler settings. It is one of few C++ libraries to survive `clang++ -Weverything` (with a small number of unavoidable exceptions &mdash; see below).

**Note**: The name of this library is **`dznl`**, not DZNL, to accord with C++ standard library naming conventions (and so that scientists don't think I'm a national lab).
