# `dznl`

**`dznl`** is a header-only C++17 math library that provides high-performance implementations of:

- numerical calculus and linear algebra
- nonlinear root-finding and optimization
- high-precision floating-point arithmetic



## Design Goals

- **Zero required dependencies** &mdash; ***not even the C++ standard library!*** **`dznl`** is great for environments like WebAssembly and embedded systems where a standard library implementation may not be available.

- **Zero dynamic allocation** &mdash; **`dznl`** does not contain a single call to `malloc` or `operator new` (except in unit tests). This makes **`dznl`** suitable for resource-constrained environments where every last kilobyte must be carefully managed.

- **No recursion or exceptions** &mdash; **`dznl`** uses completely predictable static resource allocation with no possibility of stack overflow or unwinding.

- **Arbitrary precision** &mdash; **`dznl`** works equally well with all numeric types, including nonstandard and user-defined types, with no baked-in assumptions about 32/64-bit precision or tolerances. Want to run the Nelder-Mead algorithm using `bfloat16`? How about gradient descent with `_Decimal128` or `boost::multiprecision`? **`dznl`** makes all of this just as easy as using `float` or `double`.

- **Supreme flexibility** &mdash; **`dznl`** does not limit the user to a fixed set of baked-in constraints and stopping criteria. Its optimization algorithms are designed to adaptively handle the geometry of any feasible set and provide full control over the optimization loop.

- **Clean code** &mdash; **`dznl`** is written in standards-conforming C++17 that throws zero warnings, even on the most aggressive compiler settings. It is one of few C++ libraries to survive `clang++ -Weverything` (with a small number of unavoidable exceptions &mdash; see below).

- **No pollution** &mdash; **`dznl`** only defines identifiers in the `dznl::` namespace or with a `DZNL_` prefix and does not drag in any outside header files (unless cross-library features are explicitly requested).



## Usage Example

```c++
#include <dznl/NelderMeadOptimizer.hpp>
#include <dznl/RandomNumberGenerator.hpp>
#include <iostream>
#include <vector>

// a classic example of a nonlinear objective function
double rosenbrock_function(const double *x) {
    const double a = x[0] - 1.0;
    const double b = x[1] - x[0] * x[0];
    return a * a + 100.0 * b * b;
}

// dznl is constexpr-friendly
constexpr int DIMENSION = 2;
constexpr int WORKSPACE_SIZE =
    dznl::nelder_mead_workspace_size(DIMENSION);

int main() {

    // generate a random initial point
    dznl::RandomNumberGenerator rng(1729); // pick your favorite seed

    // load coordinates of initial point into workspace array
    std::vector<double> workspace(WORKSPACE_SIZE);
    workspace[0] = rng.random_f64();
    workspace[1] = rng.random_f64();

    auto optimizer = dznl::make_nelder_mead_optimizer(
        rosenbrock_function, // function to be optimized
        workspace.data(),    // pointer to workspace
        DIMENSION,           // number of dimensions
        0.1                  // initial step length
    );

    while (optimizer.step()) {
        // yes, we can optimize THIS precisely
        if (optimizer.get_current_objective_value() < 1.0e-30) break;
        // but you can use any stopping criterion your heart desires
    }

    // optimal point stays at the front of the workspace
    // you can also use `optimizer.get_current_point()`
    std::cout << workspace[0] << ", " << workspace[1] << std::endl;
    return 0;

}
```



## Supported Platforms

**`dznl`** is regularly built and tested on Windows 11 x86-64, macOS 14 ARM, and Linux (LMDE 6) x86-64 using GCC 14 and Clang 19. Any issue that arises on one of these platforms with one of these compilers is a defect that should be reported.

Users are also welcome to open issues about different platforms and compilers, but these may be deprioritized. Note that **MSVC is currently unsupported**.
