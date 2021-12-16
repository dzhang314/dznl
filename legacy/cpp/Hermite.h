#ifndef DZNL_HERMITE_H
#define DZNL_HERMITE_H

#include <cmath>
#include <stdexcept>

namespace dznl { // @formatter:off

    double hermiteH(int n, double x) {
        double x2 = x * x;
        if (n == 0) {
            return 1.0;
        } else if (n == 1) {
            return 2.0 * x;
        } else if (n == 2) {
            return std::fma(4.0, x2, -2.0);
        } else if (n == 3) {
            return x * std::fma(8.0, x2, -12.0);
        } else if (n == 4) {
            return std::fma(x2, std::fma(16.0, x2, -48.0), 12.0);
        } else if (n == 5) {
            return x * std::fma(x2, std::fma(32.0, x2, -160.0), 120.0);
        } else if (n == 6) {
            return std::fma(x2, std::fma(x2, std::fma(64.0, x2, -480.0), 720.0), -120.0);
        } else if (n == 7) {
            return x * std::fma(x2, std::fma(x2, std::fma(128.0, x2, -1344.0), 3360.0), -1680.0);
        } else if (n == 8) {
            return std::fma(x2, std::fma(x2, std::fma(x2, std::fma(256.0, x2, -3584.0), 13440.0), -13440.0), 1680.0);
        } else if (n == 9) {
            return x * std::fma(x2, std::fma(x2, std::fma(x2, std::fma(512.0, x2, -9216.0), 48384.0), -80640.0), 30240.0);
        } else {
            throw std::invalid_argument("argument n of hermiteH(n, x) out of range");
        }
    }

    double hermiteHe(int n, double x) {
        double x2 = x * x;
        if (n == 0) {
            return 1.0;
        } else if (n == 1) {
            return x;
        } else if (n == 2) {
            return -1.0 + x2;
        } else if (n == 3) {
            return x * (-3.0 + x2);
        } else if (n == 4) {
            return std::fma(x2, -6.0 + x2, 3.0);
        } else if (n == 5) {
            return x * std::fma(x2, -10.0 + x2, 15.0);
        } else if (n == 6) {
            return std::fma(x2, std::fma(x2, -15.0 + x2, 45.0), -15.0);
        } else if (n == 7) {
            return x * std::fma(x2, std::fma(x2, -21.0 + x2, 105.0), -105.0);
        } else if (n == 8) {
            return std::fma(x2, std::fma(x2, std::fma(x2, -28.0 + x2, 210.0), -420.0), 105.0);
        } else if (n == 9) {
            return x * std::fma(x2, std::fma(x2, std::fma(x2, -36.0 + x2, 378.0), -1260.0), 945.0);
        } else {
            throw std::invalid_argument("argument n of hermiteHe(n, x) out of range");
        }
    }

    double hermiteHi(int n, double x) {
        double x2 = x * x;
        if (n == 0) {
            return 1.0;
        } else if (n == 1) {
            return x;
        } else if (n == 2) {
            return 1.0 + x2;
        } else if (n == 3) {
            return x * (3.0 + x2);
        } else if (n == 4) {
            return std::fma(x2, 6.0 + x2, 3.0);
        } else if (n == 5) {
            return x * std::fma(x2, 10.0 + x2, 15.0);
        } else if (n == 6) {
            return std::fma(x2, std::fma(x2, 15.0 + x2, 45.0), 15.0);
        } else if (n == 7) {
            return x * std::fma(x2, std::fma(x2, 21.0 + x2, 105.0), 105.0);
        } else if (n == 8) {
            return std::fma(x2, std::fma(x2, std::fma(x2, 28.0 + x2, 210.0), 420.0), 105.0);
        } else if (n == 9) {
            return x * std::fma(x2, std::fma(x2, std::fma(x2, 36.0 + x2, 378.0), 1260.0), 945.0);
        } else {
            throw std::invalid_argument("argument n of hermiteHi(n, x) out of range");
        }
    }

} // namespace dznl

#endif // DZNL_HERMITE_H
