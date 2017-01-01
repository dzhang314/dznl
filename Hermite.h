#ifndef DZNL_HERMITE_H
#define DZNL_HERMITE_H

namespace dznl {

    double hermiteH(unsigned int n, double x) {
        if (n == 0) {
            return 1.0;
        } else if (n == 1) {
            return 2.0 * x;
        } else {
            return 2.0 *
                   (x * hermiteH(n - 1, x) - (n - 1) * hermiteH(n - 2, x));
        }
    }

    double hermiteHe(unsigned int n, double x) {
        if (n == 0) {
            return 1.0;
        } else if (n == 1) {
            return x;
        } else {
            return x * hermiteHe(n - 1, x) - (n - 1) * hermiteHe(n - 2, x);
        }
    }

    double hermiteHi(unsigned int n, double x) {
        if (n == 0) {
            return 1.0;
        } else if (n == 1) {
            return x;
        } else {
            return x * hermiteHi(n - 1, x) + (n - 1) * hermiteHi(n - 2, x);
        }
    }

} // namespace dznl

#endif // DZNL_HERMITE_H
