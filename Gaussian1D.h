#ifndef DZNL_GAUSSIAN1D_H
#define DZNL_GAUSSIAN1D_H

#include <cmath>
#include "Constants.h"
#include "Hermite.h"

namespace dznl {

    class Gaussian1D {

    private: // =================================================== DATA MEMBERS

        double a; // inverse width
        double c; // center

    public: // ===================================================== CONSTRUCTOR

        Gaussian1D() : a(1.0), c(0.0) {}

        Gaussian1D(double invWidth) : a(invWidth), c(0.0) {}

        Gaussian1D(double invWidth, double center) : a(invWidth), c(center) {}

    public: // ====================================================== EVALUATION

        double evaluateAt(double x) const {
            const double dist = x - c;
            return std::exp(-0.5 * a * dist * dist);
        }

        double operator()(double x) const {
            return evaluateAt(x);
        }

    public: // ================================================= MATRIX ELEMENTS

        static double innerProduct(const Gaussian1D &g1, const Gaussian1D &g2) {
            const double aSum = g1.a + g2.a;
            const double dist = g2.c - g1.c;
            return std::sqrt(constants::tau / aSum) *
                   std::exp(-0.5 * g1.a * g2.a * dist * dist / aSum);
        }

        double operator*(const Gaussian1D &g) const {
            return innerProduct(*this, g);
        }

        static double xMatrixElement(const Gaussian1D &g1, const Gaussian1D &g2,
                                     unsigned int n) {
            const double aInv = 1.0 / sqrt(g1.a + g2.a);
            return innerProduct(g1, g2) * pow(aInv, n) *
                   hermiteHi(n, aInv * (g1.a * g1.c + g2.a * g2.c));
        }

        static double ddxMatrixElement(const Gaussian1D &g1,
                                       const Gaussian1D &g2,
                                       unsigned int n) {
            const double aInv = sqrt(g1.a * g2.a / (g1.a + g2.a));
            return innerProduct(g1, g2) * pow(aInv, n) *
                   hermiteHe(n, aInv * (g2.c - g1.c));
        }

    public: // ========================================= COMPARISON AND ORDERING

        bool operator==(const Gaussian1D &g) const {
            return (a == g.a) && (c == g.c);
        }

        bool operator!=(const Gaussian1D &g) const {
            return !(*this == g);
        }

        bool operator<(const Gaussian1D &g) const {
            if (c < g.c) {
                return true;
            } else if (c > g.c) {
                return false;
            } else {
                return a < g.a;
            }
        }

        bool operator>(const Gaussian1D &g) const {
            return g < *this;
        }

        bool operator<=(const Gaussian1D &g) const {
            return (*this < g) || (*this == g);
        }

        bool operator>=(const Gaussian1D &g) const {
            return (*this > g) || (*this == g);
        }

    public: // ======================================================== PRINTING

        friend std::ostream &operator<<(std::ostream &os, const Gaussian1D &g) {
            os << "Gaussian1D(" << g.a << ", " << g.c << ")";
            return os;
        }

    };

} // namespace dznl

#endif // DZNL_GAUSSIAN1D_H
