#ifndef DZNL_GAUSSIAN1D_H
#define DZNL_GAUSSIAN1D_H

#include <cmath>
#include "Constants.h"
#include "Hermite.h"

namespace dznl {

    template<typename TReal>
    class Gaussian1D {

    private: // =================================================== DATA MEMBERS

        TReal a; // inverse width
        TReal c; // center

    public: // ===================================================== CONSTRUCTOR

        Gaussian1D() : a(1.0), c(0.0) {}

        Gaussian1D(const TReal &invWidth) : a(invWidth), c() {}

        Gaussian1D(const TReal &invWidth, const TReal &center) :
                a(invWidth), c(center) {}

    public: // ====================================================== EVALUATION

        TReal evaluateAt(const TReal &x) const {
            const TReal dist = x - c;
            return exp(-0.5 * a * dist * dist);
        }

        TReal operator()(const TReal &x) const {
            return evaluateAt(x);
        }

    public: // ================================================= MATRIX ELEMENTS

        static TReal innerProduct(const Gaussian1D &g1, const Gaussian1D &g2) {
            const TReal aSum = g1.a + g2.a;
            const TReal dist = g2.c - g1.c;
            return sqrt(constants::tau / aSum) *
                   exp(-0.5 * g1.a * g2.a * dist * dist / aSum);
        }

        TReal operator*(const Gaussian1D &g) const {
            return innerProduct(*this, g);
        }

        static TReal xMatrixElement(const Gaussian1D &g1, const Gaussian1D &g2,
                                    unsigned int n) {
            const TReal aInv = 1.0 / sqrt(g1.a + g2.a);
            return innerProduct(g1, g2) * pow(aInv, n) *
                   hermiteHi(n, aInv * (g1.a * g1.c + g2.a * g2.c));
        }

        static TReal ddxMatrixElement(const Gaussian1D &g1,
                                      const Gaussian1D &g2,
                                      unsigned int n) {
            const TReal aInv = sqrt(g1.a * g2.a / (g1.a + g2.a));
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

    }; // class Gaussian1D

} // namespace dznl

#endif // DZNL_GAUSSIAN1D_H
