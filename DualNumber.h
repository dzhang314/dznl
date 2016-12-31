#ifndef DZNL_DUALNUMBER_H
#define DZNL_DUALNUMBER_H

#include <iostream>

namespace dznl {

    template<typename TNum>
    class DualNumber {

    public: // ==================================================== DATA MEMBERS

        TNum real;
        TNum dual;

    public: // ==================================================== CONSTRUCTORS

        DualNumber() : real(), dual() {}

        DualNumber(const TNum &re) : real(re), dual() {}

        DualNumber(const TNum &re, const TNum &du) : real(re), dual(du) {}

    public: // ======================================== REAL ASSIGNMENT OPERATOR

        DualNumber &operator=(const TNum &a) {
            real = a;
            dual = TNum();
            return *this;
        }

    public: // ============================== REAL COMPOUND ASSIGNMENT OPERATORS

        DualNumber &operator+=(const TNum &a) {
            real += a;
            return *this;
        }

        DualNumber &operator-=(const TNum &a) {
            real -= a;
            return *this;
        }

        DualNumber &operator*=(const TNum &a) {
            real *= a;
            dual *= a;
            return *this;
        }

        DualNumber &operator/=(const TNum &a) {
            real /= a;
            dual /= a;
            return *this;
        }

    public: // ======================================= REAL ARITHMETIC OPERATORS

        DualNumber operator+(const TNum &a) const {
            return DualNumber(real + a, dual);
        }

        DualNumber operator-(const TNum &a) const {
            return DualNumber(real - a, dual);
        }

        DualNumber operator*(const TNum &a) const {
            return DualNumber(real * a, dual * a);
        }

        DualNumber operator/(const TNum &a) const {
            return DualNumber(real / a, dual / a);
        }

    public: // ================================ FRIEND REAL ARITHMETIC OPERATORS

        friend DualNumber operator+(const TNum &a, const DualNumber &b) {
            return DualNumber(a + b.real, b.dual);
        }

        friend DualNumber operator-(const TNum &a, const DualNumber &b) {
            return DualNumber(a - b.real, -b.dual);
        }

        friend DualNumber operator*(const TNum &a, const DualNumber &b) {
            return DualNumber(a * b.real, a * b.dual);
        }

        friend DualNumber operator/(const TNum &a, const DualNumber &b) {
            const TNum quot = a / b.real;
            return DualNumber(quot, -quot * b.dual / b.real);
        }

    public: // ============================== DUAL COMPOUND ASSIGNMENT OPERATORS

        DualNumber &operator+=(const DualNumber &a) {
            real += a.real;
            dual += a.dual;
            return *this;
        }

        DualNumber &operator-=(const DualNumber &a) {
            real -= a.real;
            dual -= a.dual;
            return *this;
        }

        DualNumber &operator*=(const DualNumber &a) {
            *this = *this * a;
            return *this;
        }

        DualNumber &operator/=(const DualNumber &a) {
            *this = *this / a;
            return *this;
        }

    public: // ======================================= DUAL ARITHMETIC OPERATORS

        DualNumber operator+(const DualNumber &a) const {
            return DualNumber(real + a.real, dual + a.dual);
        }

        DualNumber operator-(const DualNumber &a) const {
            return DualNumber(real - a.real, dual - a.dual);
        }

        DualNumber operator-() const {
            return DualNumber(-real, -dual);
        }

        DualNumber operator*(const DualNumber &a) const {
            return DualNumber(real * a.real,
                              dual * a.real + real * a.dual);
        }

        DualNumber operator/(const DualNumber &a) const {
            const TNum quot = real / a.real;
            return DualNumber(quot, dual - quot * a.dual / a.real);
        }

    public: // ======================================================== PRINTING

        friend std::ostream &
        operator<<(std::ostream &os, const DualNumber &a) {
            os << "(" << a.real << ", " << a.dual << ")";
            return os;
        }

    }; // class DualNumber

} // namespace dznl

#endif // DZNL_DUALNUMBER_H
