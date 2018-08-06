#ifndef DZNL_COMPLEXNUMBER_H
#define DZNL_COMPLEXNUMBER_H

#include <iostream>

namespace dznl {

    template<typename T>
    class ComplexNumber {

    public: // ==================================================== DATA MEMBERS

        T real;
        T imag;

    public: // ==================================================== CONSTRUCTORS

        ComplexNumber() : real(), imag() {}

        ComplexNumber(const T &re) : real(re), imag() {}

        ComplexNumber(const T &re, const T &im) : real(re), imag(im) {}

    public: // ======================================== REAL ASSIGNMENT OPERATOR

        ComplexNumber &operator=(const T &a) {
            real = a;
            imag = T();
            return *this;
        }

    public: // ============================== REAL COMPOUND ASSIGNMENT OPERATORS

        ComplexNumber &operator+=(const T &a) {
            real += a;
            return *this;
        }

        ComplexNumber &operator-=(const T &a) {
            real -= a;
            return *this;
        }

        ComplexNumber &operator*=(const T &a) {
            real *= a;
            imag *= a;
            return *this;
        }

        ComplexNumber &operator/=(const T &a) {
            real /= a;
            imag /= a;
            return *this;
        }

    public: // ======================================= REAL ARITHMETIC OPERATORS

        ComplexNumber operator+(const T &a) const {
            return ComplexNumber(real + a, imag);
        }

        ComplexNumber operator-(const T &a) const {
            return ComplexNumber(real - a, imag);
        }

        ComplexNumber operator*(const T &a) const {
            return ComplexNumber(real * a, imag * a);
        }

        ComplexNumber operator/(const T &a) const {
            return ComplexNumber(real / a, imag / a);
        }

    public: // ================================ FRIEND REAL ARITHMETIC OPERATORS

        friend ComplexNumber operator+(const T &a, const ComplexNumber &b) {
            return ComplexNumber(a + b.real, b.imag);
        }

        friend ComplexNumber operator-(const T &a, const ComplexNumber &b) {
            return ComplexNumber(a - b.real, -b.imag);
        }

        friend ComplexNumber operator*(const T &a, const ComplexNumber &b) {
            return ComplexNumber(a * b.real, a * b.imag);
        }

        friend ComplexNumber operator/(const T &a, const ComplexNumber &b) {
            const T denom = b.abs2();
            return ComplexNumber(a * b.real / denom, -a * b.imag / denom);
        }

    public: // =========================== COMPLEX COMPOUND ASSIGNMENT OPERATORS

        ComplexNumber &operator+=(const ComplexNumber &a) {
            real += a.real;
            imag += a.imag;
            return *this;
        }

        ComplexNumber &operator-=(const ComplexNumber &a) {
            real -= a.real;
            imag -= a.imag;
            return *this;
        }

        ComplexNumber &operator*=(const ComplexNumber &a) {
            *this = *this * a;
            return *this;
        }

        ComplexNumber &operator/=(const ComplexNumber &a) {
            *this = *this / a;
            return *this;
        }

    public: // ==================================== COMPLEX ARITHMETIC OPERATORS

        ComplexNumber operator+(const ComplexNumber &a) const {
            return ComplexNumber(real + a.real, imag + a.imag);
        }

        ComplexNumber operator-(const ComplexNumber &a) const {
            return ComplexNumber(real - a.real, imag - a.imag);
        }

        ComplexNumber operator-() const {
            return ComplexNumber(-real, -imag);
        }

        ComplexNumber operator*(const ComplexNumber &a) const {
            return ComplexNumber(real * a.real - imag * a.imag,
                                 imag * a.real + real * a.imag);
        }

        ComplexNumber operator/(const ComplexNumber &a) const {
            const T denom = a.abs2();
            return ComplexNumber((real * a.real + imag * a.imag) / denom,
                                 (imag * a.real - real * a.imag) / denom);
        }

    public: // ========================================= COMPLEX MATH OPERATIONS

        ComplexNumber conj() const {
            return ComplexNumber(real, -imag);
        }

        T abs2() const {
            return real * real + imag * imag;
        }

    public: // ======================================================== PRINTING

        friend std::ostream &
        operator<<(std::ostream &os, const ComplexNumber &a) {
            os << "(" << a.real << ", " << a.imag << ")";
            return os;
        }

    }; // class ComplexNumber

} // namespace dznl

#endif // DZNL_COMPLEXNUMBER_H
