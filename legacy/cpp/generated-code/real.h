#ifndef DZNL_REAL_H
#define DZNL_REAL_H

struct real {
    double real;
};

real operator+(const real &x) {
    return {
            .real = +x.real,
    };
}

real operator-(const real &x) {
    return {
            .real = -x.real,
    };
}

real operator+(const real &x, const real &y) {
    return {
            .real = x.real + y.real,
    };
}

real operator-(const real &x, const real &y) {
    return {
            .real = x.real - y.real,
    };
}

real operator*(const real &x, const real &y) {
    return {
            .real = x.real * y.real,
    };
}

real operator/(const real &x, const real &y) {
    const auto u = x.real / y.real;
    return {
            .real = u,
    };
}

#endif // DZNL_REAL_H
