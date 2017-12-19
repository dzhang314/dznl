#ifndef DZNL_HYPERDUAL3_H
#define DZNL_HYPERDUAL3_H

struct hyperdual3 {
    double real;
    double dual1;
    double dual2;
    double dual12;
    double dual3;
    double dual13;
    double dual23;
    double dual123;
};

hyperdual3 operator+(const hyperdual3 &x) {
    return {
            .real = +x.real,
            .dual1 = +x.dual1,
            .dual2 = +x.dual2,
            .dual12 = +x.dual12,
            .dual3 = +x.dual3,
            .dual13 = +x.dual13,
            .dual23 = +x.dual23,
            .dual123 = +x.dual123,
    };
}

hyperdual3 operator-(const hyperdual3 &x) {
    return {
            .real = -x.real,
            .dual1 = -x.dual1,
            .dual2 = -x.dual2,
            .dual12 = -x.dual12,
            .dual3 = -x.dual3,
            .dual13 = -x.dual13,
            .dual23 = -x.dual23,
            .dual123 = -x.dual123,
    };
}

hyperdual3 operator+(const hyperdual3 &x, const hyperdual3 &y) {
    return {
            .real = x.real + y.real,
            .dual1 = x.dual1 + y.dual1,
            .dual2 = x.dual2 + y.dual2,
            .dual12 = x.dual12 + y.dual12,
            .dual3 = x.dual3 + y.dual3,
            .dual13 = x.dual13 + y.dual13,
            .dual23 = x.dual23 + y.dual23,
            .dual123 = x.dual123 + y.dual123,
    };
}

hyperdual3 operator-(const hyperdual3 &x, const hyperdual3 &y) {
    return {
            .real = x.real - y.real,
            .dual1 = x.dual1 - y.dual1,
            .dual2 = x.dual2 - y.dual2,
            .dual12 = x.dual12 - y.dual12,
            .dual3 = x.dual3 - y.dual3,
            .dual13 = x.dual13 - y.dual13,
            .dual23 = x.dual23 - y.dual23,
            .dual123 = x.dual123 - y.dual123,
    };
}

hyperdual3 operator*(const hyperdual3 &x, const hyperdual3 &y) {
    return {
            .real = x.real * y.real,
            .dual1 = x.dual1 * y.real + x.real * y.dual1,
            .dual2 = x.dual2 * y.real + x.real * y.dual2,
            .dual12 = x.dual12 * y.real + x.dual2 * y.dual1 +
                      x.dual1 * y.dual2 + x.real * y.dual12,
            .dual3 = x.dual3 * y.real + x.real * y.dual3,
            .dual13 = x.dual13 * y.real + x.dual3 * y.dual1 +
                      x.dual1 * y.dual3 + x.real * y.dual13,
            .dual23 = x.dual23 * y.real + x.dual3 * y.dual2 +
                      x.dual2 * y.dual3 + x.real * y.dual23,
            .dual123 = x.dual123 * y.real + x.dual23 * y.dual1 +
                       x.dual13 * y.dual2 + x.dual3 * y.dual12 +
                       x.dual12 * y.dual3 + x.dual2 * y.dual13 +
                       x.dual1 * y.dual23 + x.real * y.dual123,
    };
}

hyperdual3 operator/(const hyperdual3 &x, const hyperdual3 &y) {
    const auto u = x.real / y.real;
    const auto u1 = x.dual1 / y.real;
    const auto u2 = x.dual2 / y.real;
    const auto u12 = x.dual12 / y.real;
    const auto u3 = x.dual3 / y.real;
    const auto u13 = x.dual13 / y.real;
    const auto u23 = x.dual23 / y.real;
    const auto u123 = x.dual123 / y.real;
    const auto v1 = y.dual1 / y.real;
    const auto v2 = y.dual2 / y.real;
    const auto v12 = y.dual12 / y.real;
    const auto v3 = y.dual3 / y.real;
    const auto v13 = y.dual13 / y.real;
    const auto v23 = y.dual23 / y.real;
    const auto v123 = y.dual123 / y.real;
    return {
            .real = u,
            .dual1 = u1 - u * v1,
            .dual2 = u2 - u * v2,
            .dual12 = u12 - u2 * v1 - u1 * v2 + 2 * u * v1 * v2 - u * v12,
            .dual3 = u3 - u * v3,
            .dual13 = u13 - u3 * v1 - u1 * v3 + 2 * u * v1 * v3 - u * v13,
            .dual23 = u23 - u3 * v2 - u2 * v3 + 2 * u * v2 * v3 - u * v23,
            .dual123 = u123 - u23 * v1 - u13 * v2 + 2 * u3 * v1 * v2 -
                       u3 * v12 - u12 * v3 + 2 * u2 * v1 * v3 +
                       2 * u1 * v2 * v3 - 6 * u * v1 * v2 * v3 +
                       2 * u * v12 * v3 - u2 * v13 + 2 * u * v2 * v13 -
                       u1 * v23 + 2 * u * v1 * v23 - u * v123,
    };
}

#endif // DZNL_HYPERDUAL3_H
