#ifndef DZNL_HYPERDUAL4_H
#define DZNL_HYPERDUAL4_H

struct hyperdual4 {
    double real;
    double dual1;
    double dual2;
    double dual12;
    double dual3;
    double dual13;
    double dual23;
    double dual123;
    double dual4;
    double dual14;
    double dual24;
    double dual124;
    double dual34;
    double dual134;
    double dual234;
    double dual1234;
};

hyperdual4 operator+(const hyperdual4 &x) {
    return {
            .real = +x.real,
            .dual1 = +x.dual1,
            .dual2 = +x.dual2,
            .dual12 = +x.dual12,
            .dual3 = +x.dual3,
            .dual13 = +x.dual13,
            .dual23 = +x.dual23,
            .dual123 = +x.dual123,
            .dual4 = +x.dual4,
            .dual14 = +x.dual14,
            .dual24 = +x.dual24,
            .dual124 = +x.dual124,
            .dual34 = +x.dual34,
            .dual134 = +x.dual134,
            .dual234 = +x.dual234,
            .dual1234 = +x.dual1234,
    };
}

hyperdual4 operator-(const hyperdual4 &x) {
    return {
            .real = -x.real,
            .dual1 = -x.dual1,
            .dual2 = -x.dual2,
            .dual12 = -x.dual12,
            .dual3 = -x.dual3,
            .dual13 = -x.dual13,
            .dual23 = -x.dual23,
            .dual123 = -x.dual123,
            .dual4 = -x.dual4,
            .dual14 = -x.dual14,
            .dual24 = -x.dual24,
            .dual124 = -x.dual124,
            .dual34 = -x.dual34,
            .dual134 = -x.dual134,
            .dual234 = -x.dual234,
            .dual1234 = -x.dual1234,
    };
}

hyperdual4 operator+(const hyperdual4 &x, const hyperdual4 &y) {
    return {
            .real = x.real + y.real,
            .dual1 = x.dual1 + y.dual1,
            .dual2 = x.dual2 + y.dual2,
            .dual12 = x.dual12 + y.dual12,
            .dual3 = x.dual3 + y.dual3,
            .dual13 = x.dual13 + y.dual13,
            .dual23 = x.dual23 + y.dual23,
            .dual123 = x.dual123 + y.dual123,
            .dual4 = x.dual4 + y.dual4,
            .dual14 = x.dual14 + y.dual14,
            .dual24 = x.dual24 + y.dual24,
            .dual124 = x.dual124 + y.dual124,
            .dual34 = x.dual34 + y.dual34,
            .dual134 = x.dual134 + y.dual134,
            .dual234 = x.dual234 + y.dual234,
            .dual1234 = x.dual1234 + y.dual1234,
    };
}

hyperdual4 operator-(const hyperdual4 &x, const hyperdual4 &y) {
    return {
            .real = x.real - y.real,
            .dual1 = x.dual1 - y.dual1,
            .dual2 = x.dual2 - y.dual2,
            .dual12 = x.dual12 - y.dual12,
            .dual3 = x.dual3 - y.dual3,
            .dual13 = x.dual13 - y.dual13,
            .dual23 = x.dual23 - y.dual23,
            .dual123 = x.dual123 - y.dual123,
            .dual4 = x.dual4 - y.dual4,
            .dual14 = x.dual14 - y.dual14,
            .dual24 = x.dual24 - y.dual24,
            .dual124 = x.dual124 - y.dual124,
            .dual34 = x.dual34 - y.dual34,
            .dual134 = x.dual134 - y.dual134,
            .dual234 = x.dual234 - y.dual234,
            .dual1234 = x.dual1234 - y.dual1234,
    };
}

hyperdual4 operator*(const hyperdual4 &x, const hyperdual4 &y) {
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
            .dual4 = x.dual4 * y.real + x.real * y.dual4,
            .dual14 = x.dual14 * y.real + x.dual4 * y.dual1 +
                      x.dual1 * y.dual4 + x.real * y.dual14,
            .dual24 = x.dual24 * y.real + x.dual4 * y.dual2 +
                      x.dual2 * y.dual4 + x.real * y.dual24,
            .dual124 = x.dual124 * y.real + x.dual24 * y.dual1 +
                       x.dual14 * y.dual2 + x.dual4 * y.dual12 +
                       x.dual12 * y.dual4 + x.dual2 * y.dual14 +
                       x.dual1 * y.dual24 + x.real * y.dual124,
            .dual34 = x.dual34 * y.real + x.dual4 * y.dual3 +
                      x.dual3 * y.dual4 + x.real * y.dual34,
            .dual134 = x.dual134 * y.real + x.dual34 * y.dual1 +
                       x.dual14 * y.dual3 + x.dual4 * y.dual13 +
                       x.dual13 * y.dual4 + x.dual3 * y.dual14 +
                       x.dual1 * y.dual34 + x.real * y.dual134,
            .dual234 = x.dual234 * y.real + x.dual34 * y.dual2 +
                       x.dual24 * y.dual3 + x.dual4 * y.dual23 +
                       x.dual23 * y.dual4 + x.dual3 * y.dual24 +
                       x.dual2 * y.dual34 + x.real * y.dual234,
            .dual1234 = x.dual1234 * y.real + x.dual234 * y.dual1 +
                        x.dual134 * y.dual2 + x.dual34 * y.dual12 +
                        x.dual124 * y.dual3 + x.dual24 * y.dual13 +
                        x.dual14 * y.dual23 + x.dual4 * y.dual123 +
                        x.dual123 * y.dual4 + x.dual23 * y.dual14 +
                        x.dual13 * y.dual24 + x.dual3 * y.dual124 +
                        x.dual12 * y.dual34 + x.dual2 * y.dual134 +
                        x.dual1 * y.dual234 + x.real * y.dual1234,
    };
}

hyperdual4 operator/(const hyperdual4 &x, const hyperdual4 &y) {
    const auto u = x.real / y.real;
    const auto u1 = x.dual1 / y.real;
    const auto u2 = x.dual2 / y.real;
    const auto u12 = x.dual12 / y.real;
    const auto u3 = x.dual3 / y.real;
    const auto u13 = x.dual13 / y.real;
    const auto u23 = x.dual23 / y.real;
    const auto u123 = x.dual123 / y.real;
    const auto u4 = x.dual4 / y.real;
    const auto u14 = x.dual14 / y.real;
    const auto u24 = x.dual24 / y.real;
    const auto u124 = x.dual124 / y.real;
    const auto u34 = x.dual34 / y.real;
    const auto u134 = x.dual134 / y.real;
    const auto u234 = x.dual234 / y.real;
    const auto u1234 = x.dual1234 / y.real;
    const auto v1 = y.dual1 / y.real;
    const auto v2 = y.dual2 / y.real;
    const auto v12 = y.dual12 / y.real;
    const auto v3 = y.dual3 / y.real;
    const auto v13 = y.dual13 / y.real;
    const auto v23 = y.dual23 / y.real;
    const auto v123 = y.dual123 / y.real;
    const auto v4 = y.dual4 / y.real;
    const auto v14 = y.dual14 / y.real;
    const auto v24 = y.dual24 / y.real;
    const auto v124 = y.dual124 / y.real;
    const auto v34 = y.dual34 / y.real;
    const auto v134 = y.dual134 / y.real;
    const auto v234 = y.dual234 / y.real;
    const auto v1234 = y.dual1234 / y.real;
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
            .dual4 = u4 - u * v4,
            .dual14 = u14 - u4 * v1 - u1 * v4 + 2 * u * v1 * v4 - u * v14,
            .dual24 = u24 - u4 * v2 - u2 * v4 + 2 * u * v2 * v4 - u * v24,
            .dual124 = u124 - u24 * v1 - u14 * v2 + 2 * u4 * v1 * v2 -
                       u4 * v12 - u12 * v4 + 2 * u2 * v1 * v4 +
                       2 * u1 * v2 * v4 - 6 * u * v1 * v2 * v4 +
                       2 * u * v12 * v4 - u2 * v14 + 2 * u * v2 * v14 -
                       u1 * v24 + 2 * u * v1 * v24 - u * v124,
            .dual34 = u34 - u4 * v3 - u3 * v4 + 2 * u * v3 * v4 - u * v34,
            .dual134 = u134 - u34 * v1 - u14 * v3 + 2 * u4 * v1 * v3 -
                       u4 * v13 - u13 * v4 + 2 * u3 * v1 * v4 +
                       2 * u1 * v3 * v4 - 6 * u * v1 * v3 * v4 +
                       2 * u * v13 * v4 - u3 * v14 + 2 * u * v3 * v14 -
                       u1 * v34 + 2 * u * v1 * v34 - u * v134,
            .dual234 = u234 - u34 * v2 - u24 * v3 + 2 * u4 * v2 * v3 -
                       u4 * v23 - u23 * v4 + 2 * u3 * v2 * v4 +
                       2 * u2 * v3 * v4 - 6 * u * v2 * v3 * v4 +
                       2 * u * v23 * v4 - u3 * v24 + 2 * u * v3 * v24 -
                       u2 * v34 + 2 * u * v2 * v34 - u * v234,
            .dual1234 = u1234 - u234 * v1 - u134 * v2 + 2 * u34 * v1 * v2 -
                        u34 * v12 - u124 * v3 + 2 * u24 * v1 * v3 +
                        2 * u14 * v2 * v3 - 6 * u4 * v1 * v2 * v3 +
                        2 * u4 * v12 * v3 - u24 * v13 + 2 * u4 * v2 * v13 -
                        u14 * v23 + 2 * u4 * v1 * v23 - u4 * v123 - u123 * v4 +
                        2 * u23 * v1 * v4 + 2 * u13 * v2 * v4 -
                        6 * u3 * v1 * v2 * v4 + 2 * u3 * v12 * v4 +
                        2 * u12 * v3 * v4 - 6 * u2 * v1 * v3 * v4 -
                        6 * u1 * v2 * v3 * v4 + 24 * u * v1 * v2 * v3 * v4 -
                        6 * u * v12 * v3 * v4 + 2 * u2 * v13 * v4 -
                        6 * u * v2 * v13 * v4 + 2 * u1 * v23 * v4 -
                        6 * u * v1 * v23 * v4 + 2 * u * v123 * v4 - u23 * v14 +
                        2 * u3 * v2 * v14 + 2 * u2 * v3 * v14 -
                        6 * u * v2 * v3 * v14 + 2 * u * v23 * v14 - u13 * v24 +
                        2 * u3 * v1 * v24 + 2 * u1 * v3 * v24 -
                        6 * u * v1 * v3 * v24 + 2 * u * v13 * v24 - u3 * v124 +
                        2 * u * v3 * v124 - u12 * v34 + 2 * u2 * v1 * v34 +
                        2 * u1 * v2 * v34 - 6 * u * v1 * v2 * v34 +
                        2 * u * v12 * v34 - u2 * v134 + 2 * u * v2 * v134 -
                        u1 * v234 + 2 * u * v1 * v234 - u * v1234,
    };
}

#endif // DZNL_HYPERDUAL4_H
