#ifndef DZNL_HYPERDUAL5_H
#define DZNL_HYPERDUAL5_H

struct hyperdual5 {
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
    double dual5;
    double dual15;
    double dual25;
    double dual125;
    double dual35;
    double dual135;
    double dual235;
    double dual1235;
    double dual45;
    double dual145;
    double dual245;
    double dual1245;
    double dual345;
    double dual1345;
    double dual2345;
    double dual12345;
};

hyperdual5 operator+(const hyperdual5 &x) {
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
            .dual5 = +x.dual5,
            .dual15 = +x.dual15,
            .dual25 = +x.dual25,
            .dual125 = +x.dual125,
            .dual35 = +x.dual35,
            .dual135 = +x.dual135,
            .dual235 = +x.dual235,
            .dual1235 = +x.dual1235,
            .dual45 = +x.dual45,
            .dual145 = +x.dual145,
            .dual245 = +x.dual245,
            .dual1245 = +x.dual1245,
            .dual345 = +x.dual345,
            .dual1345 = +x.dual1345,
            .dual2345 = +x.dual2345,
            .dual12345 = +x.dual12345,
    };
}

hyperdual5 operator-(const hyperdual5 &x) {
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
            .dual5 = -x.dual5,
            .dual15 = -x.dual15,
            .dual25 = -x.dual25,
            .dual125 = -x.dual125,
            .dual35 = -x.dual35,
            .dual135 = -x.dual135,
            .dual235 = -x.dual235,
            .dual1235 = -x.dual1235,
            .dual45 = -x.dual45,
            .dual145 = -x.dual145,
            .dual245 = -x.dual245,
            .dual1245 = -x.dual1245,
            .dual345 = -x.dual345,
            .dual1345 = -x.dual1345,
            .dual2345 = -x.dual2345,
            .dual12345 = -x.dual12345,
    };
}

hyperdual5 operator+(const hyperdual5 &x, const hyperdual5 &y) {
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
            .dual5 = x.dual5 + y.dual5,
            .dual15 = x.dual15 + y.dual15,
            .dual25 = x.dual25 + y.dual25,
            .dual125 = x.dual125 + y.dual125,
            .dual35 = x.dual35 + y.dual35,
            .dual135 = x.dual135 + y.dual135,
            .dual235 = x.dual235 + y.dual235,
            .dual1235 = x.dual1235 + y.dual1235,
            .dual45 = x.dual45 + y.dual45,
            .dual145 = x.dual145 + y.dual145,
            .dual245 = x.dual245 + y.dual245,
            .dual1245 = x.dual1245 + y.dual1245,
            .dual345 = x.dual345 + y.dual345,
            .dual1345 = x.dual1345 + y.dual1345,
            .dual2345 = x.dual2345 + y.dual2345,
            .dual12345 = x.dual12345 + y.dual12345,
    };
}

hyperdual5 operator-(const hyperdual5 &x, const hyperdual5 &y) {
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
            .dual5 = x.dual5 - y.dual5,
            .dual15 = x.dual15 - y.dual15,
            .dual25 = x.dual25 - y.dual25,
            .dual125 = x.dual125 - y.dual125,
            .dual35 = x.dual35 - y.dual35,
            .dual135 = x.dual135 - y.dual135,
            .dual235 = x.dual235 - y.dual235,
            .dual1235 = x.dual1235 - y.dual1235,
            .dual45 = x.dual45 - y.dual45,
            .dual145 = x.dual145 - y.dual145,
            .dual245 = x.dual245 - y.dual245,
            .dual1245 = x.dual1245 - y.dual1245,
            .dual345 = x.dual345 - y.dual345,
            .dual1345 = x.dual1345 - y.dual1345,
            .dual2345 = x.dual2345 - y.dual2345,
            .dual12345 = x.dual12345 - y.dual12345,
    };
}

hyperdual5 operator*(const hyperdual5 &x, const hyperdual5 &y) {
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
            .dual5 = x.dual5 * y.real + x.real * y.dual5,
            .dual15 = x.dual15 * y.real + x.dual5 * y.dual1 +
                      x.dual1 * y.dual5 + x.real * y.dual15,
            .dual25 = x.dual25 * y.real + x.dual5 * y.dual2 +
                      x.dual2 * y.dual5 + x.real * y.dual25,
            .dual125 = x.dual125 * y.real + x.dual25 * y.dual1 +
                       x.dual15 * y.dual2 + x.dual5 * y.dual12 +
                       x.dual12 * y.dual5 + x.dual2 * y.dual15 +
                       x.dual1 * y.dual25 + x.real * y.dual125,
            .dual35 = x.dual35 * y.real + x.dual5 * y.dual3 +
                      x.dual3 * y.dual5 + x.real * y.dual35,
            .dual135 = x.dual135 * y.real + x.dual35 * y.dual1 +
                       x.dual15 * y.dual3 + x.dual5 * y.dual13 +
                       x.dual13 * y.dual5 + x.dual3 * y.dual15 +
                       x.dual1 * y.dual35 + x.real * y.dual135,
            .dual235 = x.dual235 * y.real + x.dual35 * y.dual2 +
                       x.dual25 * y.dual3 + x.dual5 * y.dual23 +
                       x.dual23 * y.dual5 + x.dual3 * y.dual25 +
                       x.dual2 * y.dual35 + x.real * y.dual235,
            .dual1235 = x.dual1235 * y.real + x.dual235 * y.dual1 +
                        x.dual135 * y.dual2 + x.dual35 * y.dual12 +
                        x.dual125 * y.dual3 + x.dual25 * y.dual13 +
                        x.dual15 * y.dual23 + x.dual5 * y.dual123 +
                        x.dual123 * y.dual5 + x.dual23 * y.dual15 +
                        x.dual13 * y.dual25 + x.dual3 * y.dual125 +
                        x.dual12 * y.dual35 + x.dual2 * y.dual135 +
                        x.dual1 * y.dual235 + x.real * y.dual1235,
            .dual45 = x.dual45 * y.real + x.dual5 * y.dual4 +
                      x.dual4 * y.dual5 + x.real * y.dual45,
            .dual145 = x.dual145 * y.real + x.dual45 * y.dual1 +
                       x.dual15 * y.dual4 + x.dual5 * y.dual14 +
                       x.dual14 * y.dual5 + x.dual4 * y.dual15 +
                       x.dual1 * y.dual45 + x.real * y.dual145,
            .dual245 = x.dual245 * y.real + x.dual45 * y.dual2 +
                       x.dual25 * y.dual4 + x.dual5 * y.dual24 +
                       x.dual24 * y.dual5 + x.dual4 * y.dual25 +
                       x.dual2 * y.dual45 + x.real * y.dual245,
            .dual1245 = x.dual1245 * y.real + x.dual245 * y.dual1 +
                        x.dual145 * y.dual2 + x.dual45 * y.dual12 +
                        x.dual125 * y.dual4 + x.dual25 * y.dual14 +
                        x.dual15 * y.dual24 + x.dual5 * y.dual124 +
                        x.dual124 * y.dual5 + x.dual24 * y.dual15 +
                        x.dual14 * y.dual25 + x.dual4 * y.dual125 +
                        x.dual12 * y.dual45 + x.dual2 * y.dual145 +
                        x.dual1 * y.dual245 + x.real * y.dual1245,
            .dual345 = x.dual345 * y.real + x.dual45 * y.dual3 +
                       x.dual35 * y.dual4 + x.dual5 * y.dual34 +
                       x.dual34 * y.dual5 + x.dual4 * y.dual35 +
                       x.dual3 * y.dual45 + x.real * y.dual345,
            .dual1345 = x.dual1345 * y.real + x.dual345 * y.dual1 +
                        x.dual145 * y.dual3 + x.dual45 * y.dual13 +
                        x.dual135 * y.dual4 + x.dual35 * y.dual14 +
                        x.dual15 * y.dual34 + x.dual5 * y.dual134 +
                        x.dual134 * y.dual5 + x.dual34 * y.dual15 +
                        x.dual14 * y.dual35 + x.dual4 * y.dual135 +
                        x.dual13 * y.dual45 + x.dual3 * y.dual145 +
                        x.dual1 * y.dual345 + x.real * y.dual1345,
            .dual2345 = x.dual2345 * y.real + x.dual345 * y.dual2 +
                        x.dual245 * y.dual3 + x.dual45 * y.dual23 +
                        x.dual235 * y.dual4 + x.dual35 * y.dual24 +
                        x.dual25 * y.dual34 + x.dual5 * y.dual234 +
                        x.dual234 * y.dual5 + x.dual34 * y.dual25 +
                        x.dual24 * y.dual35 + x.dual4 * y.dual235 +
                        x.dual23 * y.dual45 + x.dual3 * y.dual245 +
                        x.dual2 * y.dual345 + x.real * y.dual2345,
            .dual12345 = x.dual12345 * y.real + x.dual2345 * y.dual1 +
                         x.dual1345 * y.dual2 + x.dual345 * y.dual12 +
                         x.dual1245 * y.dual3 + x.dual245 * y.dual13 +
                         x.dual145 * y.dual23 + x.dual45 * y.dual123 +
                         x.dual1235 * y.dual4 + x.dual235 * y.dual14 +
                         x.dual135 * y.dual24 + x.dual35 * y.dual124 +
                         x.dual125 * y.dual34 + x.dual25 * y.dual134 +
                         x.dual15 * y.dual234 + x.dual5 * y.dual1234 +
                         x.dual1234 * y.dual5 + x.dual234 * y.dual15 +
                         x.dual134 * y.dual25 + x.dual34 * y.dual125 +
                         x.dual124 * y.dual35 + x.dual24 * y.dual135 +
                         x.dual14 * y.dual235 + x.dual4 * y.dual1235 +
                         x.dual123 * y.dual45 + x.dual23 * y.dual145 +
                         x.dual13 * y.dual245 + x.dual3 * y.dual1245 +
                         x.dual12 * y.dual345 + x.dual2 * y.dual1345 +
                         x.dual1 * y.dual2345 + x.real * y.dual12345,
    };
}

hyperdual5 operator/(const hyperdual5 &x, const hyperdual5 &y) {
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
    const auto u5 = x.dual5 / y.real;
    const auto u15 = x.dual15 / y.real;
    const auto u25 = x.dual25 / y.real;
    const auto u125 = x.dual125 / y.real;
    const auto u35 = x.dual35 / y.real;
    const auto u135 = x.dual135 / y.real;
    const auto u235 = x.dual235 / y.real;
    const auto u1235 = x.dual1235 / y.real;
    const auto u45 = x.dual45 / y.real;
    const auto u145 = x.dual145 / y.real;
    const auto u245 = x.dual245 / y.real;
    const auto u1245 = x.dual1245 / y.real;
    const auto u345 = x.dual345 / y.real;
    const auto u1345 = x.dual1345 / y.real;
    const auto u2345 = x.dual2345 / y.real;
    const auto u12345 = x.dual12345 / y.real;
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
    const auto v5 = y.dual5 / y.real;
    const auto v15 = y.dual15 / y.real;
    const auto v25 = y.dual25 / y.real;
    const auto v125 = y.dual125 / y.real;
    const auto v35 = y.dual35 / y.real;
    const auto v135 = y.dual135 / y.real;
    const auto v235 = y.dual235 / y.real;
    const auto v1235 = y.dual1235 / y.real;
    const auto v45 = y.dual45 / y.real;
    const auto v145 = y.dual145 / y.real;
    const auto v245 = y.dual245 / y.real;
    const auto v1245 = y.dual1245 / y.real;
    const auto v345 = y.dual345 / y.real;
    const auto v1345 = y.dual1345 / y.real;
    const auto v2345 = y.dual2345 / y.real;
    const auto v12345 = y.dual12345 / y.real;
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
            .dual5 = u5 - u * v5,
            .dual15 = u15 - u5 * v1 - u1 * v5 + 2 * u * v1 * v5 - u * v15,
            .dual25 = u25 - u5 * v2 - u2 * v5 + 2 * u * v2 * v5 - u * v25,
            .dual125 = u125 - u25 * v1 - u15 * v2 + 2 * u5 * v1 * v2 -
                       u5 * v12 - u12 * v5 + 2 * u2 * v1 * v5 +
                       2 * u1 * v2 * v5 - 6 * u * v1 * v2 * v5 +
                       2 * u * v12 * v5 - u2 * v15 + 2 * u * v2 * v15 -
                       u1 * v25 + 2 * u * v1 * v25 - u * v125,
            .dual35 = u35 - u5 * v3 - u3 * v5 + 2 * u * v3 * v5 - u * v35,
            .dual135 = u135 - u35 * v1 - u15 * v3 + 2 * u5 * v1 * v3 -
                       u5 * v13 - u13 * v5 + 2 * u3 * v1 * v5 +
                       2 * u1 * v3 * v5 - 6 * u * v1 * v3 * v5 +
                       2 * u * v13 * v5 - u3 * v15 + 2 * u * v3 * v15 -
                       u1 * v35 + 2 * u * v1 * v35 - u * v135,
            .dual235 = u235 - u35 * v2 - u25 * v3 + 2 * u5 * v2 * v3 -
                       u5 * v23 - u23 * v5 + 2 * u3 * v2 * v5 +
                       2 * u2 * v3 * v5 - 6 * u * v2 * v3 * v5 +
                       2 * u * v23 * v5 - u3 * v25 + 2 * u * v3 * v25 -
                       u2 * v35 + 2 * u * v2 * v35 - u * v235,
            .dual1235 = u1235 - u235 * v1 - u135 * v2 + 2 * u35 * v1 * v2 -
                        u35 * v12 - u125 * v3 + 2 * u25 * v1 * v3 +
                        2 * u15 * v2 * v3 - 6 * u5 * v1 * v2 * v3 +
                        2 * u5 * v12 * v3 - u25 * v13 + 2 * u5 * v2 * v13 -
                        u15 * v23 + 2 * u5 * v1 * v23 - u5 * v123 - u123 * v5 +
                        2 * u23 * v1 * v5 + 2 * u13 * v2 * v5 -
                        6 * u3 * v1 * v2 * v5 + 2 * u3 * v12 * v5 +
                        2 * u12 * v3 * v5 - 6 * u2 * v1 * v3 * v5 -
                        6 * u1 * v2 * v3 * v5 + 24 * u * v1 * v2 * v3 * v5 -
                        6 * u * v12 * v3 * v5 + 2 * u2 * v13 * v5 -
                        6 * u * v2 * v13 * v5 + 2 * u1 * v23 * v5 -
                        6 * u * v1 * v23 * v5 + 2 * u * v123 * v5 - u23 * v15 +
                        2 * u3 * v2 * v15 + 2 * u2 * v3 * v15 -
                        6 * u * v2 * v3 * v15 + 2 * u * v23 * v15 - u13 * v25 +
                        2 * u3 * v1 * v25 + 2 * u1 * v3 * v25 -
                        6 * u * v1 * v3 * v25 + 2 * u * v13 * v25 - u3 * v125 +
                        2 * u * v3 * v125 - u12 * v35 + 2 * u2 * v1 * v35 +
                        2 * u1 * v2 * v35 - 6 * u * v1 * v2 * v35 +
                        2 * u * v12 * v35 - u2 * v135 + 2 * u * v2 * v135 -
                        u1 * v235 + 2 * u * v1 * v235 - u * v1235,
            .dual45 = u45 - u5 * v4 - u4 * v5 + 2 * u * v4 * v5 - u * v45,
            .dual145 = u145 - u45 * v1 - u15 * v4 + 2 * u5 * v1 * v4 -
                       u5 * v14 - u14 * v5 + 2 * u4 * v1 * v5 +
                       2 * u1 * v4 * v5 - 6 * u * v1 * v4 * v5 +
                       2 * u * v14 * v5 - u4 * v15 + 2 * u * v4 * v15 -
                       u1 * v45 + 2 * u * v1 * v45 - u * v145,
            .dual245 = u245 - u45 * v2 - u25 * v4 + 2 * u5 * v2 * v4 -
                       u5 * v24 - u24 * v5 + 2 * u4 * v2 * v5 +
                       2 * u2 * v4 * v5 - 6 * u * v2 * v4 * v5 +
                       2 * u * v24 * v5 - u4 * v25 + 2 * u * v4 * v25 -
                       u2 * v45 + 2 * u * v2 * v45 - u * v245,
            .dual1245 = u1245 - u245 * v1 - u145 * v2 + 2 * u45 * v1 * v2 -
                        u45 * v12 - u125 * v4 + 2 * u25 * v1 * v4 +
                        2 * u15 * v2 * v4 - 6 * u5 * v1 * v2 * v4 +
                        2 * u5 * v12 * v4 - u25 * v14 + 2 * u5 * v2 * v14 -
                        u15 * v24 + 2 * u5 * v1 * v24 - u5 * v124 - u124 * v5 +
                        2 * u24 * v1 * v5 + 2 * u14 * v2 * v5 -
                        6 * u4 * v1 * v2 * v5 + 2 * u4 * v12 * v5 +
                        2 * u12 * v4 * v5 - 6 * u2 * v1 * v4 * v5 -
                        6 * u1 * v2 * v4 * v5 + 24 * u * v1 * v2 * v4 * v5 -
                        6 * u * v12 * v4 * v5 + 2 * u2 * v14 * v5 -
                        6 * u * v2 * v14 * v5 + 2 * u1 * v24 * v5 -
                        6 * u * v1 * v24 * v5 + 2 * u * v124 * v5 - u24 * v15 +
                        2 * u4 * v2 * v15 + 2 * u2 * v4 * v15 -
                        6 * u * v2 * v4 * v15 + 2 * u * v24 * v15 - u14 * v25 +
                        2 * u4 * v1 * v25 + 2 * u1 * v4 * v25 -
                        6 * u * v1 * v4 * v25 + 2 * u * v14 * v25 - u4 * v125 +
                        2 * u * v4 * v125 - u12 * v45 + 2 * u2 * v1 * v45 +
                        2 * u1 * v2 * v45 - 6 * u * v1 * v2 * v45 +
                        2 * u * v12 * v45 - u2 * v145 + 2 * u * v2 * v145 -
                        u1 * v245 + 2 * u * v1 * v245 - u * v1245,
            .dual345 = u345 - u45 * v3 - u35 * v4 + 2 * u5 * v3 * v4 -
                       u5 * v34 - u34 * v5 + 2 * u4 * v3 * v5 +
                       2 * u3 * v4 * v5 - 6 * u * v3 * v4 * v5 +
                       2 * u * v34 * v5 - u4 * v35 + 2 * u * v4 * v35 -
                       u3 * v45 + 2 * u * v3 * v45 - u * v345,
            .dual1345 = u1345 - u345 * v1 - u145 * v3 + 2 * u45 * v1 * v3 -
                        u45 * v13 - u135 * v4 + 2 * u35 * v1 * v4 +
                        2 * u15 * v3 * v4 - 6 * u5 * v1 * v3 * v4 +
                        2 * u5 * v13 * v4 - u35 * v14 + 2 * u5 * v3 * v14 -
                        u15 * v34 + 2 * u5 * v1 * v34 - u5 * v134 - u134 * v5 +
                        2 * u34 * v1 * v5 + 2 * u14 * v3 * v5 -
                        6 * u4 * v1 * v3 * v5 + 2 * u4 * v13 * v5 +
                        2 * u13 * v4 * v5 - 6 * u3 * v1 * v4 * v5 -
                        6 * u1 * v3 * v4 * v5 + 24 * u * v1 * v3 * v4 * v5 -
                        6 * u * v13 * v4 * v5 + 2 * u3 * v14 * v5 -
                        6 * u * v3 * v14 * v5 + 2 * u1 * v34 * v5 -
                        6 * u * v1 * v34 * v5 + 2 * u * v134 * v5 - u34 * v15 +
                        2 * u4 * v3 * v15 + 2 * u3 * v4 * v15 -
                        6 * u * v3 * v4 * v15 + 2 * u * v34 * v15 - u14 * v35 +
                        2 * u4 * v1 * v35 + 2 * u1 * v4 * v35 -
                        6 * u * v1 * v4 * v35 + 2 * u * v14 * v35 - u4 * v135 +
                        2 * u * v4 * v135 - u13 * v45 + 2 * u3 * v1 * v45 +
                        2 * u1 * v3 * v45 - 6 * u * v1 * v3 * v45 +
                        2 * u * v13 * v45 - u3 * v145 + 2 * u * v3 * v145 -
                        u1 * v345 + 2 * u * v1 * v345 - u * v1345,
            .dual2345 = u2345 - u345 * v2 - u245 * v3 + 2 * u45 * v2 * v3 -
                        u45 * v23 - u235 * v4 + 2 * u35 * v2 * v4 +
                        2 * u25 * v3 * v4 - 6 * u5 * v2 * v3 * v4 +
                        2 * u5 * v23 * v4 - u35 * v24 + 2 * u5 * v3 * v24 -
                        u25 * v34 + 2 * u5 * v2 * v34 - u5 * v234 - u234 * v5 +
                        2 * u34 * v2 * v5 + 2 * u24 * v3 * v5 -
                        6 * u4 * v2 * v3 * v5 + 2 * u4 * v23 * v5 +
                        2 * u23 * v4 * v5 - 6 * u3 * v2 * v4 * v5 -
                        6 * u2 * v3 * v4 * v5 + 24 * u * v2 * v3 * v4 * v5 -
                        6 * u * v23 * v4 * v5 + 2 * u3 * v24 * v5 -
                        6 * u * v3 * v24 * v5 + 2 * u2 * v34 * v5 -
                        6 * u * v2 * v34 * v5 + 2 * u * v234 * v5 - u34 * v25 +
                        2 * u4 * v3 * v25 + 2 * u3 * v4 * v25 -
                        6 * u * v3 * v4 * v25 + 2 * u * v34 * v25 - u24 * v35 +
                        2 * u4 * v2 * v35 + 2 * u2 * v4 * v35 -
                        6 * u * v2 * v4 * v35 + 2 * u * v24 * v35 - u4 * v235 +
                        2 * u * v4 * v235 - u23 * v45 + 2 * u3 * v2 * v45 +
                        2 * u2 * v3 * v45 - 6 * u * v2 * v3 * v45 +
                        2 * u * v23 * v45 - u3 * v245 + 2 * u * v3 * v245 -
                        u2 * v345 + 2 * u * v2 * v345 - u * v2345,
            .dual12345 =
                    u12345 - u2345 * v1 - u1345 * v2 + 2 * u345 * v1 * v2 -
                    u345 * v12 - u1245 * v3 + 2 * u245 * v1 * v3 +
                    2 * u145 * v2 * v3 - 6 * u45 * v1 * v2 * v3 +
                    2 * u45 * v12 * v3 - u245 * v13 + 2 * u45 * v2 * v13 -
                    u145 * v23 + 2 * u45 * v1 * v23 - u45 * v123 - u1235 * v4 +
                    2 * u235 * v1 * v4 + 2 * u135 * v2 * v4 -
                    6 * u35 * v1 * v2 * v4 + 2 * u35 * v12 * v4 +
                    2 * u125 * v3 * v4 - 6 * u25 * v1 * v3 * v4 -
                    6 * u15 * v2 * v3 * v4 + 24 * u5 * v1 * v2 * v3 * v4 -
                    6 * u5 * v12 * v3 * v4 + 2 * u25 * v13 * v4 -
                    6 * u5 * v2 * v13 * v4 + 2 * u15 * v23 * v4 -
                    6 * u5 * v1 * v23 * v4 + 2 * u5 * v123 * v4 - u235 * v14 +
                    2 * u35 * v2 * v14 + 2 * u25 * v3 * v14 -
                    6 * u5 * v2 * v3 * v14 + 2 * u5 * v23 * v14 - u135 * v24 +
                    2 * u35 * v1 * v24 + 2 * u15 * v3 * v24 -
                    6 * u5 * v1 * v3 * v24 + 2 * u5 * v13 * v24 - u35 * v124 +
                    2 * u5 * v3 * v124 - u125 * v34 + 2 * u25 * v1 * v34 +
                    2 * u15 * v2 * v34 - 6 * u5 * v1 * v2 * v34 +
                    2 * u5 * v12 * v34 - u25 * v134 + 2 * u5 * v2 * v134 -
                    u15 * v234 + 2 * u5 * v1 * v234 - u5 * v1234 - u1234 * v5 +
                    2 * u234 * v1 * v5 + 2 * u134 * v2 * v5 -
                    6 * u34 * v1 * v2 * v5 + 2 * u34 * v12 * v5 +
                    2 * u124 * v3 * v5 - 6 * u24 * v1 * v3 * v5 -
                    6 * u14 * v2 * v3 * v5 + 24 * u4 * v1 * v2 * v3 * v5 -
                    6 * u4 * v12 * v3 * v5 + 2 * u24 * v13 * v5 -
                    6 * u4 * v2 * v13 * v5 + 2 * u14 * v23 * v5 -
                    6 * u4 * v1 * v23 * v5 + 2 * u4 * v123 * v5 +
                    2 * u123 * v4 * v5 - 6 * u23 * v1 * v4 * v5 -
                    6 * u13 * v2 * v4 * v5 + 24 * u3 * v1 * v2 * v4 * v5 -
                    6 * u3 * v12 * v4 * v5 - 6 * u12 * v3 * v4 * v5 +
                    24 * u2 * v1 * v3 * v4 * v5 + 24 * u1 * v2 * v3 * v4 * v5 -
                    120 * u * v1 * v2 * v3 * v4 * v5 +
                    24 * u * v12 * v3 * v4 * v5 - 6 * u2 * v13 * v4 * v5 +
                    24 * u * v2 * v13 * v4 * v5 - 6 * u1 * v23 * v4 * v5 +
                    24 * u * v1 * v23 * v4 * v5 - 6 * u * v123 * v4 * v5 +
                    2 * u23 * v14 * v5 - 6 * u3 * v2 * v14 * v5 -
                    6 * u2 * v3 * v14 * v5 + 24 * u * v2 * v3 * v14 * v5 -
                    6 * u * v23 * v14 * v5 + 2 * u13 * v24 * v5 -
                    6 * u3 * v1 * v24 * v5 - 6 * u1 * v3 * v24 * v5 +
                    24 * u * v1 * v3 * v24 * v5 - 6 * u * v13 * v24 * v5 +
                    2 * u3 * v124 * v5 - 6 * u * v3 * v124 * v5 +
                    2 * u12 * v34 * v5 - 6 * u2 * v1 * v34 * v5 -
                    6 * u1 * v2 * v34 * v5 + 24 * u * v1 * v2 * v34 * v5 -
                    6 * u * v12 * v34 * v5 + 2 * u2 * v134 * v5 -
                    6 * u * v2 * v134 * v5 + 2 * u1 * v234 * v5 -
                    6 * u * v1 * v234 * v5 + 2 * u * v1234 * v5 - u234 * v15 +
                    2 * u34 * v2 * v15 + 2 * u24 * v3 * v15 -
                    6 * u4 * v2 * v3 * v15 + 2 * u4 * v23 * v15 +
                    2 * u23 * v4 * v15 - 6 * u3 * v2 * v4 * v15 -
                    6 * u2 * v3 * v4 * v15 + 24 * u * v2 * v3 * v4 * v15 -
                    6 * u * v23 * v4 * v15 + 2 * u3 * v24 * v15 -
                    6 * u * v3 * v24 * v15 + 2 * u2 * v34 * v15 -
                    6 * u * v2 * v34 * v15 + 2 * u * v234 * v15 - u134 * v25 +
                    2 * u34 * v1 * v25 + 2 * u14 * v3 * v25 -
                    6 * u4 * v1 * v3 * v25 + 2 * u4 * v13 * v25 +
                    2 * u13 * v4 * v25 - 6 * u3 * v1 * v4 * v25 -
                    6 * u1 * v3 * v4 * v25 + 24 * u * v1 * v3 * v4 * v25 -
                    6 * u * v13 * v4 * v25 + 2 * u3 * v14 * v25 -
                    6 * u * v3 * v14 * v25 + 2 * u1 * v34 * v25 -
                    6 * u * v1 * v34 * v25 + 2 * u * v134 * v25 - u34 * v125 +
                    2 * u4 * v3 * v125 + 2 * u3 * v4 * v125 -
                    6 * u * v3 * v4 * v125 + 2 * u * v34 * v125 - u124 * v35 +
                    2 * u24 * v1 * v35 + 2 * u14 * v2 * v35 -
                    6 * u4 * v1 * v2 * v35 + 2 * u4 * v12 * v35 +
                    2 * u12 * v4 * v35 - 6 * u2 * v1 * v4 * v35 -
                    6 * u1 * v2 * v4 * v35 + 24 * u * v1 * v2 * v4 * v35 -
                    6 * u * v12 * v4 * v35 + 2 * u2 * v14 * v35 -
                    6 * u * v2 * v14 * v35 + 2 * u1 * v24 * v35 -
                    6 * u * v1 * v24 * v35 + 2 * u * v124 * v35 - u24 * v135 +
                    2 * u4 * v2 * v135 + 2 * u2 * v4 * v135 -
                    6 * u * v2 * v4 * v135 + 2 * u * v24 * v135 - u14 * v235 +
                    2 * u4 * v1 * v235 + 2 * u1 * v4 * v235 -
                    6 * u * v1 * v4 * v235 + 2 * u * v14 * v235 - u4 * v1235 +
                    2 * u * v4 * v1235 - u123 * v45 + 2 * u23 * v1 * v45 +
                    2 * u13 * v2 * v45 - 6 * u3 * v1 * v2 * v45 +
                    2 * u3 * v12 * v45 + 2 * u12 * v3 * v45 -
                    6 * u2 * v1 * v3 * v45 - 6 * u1 * v2 * v3 * v45 +
                    24 * u * v1 * v2 * v3 * v45 - 6 * u * v12 * v3 * v45 +
                    2 * u2 * v13 * v45 - 6 * u * v2 * v13 * v45 +
                    2 * u1 * v23 * v45 - 6 * u * v1 * v23 * v45 +
                    2 * u * v123 * v45 - u23 * v145 + 2 * u3 * v2 * v145 +
                    2 * u2 * v3 * v145 - 6 * u * v2 * v3 * v145 +
                    2 * u * v23 * v145 - u13 * v245 + 2 * u3 * v1 * v245 +
                    2 * u1 * v3 * v245 - 6 * u * v1 * v3 * v245 +
                    2 * u * v13 * v245 - u3 * v1245 + 2 * u * v3 * v1245 -
                    u12 * v345 + 2 * u2 * v1 * v345 + 2 * u1 * v2 * v345 -
                    6 * u * v1 * v2 * v345 + 2 * u * v12 * v345 - u2 * v1345 +
                    2 * u * v2 * v1345 - u1 * v2345 + 2 * u * v1 * v2345 -
                    u * v12345,
    };
}

#endif // DZNL_HYPERDUAL5_H
