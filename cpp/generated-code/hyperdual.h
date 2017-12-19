#ifndef DZNL_HYPERDUAL_H
#define DZNL_HYPERDUAL_H

struct hyperdual {
    double real;
    double dual1;
    double dual2;
    double dual12;
};

hyperdual operator+(const hyperdual &x) {
    return {
            .real = +x.real,
            .dual1 = +x.dual1,
            .dual2 = +x.dual2,
            .dual12 = +x.dual12,
    };
}

hyperdual operator-(const hyperdual &x) {
    return {
            .real = -x.real,
            .dual1 = -x.dual1,
            .dual2 = -x.dual2,
            .dual12 = -x.dual12,
    };
}

hyperdual operator+(const hyperdual &x, const hyperdual &y) {
    return {
            .real = x.real + y.real,
            .dual1 = x.dual1 + y.dual1,
            .dual2 = x.dual2 + y.dual2,
            .dual12 = x.dual12 + y.dual12,
    };
}

hyperdual operator-(const hyperdual &x, const hyperdual &y) {
    return {
            .real = x.real - y.real,
            .dual1 = x.dual1 - y.dual1,
            .dual2 = x.dual2 - y.dual2,
            .dual12 = x.dual12 - y.dual12,
    };
}

hyperdual operator*(const hyperdual &x, const hyperdual &y) {
    return {
            .real = x.real * y.real,
            .dual1 = x.dual1 * y.real + x.real * y.dual1,
            .dual2 = x.dual2 * y.real + x.real * y.dual2,
            .dual12 = x.dual12 * y.real + x.dual2 * y.dual1 +
                      x.dual1 * y.dual2 + x.real * y.dual12,
    };
}

hyperdual operator/(const hyperdual &x, const hyperdual &y) {
    const auto u = x.real / y.real;
    const auto u1 = x.dual1 / y.real;
    const auto u2 = x.dual2 / y.real;
    const auto u12 = x.dual12 / y.real;
    const auto v1 = y.dual1 / y.real;
    const auto v2 = y.dual2 / y.real;
    const auto v12 = y.dual12 / y.real;
    return {
            .real = u,
            .dual1 = u1 - u * v1,
            .dual2 = u2 - u * v2,
            .dual12 = u12 - u2 * v1 - u1 * v2 + 2 * u * v1 * v2 - u * v12,
    };
}

#endif // DZNL_HYPERDUAL_H
