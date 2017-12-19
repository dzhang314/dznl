#ifndef DZNL_DUAL_H
#define DZNL_DUAL_H

struct dual {
    double real;
    double dual;
};

dual operator+(const dual &x) {
    return {
            .real = +x.real, .dual = +x.dual,
    };
}

dual operator-(const dual &x) {
    return {
            .real = -x.real, .dual = -x.dual,
    };
}

dual operator+(const dual &x, const dual &y) {
    return {
            .real = x.real + y.real, .dual = x.dual + y.dual,
    };
}

dual operator-(const dual &x, const dual &y) {
    return {
            .real = x.real - y.real, .dual = x.dual - y.dual,
    };
}

dual operator*(const dual &x, const dual &y) {
    return {
            .real = x.real * y.real, .dual = x.dual * y.real + x.real * y.dual,
    };
}

dual operator/(const dual &x, const dual &y) {
    const auto u = x.real / y.real;
    const auto u1 = x.dual / y.real;
    const auto v1 = y.dual / y.real;
    return {
            .real = u, .dual = u1 - u * v1,
    };
}

#endif // DZNL_DUAL_H
