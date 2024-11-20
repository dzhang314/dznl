import typing
import z3


def count_leading_zeros(b: z3.BitVecRef, result_width: int) -> z3.BitVecRef:
    result: z3.BitVecRef = z3.BitVecVal(0, result_width)
    for i in range(1, b.size() + 1):
        substr: z3.BitVecRef = z3.Extract(b.size() - 1, b.size() - i, b)
        zeros: z3.BitVecRef = z3.BitVecVal(0, i)
        result = z3.If(substr == zeros, z3.BitVecVal(i, result_width), result)
    return result


def count_leading_ones(b: z3.BitVecRef, result_width: int) -> z3.BitVecRef:
    result: z3.BitVecRef = z3.BitVecVal(0, result_width)
    for i in range(1, b.size() + 1):
        substr: z3.BitVecRef = z3.Extract(b.size() - 1, b.size() - i, b)
        ones: z3.BitVecRef = z3.BitVecVal(2**i - 1, i)
        result = z3.If(substr == ones, z3.BitVecVal(i, result_width), result)
    return result


def count_trailing_zeros(b: z3.BitVecRef, result_width: int) -> z3.BitVecRef:
    result: z3.BitVecRef = z3.BitVecVal(0, result_width)
    for i in range(1, b.size() + 1):
        substr: z3.BitVecRef = z3.Extract(i - 1, 0, b)
        zeros: z3.BitVecRef = z3.BitVecVal(0, i)
        result = z3.If(substr == zeros, z3.BitVecVal(i, result_width), result)
    return result


def count_trailing_ones(b: z3.BitVecRef, result_width: int) -> z3.BitVecRef:
    result: z3.BitVecRef = z3.BitVecVal(0, result_width)
    for i in range(1, b.size() + 1):
        substr: z3.BitVecRef = z3.Extract(i - 1, 0, b)
        ones: z3.BitVecRef = z3.BitVecVal(2**i - 1, i)
        result = z3.If(substr == ones, z3.BitVecVal(i, result_width), result)
    return result


BoolVar = typing.TypeVar("BoolVar", z3.BoolRef, z3.BitVecRef)
IntVar = typing.TypeVar("IntVar", z3.ArithRef, z3.BitVecRef)
FloatVar = typing.TypeVar("FloatVar")


def two_sum_lemmas(
    x: FloatVar,
    y: FloatVar,
    s: FloatVar,
    e: FloatVar,
    sx: BoolVar,
    sy: BoolVar,
    ss: BoolVar,
    se: BoolVar,
    lbx: z3.BoolRef,
    lby: z3.BoolRef,
    lbs: z3.BoolRef,
    lbe: z3.BoolRef,
    tbx: z3.BoolRef,
    tby: z3.BoolRef,
    tbs: z3.BoolRef,
    tbe: z3.BoolRef,
    ex: IntVar,
    ey: IntVar,
    es: IntVar,
    ee: IntVar,
    nlbx: IntVar,
    nlby: IntVar,
    nlbs: IntVar,
    nlbe: IntVar,
    ntbx: IntVar,
    ntby: IntVar,
    ntbs: IntVar,
    ntbe: IntVar,
    is_zero: typing.Callable[[FloatVar], z3.BoolRef],
    is_positive: typing.Callable[[FloatVar], z3.BoolRef],
    is_negative: typing.Callable[[FloatVar], z3.BoolRef],
    is_equal: typing.Callable[[FloatVar, FloatVar], z3.BoolRef],
    p: IntVar,
    one: IntVar,
    two: IntVar,
    three: IntVar,
) -> dict[str, z3.BoolRef]:

    result: dict[str, z3.BoolRef] = {}

    x_zero: z3.BoolRef = is_zero(x)
    x_pos_zero: z3.BoolRef = z3.And(is_positive(x), x_zero)
    x_neg_zero: z3.BoolRef = z3.And(is_negative(x), x_zero)
    y_zero: z3.BoolRef = is_zero(y)
    y_pos_zero: z3.BoolRef = z3.And(is_positive(y), y_zero)
    y_neg_zero: z3.BoolRef = z3.And(is_negative(y), y_zero)
    s_zero: z3.BoolRef = is_zero(s)
    s_pos_zero: z3.BoolRef = z3.And(is_positive(s), s_zero)
    s_neg_zero: z3.BoolRef = z3.And(is_negative(s), s_zero)
    e_pos_zero: z3.BoolRef = z3.And(is_positive(e), is_zero(e))
    s_equals_x: z3.BoolRef = is_equal(s, x)
    s_equals_y: z3.BoolRef = is_equal(s, y)
    e_equals_x: z3.BoolRef = is_equal(e, x)
    e_equals_y: z3.BoolRef = is_equal(e, y)

    ############################################################################

    result["TwoSum-AXD"] = z3.Implies(
        z3.And(
            sx != sy,
            z3.Not(lbx),
            nlbx + one < p,  # cannot be weakened
            ex > ey + nlbx + one,  # cannot be weakened
        ),
        es == ex,
    )
    result["TwoSum-AYD"] = z3.Implies(
        z3.And(
            sx != sy,
            z3.Not(lby),
            nlby + one < p,  # cannot be weakened
            ex + nlby + one < ey,  # cannot be weakened
        ),
        es == ey,
    )

    result["TwoSum-BXD"] = z3.Implies(
        z3.And(
            sx != sy,
            lbx,
            ex > ey + one,  # cannot be weakened
        ),
        es == ex,
    )
    result["TwoSum-BYD"] = z3.Implies(
        z3.And(
            sx != sy,
            lby,
            ex + one < ey,  # cannot be weakened
        ),
        es == ey,
    )

    ############################################################################

    case_0p: z3.BoolRef = z3.Or(
        z3.And(x_pos_zero, y_pos_zero),
        z3.And(x_pos_zero, y_neg_zero),
        z3.And(x_neg_zero, y_pos_zero),
    )
    result["TwoSum-0P"] = z3.Implies(case_0p, z3.And(s_pos_zero, e_pos_zero))

    case_0n: z3.BoolRef = z3.And(x_neg_zero, y_neg_zero)
    result["TwoSum-0N"] = z3.Implies(case_0n, z3.And(s_neg_zero, e_pos_zero))

    case_0x: z3.BoolRef = z3.And(z3.Not(x_zero), y_zero)
    result["TwoSum-0X"] = z3.Implies(case_0x, z3.And(s_equals_x, e_pos_zero))

    case_0y: z3.BoolRef = z3.And(x_zero, z3.Not(y_zero))
    result["TwoSum-0Y"] = z3.Implies(case_0y, z3.And(s_equals_y, e_pos_zero))

    ############################################################################

    case_1x: z3.BoolRef = z3.And(ex > ey + (p + one), z3.Not(y_zero))
    result["TwoSum-1X"] = z3.Implies(case_1x, z3.And(s_equals_x, e_equals_y))

    case_1y: z3.BoolRef = z3.And(ex + (p + one) < ey, z3.Not(x_zero))
    result["TwoSum-1Y"] = z3.Implies(case_1y, z3.And(s_equals_y, e_equals_x))

    ############################################################################

    case_2xs: z3.BoolRef = z3.And(
        ex == ey + (p + one),
        sx == sy,
        z3.Not(y_zero),  # cannot be omitted
    )
    result["TwoSum-2XS"] = z3.Implies(case_2xs, z3.And(s_equals_x, e_equals_y))

    case_2ys: z3.BoolRef = z3.And(
        ex + (p + one) == ey,
        sx == sy,
        z3.Not(x_zero),  # cannot be omitted
    )
    result["TwoSum-2YS"] = z3.Implies(case_2ys, z3.And(s_equals_y, e_equals_x))

    case_2xd: z3.BoolRef = z3.And(
        ex == ey + (p + one),
        sx != sy,
        z3.Not(y_zero),  # cannot be omitted
    )
    result["TwoSum-2XD"] = z3.Implies(
        case_2xd,
        z3.Or(
            z3.And(
                ss == sx,
                es == ex - one,
                se != sy,
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey - one,  # cannot be strengthened
            ),
            z3.And(s_equals_x, e_equals_y),
        ),
    )

    case_2yd: z3.BoolRef = z3.And(
        ex + (p + one) == ey,
        sx != sy,
        z3.Not(x_zero),  # cannot be omitted
    )
    result["TwoSum-2YD"] = z3.Implies(
        case_2yd,
        z3.Or(
            z3.And(
                ss == sy,
                es == ey - one,
                se != sx,
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex - one,  # cannot be strengthened
            ),
            z3.And(s_equals_y, e_equals_x),
        ),
    )

    ############################################################################

    case_3xs: z3.BoolRef = z3.And(ex == ey + p, sx == sy)
    result["TwoSum-3XS"] = z3.Implies(
        case_3xs,
        z3.Or(
            z3.And(s_equals_x, e_equals_y),
            z3.And(
                ss == sx,
                es >= ex,  # cannot be strengthened
                es <= ex + one,  # cannot be strengthened
                se != sy,
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey,  # cannot be strengthened
            ),
        ),
    )

    case_3ys: z3.BoolRef = z3.And(ex + p == ey, sx == sy)
    result["TwoSum-3YS"] = z3.Implies(
        case_3ys,
        z3.Or(
            z3.And(s_equals_y, e_equals_x),
            z3.And(
                ss == sy,
                es >= ey,  # cannot be strengthened
                es <= ey + one,  # cannot be strengthened
                se != sx,
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex,  # cannot be strengthened
            ),
        ),
    )

    case_3xd: z3.BoolRef = z3.And(ex == ey + p, sx != sy)
    result["TwoSum-3XD"] = z3.Implies(
        case_3xd,
        z3.Or(
            z3.And(s_equals_x, e_equals_y),
            z3.And(
                ss == sx,
                es == ex - one,
                e_pos_zero,
            ),
            z3.And(
                ss == sx,
                es == ex - one,
                se == sy,
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey - two,  # cannot be strengthened
            ),
            z3.And(
                ss == sx,
                es == ex - one,
                se != sy,
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey - one,  # cannot be strengthened
            ),
            z3.And(
                ss == sx,
                es == ex,
                se != sy,
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey,  # cannot be strengthened
            ),
        ),
    )

    case_3yd: z3.BoolRef = z3.And(ex + p == ey, sx != sy)
    result["TwoSum-3YD"] = z3.Implies(
        case_3yd,
        z3.Or(
            z3.And(s_equals_y, e_equals_x),
            z3.And(
                ss == sy,
                es == ey - one,
                e_pos_zero,
            ),
            z3.And(
                ss == sy,
                es == ey - one,
                se == sx,
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex - two,  # cannot be strengthened
            ),
            z3.And(
                ss == sy,
                es == ey - one,
                se != sx,
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex - one,  # cannot be strengthened
            ),
            z3.And(
                ss == sy,
                es == ey,
                se != sx,
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex,  # cannot be strengthened
            ),
        ),
    )

    ############################################################################

    case_4xs: z3.BoolRef = z3.And(ex == ey + (p - one), sx == sy)
    result["TwoSum-4XS"] = z3.Implies(
        case_4xs,
        z3.Or(
            z3.And(
                ss == sx,
                es >= ex,  # cannot be strengthened
                es <= ex + one,  # cannot be strengthened
                e_pos_zero,
            ),
            z3.And(
                ss == sx,
                es >= ex,  # cannot be strengthened
                es <= ex + one,  # cannot be strengthened
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey - one,  # cannot be strengthened
            ),
        ),
    )

    case_4ys: z3.BoolRef = z3.And(ex + (p - one) == ey, sx == sy)
    result["TwoSum-4YS"] = z3.Implies(
        case_4ys,
        z3.Or(
            z3.And(
                ss == sy,
                es >= ey,  # cannot be strengthened
                es <= ey + one,  # cannot be strengthened
                e_pos_zero,
            ),
            z3.And(
                ss == sy,
                es >= ey,  # cannot be strengthened
                es <= ey + one,  # cannot be strengthened
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex - one,  # cannot be strengthened
            ),
        ),
    )

    case_4xd: z3.BoolRef = z3.And(ex == ey + (p - one), sx != sy)
    result["TwoSum-4XD"] = z3.Implies(
        case_4xd,
        z3.Or(
            z3.And(
                ss == sx,
                es >= ex - one,  # cannot be strengthened
                es <= ex,  # cannot be strengthened
                e_pos_zero,
            ),
            z3.And(
                ss == sx,
                es == ex - one,
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey - two,  # cannot be strengthened
            ),
            z3.And(
                ss == sx,
                es == ex,
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey - one,  # cannot be strengthened
            ),
        ),
    )

    case_4yd: z3.BoolRef = z3.And(ex + (p - one) == ey, sx != sy)
    result["TwoSum-4YD"] = z3.Implies(
        case_4yd,
        z3.Or(
            z3.And(
                ss == sy,
                es >= ey - one,  # cannot be strengthened
                es <= ey,  # cannot be strengthened
                e_pos_zero,
            ),
            z3.And(
                ss == sy,
                es == ey - one,
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex - two,  # cannot be strengthened
            ),
            z3.And(
                ss == sy,
                es == ey,
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex - one,  # cannot be strengthened
            ),
        ),
    )

    ############################################################################

    case_5xs: z3.BoolRef = z3.And(ex == ey + (p - two), sx == sy)
    result["TwoSum-5XS"] = z3.Implies(
        case_5xs,
        z3.Or(
            z3.And(
                ss == sx,
                es >= ex,  # cannot be strengthened
                es <= ex + one,  # cannot be strengthened
                e_pos_zero,
            ),
            z3.And(
                ss == sx,
                es == ex,
                se == sy,
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey - two,  # cannot be strengthened
            ),
            z3.And(
                ss == sx,
                es == ex + one,
                se == sy,
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey - one,  # cannot be strengthened
            ),
            z3.And(
                ss == sx,
                es >= ex,  # cannot be strengthened
                es <= ex + one,  # cannot be strengthened
                se != sy,
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey - two,  # cannot be strengthened
            ),
        ),
    )

    case_5ys: z3.BoolRef = z3.And(ex + (p - two) == ey, sx == sy)
    result["TwoSum-5YS"] = z3.Implies(
        case_5ys,
        z3.Or(
            z3.And(
                ss == sy,
                es >= ey,  # cannot be strengthened
                es <= ey + one,  # cannot be strengthened
                e_pos_zero,
            ),
            z3.And(
                ss == sy,
                es == ey,
                se == sx,
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex - two,  # cannot be strengthened
            ),
            z3.And(
                ss == sy,
                es == ey + one,
                se == sx,
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex - one,  # cannot be strengthened
            ),
            z3.And(
                ss == sy,
                es >= ey,  # cannot be strengthened
                es <= ey + one,  # cannot be strengthened
                se != sx,
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex - two,  # cannot be strengthened
            ),
        ),
    )

    case_5xd: z3.BoolRef = z3.And(ex == ey + (p - two), sx != sy)
    result["TwoSum-5XD"] = z3.Implies(
        case_5xd,
        z3.Or(
            z3.And(
                ss == sx,
                es >= ex - one,  # cannot be strengthened
                es <= ex,  # cannot be strengthened
                e_pos_zero,
            ),
            z3.And(
                ss == sx,
                es == ex - one,
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey - three,  # cannot be strengthened
            ),
            z3.And(
                ss == sx,
                es == ex,
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey - two,  # cannot be strengthened
            ),
        ),
    )

    case_5yd: z3.BoolRef = z3.And(ex + (p - two) == ey, sx != sy)
    result["TwoSum-5YD"] = z3.Implies(
        case_5yd,
        z3.Or(
            z3.And(
                ss == sy,
                es >= ey - one,  # cannot be strengthened
                es <= ey,  # cannot be strengthened
                e_pos_zero,
            ),
            z3.And(
                ss == sy,
                es == ey - one,
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex - three,  # cannot be strengthened
            ),
            z3.And(
                ss == sy,
                es == ey,
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex - two,  # cannot be strengthened
            ),
        ),
    )

    ############################################################################

    case_6xs: z3.BoolRef = z3.And(two <= ex - ey, ex - ey <= p - three, sx == sy)
    result["TwoSum-6XS"] = z3.Implies(
        case_6xs,
        z3.Or(
            z3.And(
                ss == sx,
                es >= ex,  # cannot be strengthened
                es <= ex + one,  # cannot be strengthened
                e_pos_zero,
            ),
            z3.And(
                ss == sx,
                es == ex,
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey - (p - (ex - ey)),  # cannot be strengthened
            ),
            z3.And(
                ss == sx,
                es == ex + one,
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey - (p - ((ex - ey) + one)),  # cannot be strengthened
            ),
        ),
    )

    case_6ys: z3.BoolRef = z3.And(two <= ey - ex, ey - ex <= p - three, sx == sy)
    result["TwoSum-6YS"] = z3.Implies(
        case_6ys,
        z3.Or(
            z3.And(
                ss == sy,
                es >= ey,  # cannot be strengthened
                es <= ey + one,  # cannot be strengthened
                e_pos_zero,
            ),
            z3.And(
                ss == sy,
                es == ey,
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex - (p - (ey - ex)),  # cannot be strengthened
            ),
            z3.And(
                ss == sy,
                es == ey + one,
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex - (p - ((ey - ex) + one)),  # cannot be strengthened
            ),
        ),
    )

    case_6xd: z3.BoolRef = z3.And(two <= ex - ey, ex - ey <= p - three, sx != sy)
    result["TwoSum-6XD"] = z3.Implies(
        case_6xd,
        z3.Or(
            z3.And(
                ss == sx,
                es >= ex - one,  # cannot be strengthened
                es <= ex,  # cannot be strengthened
                e_pos_zero,
            ),
            z3.And(
                ss == sx,
                es == ex - one,
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey - (p - ((ex - ey) - one)),  # cannot be strengthened
            ),
            z3.And(
                ss == sx,
                es == ex,
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey - (p - (ex - ey)),  # cannot be strengthened
            ),
        ),
    )

    case_6yd: z3.BoolRef = z3.And(two <= ey - ex, ey - ex <= p - three, sx != sy)
    result["TwoSum-6YD"] = z3.Implies(
        case_6yd,
        z3.Or(
            z3.And(
                ss == sy,
                es >= ey - one,  # cannot be strengthened
                es <= ey,  # cannot be strengthened
                e_pos_zero,
            ),
            z3.And(
                ss == sy,
                es == ey - one,
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex - (p - ((ey - ex) - one)),  # cannot be strengthened
            ),
            z3.And(
                ss == sy,
                es == ey,
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex - (p - (ey - ex)),  # cannot be strengthened
            ),
        ),
    )

    ############################################################################

    case_7xs: z3.BoolRef = z3.And(ex == ey + one, sx == sy)
    result["TwoSum-7XS"] = z3.Implies(
        case_7xs,
        z3.Or(
            z3.And(
                ss == sx,
                es >= ex,  # cannot be strengthened
                es <= ex + one,  # cannot be strengthened
                e_pos_zero,
            ),
            z3.And(
                ss == sx,
                es == ex,
                ee == ey - (p - one),
            ),
            z3.And(
                ss == sx,
                es == ex + one,
                ee >= ey - (p - one),  # cannot be strengthened
                ee <= ey - (p - two),  # cannot be strengthened
            ),
        ),
    )

    case_7ys: z3.BoolRef = z3.And(ex + one == ey, sx == sy)
    result["TwoSum-7YS"] = z3.Implies(
        case_7ys,
        z3.Or(
            z3.And(
                ss == sy,
                es >= ey,  # cannot be strengthened
                es <= ey + one,  # cannot be strengthened
                e_pos_zero,
            ),
            z3.And(
                ss == sy,
                es == ey,
                ee == ex - (p - one),
            ),
            z3.And(
                ss == sy,
                es == ey + one,
                ee >= ex - (p - one),  # cannot be strengthened
                ee <= ex - (p - two),  # cannot be strengthened
            ),
        ),
    )

    case_7xd: z3.BoolRef = z3.And(ex == ey + one, sx != sy)
    result["TwoSum-7XD"] = z3.Implies(
        case_7xd,
        z3.Or(
            z3.And(
                ss == sx,
                es >= ex - p,  # cannot be strengthened
                es <= ex,  # cannot be strengthened
                e_pos_zero,
            ),
            z3.And(
                ss == sx,
                es == ex,
                ee == ey - (p - one),
            ),
        ),
    )

    case_7yd: z3.BoolRef = z3.And(ex + one == ey, sx != sy)
    result["TwoSum-7YD"] = z3.Implies(
        case_7yd,
        z3.Or(
            z3.And(
                ss == sy,
                es >= ey - p,  # cannot be strengthened
                es <= ey,  # cannot be strengthened
                e_pos_zero,
            ),
            z3.And(
                ss == sy,
                es == ey,
                ee == ex - (p - one),
            ),
        ),
    )

    ############################################################################

    case_8s: z3.BoolRef = z3.And(
        ex == ey,
        sx == sy,
        z3.Not(x_zero),  # cannot be omitted
        z3.Not(y_zero),  # cannot be omitted
    )
    result["TwoSum-8S"] = z3.Implies(
        case_8s,
        z3.Or(
            z3.And(ss == sx, es == ex + one, e_pos_zero),
            z3.And(ss == sx, es == ex + one, ee == ex - (p - one)),
        ),
    )

    case_8d: z3.BoolRef = z3.And(ex == ey, sx != sy)
    result["TwoSum-8D"] = z3.Implies(
        case_8d,
        z3.Or(
            z3.And(s_pos_zero, e_pos_zero),
            z3.And(
                es >= ex - (p - one),  # cannot be strengthened
                es <= ex - one,  # cannot be strengthened
                e_pos_zero,
            ),
        ),
    )

    ############################################################################

    return result
