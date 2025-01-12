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


# This wrapper function works around Python type checkers
# being unable to resolve overloads through type variables.
def z3_If(c: z3.BoolRef, a: IntVar, b: IntVar) -> IntVar:
    return z3.If(c, a, b)  # type: ignore


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

    lzx: z3.BoolRef = z3.Not(lbx)
    lzy: z3.BoolRef = z3.Not(lby)
    lzs: z3.BoolRef = z3.Not(lbs)
    lze: z3.BoolRef = z3.Not(lbe)
    tzx: z3.BoolRef = z3.Not(tbx)
    tzy: z3.BoolRef = z3.Not(tby)
    tzs: z3.BoolRef = z3.Not(tbs)
    tze: z3.BoolRef = z3.Not(tbe)

    same_sign = sx == sy
    diff_sign = sx != sy

    fx: IntVar = z3_If(tbx, ex - (p - one), ex - (p - one) + ntbx)
    fy: IntVar = z3_If(tby, ey - (p - one), ey - (p - one) + ntby)
    fs: IntVar = z3_If(tbs, es - (p - one), es - (p - one) + ntbs)
    fe: IntVar = z3_If(tbe, ee - (p - one), ee - (p - one) + ntbe)

    ############################################################################

    result["TwoSum-4-X"] = z3.Implies(
        z3.And(diff_sign, ex > fy + (p + one), fx < ey + (p + one), ex == fx),
        z3.Or(
            z3.And(
                ss == sx,
                es == ex - one,
                fs >= ex - p,
                fs <= ey - one,
                ee >= fy,
                ee <= ex - (p + two),
                fe == fy,
            ),
            z3.And(
                ss == sx,
                es == ex - one,
                fs == ey,
                se == sy,
                ee >= fy,
                ee <= ex - (p + two),
                fe == fy,
            ),
            z3.And(
                ss == sx,
                es == ex - one,
                fs == ey + one,
                se != sy,
                ee >= fy,
                ee <= ex - (p + two),
                fe == fy,
            ),
        ),
    )
    result["TwoSum-4-Y"] = z3.Implies(
        z3.And(diff_sign, ey > fx + (p + one), fy < ex + (p + one), ey == fy),
        z3.Or(
            z3.And(
                ss == sy,
                es == ey - one,
                fs >= ey - p,
                fs <= ex - one,
                ee >= fx,
                ee <= ey - (p + two),
                fe == fx,
            ),
            z3.And(
                ss == sy,
                es == ey - one,
                fs == ex,
                se == sx,
                ee >= fx,
                ee <= ey - (p + two),
                fe == fx,
            ),
            z3.And(
                ss == sy,
                es == ey - one,
                fs == ex + one,
                se != sx,
                ee >= fx,
                ee <= ey - (p + two),
                fe == fx,
            ),
        ),
    )

    ############################################################################

    """
    result["TwoSum-AXS"] = z3.Implies(z3.And(sx == sy, lzx, ex > ey + one), es == ex)
    result["TwoSum-AYS"] = z3.Implies(z3.And(sx == sy, lzy, ex + one < ey), es == ey)
    result["TwoSum-AXD"] = z3.Implies(z3.And(sx != sy, lbx, ex > ey + one), es == ex)
    result["TwoSum-AYD"] = z3.Implies(z3.And(sx != sy, lby, ex + one < ey), es == ey)

    result["TwoSum-BXS"] = z3.Implies(
        z3.And(sx == sy, lbx, ex > ey + nlbx + one),  # cannot be weakened
        z3.And(es == ex, lbs, nlbs >= nlbx),  # cannot be strengthened
    )
    result["TwoSum-BYS"] = z3.Implies(
        z3.And(sx == sy, lby, ex + nlby + one < ey),  # cannot be weakened
        z3.And(es == ey, lbs, nlbs >= nlby),  # cannot be strengthened
    )
    result["TwoSum-BXD"] = z3.Implies(
        z3.And(sx != sy, lzx, ex > ey + nlbx + one, nlbx != p - one),
        z3.And(es == ex, lzs, nlbs >= nlbx),  # cannot be strengthened
    )
    result["TwoSum-BYD"] = z3.Implies(
        z3.And(sx != sy, lzy, ex + nlby + one < ey, nlby != p - one),
        z3.And(es == ey, lzs, nlbs >= nlby),  # cannot be strengthened
    )

    result["TwoSum-CXD"] = z3.Implies(
        z3.And(sx != sy, ex > ey + two, es == ex - one),
        z3.And(lbs, nlbs >= ex - ey - two),
    )
    result["TwoSum-CYD"] = z3.Implies(
        z3.And(sx != sy, ex + two < ey, es == ey - one),
        z3.And(lbs, nlbs >= ey - ex - two),
    )

    result["TwoSum-U"] = z3.Or(e_pos_zero, es > ee + p, z3.And(es == ee + p, e_pow_two))

    result["TwoSum-E"] = z3.Implies(
        z3.And(
            z3.Or(ex >= es, z3.And(tzx, ex + ntbx >= es)),  # cannot be weakened
            z3.Or(ey >= es, z3.And(tzy, ey + ntby >= es)),  # cannot be weakened
        ),
        e_pos_zero,
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
    """

    ############################################################################

    return result
