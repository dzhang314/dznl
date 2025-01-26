import z3
from smt_utils import BoolVar, IntVar, FloatVar, z3_If
from typing import Callable


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
    is_zero: Callable[[FloatVar], z3.BoolRef],
    is_positive: Callable[[FloatVar], z3.BoolRef],
    is_negative: Callable[[FloatVar], z3.BoolRef],
    is_equal: Callable[[FloatVar, FloatVar], z3.BoolRef],
    p: IntVar,
    one: IntVar,
    two: IntVar,
    three: IntVar,
) -> dict[str, z3.BoolRef]:

    result: dict[str, z3.BoolRef] = {}

    x_zero: z3.BoolRef = is_zero(x)
    # x_pos_zero: z3.BoolRef = z3.And(is_positive(x), x_zero)
    # x_neg_zero: z3.BoolRef = z3.And(is_negative(x), x_zero)

    y_zero: z3.BoolRef = is_zero(y)
    # y_pos_zero: z3.BoolRef = z3.And(is_positive(y), y_zero)
    # y_neg_zero: z3.BoolRef = z3.And(is_negative(y), y_zero)
    xy_nonzero: z3.BoolRef = z3.And(z3.Not(x_zero), z3.Not(y_zero))

    # s_zero: z3.BoolRef = is_zero(s)
    # s_pos_zero: z3.BoolRef = z3.And(is_positive(s), s_zero)
    # s_neg_zero: z3.BoolRef = z3.And(is_negative(s), s_zero)
    e_pos_zero: z3.BoolRef = z3.And(is_positive(e), is_zero(e))

    # s_equals_x: z3.BoolRef = is_equal(s, x)
    # s_equals_y: z3.BoolRef = is_equal(s, y)
    # e_equals_x: z3.BoolRef = is_equal(e, x)
    # e_equals_y: z3.BoolRef = is_equal(e, y)

    fx: IntVar = z3_If(tbx, ex - (p - one), ex - (p - (ntbx + one)))
    fy: IntVar = z3_If(tby, ey - (p - one), ey - (p - (ntby + one)))
    fs: IntVar = z3_If(tbs, es - (p - one), es - (p - (ntbs + one)))
    # fe: IntVar = z3_If(tbe, ee - (p - one), ee - (p - (ntbe + one)))

    gx: IntVar = z3_If(lbx, ex - nlbx, ex)
    gy: IntVar = z3_If(lby, ey - nlby, ey)
    gs: IntVar = z3_If(lbs, es - nlbs, es)
    # ge: IntVar = z3_If(lbe, ee - nlbe, ee)

    hx: IntVar = z3_If(lbx, ex, ex - nlbx)
    hy: IntVar = z3_If(lby, ey, ey - nlby)
    hs: IntVar = z3_If(lbs, es, es - nlbs)
    # he: IntVar = z3_If(lbe, ee, ee - nlbe)

    same_sign: z3.BoolRef = sx == sy
    diff_sign: z3.BoolRef = sx != sy

    ############################################################# LEMMA FAMILY D

    # All hypotheses are strictly necessary.
    result["TwoSum-D1-X"] = z3.Implies(
        z3.And(diff_sign, ex > gx, ex > ey + one), z3.And(ss == sx, es == ex)
    )
    result["TwoSum-D1-Y"] = z3.Implies(
        z3.And(diff_sign, ey > gy, ey > ex + one), z3.And(ss == sy, es == ey)
    )

    # All hypotheses are strictly necessary.
    result["TwoSum-D2-X"] = z3.Implies(
        z3.And(ex > ey + two, es < ex),
        z3.And(lbs, nlbs >= ex - ey - two),
    )
    result["TwoSum-D2-Y"] = z3.Implies(
        z3.And(ex + two < ey, es < ey),
        z3.And(lbs, nlbs >= ey - ex - two),
    )

    # All hypotheses are strictly necessary.
    result["TwoSum-D3-X"] = z3.Implies(
        z3.And(same_sign, ex > hx, hx > ey),
        z3.And(ss == sx, es == ex, hs <= hx + one),
    )
    result["TwoSum-D3-Y"] = z3.Implies(
        z3.And(same_sign, ey > hy, hy > ex),
        z3.And(ss == sy, es == ey, hs <= hy + one),
    )

    # All hypotheses are strictly necessary.
    result["TwoSum-D4-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex > ey, fy + one > hx),
        z3.And(ss == sx, es == ex, hs == ey + one),
    )
    result["TwoSum-D4-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey > ex, fx + one > hy),
        z3.And(ss == sy, es == ey, hs == ex + one),
    )

    # All hypotheses are strictly necessary.
    result["TwoSum-D5-X"] = z3.Implies(
        z3.And(ex > gx, gx > ey + one),
        z3.And(ss == sx, es == ex, gs <= gx + one),
    )
    result["TwoSum-D5-Y"] = z3.Implies(
        z3.And(ey > gy, gy > ex + one),
        z3.And(ss == sy, es == ey, gs <= gy + one),
    )

    # All hypotheses are strictly necessary.
    result["TwoSum-D6-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, gx == ey + one, ey == fy, fy + p > ex),
        z3.And(ss == sx, es == ex, gs <= ey),
    )
    result["TwoSum-D6-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, gy == ex + one, ex == fx, fx + p > ey),
        z3.And(ss == sy, es == ey, gs <= ex),
    )

    # All hypotheses are strictly necessary.
    result["TwoSum-D7-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex > ey + one, hx < ey + one),
        z3.And(ss == sx, es + one == ex, gs <= ey + one),
    )
    result["TwoSum-D7-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey > ex + one, hy <= ex),
        z3.And(ss == sy, es + one == ey, gs <= ex + one),
    )

    # All hypotheses are strictly necessary.
    result["TwoSum-D8-X"] = z3.Implies(
        z3.And(diff_sign, ex > fx, hx > ey + one),
        z3.And(ss == sx, es == ex, hs <= hx),
    )
    result["TwoSum-D8-Y"] = z3.Implies(
        z3.And(diff_sign, ey > fy, hy > ex + one),
        z3.And(ss == sy, es == ey, hs <= hy),
    )

    ############################################################# LEMMA FAMILY C

    # All hypotheses are strictly necessary.
    # This lemma is complete.
    result["TwoSum-C1-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, fx == gx, fx == ey, ey == fy),
        z3.And(ss == sx, es == ex + one, fs == es, e_pos_zero),
    )
    result["TwoSum-C1-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, fy == gy, fy == ex, ex == fx),
        z3.And(ss == sy, es == ey + one, fs == es, e_pos_zero),
    )

    # All hypotheses are strictly necessary.
    # This lemma is complete.
    result["TwoSum-C2-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex > fx, fx == gx, fx == ey, ey == fy),
        z3.And(ss == sx, es == ex, fs == gs, fs == ey + one, e_pos_zero),
    )
    result["TwoSum-C2-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey > fy, fy == gy, fy == ex, ex == fx),
        z3.And(ss == sy, es == ey, fs == gs, fs == ex + one, e_pos_zero),
    )

    return result
