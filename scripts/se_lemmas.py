import z3
from smt_utils import BoolVar, IntVar, FloatVar
from typing import Callable


def two_sum_se_lemmas(
    x: FloatVar,
    y: FloatVar,
    s: FloatVar,
    e: FloatVar,
    sx: BoolVar,
    sy: BoolVar,
    ss: BoolVar,
    se: BoolVar,
    ex: IntVar,
    ey: IntVar,
    es: IntVar,
    ee: IntVar,
    is_zero: Callable[[FloatVar], z3.BoolRef],
    is_positive: Callable[[FloatVar], z3.BoolRef],
    is_negative: Callable[[FloatVar], z3.BoolRef],
    is_equal: Callable[[FloatVar, FloatVar], z3.BoolRef],
    p: IntVar,
    one: IntVar,
    two: IntVar,
) -> dict[str, z3.BoolRef]:

    result: dict[str, z3.BoolRef] = {}

    x_zero: z3.BoolRef = is_zero(x)
    x_pos_zero: z3.BoolRef = z3.And(is_positive(x), x_zero)
    x_neg_zero: z3.BoolRef = z3.And(is_negative(x), x_zero)

    y_zero: z3.BoolRef = is_zero(y)
    y_pos_zero: z3.BoolRef = z3.And(is_positive(y), y_zero)
    y_neg_zero: z3.BoolRef = z3.And(is_negative(y), y_zero)
    xy_nonzero: z3.BoolRef = z3.And(z3.Not(x_zero), z3.Not(y_zero))

    s_zero: z3.BoolRef = is_zero(s)
    s_pos_zero: z3.BoolRef = z3.And(is_positive(s), s_zero)
    s_neg_zero: z3.BoolRef = z3.And(is_negative(s), s_zero)
    e_pos_zero: z3.BoolRef = z3.And(is_positive(e), is_zero(e))

    s_equals_x: z3.BoolRef = is_equal(s, x)
    s_equals_y: z3.BoolRef = is_equal(s, y)
    e_equals_x: z3.BoolRef = is_equal(e, x)
    e_equals_y: z3.BoolRef = is_equal(e, y)

    same_sign: z3.BoolRef = sx == sy
    diff_sign: z3.BoolRef = sx != sy

    ###################################################### LEMMA FAMILY SE-Z (2)

    # Lemmas in Family SE-Z (for "zero") apply
    # when one or both addends are zero.

    # Lemma SE-Z1: Both addends are zero.
    result["TwoSum-SE-Z1-PP"] = z3.Implies(
        z3.And(x_pos_zero, y_pos_zero),
        z3.And(s_pos_zero, e_pos_zero),
    )
    result["TwoSum-SE-Z1-PN"] = z3.Implies(
        z3.And(x_pos_zero, y_neg_zero),
        z3.And(s_pos_zero, e_pos_zero),
    )
    result["TwoSum-SE-Z1-NP"] = z3.Implies(
        z3.And(x_neg_zero, y_pos_zero),
        z3.And(s_pos_zero, e_pos_zero),
    )
    result["TwoSum-SE-Z1-NN"] = z3.Implies(
        z3.And(x_neg_zero, y_neg_zero),
        z3.And(s_neg_zero, e_pos_zero),
    )

    # Lemma SE-Z2: One addend is zero.
    result["TwoSum-SE-Z2-X"] = z3.Implies(
        z3.And(y_zero, z3.Not(x_zero)),
        z3.And(s_equals_x, e_pos_zero),
    )
    result["TwoSum-SE-Z2-Y"] = z3.Implies(
        z3.And(x_zero, z3.Not(y_zero)),
        z3.And(s_equals_y, e_pos_zero),
    )

    ############################################################# LEMMA SE-I (1)

    # Lemma SE-I (for "identical") applies to addends
    # returned unchanged by the TwoSum algorithm.

    result["TwoSum-SE-I-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            z3.Or(ex > ey + (p + one), z3.And(ex == ey + (p + one), same_sign)),
        ),
        z3.And(s_equals_x, e_equals_y),
    )
    result["TwoSum-SE-I-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            z3.Or(ey > ex + (p + one), z3.And(ey == ex + (p + one), same_sign)),
        ),
        z3.And(s_equals_y, e_equals_x),
    )

    ########################################################### HELPER FUNCTIONS

    def se_case(
        ss_value: BoolVar | tuple[BoolVar] | None,
        es_range: IntVar | tuple[IntVar, IntVar],
        se_value: BoolVar | tuple[BoolVar] | None,
        ee_range: IntVar | tuple[IntVar, IntVar],
    ) -> z3.BoolRef:
        result: list[z3.BoolRef] = []
        if isinstance(ss_value, tuple):
            result.append(ss != ss_value[0])
        elif ss_value is not None:
            result.append(ss == ss_value)
        if isinstance(es_range, tuple):
            result.append(es >= es_range[0])
            result.append(es <= es_range[1])
        else:
            result.append(es == es_range)
        if isinstance(se_value, tuple):
            result.append(se != se_value[0])
        elif se_value is not None:
            result.append(se == se_value)
        if isinstance(ee_range, tuple):
            result.append(ee >= ee_range[0])
            result.append(ee <= ee_range[1])
        else:
            result.append(ee == ee_range)
        return z3.And(*result)

    def se_case_zero(
        ss_value: BoolVar | tuple[BoolVar] | None,
        es_range: IntVar | tuple[IntVar, IntVar],
    ) -> z3.BoolRef:
        result: list[z3.BoolRef] = []
        if isinstance(ss_value, tuple):
            result.append(ss != ss_value[0])
        elif ss_value is not None:
            result.append(ss == ss_value)
        if isinstance(es_range, tuple):
            result.append(es >= es_range[0])
            result.append(es <= es_range[1])
        else:
            result.append(es == es_range)
        result.append(e_pos_zero)
        return z3.And(*result)

    ###################################################### LEMMA FAMILY SE-S (5)

    # Lemmas in Family SE-S apply to addends with the same sign.

    result["TwoSum-SE-S1-X"] = z3.Implies(
        z3.And(same_sign, ex == ey + p),
        z3.Or(
            se_case(sx, (ex, ex + one), (sy,), (ey - (p - one), ex - p)),
            z3.And(s_equals_x, e_equals_y),
        ),
    )
    result["TwoSum-SE-S1-Y"] = z3.Implies(
        z3.And(same_sign, ey == ex + p),
        z3.Or(
            se_case(sy, (ey, ey + one), (sx,), (ex - (p - one), ey - p)),
            z3.And(s_equals_y, e_equals_x),
        ),
    )

    result["TwoSum-SE-S2-X"] = z3.Implies(
        z3.And(same_sign, ex == ey + (p - one)),
        z3.Or(
            se_case_zero(sx, (ex, ex + one)),
            se_case(sx, (ex, ex + one), None, (ey - (p - one), ex - p)),
        ),
    )
    result["TwoSum-SE-S2-Y"] = z3.Implies(
        z3.And(same_sign, ey == ex + (p - one)),
        z3.Or(
            se_case_zero(sy, (ey, ey + one)),
            se_case(sy, (ey, ey + one), None, (ex - (p - one), ey - p)),
        ),
    )

    result["TwoSum-SE-S3-X"] = z3.Implies(
        z3.And(same_sign, ex == ey + (p - two)),
        z3.Or(
            se_case_zero(sx, (ex, ex + one)),
            se_case(sx, (ex, ex + one), (sy,), (ey - (p - one), ex - p)),
            se_case(sx, ex, sy, (ey - (p - one), ex - p)),
            se_case(sx, ex + one, sy, (ey - (p - one), ex - (p - one))),
        ),
    )
    result["TwoSum-SE-S3-Y"] = z3.Implies(
        z3.And(same_sign, ey == ex + (p - two)),
        z3.Or(
            se_case_zero(sy, (ey, ey + one)),
            se_case(sy, (ey, ey + one), (sx,), (ex - (p - one), ey - p)),
            se_case(sy, ey, sx, (ex - (p - one), ey - p)),
            se_case(sy, ey + one, sx, (ex - (p - one), ey - (p - one))),
        ),
    )

    result["TwoSum-SE-S4-X"] = z3.Implies(
        z3.And(same_sign, ex > ey, ex < ey + (p - two)),
        z3.Or(
            se_case_zero(sx, (ex, ex + one)),
            se_case(sx, ex, None, (ey - (p - one), ex - p)),
            se_case(sx, ex + one, None, (ey - (p - one), ex - (p - one))),
        ),
    )
    result["TwoSum-SE-S4-Y"] = z3.Implies(
        z3.And(same_sign, ey > ex, ey < ex + (p - two)),
        z3.Or(
            se_case_zero(sy, (ey, ey + one)),
            se_case(sy, ey, None, (ex - (p - one), ey - p)),
            se_case(sy, ey + one, None, (ex - (p - one), ey - (p - one))),
        ),
    )

    result["TwoSum-SE-S5"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex == ey),
        z3.Or(
            se_case_zero(sx, ex + one),
            se_case(sx, ex + one, None, ex - (p - one)),
        ),
    )

    ###################################################### LEMMA FAMILY SE-D (5)

    # Lemmas in Family SE-D apply to addends with different signs.

    result["TwoSum-SE-D1-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey + (p + one)),
        z3.Or(
            se_case(sx, ex - one, (sy,), (ey - (p - one), ex - (p + two))),
            z3.And(s_equals_x, e_equals_y),
        ),
    )
    result["TwoSum-SE-D1-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == ex + (p + one)),
        z3.Or(
            se_case(sy, ey - one, (sx,), (ex - (p - one), ey - (p + two))),
            z3.And(s_equals_y, e_equals_x),
        ),
    )

    result["TwoSum-SE-D2-X"] = z3.Implies(
        z3.And(diff_sign, ex == ey + p),
        z3.Or(
            se_case_zero(sx, ex - one),
            se_case(sx, ex - one, sy, (ey - (p - one), ex - (p + two))),
            se_case(sx, ex - one, (sy,), (ey - (p - one), ex - (p + one))),
            se_case(sx, ex, (sy,), (ey - (p - one), ex - p)),
            z3.And(s_equals_x, e_equals_y),
        ),
    )
    result["TwoSum-SE-D2-Y"] = z3.Implies(
        z3.And(diff_sign, ey == ex + p),
        z3.Or(
            se_case_zero(sy, ey - one),
            se_case(sy, ey - one, sx, (ex - (p - one), ey - (p + two))),
            se_case(sy, ey - one, (sx,), (ex - (p - one), ey - (p + one))),
            se_case(sy, ey, (sx,), (ex - (p - one), ey - p)),
            z3.And(s_equals_y, e_equals_x),
        ),
    )

    result["TwoSum-SE-D3-X"] = z3.Implies(
        z3.And(diff_sign, ex > ey + one, ex < ey + p),
        z3.Or(
            se_case_zero(sx, (ex - one, ex)),
            se_case(sx, ex - one, None, (ey - (p - one), ex - (p + one))),
            se_case(sx, ex, None, (ey - (p - one), ex - p)),
        ),
    )
    result["TwoSum-SE-D3-Y"] = z3.Implies(
        z3.And(diff_sign, ey > ex + one, ey < ex + p),
        z3.Or(
            se_case_zero(sy, (ey - one, ey)),
            se_case(sy, ey - one, None, (ex - (p - one), ey - (p + one))),
            se_case(sy, ey, None, (ex - (p - one), ey - p)),
        ),
    )

    result["TwoSum-SE-D4-X"] = z3.Implies(
        z3.And(diff_sign, ex == ey + one),
        z3.Or(
            se_case_zero(sx, (ex - p, ex)),
            se_case(sx, ex, None, ex - p),
        ),
    )
    result["TwoSum-SE-D4-Y"] = z3.Implies(
        z3.And(diff_sign, ey == ex + one),
        z3.Or(
            se_case_zero(sy, (ey - p, ey)),
            se_case(sy, ey, None, ey - p),
        ),
    )

    result["TwoSum-SE-D5"] = z3.Implies(
        z3.And(diff_sign, ex == ey),
        z3.Or(
            z3.And(s_pos_zero, e_pos_zero),
            se_case_zero(None, (ex - (p - one), ex - one)),
        ),
    )

    return result
