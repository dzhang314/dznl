import z3
from smt_utils import BoolVar, IntVar, FloatVar
from typing import Callable


def two_sum_setz_lemmas(
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
    ntzx: IntVar,
    ntzy: IntVar,
    ntzs: IntVar,
    ntze: IntVar,
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

    fx: IntVar = ex - (p - (ntzx + one))
    fy: IntVar = ey - (p - (ntzy + one))
    fs: IntVar = es - (p - (ntzs + one))
    fe: IntVar = ee - (p - (ntze + one))

    same_sign: z3.BoolRef = sx == sy
    diff_sign: z3.BoolRef = sx != sy

    #################################################### LEMMA FAMILY SETZ-Z (2)

    # Lemmas in Family SETZ-Z (for "zero") apply
    # when one or both addends are zero.

    result["TwoSum-SETZ-Z1-PP"] = z3.Implies(
        z3.And(x_pos_zero, y_pos_zero),
        z3.And(s_pos_zero, e_pos_zero),
    )
    result["TwoSum-SETZ-Z1-PN"] = z3.Implies(
        z3.And(x_pos_zero, y_neg_zero),
        z3.And(s_pos_zero, e_pos_zero),
    )
    result["TwoSum-SETZ-Z1-NP"] = z3.Implies(
        z3.And(x_neg_zero, y_pos_zero),
        z3.And(s_pos_zero, e_pos_zero),
    )
    result["TwoSum-SETZ-Z1-NN"] = z3.Implies(
        z3.And(x_neg_zero, y_neg_zero),
        z3.And(s_neg_zero, e_pos_zero),
    )

    result["TwoSum-SETZ-Z2-X"] = z3.Implies(
        z3.And(y_zero, z3.Not(x_zero)),
        z3.And(s_equals_x, e_pos_zero),
    )
    result["TwoSum-SETZ-Z2-Y"] = z3.Implies(
        z3.And(x_zero, z3.Not(y_zero)),
        z3.And(s_equals_y, e_pos_zero),
    )

    ########################################################### LEMMA SETZ-I (1)

    # Lemma SETZ-I (for "identical") applies to addends
    # returned unchanged by the TwoSum algorithm.

    result["TwoSum-SETZ-I-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            z3.Or(
                ex > ey + (p + one),
                z3.And(ex == ey + (p + one), z3.Or(ey == fy, same_sign, ex > fx)),
                z3.And(
                    ex == ey + p,
                    ey == fy,
                    z3.Or(same_sign, ex > fx),
                    ex < fx + (p - one),
                ),
            ),
        ),
        z3.And(s_equals_x, e_equals_y),
    )
    result["TwoSum-SETZ-I-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            z3.Or(
                ey > ex + (p + one),
                z3.And(ey == ex + (p + one), z3.Or(ex == fx, same_sign, ey > fy)),
                z3.And(
                    ey == ex + p,
                    ex == fx,
                    z3.Or(same_sign, ey > fy),
                    ey < fy + (p - one),
                ),
            ),
        ),
        z3.And(s_equals_y, e_equals_x),
    )

    ########################################################### HELPER FUNCTIONS

    def setz_case(
        ss_value: BoolVar,
        es_range: IntVar | tuple[IntVar, IntVar],
        fs_range: IntVar | tuple[IntVar, IntVar],
        se_value: BoolVar | tuple[BoolVar] | None,
        ee_max: IntVar,
        fe_value: IntVar,
    ) -> z3.BoolRef:
        conditions: list[z3.BoolRef] = []
        conditions.append(ss == ss_value)
        if isinstance(es_range, tuple):
            conditions.append(es >= es_range[0])
            conditions.append(es <= es_range[1])
        else:
            conditions.append(es == es_range)
        if isinstance(fs_range, tuple):
            conditions.append(fs >= fs_range[0])
            conditions.append(fs <= fs_range[1])
        else:
            conditions.append(fs == fs_range)
        if isinstance(se_value, tuple):
            conditions.append(se != se_value[0])
        elif se_value is not None:
            conditions.append(se == se_value)
        conditions.append(ee <= ee_max)
        conditions.append(ee >= fe_value)
        conditions.append(fe == fe_value)
        return z3.And(*conditions)

    def setz_case_zero(
        ss_value: BoolVar | None,
        es_range: IntVar | tuple[IntVar, IntVar],
        fs_range: IntVar | tuple[IntVar, IntVar],
    ) -> z3.BoolRef:
        conditions: list[z3.BoolRef] = []
        if ss_value is not None:
            conditions.append(ss == ss_value)
        if isinstance(es_range, tuple):
            conditions.append(es >= es_range[0])
            conditions.append(es <= es_range[1])
        else:
            conditions.append(es == es_range)
        if isinstance(fs_range, tuple):
            conditions.append(fs >= fs_range[0])
            conditions.append(fs <= fs_range[1])
        else:
            conditions.append(fs == fs_range)
        conditions.append(e_pos_zero)
        return z3.And(*conditions)

    #################################################### LEMMA FAMILY SETZ-F (7)

    # Lemmas in Family SETZ-F apply to addends
    # with the same trailing exponent (fx == fy).

    # The trailing exponent of a floating-point number x, denoted by
    # fx, is the place value of the last nonzero bit in its mantissa.

    result["TwoSum-SETZ-FS0-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, fx == fy, ex > ey + one),
        z3.Or(
            setz_case_zero(sx, ex, (fx + one, ex - one)),
            setz_case_zero(sx, ex + one, (fx + one, ey)),
            setz_case_zero(sx, ex + one, ex + one),
        ),
    )
    result["TwoSum-SETZ-FS0-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, fx == fy, ey > ex + one),
        z3.Or(
            setz_case_zero(sy, ey, (fy + one, ey - one)),
            setz_case_zero(sy, ey + one, (fy + one, ex)),
            setz_case_zero(sy, ey + one, ey + one),
        ),
    )

    result["TwoSum-SETZ-FS1-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, fx == fy, ex == ey + one),
        z3.Or(
            setz_case_zero(sx, ex, (fx + one, ex - two)),
            setz_case_zero(sx, ex + one, (fx + one, ey)),
            setz_case_zero(sx, ex + one, ex + one),
        ),
    )
    result["TwoSum-SETZ-FS1-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, fx == fy, ey == ex + one),
        z3.Or(
            setz_case_zero(sy, ey, (fy + one, ey - two)),
            setz_case_zero(sy, ey + one, (fy + one, ex)),
            setz_case_zero(sy, ey + one, ey + one),
        ),
    )

    result["TwoSum-SETZ-FS2"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, fx == fy, ex == ey, ex > fx),
        setz_case_zero(sx, ex + one, (fx + one, ex)),
    )

    result["TwoSum-SETZ-FS3"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, fx == fy, ex == ey, ex == fx),
        setz_case_zero(sx, ex + one, ex + one),
    )

    result["TwoSum-SETZ-FD0-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, fx == fy, ex > ey + one),
        z3.Or(
            setz_case_zero(sx, ex - one, (fx + one, ey)),
            setz_case_zero(sx, ex, (fx + one, ex)),
        ),
    )
    result["TwoSum-SETZ-FD0-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, fx == fy, ey > ex + one),
        z3.Or(
            setz_case_zero(sy, ey - one, (fy + one, ex)),
            setz_case_zero(sy, ey, (fy + one, ey)),
        ),
    )

    result["TwoSum-SETZ-FD1-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, fx == fy, ex == ey + one),
        z3.Or(
            z3.And(
                ss == sx,
                es >= fx + one,
                es <= ex - one,
                fs >= fx + one,
                fs <= es,
                e_pos_zero,
            ),
            setz_case_zero(sx, ex, (fx + one, ex - two)),
            setz_case_zero(sx, ex, ex),
        ),
    )
    result["TwoSum-SETZ-FD1-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, fx == fy, ey == ex + one),
        z3.Or(
            z3.And(
                ss == sy,
                es >= fy + one,
                es <= ey - one,
                fs >= fy + one,
                fs <= es,
                e_pos_zero,
            ),
            setz_case_zero(sy, ey, (fy + one, ey - two)),
            setz_case_zero(sy, ey, ey),
        ),
    )

    result["TwoSum-SETZ-FD2"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, fx == fy, ex == ey),
        z3.Or(
            z3.And(s_pos_zero, e_pos_zero),
            z3.And(
                es >= fx + one, es <= ex - one, fs >= fx + one, fs <= es, e_pos_zero
            ),
        ),
    )

    ################################################### LEMMA FAMILY SETZ-E (15)

    # Lemmas in Family SETZ-E (for "exact") apply to addends with
    # different trailing exponents whose floating-point sum is exact.

    result["TwoSum-SETZ-EN0-X"] = z3.Implies(
        z3.And(xy_nonzero, z3.Or(same_sign, ex > fx), fx > ey, ex < fy + p),
        setz_case_zero(sx, ex, fy),
    )
    result["TwoSum-SETZ-EN0-Y"] = z3.Implies(
        z3.And(xy_nonzero, z3.Or(same_sign, ey > fy), fy > ex, ey < fx + p),
        setz_case_zero(sy, ey, fx),
    )

    result["TwoSum-SETZ-EN1-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            diff_sign,
            z3.Or(
                z3.And(ex == fx, fx > ey + one, ex < fy + (p + one)),
                z3.And(ex == fx + one, fx == ey, ey > fy),
            ),
        ),
        setz_case_zero(sx, ex - one, fy),
    )
    result["TwoSum-SETZ-EN1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            diff_sign,
            z3.Or(
                z3.And(ey == fy, fy > ex + one, ey < fx + (p + one)),
                z3.And(ey == fy + one, fy == ex, ex > fx),
            ),
        ),
        setz_case_zero(sy, ey - one, fx),
    )

    result["TwoSum-SETZ-ESP0-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            z3.Or(z3.And(ex > ey, ey > fx), z3.And(ex > ey + one, ey + one > fx)),
            fx > fy,
            ex < fy + (p - one),
        ),
        setz_case_zero(sx, (ex, ex + one), fy),
    )
    result["TwoSum-SETZ-ESP0-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            z3.Or(z3.And(ey > ex, ex > fy), z3.And(ey > ex + one, ex + one > fy)),
            fy > fx,
            ey < fx + (p - one),
        ),
        setz_case_zero(sy, (ey, ey + one), fx),
    )

    result["TwoSum-SETZ-ESP1-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ex == ey + one,
            ey == fx,
            fx > fy,
            ex < fy + (p - one),
        ),
        setz_case_zero(sx, ex + one, fy),
    )
    result["TwoSum-SETZ-ESP1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ey == ex + one,
            ex == fy,
            fy > fx,
            ey < fx + (p - one),
        ),
        setz_case_zero(sy, ey + one, fx),
    )

    result["TwoSum-SETZ-ESC-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex > ey, fx < fy, ex < fx + (p - one)),
        setz_case_zero(sx, (ex, ex + one), fx),
    )
    result["TwoSum-SETZ-ESC-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey > ex, fy < fx, ey < fy + (p - one)),
        setz_case_zero(sy, (ey, ey + one), fy),
    )

    result["TwoSum-SETZ-ESS-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ex == ey,
            fx < fy,
            ex < fx + (p - one),
            ey < fy + (p - one),
        ),
        setz_case_zero(sx, ex + one, fx),
    )
    result["TwoSum-SETZ-ESS-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ex == ey,
            fx > fy,
            ex < fx + (p - one),
            ey < fy + (p - one),
        ),
        setz_case_zero(sx, ex + one, fy),
    )

    result["TwoSum-SETZ-EDP0-X"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, ex > ey + one, ey + one > fx, fx > fy, ex < fy + p
        ),
        setz_case_zero(sx, (ex - one, ex), fy),
    )
    result["TwoSum-SETZ-EDP0-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, ey > ex + one, ex + one > fy, fy > fx, ey < fx + p
        ),
        setz_case_zero(sy, (ey - one, ey), fx),
    )

    result["TwoSum-SETZ-EDP1-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey + one, ey > fx, fx > fy, ex < fy + p),
        setz_case_zero(sx, (fx, ex), fy),
    )
    result["TwoSum-SETZ-EDP1-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == ex + one, ex > fy, fy > fx, ey < fx + p),
        setz_case_zero(sy, (fy, ey), fx),
    )

    result["TwoSum-SETZ-EDP2-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey + one, ex == fx, fx > fy + one),
        setz_case_zero(sx, (fy, ex - two), fy),
    )
    result["TwoSum-SETZ-EDP2-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == ex + one, ey == fy, fy > fx + one),
        setz_case_zero(sy, (fx, ey - two), fx),
    )

    result["TwoSum-SETZ-EDP3-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey + one, ex == fx, ey == fy),
        setz_case_zero(sx, (fy, ex - one), fy),
    )
    result["TwoSum-SETZ-EDP3-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == ex + one, ey == fy, ex == fx),
        setz_case_zero(sy, (fx, ey - one), fx),
    )

    result["TwoSum-SETZ-EDC0-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex > ey + one, fx < fy),
        setz_case_zero(sx, (ex - one, ex), fx),
    )
    result["TwoSum-SETZ-EDC0-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey > ex + one, fy < fx),
        setz_case_zero(sy, (ey - one, ey), fy),
    )

    result["TwoSum-SETZ-EDC1-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey + one, fx < fy),
        setz_case_zero(sx, (fy, ex), fx),
    )
    result["TwoSum-SETZ-EDC1-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == ex + one, fy < fx),
        setz_case_zero(sy, (fx, ey), fy),
    )

    result["TwoSum-SETZ-EDC2-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey, ey == fy, fx < fy),
        setz_case_zero(sx, (fx, ex - one), fx),
    )
    result["TwoSum-SETZ-EDC2-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == ex, ex == fx, fy < fx),
        setz_case_zero(sy, (fy, ey - one), fy),
    )

    result["TwoSum-SETZ-EDS0-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey, fx < fy, ex > fx + one, ey > fy + one),
        setz_case_zero(None, (fx, ex - one), fx),
    )
    result["TwoSum-SETZ-EDS0-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey, fx > fy, ex > fx + one, ey > fy + one),
        setz_case_zero(None, (fy, ey - one), fy),
    )

    result["TwoSum-SETZ-EDS1-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey, ex > fx + one, ey == fy + one),
        setz_case_zero(None, (fx, ex - two), fx),
    )
    result["TwoSum-SETZ-EDS1-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey, ex == fx + one, ey > fy + one),
        setz_case_zero(None, (fy, ey - two), fy),
    )

    #################################################### LEMMA FAMILY SETZ-O (3)

    # Lemmas in Family SETZ-O (for "overlap") apply to addends
    # that completely overlap but cannot be summed exactly.

    result["TwoSum-SETZ-O0-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex == fx + (p - one), ex > ey, ey > fy, fy > fx),
        z3.Or(
            setz_case_zero(sx, ex, fx),
            setz_case(sx, ex + one, (ex - (p - three), ey), None, ex - (p - one), fx),
            setz_case(sx, ex + one, ex + one, sy, ex - (p - one), fx),
        ),
    )
    result["TwoSum-SETZ-O0-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey == fy + (p - one), ey > ex, ex > fx, fx > fy),
        z3.Or(
            setz_case_zero(sy, ey, fy),
            setz_case(sy, ey + one, (ey - (p - three), ex), None, ey - (p - one), fy),
            setz_case(sy, ey + one, ey + one, sx, ey - (p - one), fy),
        ),
    )

    result["TwoSum-SETZ-O1-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ex == fx + (p - one),
            ex > ey,
            ey == fy,
            fy > fx + one,
        ),
        z3.Or(
            setz_case_zero(sx, ex, fx),
            setz_case(
                sx, ex + one, (ex - (p - three), ey - one), None, ex - (p - one), fx
            ),
            setz_case(sx, ex + one, ey, (sy,), ex - (p - one), fx),
            setz_case(sx, ex + one, ex + one, sy, ex - (p - one), fx),
        ),
    )
    result["TwoSum-SETZ-O1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ey == fy + (p - one),
            ey > ex,
            ex == fx,
            fx > fy + one,
        ),
        z3.Or(
            setz_case_zero(sy, ey, fy),
            setz_case(
                sy, ey + one, (ey - (p - three), ex - one), None, ey - (p - one), fy
            ),
            setz_case(sy, ey + one, ex, (sx,), ey - (p - one), fy),
            setz_case(sy, ey + one, ey + one, sx, ey - (p - one), fy),
        ),
    )

    result["TwoSum-SETZ-O2-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex == fx + (p - one), ey == fy, fy == fx + one),
        z3.Or(
            setz_case_zero(sx, ex, fx),
            setz_case(sx, ex + one, ex + one, sy, ex - (p - one), fx),
        ),
    )
    result["TwoSum-SETZ-O2-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey == fy + (p - one), ex == fx, fx == fy + one),
        z3.Or(
            setz_case_zero(sy, ey, fy),
            setz_case(sy, ey + one, ey + one, sx, ey - (p - one), fy),
        ),
    )

    #################################################### LEMMA FAMILY SETZ-1 (4)

    result["TwoSum-SETZ-1-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            ex < ey + p,
            ex > fy + p,
            fx > ey + one,
            z3.Or(ex > fx, same_sign),
        ),
        z3.Or(
            setz_case(sx, ex, (ex - (p - one), ey - one), None, ex - (p + one), fy),
            setz_case(sx, ex, ey, sy, ex - (p + one), fy),
            setz_case(sx, ex, ey + one, (sy,), ex - (p + one), fy),
        ),
    )
    result["TwoSum-SETZ-1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            ey < ex + p,
            ey > fx + p,
            fy > ex + one,
            z3.Or(ey > fy, same_sign),
        ),
        z3.Or(
            setz_case(sy, ey, (ey - (p - one), ex - one), None, ey - (p + one), fx),
            setz_case(sy, ey, ex, sx, ey - (p + one), fx),
            setz_case(sy, ey, ex + one, (sx,), ey - (p + one), fx),
        ),
    )

    result["TwoSum-SETZ-1A-X"] = z3.Implies(
        z3.And(ex == ey + p, ex > fy + p, fx > ey + one, z3.Or(ex > fx, same_sign)),
        setz_case(sx, ex, ey + one, (sy,), ex - (p + one), fy),
    )
    result["TwoSum-SETZ-1A-Y"] = z3.Implies(
        z3.And(ey == ex + p, ey > fx + p, fy > ex + one, z3.Or(ey > fy, same_sign)),
        setz_case(sy, ey, ex + one, (sx,), ey - (p + one), fx),
    )

    result["TwoSum-SETZ-1B0-X"] = z3.Implies(
        z3.And(
            ex < ey + (p - one), ex == fy + p, fx > ey + one, z3.Or(ex > fx, same_sign)
        ),
        z3.Or(
            setz_case(sx, ex, (ex - (p - two), ey - one), None, ex - p, fy),
            setz_case(sx, ex, ey, sy, ex - p, fy),
            setz_case(sx, ex, ey + one, (sy,), ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-1B0-Y"] = z3.Implies(
        z3.And(
            ey < ex + (p - one), ey == fx + p, fy > ex + one, z3.Or(ey > fy, same_sign)
        ),
        z3.Or(
            setz_case(sy, ey, (ey - (p - two), ex - one), None, ey - p, fx),
            setz_case(sy, ey, ex, sx, ey - p, fx),
            setz_case(sy, ey, ex + one, (sx,), ey - p, fx),
        ),
    )

    result["TwoSum-SETZ-1B1-X"] = z3.Implies(
        z3.And(
            ex == ey + (p - one), ex == fy + p, fx > ey + one, z3.Or(ex > fx, same_sign)
        ),
        setz_case(sx, ex, ey + one, (sy,), ex - p, fy),
    )
    result["TwoSum-SETZ-1B1-Y"] = z3.Implies(
        z3.And(
            ey == ex + (p - one), ey == fx + p, fy > ex + one, z3.Or(ey > fy, same_sign)
        ),
        setz_case(sy, ey, ex + one, (sx,), ey - p, fx),
    )

    ################################################### LEMMA FAMILY SETZ-2 (18)

    result["TwoSum-SETZ-2-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex > fy + p, fx < ey),
        z3.Or(
            setz_case(sx, ex, (ex - (p - one), ex - one), None, ex - (p + one), fy),
            setz_case(sx, ex + one, (ex - (p - two), ey), None, ex - p, fy),
            setz_case(sx, ex + one, ex + one, (sy,), ex - (p + one), fy),
            setz_case(sx, ex + one, ex + one, sy, ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-2-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey > fx + p, fy < ex),
        z3.Or(
            setz_case(sy, ey, (ey - (p - one), ey - one), None, ey - (p + one), fx),
            setz_case(sy, ey + one, (ey - (p - two), ex), None, ey - p, fx),
            setz_case(sy, ey + one, ey + one, (sx,), ey - (p + one), fx),
            setz_case(sy, ey + one, ey + one, sx, ey - p, fx),
        ),
    )

    result["TwoSum-SETZ-2A0-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex == fy + p, fx < ey, ey < fy + (p - one)),
        z3.Or(
            setz_case(sx, ex, (ex - (p - two), ex - one), None, ex - p, fy),
            setz_case(sx, ex + one, (ex - (p - two), ey), None, ex - p, fy),
            setz_case(sx, ex + one, ex + one, None, ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-2A0-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey == fx + p, fy < ex, ex < fx + (p - one)),
        z3.Or(
            setz_case(sy, ey, (ey - (p - two), ey - one), None, ey - p, fx),
            setz_case(sy, ey + one, (ey - (p - two), ex), None, ey - p, fx),
            setz_case(sy, ey + one, ey + one, None, ey - p, fx),
        ),
    )

    result["TwoSum-SETZ-2A1-X"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ex == fy + p, fx + one < ey, ey == fy + (p - one)
        ),
        z3.Or(
            setz_case(sx, ex, (ex - (p - two), ex - two), None, ex - p, fy),
            setz_case(sx, ex + one, (ex - (p - two), ey), None, ex - p, fy),
            setz_case(sx, ex + one, ex + one, None, ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-2A1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ey == fx + p, fy + one < ex, ex == fx + (p - one)
        ),
        z3.Or(
            setz_case(sy, ey, (ey - (p - two), ey - two), None, ey - p, fx),
            setz_case(sy, ey + one, (ey - (p - two), ex), None, ey - p, fx),
            setz_case(sy, ey + one, ey + one, None, ey - p, fx),
        ),
    )

    result["TwoSum-SETZ-2A2-X"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ex == fy + p, fx + one == ey, ey == fy + (p - one)
        ),
        z3.Or(
            setz_case(sx, ex, (ex - (p - two), ey - two), None, ex - p, fy),
            setz_case(sx, ex, ey - one, sy, ex - p, fy),
            setz_case(sx, ex + one, (ex - (p - two), ey), None, ex - p, fy),
            setz_case(sx, ex + one, ex + one, None, ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-2A2-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ey == fx + p, fy + one == ex, ex == fx + (p - one)
        ),
        z3.Or(
            setz_case(sy, ey, (ey - (p - two), ex - two), None, ey - p, fx),
            setz_case(sy, ey, ex - one, sx, ey - p, fx),
            setz_case(sy, ey + one, (ey - (p - two), ex), None, ey - p, fx),
            setz_case(sy, ey + one, ey + one, None, ey - p, fx),
        ),
    )

    result["TwoSum-SETZ-2B0-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex > fy + p, fx == ey, ex < fx + (p - one)),
        z3.Or(
            setz_case(sx, ex, (ex - (p - one), ey - one), None, ex - (p + one), fy),
            setz_case(sx, ex, ey, (sy,), ex - (p + one), fy),
            setz_case(sx, ex, (ey + one, ex - one), sy, ex - (p + one), fy),
            setz_case(sx, ex + one, (ex - (p - two), ey - one), None, ex - p, fy),
            setz_case(sx, ex + one, ey, (sy,), ex - p, fy),
            setz_case(sx, ex + one, ex + one, sy, ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-2B0-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey > fx + p, fy == ex, ey < fy + (p - one)),
        z3.Or(
            setz_case(sy, ey, (ey - (p - one), ex - one), None, ey - (p + one), fx),
            setz_case(sy, ey, ex, (sx,), ey - (p + one), fx),
            setz_case(sy, ey, (ex + one, ey - one), sx, ey - (p + one), fx),
            setz_case(sy, ey + one, (ey - (p - two), ex - one), None, ey - p, fx),
            setz_case(sy, ey + one, ex, (sx,), ey - p, fx),
            setz_case(sy, ey + one, ey + one, sx, ey - p, fx),
        ),
    )

    result["TwoSum-SETZ-2B1-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex > fy + p, fx == ey, ex == fx + (p - one)),
        z3.Or(
            setz_case(sx, ex, ey, (sy,), ex - (p + one), fy),
            setz_case(sx, ex, (ey + one, ex - one), sy, ex - (p + one), fy),
            setz_case(sx, ex + one, ex + one, sy, ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-2B1-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey > fx + p, fy == ex, ey == fy + (p - one)),
        z3.Or(
            setz_case(sy, ey, ex, (sx,), ey - (p + one), fx),
            setz_case(sy, ey, (ex + one, ey - one), sx, ey - (p + one), fx),
            setz_case(sy, ey + one, ey + one, sx, ey - p, fx),
        ),
    )

    result["TwoSum-SETZ-2C0-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ex == fy + (p - one),
            fx < ey,
            ex < fx + (p - one),
            ey < fy + (p - one),
        ),
        z3.Or(
            setz_case_zero(sx, ex, fy),
            setz_case(sx, ex + one, (ex - (p - three), ey), None, ex - (p - one), fy),
            setz_case(sx, ex + one, ex + one, sy, ex - (p - one), fy),
        ),
    )
    result["TwoSum-SETZ-2C0-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ey == fx + (p - one),
            fy < ex,
            ey < fy + (p - one),
            ex < fx + (p - one),
        ),
        z3.Or(
            setz_case_zero(sy, ey, fx),
            setz_case(sy, ey + one, (ey - (p - three), ex), None, ey - (p - one), fx),
            setz_case(sy, ey + one, ey + one, sx, ey - (p - one), fx),
        ),
    )

    result["TwoSum-SETZ-2C1-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ex == fy + (p - one),
            fx < ey,
            ex < fx + (p - one),
            ey == fy + (p - one),
        ),
        setz_case(sx, ex + one, (ex - (p - three), ey), None, ex - (p - one), fy),
    )
    result["TwoSum-SETZ-2C1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ey == fx + (p - one),
            fy < ex,
            ey < fy + (p - one),
            ex == fx + (p - one),
        ),
        setz_case(sy, ey + one, (ey - (p - three), ex), None, ey - (p - one), fx),
    )

    result["TwoSum-SETZ-2D0-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex > fy + p, fx == ey + one, ex < fx + (p - one)),
        z3.Or(
            setz_case(sx, ex, (ex - (p - one), ey - one), None, ex - (p + one), fy),
            setz_case(sx, ex, ey, sy, ex - (p + one), fy),
            setz_case(sx, ex, (ey + two, ex - one), (sy,), ex - (p + one), fy),
            setz_case(sx, ex + one, ex + one, (sy,), ex - (p + one), fy),
        ),
    )
    result["TwoSum-SETZ-2D0-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey > fx + p, fy == ex + one, ey < fy + (p - one)),
        z3.Or(
            setz_case(sy, ey, (ey - (p - one), ex - one), None, ey - (p + one), fx),
            setz_case(sy, ey, ex, sx, ey - (p + one), fx),
            setz_case(sy, ey, (ex + two, ey - one), (sx,), ey - (p + one), fx),
            setz_case(sy, ey + one, ey + one, (sx,), ey - (p + one), fx),
        ),
    )

    result["TwoSum-SETZ-2D1-X"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ex > fy + p, fx == ey + one, ex == fx + (p - one)
        ),
        z3.Or(
            setz_case(sx, ex, (ey + two, ex - one), (sy,), ex - (p + one), fy),
            setz_case(sx, ex + one, ex + one, (sy,), ex - (p + one), fy),
        ),
    )
    result["TwoSum-SETZ-2D1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ey > fx + p, fy == ex + one, ey == fy + (p - one)
        ),
        z3.Or(
            setz_case(sy, ey, (ex + two, ey - one), (sx,), ey - (p + one), fx),
            setz_case(sy, ey + one, ey + one, (sx,), ey - (p + one), fx),
        ),
    )

    result["TwoSum-SETZ-2AB0-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ex == fy + p,
            fx == ey,
            ex < fx + (p - one),
            ey < fy + (p - one),
        ),
        z3.Or(
            setz_case(sx, ex, (ex - (p - two), ey - one), None, ex - p, fy),
            setz_case(sx, ex, ey, (sy,), ex - p, fy),
            setz_case(sx, ex, (ey + one, ex - one), sy, ex - p, fy),
            setz_case(sx, ex + one, (ex - (p - two), ey - one), None, ex - p, fy),
            setz_case(sx, ex + one, ey, (sy,), ex - p, fy),
            setz_case(sx, ex + one, ex + one, sy, ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-2AB0-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ey == fx + p,
            fy == ex,
            ey < fy + (p - one),
            ex < fx + (p - one),
        ),
        z3.Or(
            setz_case(sy, ey, (ey - (p - two), ex - one), None, ey - p, fx),
            setz_case(sy, ey, ex, (sx,), ey - p, fx),
            setz_case(sy, ey, (ex + one, ey - one), sx, ey - p, fx),
            setz_case(sy, ey + one, (ey - (p - two), ex - one), None, ey - p, fx),
            setz_case(sy, ey + one, ex, (sx,), ey - p, fx),
            setz_case(sy, ey + one, ey + one, sx, ey - p, fx),
        ),
    )

    result["TwoSum-SETZ-2AB1-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex == fy + p, fx == ey, ex == fx + (p - one)),
        z3.Or(
            setz_case(sx, ex, (ey + one, ex - one), sy, ex - p, fy),
            setz_case(sx, ex + one, ex + one, sy, ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-2AB1-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey == fx + p, fy == ex, ey == fy + (p - one)),
        z3.Or(
            setz_case(sy, ey, (ex + one, ey - one), sx, ey - p, fx),
            setz_case(sy, ey + one, ey + one, sx, ey - p, fx),
        ),
    )

    result["TwoSum-SETZ-2AB2-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex == fy + p, fx == ey, ey == fy + (p - one)),
        z3.Or(
            setz_case(sx, ex + one, (ex - (p - two), ey - one), None, ex - p, fy),
            setz_case(sx, ex + one, ey, (sy,), ex - p, fy),
            setz_case(sx, ex + one, ex + one, sy, ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-2AB2-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey == fx + p, fy == ex, ex == fx + (p - one)),
        z3.Or(
            setz_case(sy, ey + one, (ey - (p - two), ex - one), None, ey - p, fx),
            setz_case(sy, ey + one, ex, (sx,), ey - p, fx),
            setz_case(sy, ey + one, ey + one, sx, ey - p, fx),
        ),
    )

    result["TwoSum-SETZ-2BC0-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ex == fy + (p - one),
            fx == ey,
            ey > fy + one,
            ey < fy + (p - two),
        ),
        z3.Or(
            setz_case_zero(sx, ex, fy),
            setz_case(sx, ex + one, (ex - (p - three), ey), None, ex - (p - one), fy),
            setz_case(sx, ex + one, ey, (sy,), ex - (p - one), fy),
            setz_case(sx, ex + one, ex + one, sy, ex - (p - one), fy),
        ),
    )
    result["TwoSum-SETZ-2BC0-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            same_sign,
            ey == fx + (p - one),
            fy == ex,
            ex > fx + one,
            ex < fx + (p - two),
        ),
        z3.Or(
            setz_case_zero(sy, ey, fx),
            setz_case(sy, ey + one, (ey - (p - three), ex), None, ey - (p - one), fx),
            setz_case(sy, ey + one, ex, (sx,), ey - (p - one), fx),
            setz_case(sy, ey + one, ey + one, sx, ey - (p - one), fx),
        ),
    )

    result["TwoSum-SETZ-2BC1-X"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ex == fy + (p - one), fx == ey, ey > fy + (p - three)
        ),
        z3.Or(
            setz_case(sx, ex + one, (ex - (p - three), ey), None, ex - (p - one), fy),
            setz_case(sx, ex + one, ey, (sy,), ex - (p - one), fy),
            setz_case(sx, ex + one, ex + one, sy, ex - (p - one), fy),
        ),
    )
    result["TwoSum-SETZ-2BC1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ey == fx + (p - one), fy == ex, ex > fx + (p - three)
        ),
        z3.Or(
            setz_case(sy, ey + one, (ey - (p - three), ex), None, ey - (p - one), fx),
            setz_case(sy, ey + one, ex, (sx,), ey - (p - one), fx),
            setz_case(sy, ey + one, ey + one, sx, ey - (p - one), fx),
        ),
    )

    result["TwoSum-SETZ-2BC2-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex == fy + (p - one), fx == ey, ey == fy + one),
        z3.Or(
            setz_case_zero(sx, ex, fy),
            setz_case(sx, ex + one, ex + one, sy, ex - (p - one), fy),
        ),
    )
    result["TwoSum-SETZ-2BC2-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey == fx + (p - one), fy == ex, ex == fx + one),
        z3.Or(
            setz_case_zero(sy, ey, fx),
            setz_case(sy, ey + one, ey + one, sx, ey - (p - one), fx),
        ),
    )

    result["TwoSum-SETZ-2AD0-X"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ex == fy + p, fx == ey + one, ex < fx + (p - two)
        ),
        z3.Or(
            setz_case(sx, ex, (ex - (p - two), ey - one), None, ex - p, fy),
            setz_case(sx, ex, ey, sy, ex - p, fy),
            setz_case(sx, ex, (ey + two, ex - one), (sy,), ex - p, fy),
            setz_case(sx, ex + one, ex + one, (sy,), ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-2AD0-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ey == fx + p, fy == ex + one, ey < fy + (p - two)
        ),
        z3.Or(
            setz_case(sy, ey, (ey - (p - two), ex - one), None, ey - p, fx),
            setz_case(sy, ey, ex, sx, ey - p, fx),
            setz_case(sy, ey, (ex + two, ey - one), (sx,), ey - p, fx),
            setz_case(sy, ey + one, ey + one, (sx,), ey - p, fx),
        ),
    )

    result["TwoSum-SETZ-2AD1-X"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ex == fy + p, fx == ey + one, ex > fx + (p - three)
        ),
        z3.Or(
            setz_case(sx, ex, (ey + two, ex - one), (sy,), ex - p, fy),
            setz_case(sx, ex + one, ex + one, (sy,), ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-2AD1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, same_sign, ey == fx + p, fy == ex + one, ey > fy + (p - three)
        ),
        z3.Or(
            setz_case(sy, ey, (ex + two, ey - one), (sx,), ey - p, fx),
            setz_case(sy, ey + one, ey + one, (sx,), ey - p, fx),
        ),
    )

    ################################################### LEMMA FAMILY SETZ-3 (13)

    result["TwoSum-SETZ-3-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex > fy + (p + one), fx < ey),
        z3.Or(
            setz_case(sx, ex - one, (ex - p, ey), None, ex - (p + two), fy),
            setz_case(sx, ex, (ex - (p - one), ex - one), None, ex - (p + one), fy),
            setz_case(sx, ex, ex, sy, ex - (p + two), fy),
            setz_case(sx, ex, ex, (sy,), ex - (p + one), fy),
        ),
    )
    result["TwoSum-SETZ-3-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey > fx + (p + one), fy < ex),
        z3.Or(
            setz_case(sy, ey - one, (ey - p, ex), None, ey - (p + two), fx),
            setz_case(sy, ey, (ey - (p - one), ey - one), None, ey - (p + one), fx),
            setz_case(sy, ey, ey, sx, ey - (p + two), fx),
            setz_case(sy, ey, ey, (sx,), ey - (p + one), fx),
        ),
    )

    result["TwoSum-SETZ-3A-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == fy + (p + one), fx < ey),
        z3.Or(
            setz_case(sx, ex - one, (ex - (p - one), ey), None, ex - (p + one), fy),
            setz_case(sx, ex, (ex - (p - one), ex), None, ex - (p + one), fy),
        ),
    )
    result["TwoSum-SETZ-3A-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == fx + (p + one), fy < ex),
        z3.Or(
            setz_case(sy, ey - one, (ey - (p - one), ex), None, ey - (p + one), fx),
            setz_case(sy, ey, (ey - (p - one), ey), None, ey - (p + one), fx),
        ),
    )

    result["TwoSum-SETZ-3B-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex > fy + (p + one), fx == ey),
        z3.Or(
            setz_case(sx, ex - one, (ex - p, ey - one), None, ex - (p + two), fy),
            setz_case(sx, ex - one, ey, (sy,), ex - (p + two), fy),
            setz_case(sx, ex, (ex - (p - one), ey - one), None, ex - (p + one), fy),
            setz_case(sx, ex, ey, (sy,), ex - (p + one), fy),
            setz_case(sx, ex, (ey + one, ex - one), sy, ex - (p + one), fy),
            setz_case(sx, ex, ex, sy, ex - (p + two), fy),
        ),
    )
    result["TwoSum-SETZ-3B-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey > fx + (p + one), fy == ex),
        z3.Or(
            setz_case(sy, ey - one, (ey - p, ex - one), None, ey - (p + two), fx),
            setz_case(sy, ey - one, ex, (sx,), ey - (p + two), fx),
            setz_case(sy, ey, (ey - (p - one), ex - one), None, ey - (p + one), fx),
            setz_case(sy, ey, ex, (sx,), ey - (p + one), fx),
            setz_case(sy, ey, (ex + one, ey - one), sx, ey - (p + one), fx),
            setz_case(sy, ey, ey, sx, ey - (p + two), fx),
        ),
    )

    result["TwoSum-SETZ-3C0-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == fy + p, fx < ey, ey < fy + (p - one)),
        z3.Or(
            setz_case_zero(sx, ex - one, fy),
            setz_case(sx, ex, (ex - (p - two), ex - one), None, ex - p, fy),
            setz_case(sx, ex, ex, (sy,), ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-3C0-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == fx + p, fy < ex, ex < fx + (p - one)),
        z3.Or(
            setz_case_zero(sy, ey - one, fx),
            setz_case(sy, ey, (ey - (p - two), ey - one), None, ey - p, fx),
            setz_case(sy, ey, ey, (sx,), ey - p, fx),
        ),
    )

    result["TwoSum-SETZ-3C1-X"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, ex == fy + p, fx + one < ey, ey == fy + (p - one)
        ),
        z3.Or(
            setz_case_zero(sx, (fx, ex - one), fy),
            setz_case(sx, ex, (ex - (p - two), ex - two), None, ex - p, fy),
            setz_case(sx, ex, ex, (sy,), ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-3C1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, ey == fx + p, fy + one < ex, ex == fx + (p - one)
        ),
        z3.Or(
            setz_case_zero(sy, (fy, ey - one), fx),
            setz_case(sy, ey, (ey - (p - two), ey - two), None, ey - p, fx),
            setz_case(sy, ey, ey, (sx,), ey - p, fx),
        ),
    )

    result["TwoSum-SETZ-3C2-X"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, ex == fy + p, fx + one == ey, ey == fy + (p - one)
        ),
        z3.Or(
            setz_case_zero(sx, (ex - two, ex - one), fy),
            setz_case(sx, ex, (ex - (p - two), ey - two), None, ex - p, fy),
            setz_case(sx, ex, ey - one, sy, ex - p, fy),
            setz_case(sx, ex, ex, (sy,), ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-3C2-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, ey == fx + p, fy + one == ex, ex == fx + (p - one)
        ),
        z3.Or(
            setz_case_zero(sy, (ey - two, ey - one), fx),
            setz_case(sy, ey, (ey - (p - two), ex - two), None, ey - p, fx),
            setz_case(sy, ey, ex - one, sx, ey - p, fx),
            setz_case(sy, ey, ey, (sx,), ey - p, fx),
        ),
    )

    result["TwoSum-SETZ-3D0-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex > fy + p, fx == ey + one, ex < fx + (p - one)),
        z3.Or(
            setz_case(sx, ex, (ex - (p - one), ey - one), None, ex - (p + one), fy),
            setz_case(sx, ex, ey, sy, ex - (p + one), fy),
            setz_case(sx, ex, (ey + two, ex), (sy,), ex - (p + one), fy),
        ),
    )
    result["TwoSum-SETZ-3D0-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey > fx + p, fy == ex + one, ey < fy + (p - one)),
        z3.Or(
            setz_case(sy, ey, (ey - (p - one), ex - one), None, ey - (p + one), fx),
            setz_case(sy, ey, ex, sx, ey - (p + one), fx),
            setz_case(sy, ey, (ex + two, ey), (sx,), ey - (p + one), fx),
        ),
    )

    result["TwoSum-SETZ-3D1-X"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, ex > fy + p, fx == ey + one, ex == fx + (p - one)
        ),
        setz_case(sx, ex, (ey + two, ex), (sy,), ex - (p + one), fy),
    )
    result["TwoSum-SETZ-3D1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, ey > fx + p, fy == ex + one, ey == fy + (p - one)
        ),
        setz_case(sy, ey, (ex + two, ey), (sx,), ey - (p + one), fx),
    )

    result["TwoSum-SETZ-3AB-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == fy + (p + one), fx == ey),
        z3.Or(
            setz_case(
                sx, ex - one, (ex - (p - one), ey - one), None, ex - (p + one), fy
            ),
            setz_case(sx, ex - one, ey, (sy,), ex - (p + one), fy),
            setz_case(sx, ex, (ex - (p - one), ey - one), None, ex - (p + one), fy),
            setz_case(sx, ex, ey, (sy,), ex - (p + one), fy),
            setz_case(sx, ex, (ey + one, ex), sy, ex - (p + one), fy),
        ),
    )
    result["TwoSum-SETZ-3AB-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == fx + (p + one), fy == ex),
        z3.Or(
            setz_case(
                sy, ey - one, (ey - (p - one), ex - one), None, ey - (p + one), fx
            ),
            setz_case(sy, ey - one, ex, (sx,), ey - (p + one), fx),
            setz_case(sy, ey, (ey - (p - one), ex - one), None, ey - (p + one), fx),
            setz_case(sy, ey, ex, (sx,), ey - (p + one), fx),
            setz_case(sy, ey, (ex + one, ey), sx, ey - (p + one), fx),
        ),
    )

    result["TwoSum-SETZ-3BC0-X"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, ex == fy + p, fx == ey, ex > fx + one, ey > fy + one
        ),
        z3.Or(
            setz_case_zero(sx, ex - one, fy),
            setz_case(sx, ex, (ex - (p - two), ey - one), None, ex - p, fy),
            setz_case(sx, ex, ey, (sy,), ex - p, fy),
            setz_case(sx, ex, (ey + one, ex), sy, ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-3BC0-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, ey == fx + p, fy == ex, ey > fy + one, ex > fx + one
        ),
        z3.Or(
            setz_case_zero(sy, ey - one, fx),
            setz_case(sy, ey, (ey - (p - two), ex - one), None, ey - p, fx),
            setz_case(sy, ey, ex, (sx,), ey - p, fx),
            setz_case(sy, ey, (ex + one, ey), sx, ey - p, fx),
        ),
    )

    result["TwoSum-SETZ-3BC1-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == fy + p, fx == ey, ey == fy + one),
        z3.Or(
            setz_case_zero(sx, ex - one, fy),
            setz_case(sx, ex, (ey + one, ex - one), sy, ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-3BC1-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == fx + p, fy == ex, ex == fx + one),
        z3.Or(
            setz_case_zero(sy, ey - one, fx),
            setz_case(sy, ey, (ex + one, ey - one), sx, ey - p, fx),
        ),
    )

    result["TwoSum-SETZ-3CD0-X"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, ex == fy + p, fx == ey + one, ex > fx, ey > fy + one
        ),
        z3.Or(
            setz_case(sx, ex, (ex - (p - two), ey - one), None, ex - p, fy),
            setz_case(sx, ex, ey, sy, ex - p, fy),
            setz_case(sx, ex, (ey + two, ex), (sy,), ex - p, fy),
        ),
    )
    result["TwoSum-SETZ-3CD0-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, ey == fx + p, fy == ex + one, ey > fy, ex > fx + one
        ),
        z3.Or(
            setz_case(sy, ey, (ey - (p - two), ex - one), None, ey - p, fx),
            setz_case(sy, ey, ex, sx, ey - p, fx),
            setz_case(sy, ey, (ex + two, ey), (sx,), ey - p, fx),
        ),
    )

    result["TwoSum-SETZ-3CD1-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == fy + p, fx == ey + one, ey < fy + two),
        setz_case(sx, ex, (ey + two, ex), (sy,), ex - p, fy),
    )
    result["TwoSum-SETZ-3CD1-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == fx + p, fy == ex + one, ex < fx + two),
        setz_case(sy, ey, (ex + two, ey), (sx,), ey - p, fx),
    )

    #################################################### LEMMA FAMILY SETZ-4 (4)

    result["TwoSum-SETZ-4-X"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, ex > fy + (p + one), fx < ey + (p + one), ex == fx
        ),
        z3.Or(
            setz_case(sx, ex - one, (ex - p, ey - one), None, ex - (p + two), fy),
            setz_case(sx, ex - one, ey, sy, ex - (p + two), fy),
            setz_case(sx, ex - one, ey + one, (sy,), ex - (p + two), fy),
        ),
    )
    result["TwoSum-SETZ-4-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, ey > fx + (p + one), fy < ex + (p + one), ey == fy
        ),
        z3.Or(
            setz_case(sy, ey - one, (ey - p, ex - one), None, ey - (p + two), fx),
            setz_case(sy, ey - one, ex, sx, ey - (p + two), fx),
            setz_case(sy, ey - one, ex + one, (sx,), ey - (p + two), fx),
        ),
    )

    result["TwoSum-SETZ-4A0-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == fy + (p + one), fx < ey + p, ex == fx),
        z3.Or(
            setz_case(
                sx, ex - one, (ex - (p - one), ey - one), None, ex - (p + one), fy
            ),
            setz_case(sx, ex - one, ey, sy, ex - (p + one), fy),
            setz_case(sx, ex - one, ey + one, (sy,), ex - (p + one), fy),
        ),
    )
    result["TwoSum-SETZ-4A0-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == fx + (p + one), fy < ex + p, ey == fy),
        z3.Or(
            setz_case(
                sy, ey - one, (ey - (p - one), ex - one), None, ey - (p + one), fx
            ),
            setz_case(sy, ey - one, ex, sx, ey - (p + one), fx),
            setz_case(sy, ey - one, ex + one, (sx,), ey - (p + one), fx),
        ),
    )

    result["TwoSum-SETZ-4A1-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == fy + (p + one), fx == ey + p, ex == fx),
        setz_case(sx, ex - one, (ex - (p - one), ey + one), (sy,), ex - (p + one), fy),
    )
    result["TwoSum-SETZ-4A1-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == fx + (p + one), fy == ex + p, ey == fy),
        setz_case(sy, ey - one, (ey - (p - one), ex + one), (sx,), ey - (p + one), fx),
    )

    result["TwoSum-SETZ-4B-X"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, ex > fy + (p + one), fx == ey + (p + one), ex == fx
        ),
        setz_case(sx, ex - one, (ex - p, ey + one), (sy,), ex - (p + two), fy),
    )
    result["TwoSum-SETZ-4B-Y"] = z3.Implies(
        z3.And(
            xy_nonzero, diff_sign, ey > fx + (p + one), fy == ex + (p + one), ey == fy
        ),
        setz_case(sy, ey - one, (ey - p, ex + one), (sx,), ey - (p + two), fx),
    )

    return result
