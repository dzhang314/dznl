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

    # # Lemma SETZ-Z1: Both addends are zero.
    # verifier("SETZ-Z1-PP", (x == pos_zero) & (y == pos_zero)) do lemma
    #     add_case!(lemma, pos_zero, pos_zero)
    # end
    # verifier("SETZ-Z1-PN", (x == pos_zero) & (y == neg_zero)) do lemma
    #     add_case!(lemma, pos_zero, pos_zero)
    # end
    # verifier("SETZ-Z1-NP", (x == neg_zero) & (y == pos_zero)) do lemma
    #     add_case!(lemma, pos_zero, pos_zero)
    # end
    # verifier("SETZ-Z1-NN", (x == neg_zero) & (y == neg_zero)) do lemma
    #     add_case!(lemma, neg_zero, pos_zero)
    # end
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

    # # Lemma SETZ-Z2: One addend is zero.
    # verifier("SETZ-Z2-X", y_zero & !x_zero) do lemma
    #     add_case!(lemma, x, pos_zero)
    # end
    # verifier("SETZ-Z2-Y", x_zero & !y_zero) do lemma
    #     add_case!(lemma, y, pos_zero)
    # end
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

    # fmt: off

    # verifier("SETZ-I-X",
    #     (ex > ey + (p+1)) |
    #     ((ex == ey + (p+1)) & ((ey == fy) | same_sign | (ex > fx))) |
    #     ((ex == ey + p) & (ey == fy) & (same_sign | (ex > fx)) & (ex < fx + (p-1)))
    # ) do lemma
    #     add_case!(lemma, x, y)
    # end
    # verifier("SETZ-I-Y",
    #     (ey > ex + (p+1)) |
    #     ((ey == ex + (p+1)) & ((ex == fx) | same_sign | (ey > fy))) |
    #     ((ey == ex + p) & (ex == fx) & (same_sign | (ey > fy)) & (ey < fy + (p-1)))
    # ) do lemma
    #     add_case!(lemma, y, x)
    # end
    result["TwoSum-SETZ-I-X"] = z3.Implies(z3.And(xy_nonzero, z3.Or(
                   ex >  ey + (p+one),
            z3.And(ex == ey + (p+one), z3.Or(ey == fy,       same_sign, ex > fx)),
            z3.And(ex == ey + p      ,       ey == fy, z3.Or(same_sign, ex > fx), ex < fx + (p-one)),
        )),
        z3.And(s_equals_x, e_equals_y),
    )
    result["TwoSum-SETZ-I-Y"] = z3.Implies(z3.And(xy_nonzero, z3.Or(
                   ey >  ex + (p+one),
            z3.And(ey == ex + (p+one), z3.Or(ex == fx,       same_sign, ey > fy)),
            z3.And(ey == ex + p      ,       ex == fx, z3.Or(same_sign, ey > fy), ey < fy + (p-one)),
        )),
        z3.And(s_equals_y, e_equals_x),
    )

    # fmt: on

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

    # verifier("SETZ-FS0-X", same_sign & (fx == fy) & (ex > ey + 1)) do lemma
    #     add_case!(lemma, (sx, ex  , fx+1:ex-1), pos_zero)
    #     add_case!(lemma, (sx, ex+1, fx+1:ey  ), pos_zero)
    #     add_case!(lemma, (sx, ex+1, ex+1     ), pos_zero)
    # end
    # verifier("SETZ-FS0-Y", same_sign & (fx == fy) & (ey > ex + 1)) do lemma
    #     add_case!(lemma, (sy, ey  , fy+1:ey-1), pos_zero)
    #     add_case!(lemma, (sy, ey+1, fy+1:ex  ), pos_zero)
    #     add_case!(lemma, (sy, ey+1, ey+1     ), pos_zero)
    # end
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

    # verifier("SETZ-FS1-X", same_sign & (fx == fy) & (ex == ey + 1)) do lemma
    #     add_case!(lemma, (sx, ex  , fx+1:ex-2), pos_zero)
    #     add_case!(lemma, (sx, ex+1, fx+1:ey  ), pos_zero)
    #     add_case!(lemma, (sx, ex+1, ex+1     ), pos_zero)
    # end
    # verifier("SETZ-FS1-Y", same_sign & (fx == fy) & (ey == ex + 1)) do lemma
    #     add_case!(lemma, (sy, ey  , fy+1:ey-2), pos_zero)
    #     add_case!(lemma, (sy, ey+1, fy+1:ex  ), pos_zero)
    #     add_case!(lemma, (sy, ey+1, ey+1     ), pos_zero)
    # end
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

    # verifier("SETZ-FS2", same_sign & (fx == fy) & (ex == ey) & (ex > fx)) do lemma
    #     add_case!(lemma, (sx, ex+1, fx+1:ex), pos_zero)
    # end
    result["TwoSum-SETZ-FS2"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, fx == fy, ex == ey, ex > fx),
        setz_case_zero(sx, ex + one, (fx + one, ex)),
    )

    # verifier("SETZ-FS3", same_sign & (fx == fy) & (ex == ey) & (ex == fx)) do lemma
    #     add_case!(lemma, (sx, ex+1, ex+1), pos_zero)
    # end
    result["TwoSum-SETZ-FS3"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, fx == fy, ex == ey, ex == fx),
        setz_case_zero(sx, ex + one, ex + one),
    )

    # verifier("SETZ-FD0-X", diff_sign & (fx == fy) & (ex > ey + 1)) do lemma
    #     add_case!(lemma, (sx, ex-1, fx+1:ey), pos_zero)
    #     add_case!(lemma, (sx, ex  , fx+1:ex), pos_zero)
    # end
    # verifier("SETZ-FD0-Y", diff_sign & (fx == fy) & (ey > ex + 1)) do lemma
    #     add_case!(lemma, (sy, ey-1, fy+1:ex), pos_zero)
    #     add_case!(lemma, (sy, ey  , fy+1:ey), pos_zero)
    # end
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

    # verifier("SETZ-FD1-X", diff_sign & (fx == fy) & (ex == ey + 1)) do lemma
    #     for k = fx+1:ex-1
    #         add_case!(lemma, (sx, k, fx+1:k), pos_zero)
    #     end
    #     add_case!(lemma, (sx, ex, fx+1:ex-2), pos_zero)
    #     add_case!(lemma, (sx, ex, ex       ), pos_zero)
    # end
    # verifier("SETZ-FD1-Y", diff_sign & (fx == fy) & (ey == ex + 1)) do lemma
    #     for k = fy+1:ey-1
    #         add_case!(lemma, (sy, k, fy+1:k), pos_zero)
    #     end
    #     add_case!(lemma, (sy, ey, fy+1:ey-2), pos_zero)
    #     add_case!(lemma, (sy, ey, ey       ), pos_zero)
    # end
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

    # verifier("SETZ-FD2", diff_sign & (fx == fy) & (ex == ey)) do lemma
    #     add_case!(lemma, pos_zero, pos_zero)
    #     for k = fx+1:ex-1
    #         add_case!(lemma, (±, k, fx+1:k), pos_zero)
    #     end
    # end
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

    # # Lemma SETZ-EN0: Addends do not overlap.
    # verifier("SETZ-EN0-X", (same_sign | (ex > fx)) & (fx > ey) & (ex < fy + p)) do lemma
    #     add_case!(lemma, (sx, ex, fy), pos_zero)
    # end
    # verifier("SETZ-EN0-Y", (same_sign | (ey > fy)) & (fy > ex) & (ey < fx + p)) do lemma
    #     add_case!(lemma, (sy, ey, fx), pos_zero)
    # end
    result["TwoSum-SETZ-EN0-X"] = z3.Implies(
        z3.And(xy_nonzero, z3.Or(same_sign, ex > fx), fx > ey, ex < fy + p),
        setz_case_zero(sx, ex, fy),
    )
    result["TwoSum-SETZ-EN0-Y"] = z3.Implies(
        z3.And(xy_nonzero, z3.Or(same_sign, ey > fy), fy > ex, ey < fx + p),
        setz_case_zero(sy, ey, fx),
    )

    # # Lemma SETZ-EN1: Boundary case of SETZ-EN0.
    # verifier("SETZ-EN1-X", diff_sign & (
    #     ((ex == fx) & (fx > ey + 1) & (ex < fy + (p+1))) |
    #     ((ex == fx + 1) & (fx == ey) & (ey > fy))
    # )) do lemma
    #     add_case!(lemma, (sx, ex-1, fy), pos_zero)
    # end
    # verifier("SETZ-EN1-Y", diff_sign & (
    #     ((ey == fy) & (fy > ex + 1) & (ey < fx + (p+1))) |
    #     ((ey == fy + 1) & (fy == ex) & (ex > fx))
    # )) do lemma
    #     add_case!(lemma, (sy, ey-1, fx), pos_zero)
    # end
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

    # # Lemma SETZ-ESP0: Addends have same sign and partially overlap.
    # verifier("SETZ-ESP0-X", same_sign & ((ex > ey > fx > fy) | (ex > ey + 1 > fx > fy)) & (ex < fy + (p-1))) do lemma
    #     add_case!(lemma, (sx, ex:ex+1, fy), pos_zero)
    # end
    # verifier("SETZ-ESP0-Y", same_sign & ((ey > ex > fy > fx) | (ey > ex + 1 > fy > fx)) & (ey < fx + (p-1))) do lemma
    #     add_case!(lemma, (sy, ey:ey+1, fx), pos_zero)
    # end
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

    # # Lemma SETZ-ESP1: Boundary case of SETZ-ESP0 with guaranteed carry.
    # verifier("SETZ-ESP1-X", same_sign & (ex == ey + 1) & (ey == fx > fy) & (ex < fy + (p-1))) do lemma
    #     add_case!(lemma, (sx, ex+1, fy), pos_zero)
    # end
    # verifier("SETZ-ESP1-Y", same_sign & (ey == ex + 1) & (ex == fy > fx) & (ey < fx + (p-1))) do lemma
    #     add_case!(lemma, (sy, ey+1, fx), pos_zero)
    # end
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

    # # Lemma SETZ-ESC: Addends have same sign and completely overlap.
    # verifier("SETZ-ESC-X", same_sign & (ex > ey) & (fx < fy) & (ex < fx + (p-1))) do lemma
    #     add_case!(lemma, (sx, ex:ex+1, fx), pos_zero)
    # end
    # verifier("SETZ-ESC-Y", same_sign & (ey > ex) & (fy < fx) & (ey < fy + (p-1))) do lemma
    #     add_case!(lemma, (sy, ey:ey+1, fy), pos_zero)
    # end
    result["TwoSum-SETZ-ESC-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex > ey, fx < fy, ex < fx + (p - one)),
        setz_case_zero(sx, (ex, ex + one), fx),
    )
    result["TwoSum-SETZ-ESC-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey > ex, fy < fx, ey < fy + (p - one)),
        setz_case_zero(sy, (ey, ey + one), fy),
    )

    # # Lemma SETZ-ESS: Addends have same sign and exponent.
    # verifier("SETZ-ESS-X", same_sign & (ex == ey) & (fx < fy) & (ex < fx + (p-1)) & (ey < fy + (p-1))) do lemma
    #     add_case!(lemma, (sx, ex+1, fx), pos_zero)
    # end
    # verifier("SETZ-ESS-Y", same_sign & (ex == ey) & (fx > fy) & (ex < fx + (p-1)) & (ey < fy + (p-1))) do lemma
    #     add_case!(lemma, (sx, ex+1, fy), pos_zero)
    # end
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

    # # Lemma SETZ-EDP0: Addends have different signs and partially overlap.
    # verifier("SETZ-EDP0-X", diff_sign & (ex > ey + 1 > fx > fy) & (ex < fy + p)) do lemma
    #     add_case!(lemma, (sx, ex-1:ex, fy), pos_zero)
    # end
    # verifier("SETZ-EDP0-Y", diff_sign & (ey > ex + 1 > fy > fx) & (ey < fx + p)) do lemma
    #     add_case!(lemma, (sy, ey-1:ey, fx), pos_zero)
    # end
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

    # # Lemma SETZ-EDP1: Boundary case of SETZ-EDP0 with more possible cancellation.
    # verifier("SETZ-EDP1-X", diff_sign & (ex == ey + 1) & (ey > fx > fy) & (ex < fy + p)) do lemma
    #     add_case!(lemma, (sx, fx:ex, fy), pos_zero)
    # end
    # verifier("SETZ-EDP1-Y", diff_sign & (ey == ex + 1) & (ex > fy > fx) & (ey < fx + p)) do lemma
    #     add_case!(lemma, (sy, fy:ey, fx), pos_zero)
    # end
    result["TwoSum-SETZ-EDP1-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey + one, ey > fx, fx > fy, ex < fy + p),
        setz_case_zero(sx, (fx, ex), fy),
    )
    result["TwoSum-SETZ-EDP1-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == ex + one, ex > fy, fy > fx, ey < fx + p),
        setz_case_zero(sy, (fy, ey), fx),
    )

    # # Lemma SETZ-EDP2: Boundary case of SETZ-EDP1 with guaranteed cancellation.
    # verifier("SETZ-EDP2-X", diff_sign & (ex == ey + 1 == fx) & (fx > fy + 1)) do lemma
    #     add_case!(lemma, (sx, fy:ex-2, fy), pos_zero)
    # end
    # verifier("SETZ-EDP2-Y", diff_sign & (ey == ex + 1 == fy) & (fy > fx + 1)) do lemma
    #     add_case!(lemma, (sy, fx:ey-2, fx), pos_zero)
    # end
    result["TwoSum-SETZ-EDP2-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey + one, ey + one == fx, fx > fy + one),
        setz_case_zero(sx, (fy, ex - two), fy),
    )
    result["TwoSum-SETZ-EDP2-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == ex + one, ex + one == fy, fy > fx + one),
        setz_case_zero(sy, (fx, ey - two), fx),
    )

    # # Lemma SETZ-EDP3: Boundary case of SETZ-EDP2 with less guaranteed cancellation.
    # verifier("SETZ-EDP3-X", diff_sign & (ex == ey + 1 == fx == fy + 1)) do lemma
    #     add_case!(lemma, (sx, fy:ex-1, fy), pos_zero)
    # end
    # verifier("SETZ-EDP3-Y", diff_sign & (ey == ex + 1 == fy == fx + 1)) do lemma
    #     add_case!(lemma, (sy, fx:ey-1, fx), pos_zero)
    # end
    result["TwoSum-SETZ-EDP3-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey + one, ey + one == fx, fx == fy + one),
        setz_case_zero(sx, (fy, ex - one), fy),
    )
    result["TwoSum-SETZ-EDP3-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == ex + one, ex + one == fy, fy == fx + one),
        setz_case_zero(sy, (fx, ey - one), fx),
    )

    # # Lemma SETZ-EDC0: Addends have different signs and completely overlap.
    # verifier("SETZ-EDC0-X", diff_sign & (ex > ey + 1) & (fx < fy)) do lemma
    #     add_case!(lemma, (sx, ex-1:ex, fx), pos_zero)
    # end
    # verifier("SETZ-EDC0-Y", diff_sign & (ey > ex + 1) & (fy < fx)) do lemma
    #     add_case!(lemma, (sy, ey-1:ey, fy), pos_zero)
    # end
    result["TwoSum-SETZ-EDC0-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex > ey + one, fx < fy),
        setz_case_zero(sx, (ex - one, ex), fx),
    )
    result["TwoSum-SETZ-EDC0-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey > ex + one, fy < fx),
        setz_case_zero(sy, (ey - one, ey), fy),
    )

    # # Lemma SETZ-EDC1: Boundary case of SETZ-EDC0 with more possible cancellation.
    # verifier("SETZ-EDC1-X", diff_sign & (ex == ey + 1) & (fx < fy)) do lemma
    #     add_case!(lemma, (sx, fy:ex, fx), pos_zero)
    # end
    # verifier("SETZ-EDC1-Y", diff_sign & (ey == ex + 1) & (fy < fx)) do lemma
    #     add_case!(lemma, (sy, fx:ey, fy), pos_zero)
    # end
    result["TwoSum-SETZ-EDC1-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey + one, fx < fy),
        setz_case_zero(sx, (fy, ex), fx),
    )
    result["TwoSum-SETZ-EDC1-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == ex + one, fy < fx),
        setz_case_zero(sy, (fx, ey), fy),
    )

    # # Lemma SETZ-EDC2: Boundary case of SETZ-EDC0 with guaranteed cancellation.
    # verifier("SETZ-EDC2-X", diff_sign & (ex == ey == fy) & (fx < fy)) do lemma
    #     add_case!(lemma, (sx, fx:ex-1, fx), pos_zero)
    # end
    # verifier("SETZ-EDC2-Y", diff_sign & (ey == ex == fx) & (fy < fx)) do lemma
    #     add_case!(lemma, (sy, fy:ey-1, fy), pos_zero)
    # end
    result["TwoSum-SETZ-EDC2-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey, ey == fy, fx < fy),
        setz_case_zero(sx, (fx, ex - one), fx),
    )
    result["TwoSum-SETZ-EDC2-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == ex, ex == fx, fy < fx),
        setz_case_zero(sy, (fy, ey - one), fy),
    )

    # # Lemma SETZ-EDS0: Addends have same exponent and different signs.
    # verifier("SETZ-EDS0-X", diff_sign & (ex == ey) & (fx < fy) & (ex > fx + 1) & (ey > fy + 1)) do lemma
    #     add_case!(lemma, (±, fx:ex-1, fx), pos_zero)
    # end
    # verifier("SETZ-EDS0-Y", diff_sign & (ex == ey) & (fx > fy) & (ex > fx + 1) & (ey > fy + 1)) do lemma
    #     add_case!(lemma, (±, fy:ey-1, fy), pos_zero)
    # end
    result["TwoSum-SETZ-EDS0-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey, fx < fy, ex > fx + one, ey > fy + one),
        setz_case_zero(None, (fx, ex - one), fx),
    )
    result["TwoSum-SETZ-EDS0-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey, fx > fy, ex > fx + one, ey > fy + one),
        setz_case_zero(None, (fy, ey - one), fy),
    )

    # # Lemma SETZ-EDS1: Boundary case of SETZ-EDS0 where two leading bits cancel.
    # verifier("SETZ-EDS1-X", diff_sign & (ex == ey) & (ex > fx + 1) & (ey == fy + 1)) do lemma
    #     add_case!(lemma, (±, fx:ex-2, fx), pos_zero)
    # end
    # verifier("SETZ-EDS1-Y", diff_sign & (ex == ey) & (ex == fx + 1) & (ey > fy + 1)) do lemma
    #     add_case!(lemma, (±, fy:ey-2, fy), pos_zero)
    # end
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

    # # All hypotheses are strictly necessary.
    # verifier("SETZ-O0-X", same_sign & (ex == fx + (p-1)) & (ex > ey > fy > fx)) do lemma
    #     add_case!(lemma, (sx, ex  , fx         ), pos_zero             )
    #     add_case!(lemma, (sx, ex+1, ex-(p-3):ey), (± , fx:ex-(p-1), fx))
    #     add_case!(lemma, (sx, ex+1, ex+1       ), (sy, fx:ex-(p-1), fx))
    # end
    # verifier("SETZ-O0-Y", same_sign & (ey == fy + (p-1)) & (ey > ex > fx > fy)) do lemma
    #     add_case!(lemma, (sy, ey  , fy         ), pos_zero             )
    #     add_case!(lemma, (sy, ey+1, ey-(p-3):ex), (± , fy:ey-(p-1), fy))
    #     add_case!(lemma, (sy, ey+1, ey+1       ), (sx, fy:ey-(p-1), fy))
    # end
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

    # # All hypotheses are strictly necessary.
    # verifier("SETZ-O1-X", same_sign & (ex == fx + (p-1)) & (ex > ey == fy > fx + 1)) do lemma
    #     add_case!(lemma, (sx, ex  , fx           ), pos_zero              )
    #     add_case!(lemma, (sx, ex+1, ex-(p-3):ey-1), ( ± , fx:ex-(p-1), fx))
    #     add_case!(lemma, (sx, ex+1, ey           ), (!sy, fx:ex-(p-1), fx))
    #     add_case!(lemma, (sx, ex+1, ex+1         ), ( sy, fx:ex-(p-1), fx))
    # end
    # verifier("SETZ-O1-Y", same_sign & (ey == fy + (p-1)) & (ey > ex == fx > fy + 1)) do lemma
    #     add_case!(lemma, (sy, ey  , fy           ), pos_zero              )
    #     add_case!(lemma, (sy, ey+1, ey-(p-3):ex-1), ( ± , fy:ey-(p-1), fy))
    #     add_case!(lemma, (sy, ey+1, ex           ), (!sx, fy:ey-(p-1), fy))
    #     add_case!(lemma, (sy, ey+1, ey+1         ), ( sx, fy:ey-(p-1), fy))
    # end
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

    # # All hypotheses are strictly necessary.
    # verifier("SETZ-O2-X", same_sign & (ex == fx + (p-1)) & (ey == fy == fx + 1)) do lemma
    #     add_case!(lemma, (sx, ex  , fx  ), pos_zero             )
    #     add_case!(lemma, (sx, ex+1, ex+1), (sy, fx:ex-(p-1), fx))
    # end
    # verifier("SETZ-O2-Y", same_sign & (ey == fy + (p-1)) & (ex == fx == fy + 1)) do lemma
    #     add_case!(lemma, (sy, ey  , fy  ), pos_zero             )
    #     add_case!(lemma, (sy, ey+1, ey+1), (sx, fy:ey-(p-1), fy))
    # end
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

    # verifier("SETZ-1-X", (ex < ey + p) & (ex > fy + p) & (fx > ey + 1) & ((ex > fx) | same_sign)) do lemma
    #     add_case!(lemma, (sx, ex, ex-(p-1):ey-1), ( ± , fy:ex-(p+1), fy))
    #     add_case!(lemma, (sx, ex, ey           ), ( sy, fy:ex-(p+1), fy))
    #     add_case!(lemma, (sx, ex, ey+1         ), (!sy, fy:ex-(p+1), fy))
    # end
    # verifier("SETZ-1-Y", (ey < ex + p) & (ey > fx + p) & (fy > ex + 1) & ((ey > fy) | same_sign)) do lemma
    #     add_case!(lemma, (sy, ey, ey-(p-1):ex-1), ( ± , fx:ey-(p+1), fx))
    #     add_case!(lemma, (sy, ey, ex           ), ( sx, fx:ey-(p+1), fx))
    #     add_case!(lemma, (sy, ey, ex+1         ), (!sx, fx:ey-(p+1), fx))
    # end
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

    # verifier("SETZ-1A-X", (ex == ey + p) & (ex > fy + p) & (fx > ey + 1) & ((ex > fx) | same_sign)) do lemma
    #     add_case!(lemma, (sx, ex, ey+1), (!sy, fy:ex-(p+1), fy))
    # end
    # verifier("SETZ-1A-Y", (ey == ex + p) & (ey > fx + p) & (fy > ex + 1) & ((ey > fy) | same_sign)) do lemma
    #     add_case!(lemma, (sy, ey, ex+1), (!sx, fx:ey-(p+1), fx))
    # end
    result["TwoSum-SETZ-1A-X"] = z3.Implies(
        z3.And(ex == ey + p, ex > fy + p, fx > ey + one, z3.Or(ex > fx, same_sign)),
        setz_case(sx, ex, ey + one, (sy,), ex - (p + one), fy),
    )
    result["TwoSum-SETZ-1A-Y"] = z3.Implies(
        z3.And(ey == ex + p, ey > fx + p, fy > ex + one, z3.Or(ey > fy, same_sign)),
        setz_case(sy, ey, ex + one, (sx,), ey - (p + one), fx),
    )

    # verifier("SETZ-1B0-X", (ex < ey + (p-1)) & (ex == fy + p) & (fx > ey + 1) & ((ex > fx) | same_sign)) do lemma
    #     add_case!(lemma, (sx, ex, ex-(p-2):ey-1), ( ± , fy:ex-p, fy))
    #     add_case!(lemma, (sx, ex, ey           ), ( sy, fy:ex-p, fy))
    #     add_case!(lemma, (sx, ex, ey+1         ), (!sy, fy:ex-p, fy))
    # end
    # verifier("SETZ-1B0-Y", (ey < ex + (p-1)) & (ey == fx + p) & (fy > ex + 1) & ((ey > fy) | same_sign)) do lemma
    #     add_case!(lemma, (sy, ey, ey-(p-2):ex-1), ( ± , fx:ey-p, fx))
    #     add_case!(lemma, (sy, ey, ex           ), ( sx, fx:ey-p, fx))
    #     add_case!(lemma, (sy, ey, ex+1         ), (!sx, fx:ey-p, fx))
    # end
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

    # verifier("SETZ-1B1-X", (ex == ey + (p-1)) & (ex == fy + p) & (fx > ey + 1) & ((ex > fx) | same_sign)) do lemma
    #     add_case!(lemma, (sx, ex, ey+1), (!sy, fy:ex-p, fy))
    # end
    # verifier("SETZ-1B1-Y", (ey == ex + (p-1)) & (ey == fx + p) & (fy > ex + 1) & ((ey > fy) | same_sign)) do lemma
    #     add_case!(lemma, (sy, ey, ex+1), (!sx, fx:ey-p, fx))
    # end
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

    return result

    ############################################################# LEMMA FAMILY 2

    # fmt: off

    # # Lemma 2
    # if same_sign & (ex > fy + p) & (fx < ey)
    #         push_range!(t, (sx, ex       , ex-(p-1):ex-1), (±  , fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex-(p-2):ey  ), (±  , fy:ex-p    , fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (!sy, fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-p    , fy))
    # if same_sign & (ey > fx + p) & (fy < ex)
    #         push_range!(t, (sy, ey       , ey-(p-1):ey-1), (±  , fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey-(p-2):ex  ), (±  , fx:ey-p    , fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (!sx, fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-p    , fx))
    result["TwoSum-2-X"] = z3.Implies(
        z3.And(same_sign, ex > fy + p, fx < ey),
        z3.Or(
            x_case(ex    , (ex-(p-one), ex-one), None , 1),
            x_case(ex+one, (ex-(p-two), ey)    , None , 0),
            x_case(ex+one, ex+one              , False, 1),
            x_case(ex+one, ex+one              , True , 0),
        ),
    )
    result["TwoSum-2-Y"] = z3.Implies(
        z3.And(same_sign, ey > fx + p, fy < ex),
        z3.Or(
            y_case(ey    , (ey-(p-one), ey-one), None , 1),
            y_case(ey+one, (ey-(p-two), ex)    , None , 0),
            y_case(ey+one, ey+one              , False, 1),
            y_case(ey+one, ey+one              , True , 0),
        ),
    )

    # # Lemma 2A.G
    # if same_sign & (ex == fy + p) & (fx < ey) & (ey < fy + (p - 1))
    #         push_range!(t, (sx, ex       , ex-(p-2):ex-1), (±, fy:ex-p, fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex-(p-2):ey  ), (±, fy:ex-p, fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (±, fy:ex-p, fy))
    # if same_sign & (ey == fx + p) & (fy < ex) & (ex < fx + (p - 1))
    #         push_range!(t, (sy, ey       , ey-(p-2):ey-1), (±, fx:ey-p, fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey-(p-2):ex  ), (±, fx:ey-p, fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (±, fx:ey-p, fx))
    result["TwoSum-2A-G-X"] = z3.Implies(
        z3.And(same_sign, ex == fy + p, fx < ey, ey < fy + (p - one)),
        z3.Or(
            x_case(ex    , (ex-(p-two), ex-one), None, 0),
            x_case(ex+one, (ex-(p-two), ey)    , None, 0),
            x_case(ex+one, ex+one              , None, 0),
        ),
    )
    result["TwoSum-2A-G-Y"] = z3.Implies(
        z3.And(same_sign, ey == fx + p, fy < ex, ex < fx + (p - one)),
        z3.Or(
            y_case(ey    , (ey-(p-two), ey-one), None, 0),
            y_case(ey+one, (ey-(p-two), ex)    , None, 0),
            y_case(ey+one, ey+one              , None, 0),
        ),
    )

    # # Lemma 2A.1
    # if same_sign & (ex == fy + p) & (fx + 1 < ey) & (ey == fy + (p - 1))
    #         push_range!(t, (sx, ex       , ex-(p-2):ex-2), (±, fy:ex-p, fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex-(p-2):ey  ), (±, fy:ex-p, fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (±, fy:ex-p, fy))
    # if same_sign & (ey == fx + p) & (fy + 1 < ex) & (ex == fx + (p - 1))
    #         push_range!(t, (sy, ey       , ey-(p-2):ey-2), (±, fx:ey-p, fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey-(p-2):ex  ), (±, fx:ey-p, fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (±, fx:ey-p, fx))
    result["TwoSum-2A-1-X"] = z3.Implies(
        z3.And(same_sign, ex == fy + p, fx + one < ey, ey == fy + (p - one)),
        z3.Or(
            x_case(ex    , (ex-(p-two), ex-two), None, 0),
            x_case(ex+one, (ex-(p-two), ey)    , None, 0),
            x_case(ex+one, ex+one              , None, 0),
        ),
    )
    result["TwoSum-2A-1-Y"] = z3.Implies(
        z3.And(same_sign, ey == fx + p, fy + one < ex, ex == fx + (p - one)),
        z3.Or(
            y_case(ey    , (ey-(p-two), ey-two), None, 0),
            y_case(ey+one, (ey-(p-two), ex)    , None, 0),
            y_case(ey+one, ey+one              , None, 0),
        ),
    )

    # # Lemma 2A.2
    # if same_sign & (ex == fy + p) & (fx + 1 == ey) & (ey == fy + (p - 1))
    #         push_range!(t, (sx, ex       , ex-(p-2):ey-2), (± , fy:ex-p, fy))
    #         push_range!(t, (sx, ex       , ey - 1       ), (sy, fy:ex-p, fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex-(p-2):ey  ), (± , fy:ex-p, fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (± , fy:ex-p, fy))
    # if same_sign & (ey == fx + p) & (fy + 1 == ex) & (ex == fx + (p - 1))
    #         push_range!(t, (sy, ey       , ey-(p-2):ex-2), (± , fx:ey-p, fx))
    #         push_range!(t, (sy, ey       , ex - 1       ), (sx, fx:ey-p, fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey-(p-2):ex  ), (± , fx:ey-p, fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (± , fx:ey-p, fx))
    result["TwoSum-2A-2-X"] = z3.Implies(
        z3.And(same_sign, ex == fy + p, fx + one == ey, ey == fy + (p - one)),
        z3.Or(
            x_case(ex    , (ex-(p-two), ey-two), None, 0),
            x_case(ex    , ey-one              , True, 0),
            x_case(ex+one, (ex-(p-two), ey)    , None, 0),
            x_case(ex+one, ex+one              , None, 0),
        ),
    )
    result["TwoSum-2A-2-Y"] = z3.Implies(
        z3.And(same_sign, ey == fx + p, fy + one == ex, ex == fx + (p - one)),
        z3.Or(
            y_case(ey    , (ey-(p-two), ex-two), None, 0),
            y_case(ey    , ex-one              , True, 0),
            y_case(ey+one, (ey-(p-two), ex)    , None, 0),
            y_case(ey+one, ey+one              , None, 0),
        ),
    )

    # # Lemma 2B.G
    # if same_sign & (ex > fy + p) & (fx == ey) & (ex < fx + (p - 1))
    #         push_range!(t, (sx, ex       , ex-(p-1):ey-1), (±  , fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex       , ey           ), (!sy, fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex       , ey+1:ex-1    ), (sy , fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex-(p-2):ey-1), (±  , fy:ex-p    , fy))
    #         push_range!(t, (sx, ex+1:ex+1, ey           ), (!sy, fy:ex-p    , fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-p    , fy))
    # if same_sign & (ey > fx + p) & (fy == ex) & (ey < fy + (p - 1))
    #         push_range!(t, (sy, ey       , ey-(p-1):ex-1), (±  , fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey       , ex           ), (!sx, fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey       , ex+1:ey-1    ), (sx , fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey-(p-2):ex-1), (±  , fx:ey-p    , fx))
    #         push_range!(t, (sy, ey+1:ey+1, ex           ), (!sx, fx:ey-p    , fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-p    , fx))
    result["TwoSum-2B-G-X"] = z3.Implies(
        z3.And(same_sign, ex > fy + p, fx == ey, ex < fx + (p - one)),
        z3.Or(
            x_case(ex    , (ex-(p-one), ey-one), None , 1),
            x_case(ex    , ey                  , False, 1),
            x_case(ex    , (ey+one, ex-one)    , True , 1),
            x_case(ex+one, (ex-(p-two), ey-one), None , 0),
            x_case(ex+one, ey                  , False, 0),
            x_case(ex+one, ex+one              , True , 0),
        ),
    )
    result["TwoSum-2B-G-Y"] = z3.Implies(
        z3.And(same_sign, ey > fx + p, fy == ex, ey < fy + (p - one)),
        z3.Or(
            y_case(ey    , (ey-(p-one), ex-one), None , 1),
            y_case(ey    , ex                  , False, 1),
            y_case(ey    , (ex+one, ey-one)    , True , 1),
            y_case(ey+one, (ey-(p-two), ex-one), None , 0),
            y_case(ey+one, ex                  , False, 0),
            y_case(ey+one, ey+one              , True , 0),
        ),
    )

    # # Lemma 2B.1
    # if same_sign & (ex > fy + p) & (fx == ey) & (ex == fx + (p - 1))
    #         push_range!(t, (sx, ex       , ey           ), (!sy, fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex       , ey+1:ex-1    ), (sy , fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-p    , fy))
    # if same_sign & (ey > fx + p) & (fy == ex) & (ey == fy + (p - 1))
    #         push_range!(t, (sy, ey       , ex           ), (!sx, fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey       , ex+1:ey-1    ), (sx , fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-p    , fx))
    result["TwoSum-2B-1-X"] = z3.Implies(
        z3.And(same_sign, ex > fy + p, fx == ey, ex == fx + (p - one)),
        z3.Or(
            x_case(ex    , ey              , False, 1),
            x_case(ex    , (ey+one, ex-one), True , 1),
            x_case(ex+one, ex+one          , True , 0),
        ),
    )
    result["TwoSum-2B-1-Y"] = z3.Implies(
        z3.And(same_sign, ey > fx + p, fy == ex, ey == fy + (p - one)),
        z3.Or(
            y_case(ey    , ex              , False, 1),
            y_case(ey    , (ex+one, ey-one), True , 1),
            y_case(ey+one, ey+one          , True , 0),
        ),
    )

    # # Lemma 2C.G
    # if same_sign & (ex == fy + (p - 1)) & (fx < ey) & (ex < fx + (p - 1)) & (ey < fy + (p - 1))
    #         push_range!(t, (sx, ex       , fy), pos_zero)
    #         push_range!(t, (sx, ex+1:ex+1, ex-(p-3):ey), (± , fy:ex-(p-1), fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1     ), (sy, fy:ex-(p-1), fy))
    # if same_sign & (ey == fx + (p - 1)) & (fy < ex) & (ey < fy + (p - 1)) & (ex < fx + (p - 1))
    #         push_range!(t, (sy, ey       , fx), pos_zero)
    #         push_range!(t, (sy, ey+1:ey+1, ey-(p-3):ex), (± , fx:ey-(p-1), fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1     ), (sx, fx:ey-(p-1), fx))
    result["TwoSum-2C-G-X"] = z3.Implies(
        z3.And(same_sign, ex == fy + (p - one), fx < ey, ex < fx + (p - one), ey < fy + (p - one)),
        z3.Or(
            setz_case_zero(sx, ex, fy),
            x_case(ex+one, (ex-(p-three), ey), None, -1),
            x_case(ex+one, ex+one            , True, -1),
        ),
    )
    result["TwoSum-2C-G-Y"] = z3.Implies(
        z3.And(same_sign, ey == fx + (p - one), fy < ex, ey < fy + (p - one), ex < fx + (p - one)),
        z3.Or(
            setz_case_zero(sy, ey, fx),
            y_case(ey+one, (ey-(p-three), ex), None, -1),
            y_case(ey+one, ey+one            , True, -1),
        ),
    )

    # # Lemma 2C.1
    # if same_sign & (ex == fy + (p - 1)) & (fx < ey) & (ex < fx + (p - 1)) & (ey == fy + (p - 1))
    #         push_range!(t, (sx, ex+1:ex+1, ex-(p-3):ey), (± , fy:ex-(p-1), fy))
    # if same_sign & (ey == fx + (p - 1)) & (fy < ex) & (ey < fy + (p - 1)) & (ex == fx + (p - 1))
    #         push_range!(t, (sy, ey+1:ey+1, ey-(p-3):ex), (± , fx:ey-(p-1), fx))
    result["TwoSum-2C-1-X"] = z3.Implies(
        z3.And(same_sign, ex == fy + (p - one), fx < ey, ex < fx + (p - one), ey == fy + (p - one)),
        x_case(ex+one, (ex-(p-three), ey), None, -1),
    )
    result["TwoSum-2C-1-Y"] = z3.Implies(
        z3.And(same_sign, ey == fx + (p - one), fy < ex, ey < fy + (p - one), ex == fx + (p - one)),
        y_case(ey+one, (ey-(p-three), ex), None, -1),
    )

    # # Lemma 2D.G
    # if same_sign & (ex > fy + p) & (fx == ey + 1) & (ex < fx + (p - 1))
    #         push_range!(t, (sx, ex       , ex-(p-1):ey-1), (±  , fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex       , ey           ), (sy , fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex       , ey+2:ex-1    ), (!sy, fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (!sy, fy:ex-(p+1), fy))
    # if same_sign & (ey > fx + p) & (fy == ex + 1) & (ey < fy + (p - 1))
    #         push_range!(t, (sy, ey       , ey-(p-1):ex-1), (±  , fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey       , ex           ), (sx , fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey       , ex+2:ey-1    ), (!sx, fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (!sx, fx:ey-(p+1), fx))
    result["TwoSum-2D-G-X"] = z3.Implies(
        z3.And(same_sign, ex > fy + p, fx == ey + one, ex < fx + (p - one)),
        z3.Or(
            x_case(ex    , (ex-(p-one), ey-one), None , 1),
            x_case(ex    , ey                  , True , 1),
            x_case(ex    , (ey+two, ex-one)    , False, 1),
            x_case(ex+one, ex+one              , False, 1),
        ),
    )
    result["TwoSum-2D-G-Y"] = z3.Implies(
        z3.And(same_sign, ey > fx + p, fy == ex + one, ey < fy + (p - one)),
        z3.Or(
            y_case(ey    , (ey-(p-one), ex-one), None , 1),
            y_case(ey    , ex                  , True , 1),
            y_case(ey    , (ex+two, ey-one)    , False, 1),
            y_case(ey+one, ey+one              , False, 1),
        ),
    )

    # # Lemma 2D.1
    # if same_sign & (ex > fy + p) & (fx == ey + 1) & (ex == fx + (p - 1))
    #         push_range!(t, (sx, ex       , ey+2:ex-1    ), (!sy, fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (!sy, fy:ex-(p+1), fy))
    # if same_sign & (ey > fx + p) & (fy == ex + 1) & (ey == fy + (p - 1))
    #         push_range!(t, (sy, ey       , ex+2:ey-1    ), (!sx, fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (!sx, fx:ey-(p+1), fx))
    result["TwoSum-2D-1-X"] = z3.Implies(
        z3.And(same_sign, ex > fy + p, fx == ey + one, ex == fx + (p - one)),
        z3.Or(
            x_case(ex    , (ey+two, ex-one), False, 1),
            x_case(ex+one, ex+one          , False, 1),
        ),
    )
    result["TwoSum-2D-1-Y"] = z3.Implies(
        z3.And(same_sign, ey > fx + p, fy == ex + one, ey == fy + (p - one)),
        z3.Or(
            y_case(ey    , (ex+two, ey-one), False, 1),
            y_case(ey+one, ey+one          , False, 1),
        ),
    )

    # # Lemma 2AB.G
    # if same_sign & (ex == fy + p) & (fx == ey) & (ex < fx + (p - 1)) & (ey < fy + (p - 1))
    #         push_range!(t, (sx, ex       , ex-(p-2):ey-1), (±  , fy:ex-p, fy))
    #         push_range!(t, (sx, ex       , ey           ), (!sy, fy:ex-p, fy))
    #         push_range!(t, (sx, ex       , ey+1:ex-1    ), (sy , fy:ex-p, fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex-(p-2):ey-1), (±  , fy:ex-p, fy))
    #         push_range!(t, (sx, ex+1:ex+1, ey           ), (!sy, fy:ex-p, fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-p, fy))
    # if same_sign & (ey == fx + p) & (fy == ex) & (ey < fy + (p - 1)) & (ex < fx + (p - 1))
    #         push_range!(t, (sy, ey       , ey-(p-2):ex-1), (±  , fx:ey-p, fx))
    #         push_range!(t, (sy, ey       , ex           ), (!sx, fx:ey-p, fx))
    #         push_range!(t, (sy, ey       , ex+1:ey-1    ), (sx , fx:ey-p, fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey-(p-2):ex-1), (±  , fx:ey-p, fx))
    #         push_range!(t, (sy, ey+1:ey+1, ex           ), (!sx, fx:ey-p, fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-p, fx))
    result["TwoSum-2AB-G-X"] = z3.Implies(
        z3.And(same_sign, ex == fy + p, fx == ey, ex < fx + (p - one), ey < fy + (p - one)),
        z3.Or(
            x_case(ex    , (ex-(p-two), ey-one), None , 0),
            x_case(ex    , ey                  , False, 0),
            x_case(ex    , (ey+one, ex-one)    , True , 0),
            x_case(ex+one, (ex-(p-two), ey-one), None , 0),
            x_case(ex+one, ey                  , False, 0),
            x_case(ex+one, ex+one              , True , 0),
        ),
    )
    result["TwoSum-2AB-G-Y"] = z3.Implies(
        z3.And(same_sign, ey == fx + p, fy == ex, ey < fy + (p - one), ex < fx + (p - one)),
        z3.Or(
            y_case(ey    , (ey-(p-two), ex-one), None , 0),
            y_case(ey    , ex                  , False, 0),
            y_case(ey    , (ex+one, ey-one)    , True , 0),
            y_case(ey+one, (ey-(p-two), ex-one), None , 0),
            y_case(ey+one, ex                  , False, 0),
            y_case(ey+one, ey+one              , True , 0),
        ),
    )

    # # Lemma 2AB.1
    # if same_sign & (ex == fy + p) & (fx == ey) & (ex == fx + (p - 1))
    #         push_range!(t, (sx, ex       , ey+1:ex-1    ), (sy , fy:ex-p, fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-p, fy))
    # if same_sign & (ey == fx + p) & (fy == ex) & (ey == fy + (p - 1))
    #         push_range!(t, (sy, ey       , ex+1:ey-1    ), (sx , fx:ey-p, fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-p, fx))
    result["TwoSum-2AB-1-X"] = z3.Implies(
        z3.And(same_sign, ex == fy + p, fx == ey, ex == fx + (p - one)),
        z3.Or(
            x_case(ex    , (ey+one, ex-one), True, 0),
            x_case(ex+one, ex+one          , True, 0),
        ),
    )
    result["TwoSum-2AB-1-Y"] = z3.Implies(
        z3.And(same_sign, ey == fx + p, fy == ex, ey == fy + (p - one)),
        z3.Or(
            y_case(ey    , (ex+one, ey-one), True, 0),
            y_case(ey+one, ey+one          , True, 0),
        ),
    )

    # # Lemma 2AB.2
    # if same_sign & (ex == fy + p) & (fx == ey) & (ey == fy + (p - 1))
    #         push_range!(t, (sx, ex+1:ex+1, ex-(p-2):ey-1), (±  , fy:ex-p, fy))
    #         push_range!(t, (sx, ex+1:ex+1, ey           ), (!sy, fy:ex-p, fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-p, fy))
    # if same_sign & (ey == fx + p) & (fy == ex) & (ex == fx + (p - 1))
    #         push_range!(t, (sy, ey+1:ey+1, ey-(p-2):ex-1), (±  , fx:ey-p, fx))
    #         push_range!(t, (sy, ey+1:ey+1, ex           ), (!sx, fx:ey-p, fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-p, fx))
    result["TwoSum-2AB-2-X"] = z3.Implies(
        z3.And(same_sign, ex == fy + p, fx == ey, ey == fy + (p - one)),
        z3.Or(
            x_case(ex+one, (ex-(p-two), ey-one), None , 0),
            x_case(ex+one, ey                  , False, 0),
            x_case(ex+one, ex+one              , True , 0),
        ),
    )
    result["TwoSum-2AB-2-Y"] = z3.Implies(
        z3.And(same_sign, ey == fx + p, fy == ex, ex == fx + (p - one)),
        z3.Or(
            y_case(ey+one, (ey-(p-two), ex-one), None , 0),
            y_case(ey+one, ex                  , False, 0),
            y_case(ey+one, ey+one              , True , 0),
        ),
    )

    # # Lemma 2BC.G
    # if same_sign & (ex == fy + (p - 1)) & (fx == ey) & (ey > fy + 1) & (ey < fy + (p - 2))
    #         push_range!(t, (sx, ex       , fy), pos_zero)
    #         push_range!(t, (sx, ex+1:ex+1, ex-(p-3):ey-1), (±  , fy:ex-(p-1), fy))
    #         push_range!(t, (sx, ex+1:ex+1, ey           ), (!sy, fy:ex-(p-1), fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-(p-1), fy))
    # if same_sign & (ey == fx + (p - 1)) & (fy == ex) & (ex > fx + 1) & (ex < fx + (p - 2))
    #         push_range!(t, (sy, ey       , fx), pos_zero)
    #         push_range!(t, (sy, ey+1:ey+1, ey-(p-3):ex-1), (±  , fx:ey-(p-1), fx))
    #         push_range!(t, (sy, ey+1:ey+1, ex           ), (!sx, fx:ey-(p-1), fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-(p-1), fx))
    result["TwoSum-2BC-G-X"] = z3.Implies(
        z3.And(same_sign, ex == fy + (p - one), fx == ey, ey > fy + one, ey < fy + (p - two)),
        z3.Or(
            setz_case_zero(sx, ex, fy),
            x_case(ex+one, (ex-(p-three), ey-one), None , -1),
            x_case(ex+one, ey                    , False, -1),
            x_case(ex+one, ex+one                , True , -1),
        ),
    )
    result["TwoSum-2BC-G-Y"] = z3.Implies(
        z3.And(same_sign, ey == fx + (p - one), fy == ex, ex > fx + one, ex < fx + (p - two)),
        z3.Or(
            setz_case_zero(sy, ey, fx),
            y_case(ey+one, (ey-(p-three), ex-one), None , -1),
            y_case(ey+one, ex                    , False, -1),
            y_case(ey+one, ey+one                , True , -1),
        ),
    )

    # # Lemma 2BC.1
    # if same_sign & (ex == fy + (p - 1)) & (fx == ey) & (ey > fy + (p - 3))
    #         push_range!(t, (sx, ex+1:ex+1, ex-(p-3):ey-1), (±  , fy:ex-(p-1), fy))
    #         push_range!(t, (sx, ex+1:ex+1, ey           ), (!sy, fy:ex-(p-1), fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-(p-1), fy))
    # if same_sign & (ey == fx + (p - 1)) & (fy == ex) & (ex > fx + (p - 3))
    #         push_range!(t, (sy, ey+1:ey+1, ey-(p-3):ex-1), (±  , fx:ey-(p-1), fx))
    #         push_range!(t, (sy, ey+1:ey+1, ex           ), (!sx, fx:ey-(p-1), fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-(p-1), fx))
    result["TwoSum-2BC-1-X"] = z3.Implies(
        z3.And(same_sign, ex == fy + (p - one), fx == ey, ey > fy + (p - three)),
        z3.Or(
            x_case(ex+one, (ex-(p-three), ey-one), None , -1),
            x_case(ex+one, ey                    , False, -1),
            x_case(ex+one, ex+one                , True , -1),
        ),
    )
    result["TwoSum-2BC-1-Y"] = z3.Implies(
        z3.And(same_sign, ey == fx + (p - one), fy == ex, ex > fx + (p - three)),
        z3.Or(
            y_case(ey+one, (ey-(p-three), ex-one), None , -1),
            y_case(ey+one, ex                    , False, -1),
            y_case(ey+one, ey+one                , True , -1),
        ),
    )

    # # Lemma 2BC.2
    # if same_sign & (ex == fy + (p - 1)) & (fx == ey) & (ey == fy + 1)
    #         push_range!(t, (sx, ex       , fy), pos_zero)
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-(p-1), fy))
    # if same_sign & (ey == fx + (p - 1)) & (fy == ex) & (ex == fx + 1)
    #         push_range!(t, (sy, ey       , fx), pos_zero)
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-(p-1), fx))
    result["TwoSum-2BC-2-X"] = z3.Implies(
        z3.And(same_sign, ex == fy + (p - one), fx == ey, ey == fy + one),
        z3.Or(
            setz_case_zero(sx, ex, fy),
            x_case(ex+one, ex+one, True, -1),
        ),
    )
    result["TwoSum-2BC-2-Y"] = z3.Implies(
        z3.And(same_sign, ey == fx + (p - one), fy == ex, ex == fx + one),
        z3.Or(
            setz_case_zero(sy, ey, fx),
            y_case(ey+one, ey+one, True, -1),
        ),
    )

    # # Lemma 2AD.G
    # if same_sign & (ex == fy + p) & (fx == ey + 1) & (ex < fx + (p - 2))
    #         push_range!(t, (sx, ex       , ex-(p-2):ey-1), (±  , fy:ex-p, fy))
    #         push_range!(t, (sx, ex       , ey           ), (sy , fy:ex-p, fy))
    #         push_range!(t, (sx, ex       , ey+2:ex-1    ), (!sy, fy:ex-p, fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (!sy, fy:ex-p, fy))
    # if same_sign & (ey == fx + p) & (fy == ex + 1) & (ey < fy + (p - 2))
    #         push_range!(t, (sy, ey       , ey-(p-2):ex-1), (±  , fx:ey-p, fx))
    #         push_range!(t, (sy, ey       , ex           ), (sx , fx:ey-p, fx))
    #         push_range!(t, (sy, ey       , ex+2:ey-1    ), (!sx, fx:ey-p, fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (!sx, fx:ey-p, fx))
    result["TwoSum-2AD-G-X"] = z3.Implies(
        z3.And(same_sign, ex == fy + p, fx == ey + one, ex < fx + (p - two)),
        z3.Or(
            x_case(ex    , (ex-(p-two), ey-one), None , 0),
            x_case(ex    , ey                  , True , 0),
            x_case(ex    , (ey+two, ex-one)    , False, 0),
            x_case(ex+one, ex+one              , False, 0),
        ),
    )
    result["TwoSum-2AD-G-Y"] = z3.Implies(
        z3.And(same_sign, ey == fx + p, fy == ex + one, ey < fy + (p - two)),
        z3.Or(
            y_case(ey    , (ey-(p-two), ex-one), None , 0),
            y_case(ey    , ex                  , True , 0),
            y_case(ey    , (ex+two, ey-one)    , False, 0),
            y_case(ey+one, ey+one              , False, 0),
        ),
    )

    # # Lemma 2AD.1
    # if same_sign & (ex == fy + p) & (fx == ey + 1) & (ex > fx + (p - 3))
    #         push_range!(t, (sx, ex       , ey+2:ex-1    ), (!sy, fy:ex-p, fy))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (!sy, fy:ex-p, fy))
    # if same_sign & (ey == fx + p) & (fy == ex + 1) & (ey > fy + (p - 3))
    #         push_range!(t, (sy, ey       , ex+2:ey-1    ), (!sx, fx:ey-p, fx))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (!sx, fx:ey-p, fx))
    result["TwoSum-2AD-1-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ex == fy + p, fx == ey + one, ex > fx + (p - three)),
        z3.Or(
            x_case(ex    , (ey+two, ex-one), False, 0),
            x_case(ex+one, ex+one          , False, 0),
        ),
    )
    result["TwoSum-2AD-1-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, ey == fx + p, fy == ex + one, ey > fy + (p - three)),
        z3.Or(
            y_case(ey    , (ex+two, ey-one), False, 0),
            y_case(ey+one, ey+one          , False, 0),
        ),
    )

    # fmt: on

    ############################################################# LEMMA FAMILY 3

    # fmt: off

    result["TwoSum-3-X"] = z3.Implies(
        z3.And(diff_sign, ex > fy + (p+one), fx < ey),
        z3.Or(
            x_case(ex-one, (ex-p,ey)          , None , 2),
            x_case(ex    , (ex-(p-one),ex-one), None , 1),
            x_case(ex    , ex                 , True , 2),
            x_case(ex    , ex                 , False, 1),
        ),
    )
    result["TwoSum-3-Y"] = z3.Implies(
        z3.And(diff_sign, ey > fx + (p+one), fy < ex),
        z3.Or(
            y_case(ey-one, (ey-p,ex)          , None , 2),
            y_case(ey    , (ey-(p-one),ey-one), None , 1),
            y_case(ey    , ey                 , True , 2),
            y_case(ey    , ey                 , False, 1),
        ),
    )

    result["TwoSum-3A-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + (p+one), fx < ey),
        z3.Or(
            x_case(ex-one, (ex-(p-one),ey), None, 1),
            x_case(ex    , (ex-(p-one),ex), None, 1),
        ),
    )
    result["TwoSum-3A-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + (p+one), fy < ex),
        z3.Or(
            y_case(ey-one, (ey-(p-one),ex), None, 1),
            y_case(ey    , (ey-(p-one),ey), None, 1),
        ),
    )

    result["TwoSum-3B-X"] = z3.Implies(
        z3.And(diff_sign, ex > fy + (p+one), fx == ey),
        z3.Or(
            x_case(ex-one, (ex-p,ey-one)      , None , 2),
            x_case(ex-one, ey                 , False, 2),
            x_case(ex    , (ex-(p-one),ey-one), None , 1),
            x_case(ex    , ey                 , False, 1),
            x_case(ex    , (ey+one,ex-one)    , True , 1),
            x_case(ex    , ex                 , True , 2),
        ),
    )
    result["TwoSum-3B-Y"] = z3.Implies(
        z3.And(diff_sign, ey > fx + (p+one), fy == ex),
        z3.Or(
            y_case(ey-one, (ey-p,ex-one)      , None , 2),
            y_case(ey-one, ex                 , False, 2),
            y_case(ey    , (ey-(p-one),ex-one), None , 1),
            y_case(ey    , ex                 , False, 1),
            y_case(ey    , (ex+one,ey-one)    , True , 1),
            y_case(ey    , ey                 , True , 2),
        ),
    )

    result["TwoSum-3C-G-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + p, fx < ey, ey < fy + (p-one)),
        z3.Or(
            setz_case_zero(sx, ex-one, fy),
            x_case(ex, (ex-(p-two),ex-one), None , 0),
            x_case(ex, ex                 , False, 0),
        ),
    )
    result["TwoSum-3C-G-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + p, fy < ex, ex < fx + (p-one)),
        z3.Or(
            setz_case_zero(sy, ey-one, fx),
            y_case(ey, (ey-(p-two),ey-one), None , 0),
            y_case(ey, ey                 , False, 0),
        ),
    )

    result["TwoSum-3C-1-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + p, fx + one < ey, ey == fy + (p-one)),
        z3.Or(
            setz_case_zero(sx, (fx,ex-one), fy),
            x_case(ex, (ex-(p-two),ex-two), None , 0),
            x_case(ex, ex                 , False, 0),
        ),
    )
    result["TwoSum-3C-1-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + p, fy + one < ex, ex == fx + (p-one)),
        z3.Or(
            setz_case_zero(sy, (fy,ey-one), fx),
            y_case(ey, (ey-(p-two),ey-two), None , 0),
            y_case(ey, ey                 , False, 0),
        ),
    )

    result["TwoSum-3C-2-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + p, fx + one == ey, ey == fy + (p-one)),
        z3.Or(
            setz_case_zero(sx, (ex-two,ex-one), fy),
            x_case(ex, (ex-(p-two),ey-two), None , 0),
            x_case(ex, ey-one             , True , 0),
            x_case(ex, ex                 , False, 0),
        ),
    )
    result["TwoSum-3C-2-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + p, fy + one == ex, ex == fx + (p-one)),
        z3.Or(
            setz_case_zero(sy, (ey-two,ey-one), fx),
            y_case(ey, (ey-(p-two),ex-two), None , 0),
            y_case(ey, ex-one             , True , 0),
            y_case(ey, ey                 , False, 0),
        ),
    )

    result["TwoSum-3D-G-X"] = z3.Implies(
        z3.And(diff_sign, ex > fy + p, fx == ey + one, ex < fx + (p-one)),
        z3.Or(
            x_case(ex, (ex-(p-one),ey-one), None , 1),
            x_case(ex, ey                 , True , 1),
            x_case(ex, (ey+two,ex)        , False, 1),
        ),
    )
    result["TwoSum-3D-G-Y"] = z3.Implies(
        z3.And(diff_sign, ey > fx + p, fy == ex + one, ey < fy + (p-one)),
        z3.Or(
            y_case(ey, (ey-(p-one),ex-one), None , 1),
            y_case(ey, ex                 , True , 1),
            y_case(ey, (ex+two,ey)        , False, 1),
        ),
    )

    result["TwoSum-3D-1-X"] = z3.Implies(
        z3.And(diff_sign, ex > fy + p, fx == ey + one, ex == fx + (p-one)),
        x_case(ex, (ey+two,ex), False, 1),
    )
    result["TwoSum-3D-1-Y"] = z3.Implies(
        z3.And(diff_sign, ey > fx + p, fy == ex + one, ey == fy + (p-one)),
        y_case(ey, (ex+two,ey), False, 1),
    )

    result["TwoSum-3AB-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + (p+one), fx == ey),
        z3.Or(
            x_case(ex-one, (ex-(p-one),ey-one), None , 1),
            x_case(ex-one, ey                 , False, 1),
            x_case(ex    , (ex-(p-one),ey-one), None , 1),
            x_case(ex    , ey                 , False, 1),
            x_case(ex    , (ey+one,ex)        , True , 1),
        ),
    )
    result["TwoSum-3AB-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + (p+one), fy == ex),
        z3.Or(
            y_case(ey-one, (ey-(p-one),ex-one), None , 1),
            y_case(ey-one, ex                 , False, 1),
            y_case(ey    , (ey-(p-one),ex-one), None , 1),
            y_case(ey    , ex                 , False, 1),
            y_case(ey    , (ex+one,ey)        , True , 1),
        ),
    )

    result["TwoSum-3BC-G-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + p, fx == ey, ex > fx + one, ey > fy + one),
        z3.Or(
            setz_case_zero(sx, ex-one, fy),
            x_case(ex, (ex-(p-two),ey-one), None, 0),
            x_case(ex, ey                 , False, 0),
            x_case(ex, (ey+one,ex-one)    , True, 0),
        ),
    )
    result["TwoSum-3BC-G-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + p, fy == ex, ey > fy + one, ex > fx + one),
        z3.Or(
            setz_case_zero(sy, ey-one, fx),
            y_case(ey, (ey-(p-two),ex-one), None , 0),
            y_case(ey, ex                 , False, 0),
            y_case(ey, (ex+one,ey-one)    , True , 0),
        ),
    )

    result["TwoSum-3BC-1-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + p, fx == ey, ey == fy + one),
        z3.Or(
            setz_case_zero(sx, ex-one, fy),
            x_case(ex, (ey+one,ex-one), True, 0),
        ),
    )
    result["TwoSum-3BC-1-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + p, fy == ex, ex == fx + one),
        z3.Or(
            setz_case_zero(sy, ey-one, fx),
            y_case(ey, (ex+one,ey-one), True, 0),
        ),
    )

    result["TwoSum-3CD-G-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + p, fx == ey + one, ex > fx, ey > fy + one),
        z3.Or(
            x_case(ex, (ex-(p-two),ey-one), None , 0),
            x_case(ex, ey                 , True , 0),
            x_case(ex, (ey+two,ex)        , False, 0),
        ),
    )
    result["TwoSum-3CD-G-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + p, fy == ex + one, ey > fy, ex > fx + one),
        z3.Or(
            y_case(ey, (ey-(p-two),ex-one), None , 0),
            y_case(ey, ex                 , True , 0),
            y_case(ey, (ex+two,ey)        , False, 0),
        ),
    )

    result["TwoSum-3CD-1-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == fy + p, fx == ey + one, ey < fy + two),
        x_case(ex, (ey+two,ex), False, 0),
    )
    result["TwoSum-3CD-1-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == fx + p, fy == ex + one, ex < fx + two),
        y_case(ey, (ex+two,ey), False, 0),
    )

    # fmt: on

    ############################################################# LEMMA FAMILY 4

    # fmt: off

    result["TwoSum-4-X"] = z3.Implies(
        z3.And(diff_sign, ex > fy + (p+one), fx < ey + (p+one), ex == fx),
        z3.Or(
            x_case(ex-one, (ex-p,ey-one), None , 2),
            x_case(ex-one, ey           , True , 2),
            x_case(ex-one, ey+one       , False, 2),
        ),
    )
    result["TwoSum-4-Y"] = z3.Implies(
        z3.And(diff_sign, ey > fx + (p+one), fy < ex + (p+one), ey == fy),
        z3.Or(
            y_case(ey-one, (ey-p,ex-one), None , 2),
            y_case(ey-one, ex           , True , 2),
            y_case(ey-one, ex+one       , False, 2),
        ),
    )

    result["TwoSum-4A-G-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + (p+one), fx < ey + p, ex == fx),
        z3.Or(
            x_case(ex-one, (ex-(p-one),ey-one), None , 1),
            x_case(ex-one, ey                 , True , 1),
            x_case(ex-one, ey+one             , False, 1),
        ),
    )
    result["TwoSum-4A-G-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + (p+one), fy < ex + p, ey == fy),
        z3.Or(
            y_case(ey-one, (ey-(p-one),ex-one), None , 1),
            y_case(ey-one, ex                 , True , 1),
            y_case(ey-one, ex+one             , False, 1),
        ),
    )

    result["TwoSum-4A-1-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + (p+one), fx == ey + p, ex == fx),
        x_case(ex-one, (ex-(p-one),ey+one), False, 1),
    )
    result["TwoSum-4A-1-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + (p+one), fy == ex + p, ey == fy),
        y_case(ey-one, (ey-(p-one),ex+one), False, 1),
    )

    result["TwoSum-4B-X"] = z3.Implies(
        z3.And(diff_sign, ex > fy + (p+one), fx == ey + (p+one), ex == fx),
        x_case(ex-one, (ex-p,ey+one), False, 2),
    )
    result["TwoSum-4B-Y"] = z3.Implies(
        z3.And(diff_sign, ey > fx + (p+one), fy == ex + (p+one), ey == fy),
        y_case(ey-one, (ey-p,ex+one), False, 2),
    )

    # fmt: on

    ############################################################################

    return result
