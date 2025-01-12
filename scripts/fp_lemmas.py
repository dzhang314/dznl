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
    xy_nonzero: z3.BoolRef = z3.And(z3.Not(x_zero), z3.Not(y_zero))

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
    # lzs: z3.BoolRef = z3.Not(lbs)
    # lze: z3.BoolRef = z3.Not(lbe)
    # tzx: z3.BoolRef = z3.Not(tbx)
    # tzy: z3.BoolRef = z3.Not(tby)
    # tzs: z3.BoolRef = z3.Not(tbs)
    # tze: z3.BoolRef = z3.Not(tbe)

    same_sign = sx == sy
    diff_sign = sx != sy

    fx: IntVar = z3_If(tbx, ex - (p - one), ex - (p - one) + ntbx)
    fy: IntVar = z3_If(tby, ey - (p - one), ey - (p - one) + ntby)
    fs: IntVar = z3_If(tbs, es - (p - one), es - (p - one) + ntbs)
    fe: IntVar = z3_If(tbe, ee - (p - one), ee - (p - one) + ntbe)

    def x_case(
        es_range: IntVar | tuple[IntVar, IntVar],
        fs_range: IntVar | tuple[IntVar, IntVar],
        e_sign: bool | None,
        e_offset: int,
        *,
        overlap: bool = False,
    ) -> z3.BoolRef:
        conditions: list[z3.BoolRef] = []
        conditions.append(ss == sx)
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
        if e_sign is not None:
            if e_sign:
                conditions.append(se == sy)
            else:
                conditions.append(se != sy)
        if e_offset == 0:
            conditions.append(ee <= ex - p)
        elif e_offset == 1:
            conditions.append(ee <= ex - (p + one))
        elif e_offset == -1:
            conditions.append(ee <= ex - (p - one))
        elif e_offset == 2:
            conditions.append(ee <= ex - (p + two))
        elif e_offset == -2:
            conditions.append(ee <= ex - (p - two))
        else:
            assert False
        if overlap:
            conditions.append(ee >= fx)
            conditions.append(fe == fx)
        else:
            conditions.append(ee >= fy)
            conditions.append(fe == fy)
        return z3.And(*conditions)

    def x_case_zero(
        es_range: IntVar | tuple[IntVar, IntVar],
        fs_range: IntVar | tuple[IntVar, IntVar],
    ) -> z3.BoolRef:
        conditions: list[z3.BoolRef] = []
        conditions.append(ss == sx)
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

    def y_case(
        es_range: IntVar | tuple[IntVar, IntVar],
        fs_range: IntVar | tuple[IntVar, IntVar],
        e_sign: bool | None,
        e_offset: int,
        *,
        overlap: bool = False,
    ) -> z3.BoolRef:
        conditions: list[z3.BoolRef] = []
        conditions.append(ss == sy)
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
        if e_sign is not None:
            if e_sign:
                conditions.append(se == sx)
            else:
                conditions.append(se != sx)
        if e_offset == 0:
            conditions.append(ee <= ey - p)
        elif e_offset == 1:
            conditions.append(ee <= ey - (p + one))
        elif e_offset == -1:
            conditions.append(ee <= ey - (p - one))
        elif e_offset == 2:
            conditions.append(ee <= ey - (p + two))
        elif e_offset == -2:
            conditions.append(ee <= ey - (p - two))
        else:
            assert False
        if overlap:
            conditions.append(ee >= fy)
            conditions.append(fe == fy)
        else:
            conditions.append(ee >= fx)
            conditions.append(fe == fx)
        return z3.And(*conditions)

    def y_case_zero(
        es_range: IntVar | tuple[IntVar, IntVar],
        fs_range: IntVar | tuple[IntVar, IntVar],
    ) -> z3.BoolRef:
        conditions: list[z3.BoolRef] = []
        conditions.append(ss == sy)
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

    ############################################################# LEMMA FAMILY Z

    result["TwoSum-Z1-PP"] = z3.Implies(
        z3.And(x_pos_zero, y_pos_zero),
        z3.And(s_pos_zero, e_pos_zero),
    )
    result["TwoSum-Z1-PN"] = z3.Implies(
        z3.And(x_pos_zero, y_neg_zero),
        z3.And(s_pos_zero, e_pos_zero),
    )
    result["TwoSum-Z1-NP"] = z3.Implies(
        z3.And(x_neg_zero, y_pos_zero),
        z3.And(s_pos_zero, e_pos_zero),
    )
    result["TwoSum-Z1-NN"] = z3.Implies(
        z3.And(x_neg_zero, y_neg_zero),
        z3.And(s_neg_zero, e_pos_zero),
    )

    result["TwoSum-Z2-X"] = z3.Implies(
        z3.And(z3.Not(x_zero), y_zero),
        z3.And(s_equals_x, e_pos_zero),
    )
    result["TwoSum-Z2-Y"] = z3.Implies(
        z3.And(x_zero, z3.Not(y_zero)),
        z3.And(s_equals_y, e_pos_zero),
    )

    ############################################################# LEMMA FAMILY I

    # fmt: off

    result["TwoSum-I-X"] = z3.Implies(z3.And(xy_nonzero, z3.Or(
                   ex >  ey + (p+one),
            z3.And(ex == ey + (p+one), z3.Or(ey == fy,       same_sign, ex > fx)),
            z3.And(ex == ey + p      ,       ey == fy, z3.Or(same_sign, ex > fx), ex < fx + (p-one)),
        )),
        z3.And(s_equals_x, e_equals_y),
    )
    result["TwoSum-I-Y"] = z3.Implies(z3.And(xy_nonzero, z3.Or(
                   ey >  ex + (p+one),
            z3.And(ey == ex + (p+one), z3.Or(ex == fx,       same_sign, ey > fy)),
            z3.And(ey == ex + p      ,       ex == fx, z3.Or(same_sign, ey > fy), ey < fy + (p-one)),
        )),
        z3.And(s_equals_y, e_equals_x),
    )

    # fmt: on

    ############################################################# LEMMA FAMILY F

    # # Lemma F1
    # if same_sign & (fx == fy) & (ex == ey) & (ex == fx)
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1), pos_zero)
    result["TwoSum-F1"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, fx == fy, ex == ey, ex == fx),
        x_case_zero(ex + one, ex + one),
    )

    # # Lemma F2
    # if same_sign & (fx == fy) & (ex == ey) & (ex > fx)
    #         push_range!(t, (sx, ex+1:ex+1, fx+1:ex), pos_zero)
    result["TwoSum-F2"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, fx == fy, ex == ey, ex > fx),
        x_case_zero(ex + one, (fx + one, ex)),
    )

    # fmt: off

    # # Lemma F3
    # if same_sign & (fx == fy) & (ex == ey + 1)
    #         push_range!(t, (sx, ex       , fx+1:ex-2), pos_zero)
    #         push_range!(t, (sx, ex+1:ex+1, fx+1:ey  ), pos_zero)
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1   ), pos_zero)
    # if same_sign & (fx == fy) & (ey == ex + 1)
    #         push_range!(t, (sy, ey       , fy+1:ey-2), pos_zero)
    #         push_range!(t, (sy, ey+1:ey+1, fy+1:ex  ), pos_zero)
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1   ), pos_zero)
    result["TwoSum-F3-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, fx == fy, ex == ey + one),
        z3.Or(
            x_case_zero(ex    , (fx+one, ex-two)),
            x_case_zero(ex+one, (fx+one, ey)    ),
            x_case_zero(ex+one, ex+one          ),
        ),
    )
    result["TwoSum-F3-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, fx == fy, ey == ex + one),
        z3.Or(
            y_case_zero(ey    , (fy+one, ey-two)),
            y_case_zero(ey+one, (fy+one, ex)    ),
            y_case_zero(ey+one, ey+one          ),
        ),
    )

    # # Lemma F4
    # if same_sign & (fx == fy) & (ex > ey + 1)
    #         push_range!(t, (sx, ex       , fx+1:ex-1), pos_zero)
    #         push_range!(t, (sx, ex+1:ex+1, fx+1:ey  ), pos_zero)
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1   ), pos_zero)
    # if same_sign & (fx == fy) & (ey > ex + 1)
    #         push_range!(t, (sy, ey       , fy+1:ey-1), pos_zero)
    #         push_range!(t, (sy, ey+1:ey+1, fy+1:ex  ), pos_zero)
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1   ), pos_zero)
    result["TwoSum-F4-X"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, fx == fy, ex > ey + one),
        z3.Or(
            x_case_zero(ex    , (fx+one, ex-one)),
            x_case_zero(ex+one, (fx+one, ey)    ),
            x_case_zero(ex+one, ex+one          ),
        ),
    )
    result["TwoSum-F4-Y"] = z3.Implies(
        z3.And(xy_nonzero, same_sign, fx == fy, ey > ex + one),
        z3.Or(
            y_case_zero(ey    , (fy+one, ey-one)),
            y_case_zero(ey+one, (fy+one, ex)    ),
            y_case_zero(ey+one, ey+one          ),
        ),
    )

    # # Lemma F5
    # if diff_sign & (fx == fy) & (ex == ey)
    #         push!(t, (pos_zero, pos_zero))
    #         for k = fx+1:ex-1
    #             push_range!(t, (±, k:k, fx+1:k), pos_zero)
    result["TwoSum-F5"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, fx == fy, ex == ey),
        z3.Or(
            z3.And(s_pos_zero, e_pos_zero),
            z3.And(es >= fx+one, es <= ex-one, fs >= fx+one, fs <= es, e_pos_zero)
        ),
    )

    # # Lemma F6
    # if diff_sign & (fx == fy) & (ex == ey + 1)
    #         for k = fx+1:ex-1
    #             push_range!(t, (sx, k:k, fx+1:k), pos_zero)
    #         push_range!(t, (sx, ex, fx+1:ex-2), pos_zero)
    #         push!(t, ((sx, ex, ex), pos_zero))
    # if diff_sign & (fx == fy) & (ey == ex + 1)
    #         for k = fy+1:ey-1
    #             push_range!(t, (sy, k:k, fy+1:k), pos_zero)
    #         push_range!(t, (sy, ey, fy+1:ey-2), pos_zero)
    #         push!(t, ((sy, ey, ey), pos_zero))
    result["TwoSum-F6-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, fx == fy, ex == ey + one),
        z3.Or(
            z3.And(ss == sx, es >= fx+one, es <= ex-one, fs >= fx+one, fs <= es    , e_pos_zero),
            z3.And(ss == sx, es == ex                  , fs >= fx+one, fs <= ex-two, e_pos_zero),
            z3.And(ss == sx, es == ex                  , fs == ex                  , e_pos_zero)
        ),
    )
    result["TwoSum-F6-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, fx == fy, ey == ex + one),
        z3.Or(
            z3.And(ss == sy, es >= fy+one, es <= ey-one, fs >= fy+one, fs <= es    , e_pos_zero),
            z3.And(ss == sy, es == ey                  , fs >= fy+one, fs <= ey-two, e_pos_zero),
            z3.And(ss == sy, es == ey                  , fs == ey                  , e_pos_zero)
        ),
    )

    # # Lemma F7
    # if diff_sign & (fx == fy) & (ex > ey + 1)
    #         push_range!(t, (sx, ex-1:ex-1, fx+1:ey), pos_zero)
    #         push_range!(t, (sx, ex       , fx+1:ex), pos_zero)
    # if diff_sign & (fx == fy) & (ey > ex + 1)
    #         push_range!(t, (sy, ey-1:ey-1, fy+1:ex), pos_zero)
    #         push_range!(t, (sy, ey       , fy+1:ey), pos_zero)
    result["TwoSum-F7-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, fx == fy, ex > ey + one),
        z3.Or(
            x_case_zero(ex-one, (fx+one, ey)),
            x_case_zero(ex    , (fx+one, ex)),
        )
    )
    result["TwoSum-F7-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, fx == fy, ey > ex + one),
        z3.Or(
            y_case_zero(ey-one, (fy+one, ex)),
            y_case_zero(ey    , (fy+one, ey)),
        )
    )

    # fmt: on

    ############################################################# LEMMA FAMILY E

    # # Lemma E1
    # if same_sign & (ex == ey) & (fx < fy) & (ex < fx + (p - 1)) & (ey < fy + (p - 1))
    #         push_range!(t, (sx, ex+1:ex+1, fx), pos_zero)
    # if same_sign & (ex == ey) & (fx > fy) & (ex < fx + (p - 1)) & (ey < fy + (p - 1))
    #         push_range!(t, (sx, ex+1:ex+1, fy), pos_zero)
    result["TwoSum-E1-X"] = z3.Implies(
        z3.And(same_sign, ex == ey, fx < fy, ex < fx + (p - one), ey < fy + (p - one)),
        x_case_zero(ex + one, fx),
    )
    result["TwoSum-E1-Y"] = z3.Implies(
        z3.And(same_sign, ex == ey, fx > fy, ex < fx + (p - one), ey < fy + (p - one)),
        y_case_zero(ey + one, fy),
    )

    # # Lemma E2.G
    # if diff_sign & (ex == ey) & (fx < fy) & (ex > fx + 1) & (ey > fy + 1)
    #         push_range!(t, (±, fx:ex-1, fx), pos_zero)
    # if diff_sign & (ex == ey) & (fx > fy) & (ex > fx + 1) & (ey > fy + 1)
    #         push_range!(t, (±, fy:ey-1, fy), pos_zero)
    result["TwoSum-E2-G-X"] = z3.Implies(
        z3.And(diff_sign, ex == ey, fx < fy, ex > fx + one, ey > fy + one),
        z3.And(es >= fx, es <= ex - one, fs == fx, e_pos_zero),
    )
    result["TwoSum-E2-G-Y"] = z3.Implies(
        z3.And(diff_sign, ex == ey, fx > fy, ex > fx + one, ey > fy + one),
        z3.And(es >= fy, es <= ey - one, fs == fy, e_pos_zero),
    )

    # # Lemma E2.1: Boundary case of E2 where two leading bits cancel.
    # if diff_sign & (ex == ey) & (ex > fx + 1) & (ey == fy + 1)
    #         push_range!(t, (±, fx:ex-2, fx), pos_zero)
    # if diff_sign & (ex == ey) & (ex == fx + 1) & (ey > fy + 1)
    #         push_range!(t, (±, fy:ey-2, fy), pos_zero)
    result["TwoSum-E2-1-X"] = z3.Implies(
        z3.And(diff_sign, ex == ey, ex > fx + one, ey == fy + one),
        z3.And(es >= fx, es <= ex - two, fs == fx, e_pos_zero),
    )
    result["TwoSum-E2-1-Y"] = z3.Implies(
        z3.And(diff_sign, ex == ey, ex == fx + one, ey > fy + one),
        z3.And(es >= fy, es <= ey - two, fs == fy, e_pos_zero),
    )

    # # Lemma E3.G
    # if (same_sign | (ex > fx)) & (fx > ey) & (ex < fy + p)
    #     @assert only(s) == ((sx, ex, fy), pos_zero)
    # if (same_sign | (ey > fy)) & (fy > ex) & (ey < fx + p)
    #     @assert only(s) == ((sy, ey, fx), pos_zero)
    result["TwoSum-E3-G-X"] = z3.Implies(
        z3.And(xy_nonzero, z3.Or(same_sign, (ex > fx)), fx > ey, ex < fy + p),
        x_case_zero(ex, fy),
    )
    result["TwoSum-E3-G-Y"] = z3.Implies(
        z3.And(xy_nonzero, z3.Or(same_sign, (ey > fy)), fy > ex, ey < fx + p),
        y_case_zero(ey, fx),
    )

    # # Lemma E3.1
    # if diff_sign & (
    #         ((ex == fx) & (fx > ey + 1) & (ex < fy + (p + 1))) |
    #         ((ex == fx + 1) & (fx == ey) & (ey > fy)))
    #         push_range!(t, (sx, ex-1:ex-1, fy), pos_zero)
    # if diff_sign & (
    #         ((ey == fy) & (fy > ex + 1) & (ey < fx + (p + 1))) |
    #         ((ey == fy + 1) & (fy == ex) & (ex > fx)))
    #         push_range!(t, (sy, ey-1:ey-1, fx), pos_zero)
    result["TwoSum-E3-1-X"] = z3.Implies(
        z3.And(
            xy_nonzero,
            diff_sign,
            z3.Or(
                z3.And(ex == fx, fx > ey + one, ex < fy + (p + one)),
                z3.And(ex == fx + one, fx == ey, ey > fy),
            ),
        ),
        x_case_zero(ex - one, fy),
    )
    result["TwoSum-E3-1-Y"] = z3.Implies(
        z3.And(
            xy_nonzero,
            diff_sign,
            z3.Or(
                z3.And(ey == fy, fy > ex + one, ey < fx + (p + one)),
                z3.And(ey == fy + one, fy == ex, ex > fx),
            ),
        ),
        y_case_zero(ey - one, fx),
    )

    # # Lemma E4.G
    # if same_sign & ((ex > ey > fx > fy) | (ex > ey + 1 > fx > fy)) & (ex < fy + (p - 1))
    #         push_range!(t, (sx, ex:ex+1, fy), pos_zero)
    # if same_sign & ((ey > ex > fy > fx) | (ey > ex + 1 > fy > fx)) & (ey < fx + (p - 1))
    #         push_range!(t, (sy, ey:ey+1, fx), pos_zero)
    result["TwoSum-E4-G-X"] = z3.Implies(
        z3.And(
            same_sign,
            z3.Or(
                z3.And(ex > ey, ey > fx, fx > fy, ex < fy + (p - one)),
                z3.And(ex > ey + one, ey + one > fx, fx > fy, ex < fy + (p - one)),
            ),
        ),
        x_case_zero((ex, ex + one), fy),
    )
    result["TwoSum-E4-G-Y"] = z3.Implies(
        z3.And(
            same_sign,
            z3.Or(
                z3.And(ey > ex, ex > fy, fy > fx, ey < fx + (p - one)),
                z3.And(ey > ex + one, ex + one > fy, fy > fx, ey < fx + (p - one)),
            ),
        ),
        y_case_zero((ey, ey + one), fx),
    )

    # # Lemma E4.1
    # if same_sign & (ex == ey + 1) & (ey == fx > fy) & (ex < fy + (p - 1))
    #         push_range!(t, (sx, ex+1:ex+1, fy), pos_zero)
    # if same_sign & (ey == ex + 1) & (ex == fy > fx) & (ey < fx + (p - 1))
    #         push_range!(t, (sy, ey+1:ey+1, fx), pos_zero)
    result["TwoSum-E4-1-X"] = z3.Implies(
        z3.And(
            same_sign,
            ex == ey + one,
            ey == fx,
            fx > fy,
            ex < fy + (p - one),
        ),
        x_case_zero(ex + one, fy),
    )
    result["TwoSum-E4-1-Y"] = z3.Implies(
        z3.And(
            same_sign,
            ey == ex + one,
            ex == fy,
            fy > fx,
            ey < fx + (p - one),
        ),
        y_case_zero(ey + one, fx),
    )

    # # Lemma E5.G
    # if diff_sign & (ex > ey + 1 > fx > fy) & (ex < fy + p)
    #         push_range!(t, (sx, ex-1:ex, fy), pos_zero)
    # if diff_sign & (ey > ex + 1 > fy > fx) & (ey < fx + p)
    #         push_range!(t, (sy, ey-1:ey, fx), pos_zero)
    result["TwoSum-E5-G-X"] = z3.Implies(
        z3.And(diff_sign, ex > ey + one, ey + one > fx, fx > fy, ex < fy + p),
        x_case_zero((ex - one, ex), fy),
    )
    result["TwoSum-E5-G-Y"] = z3.Implies(
        z3.And(diff_sign, ey > ex + one, ex + one > fy, fy > fx, ey < fx + p),
        y_case_zero((ey - one, ey), fx),
    )

    # # Lemma E5.1
    # if diff_sign & (ex == ey + 1) & (ey > fx > fy) & (ex < fy + p)
    #         push_range!(t, (sx, fx:ex, fy), pos_zero)
    # if diff_sign & (ey == ex + 1) & (ex > fy > fx) & (ey < fx + p)
    #         push_range!(t, (sy, fy:ey, fx), pos_zero)
    result["TwoSum-E5-1-X"] = z3.Implies(
        z3.And(diff_sign, ex == ey + one, ey > fx, fx > fy, ex < fy + p),
        x_case_zero((fx, ex), fy),
    )
    result["TwoSum-E5-1-Y"] = z3.Implies(
        z3.And(diff_sign, ey == ex + one, ex > fy, fy > fx, ey < fx + p),
        y_case_zero((fy, ey), fx),
    )

    # # Lemma E5.2
    # if diff_sign & (ex == ey + 1 == fx) & (fx > fy + 1)
    #         push_range!(t, (sx, fy:ex-2, fy), pos_zero)
    # if diff_sign & (ey == ex + 1 == fy) & (fy > fx + 1)
    #         push_range!(t, (sy, fx:ey-2, fx), pos_zero)
    result["TwoSum-E5-2-X"] = z3.Implies(
        z3.And(diff_sign, ex == ey + one, ex == fx, fx > fy + one),
        x_case_zero((fy, ex - two), fy),
    )
    result["TwoSum-E5-2-Y"] = z3.Implies(
        z3.And(diff_sign, ey == ex + one, ey == fy, fy > fx + one),
        y_case_zero((fx, ey - two), fx),
    )

    # # Lemma E5.3
    # if diff_sign & (ex == ey + 1 == fx == fy + 1)
    #         push_range!(t, (sx, fy:ex-1, fy), pos_zero)
    # if diff_sign & (ey == ex + 1 == fy == fx + 1)
    #         push_range!(t, (sy, fx:ey-1, fx), pos_zero)
    result["TwoSum-E5-3-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == ey + one, ex == fx, ey == fy),
        x_case_zero((fy, ex - one), fy),
    )
    result["TwoSum-E5-3-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == ex + one, ey == fy, ex == fx),
        y_case_zero((fx, ey - one), fx),
    )

    # # Lemma E6
    # if same_sign & (ex > ey) & (fx < fy) & (ex < fx + (p - 1))
    #         push_range!(t, (sx, ex:ex+1, fx), pos_zero)
    # if same_sign & (ey > ex) & (fy < fx) & (ey < fy + (p - 1))
    #         push_range!(t, (sy, ey:ey+1, fy), pos_zero)
    result["TwoSum-E6-X"] = z3.Implies(
        z3.And(same_sign, ex > ey, fx < fy, ex < fx + (p - one)),
        x_case_zero((ex, ex + one), fx),
    )
    result["TwoSum-E6-Y"] = z3.Implies(
        z3.And(same_sign, ey > ex, fy < fx, ey < fy + (p - one)),
        y_case_zero((ey, ey + one), fy),
    )

    # # Lemma E7.G
    # if diff_sign & (ex > ey + 1) & (fx < fy)
    #         push_range!(t, (sx, ex-1:ex, fx), pos_zero)
    # if diff_sign & (ey > ex + 1) & (fy < fx)
    #         push_range!(t, (sy, ey-1:ey, fy), pos_zero)
    result["TwoSum-E7-G-X"] = z3.Implies(
        z3.And(diff_sign, ex > ey + one, fx < fy),
        x_case_zero((ex - one, ex), fx),
    )
    result["TwoSum-E7-G-Y"] = z3.Implies(
        z3.And(diff_sign, ey > ex + one, fy < fx),
        y_case_zero((ey - one, ey), fy),
    )

    # # Lemma E7.1
    # if diff_sign & (ex == ey + 1) & (fx < fy)
    #         push_range!(t, (sx, fy:ex, fx), pos_zero)
    # if diff_sign & (ey == ex + 1) & (fy < fx)
    #         push_range!(t, (sy, fx:ey, fy), pos_zero)
    result["TwoSum-E7-1-X"] = z3.Implies(
        z3.And(diff_sign, ex == ey + one, fx < fy),
        x_case_zero((fy, ex), fx),
    )
    result["TwoSum-E7-1-Y"] = z3.Implies(
        z3.And(diff_sign, ey == ex + one, fy < fx),
        y_case_zero((fx, ey), fy),
    )

    # # Lemma E7.2
    # if diff_sign & (ex == ey == fy) & (fx < fy)
    #         push_range!(t, (sx, fx:ex-1, fx), pos_zero)
    # if diff_sign & (ey == ex == fx) & (fy < fx)
    #         push_range!(t, (sy, fy:ey-1, fy), pos_zero)
    result["TwoSum-E7-2-X"] = z3.Implies(
        z3.And(diff_sign, ex == ey, ey == fy, fx < fy),
        x_case_zero((fx, ex - one), fx),
    )
    result["TwoSum-E7-2-Y"] = z3.Implies(
        z3.And(diff_sign, ey == ex, ex == fx, fy < fx),
        y_case_zero((fy, ey - one), fy),
    )

    ############################################################# LEMMA FAMILY O

    # fmt: off

    # # Lemma O1
    # if same_sign & (ex == fx + (p - 1)) & (ex > ey > fy > fx)
    #         push_range!(t, (sx, ex       , fx), pos_zero)
    #         push_range!(t, (sx, ex+1:ex+1, ex-(p-3):ey  ), (±  , fx:ex-(p-1), fx))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fx:ex-(p-1), fx))
    # if same_sign & (ey == fy + (p - 1)) & (ey > ex > fx > fy)
    #         push_range!(t, (sy, ey       , fy), pos_zero)
    #         push_range!(t, (sy, ey+1:ey+1, ey-(p-3):ex  ), (±  , fy:ey-(p-1), fy))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fy:ey-(p-1), fy))
    result["TwoSum-O1-X"] = z3.Implies(
        z3.And(same_sign, ex == fx + (p - one), ex > ey, ey > fy, fy > fx),
        z3.Or(
            x_case_zero(ex, fx),
            x_case(ex+one, (ex-(p-three), ey), None, -1, overlap=True),
            x_case(ex+one, ex+one            , True, -1, overlap=True),
        ),
    )
    result["TwoSum-O1-Y"] = z3.Implies(
        z3.And(same_sign, ey == fy + (p - one), ey > ex, ex > fx, fx > fy),
        z3.Or(
            y_case_zero(ey, fy),
            y_case(ey+one, (ey-(p-three), ex), None, -1, overlap=True),
            y_case(ey+one, ey+one            , True, -1, overlap=True),
        ),
    )

    # # Lemma O2
    # if same_sign & (ex == fx + (p - 1)) & (ex > ey == fy > fx + 1)
    #         push_range!(t, (sx, ex       , fx), pos_zero)
    #         push_range!(t, (sx, ex+1:ex+1, ex-(p-3):ey-1), (±  , fx:ex-(p-1), fx))
    #         push_range!(t, (sx, ex+1:ex+1, ey           ), (!sy, fx:ex-(p-1), fx))
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fx:ex-(p-1), fx))
    # if same_sign & (ey == fy + (p - 1)) & (ey > ex == fx > fy + 1)
    #         push_range!(t, (sy, ey       , fy), pos_zero)
    #         push_range!(t, (sy, ey+1:ey+1, ey-(p-3):ex-1), (±  , fy:ey-(p-1), fy))
    #         push_range!(t, (sy, ey+1:ey+1, ex           ), (!sx, fy:ey-(p-1), fy))
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fy:ey-(p-1), fy))
    result["TwoSum-O2-X"] = z3.Implies(
        z3.And(same_sign, ex == fx + (p - one), ex > ey, ey == fy, fy > fx + one),
        z3.Or(
            x_case_zero(ex, fx),
            x_case(ex+one, (ex-(p-three), ey-one), None , -1, overlap=True),
            x_case(ex+one, ey                    , False, -1, overlap=True),
            x_case(ex+one, ex+one                , True , -1, overlap=True),
        ),
    )
    result["TwoSum-O2-Y"] = z3.Implies(
        z3.And(same_sign, ey == fy + (p - one), ey > ex, ex == fx, fx > fy + one),
        z3.Or(
            y_case_zero(ey, fy),
            y_case(ey+one, (ey-(p-three), ex-one), None , -1, overlap=True),
            y_case(ey+one, ex                    , False, -1, overlap=True),
            y_case(ey+one, ey+one                , True , -1, overlap=True),
        ),
    )

    # # Lemma O3
    # if same_sign & (ex == fx + (p - 1)) & (ey == fy == fx + 1)
    #         push_range!(t, (sx, ex       , fx), pos_zero)
    #         push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fx:ex-(p-1), fx))
    # if same_sign & (ey == fy + (p - 1)) & (ex == fx == fy + 1)
    #         push_range!(t, (sy, ey       , fy), pos_zero)
    #         push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fy:ey-(p-1), fy))
    result["TwoSum-O3-X"] = z3.Implies(
        z3.And(same_sign, ex == fx + (p - one), ey == fy, fy == fx + one),
        z3.Or(
            x_case_zero(ex, fx),
            x_case(ex+one, ex+one, True, -1, overlap=True),
        ),
    )
    result["TwoSum-O3-Y"] = z3.Implies(
        z3.And(same_sign, ey == fy + (p - one), ex == fx, fx == fy + one),
        z3.Or(
            y_case_zero(ey, fy),
            y_case(ey+one, ey+one, True, -1, overlap=True),
        ),
    )

    ############################################################# LEMMA FAMILY 1

    # # Lemma 1
    # if (ex < ey + p) & (ex > fy + p) & (fx > ey + 1) & ((ex > fx) | same_sign)
    #         push_range!(t, (sx, ex, ex-(p-1):ey-1), (±  , fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex, ey           ), (sy , fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex, ey + 1       ), (!sy, fy:ex-(p+1), fy))
    # if (ey < ex + p) & (ey > fx + p) & (fy > ex + 1) & ((ey > fy) | same_sign)
    #         push_range!(t, (sy, ey, ey-(p-1):ex-1), (±  , fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey, ex           ), (sx , fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey, ex + 1       ), (!sx, fx:ey-(p+1), fx))
    result["TwoSum-1-X"] = z3.Implies(
        z3.And(ex < ey + p, ex > fy + p, fx > ey + one, z3.Or(ex > fx, same_sign)),
        z3.Or(
            x_case(ex, (ex-(p-one), ey-one), None , 1),
            x_case(ex, ey                  , True , 1),
            x_case(ex, ey+one              , False, 1),
        ),
    )
    result["TwoSum-1-Y"] = z3.Implies(
        z3.And(ey < ex + p, ey > fx + p, fy > ex + one, z3.Or(ey > fy, same_sign)),
        z3.Or(
            y_case(ey, (ey-(p-one), ex-one), None , 1),
            y_case(ey, ex                  , True , 1),
            y_case(ey, ex+one              , False, 1),
        ),
    )

    # # Lemma 1A
    # if (ex == ey + p) & (ex > fy + p) & (fx > ey + 1) & ((ex > fx) | same_sign)
    #         push_range!(t, (sx, ex, ey + 1       ), (!sy, fy:ex-(p+1), fy))
    # if (ey == ex + p) & (ey > fx + p) & (fy > ex + 1) & ((ey > fy) | same_sign)
    #         push_range!(t, (sy, ey, ex + 1       ), (!sx, fx:ey-(p+1), fx))
    result["TwoSum-1A-X"] = z3.Implies(
        z3.And(ex == ey + p, ex > fy + p, fx > ey + one, z3.Or(ex > fx, same_sign)),
        x_case(ex, ey+one, False, 1),
    )
    result["TwoSum-1A-Y"] = z3.Implies(
        z3.And(ey == ex + p, ey > fx + p, fy > ex + one, z3.Or(ey > fy, same_sign)),
        y_case(ey, ex+one, False, 1),
    )

    # # Lemma 1B.G
    # if (ex < ey + (p - 1)) & (ex == fy + p) & (fx > ey + 1) & ((ex > fx) | same_sign)
    #         push_range!(t, (sx, ex, ex-(p-2):ey-1), (±  , fy:ex-p, fy))
    #         push_range!(t, (sx, ex, ey           ), (sy , fy:ex-p, fy))
    #         push_range!(t, (sx, ex, ey + 1       ), (!sy, fy:ex-p, fy))
    # if (ey < ex + (p - 1)) & (ey == fx + p) & (fy > ex + 1) & ((ey > fy) | same_sign)
    #         push_range!(t, (sy, ey, ey-(p-2):ex-1), (±  , fx:ey-p, fx))
    #         push_range!(t, (sy, ey, ex           ), (sx , fx:ey-p, fx))
    #         push_range!(t, (sy, ey, ex + 1       ), (!sx, fx:ey-p, fx))
    result["TwoSum-1B-G-X"] = z3.Implies(
        z3.And(ex < ey + (p - one), ex == fy + p, fx > ey + one, z3.Or(ex > fx, same_sign)),
        z3.Or(
            x_case(ex, (ex-(p-two), ey-one), None , 0),
            x_case(ex, ey                  , True , 0),
            x_case(ex, ey+one              , False, 0),
        ),
    )
    result["TwoSum-1B-G-Y"] = z3.Implies(
        z3.And(ey < ex + (p - one), ey == fx + p, fy > ex + one, z3.Or(ey > fy, same_sign)),
        z3.Or(
            y_case(ey, (ey-(p-two), ex-one), None , 0),
            y_case(ey, ex                  , True , 0),
            y_case(ey, ex+one              , False, 0),
        ),
    )

    # # Lemma 1B.1
    # if (ex == ey + (p - 1)) & (ex == fy + p) & (fx > ey + 1) & ((ex > fx) | same_sign)
    #         push_range!(t, (sx, ex, ey + 1       ), (!sy, fy:ex-p, fy))
    # if (ey == ex + (p - 1)) & (ey == fx + p) & (fy > ex + 1) & ((ey > fy) | same_sign)
    #         push_range!(t, (sy, ey, ex + 1       ), (!sx, fx:ey-p, fx))
    result["TwoSum-1B-1-X"] = z3.Implies(
        z3.And(ex == ey + (p - one), ex == fy + p, fx > ey + one, z3.Or(ex > fx, same_sign)),
        x_case(ex, ey+one, False, 0),
    )
    result["TwoSum-1B-1-Y"] = z3.Implies(
        z3.And(ey == ex + (p - one), ey == fx + p, fy > ex + one, z3.Or(ey > fy, same_sign)),
        y_case(ey, ex+one, False, 0),
    )

    ############################################################# LEMMA FAMILY 2

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
            x_case_zero(ex, fy),
            x_case(ex+one, (ex-(p-three), ey), None, -1),
            x_case(ex+one, ex+one            , True, -1),
        ),
    )
    result["TwoSum-2C-G-Y"] = z3.Implies(
        z3.And(same_sign, ey == fx + (p - one), fy < ex, ey < fy + (p - one), ex < fx + (p - one)),
        z3.Or(
            y_case_zero(ey, fx),
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
            x_case_zero(ex, fy),
            x_case(ex+one, (ex-(p-three), ey-one), None , -1),
            x_case(ex+one, ey                    , False, -1),
            x_case(ex+one, ex+one                , True , -1),
        ),
    )
    result["TwoSum-2BC-G-Y"] = z3.Implies(
        z3.And(same_sign, ey == fx + (p - one), fy == ex, ex > fx + one, ex < fx + (p - two)),
        z3.Or(
            y_case_zero(ey, fx),
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
            x_case_zero(ex, fy),
            x_case(ex+one, ex+one, True, -1),
        ),
    )
    result["TwoSum-2BC-2-Y"] = z3.Implies(
        z3.And(same_sign, ey == fx + (p - one), fy == ex, ex == fx + one),
        z3.Or(
            y_case_zero(ey, fx),
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

    ############################################################# LEMMA FAMILY 3

    # # Lemma 3
    # if diff_sign & (ex > fy + (p + 1)) & (fx < ey)
    #         push_range!(t, (sx, ex-1:ex-1, ex-p:ey      ), (±  , fy:ex-(p+2), fy))
    #         push_range!(t, (sx, ex       , ex-(p-1):ex-1), (±  , fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex       , ex           ), (sy , fy:ex-(p+2), fy))
    #         push_range!(t, (sx, ex       , ex           ), (!sy, fy:ex-(p+1), fy))
    # if diff_sign & (ey > fx + (p + 1)) & (fy < ex)
    #         push_range!(t, (sy, ey-1:ey-1, ey-p:ex      ), (±  , fx:ey-(p+2), fx))
    #         push_range!(t, (sy, ey       , ey-(p-1):ey-1), (±  , fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey       , ey           ), (sx , fx:ey-(p+2), fx))
    #         push_range!(t, (sy, ey       , ey           ), (!sx, fx:ey-(p+1), fx))
    result["TwoSum-3-X"] = z3.Implies(
        z3.And(diff_sign, ex > fy + (p + one), fx < ey),
        z3.Or(
            x_case(ex - one, (ex - p, ey), None, 2),
            x_case(ex, (ex - (p - one), ex - one), None, 1),
            x_case(ex, ex, True, 2),
            x_case(ex, ex, False, 1),
        ),
    )
    result["TwoSum-3-Y"] = z3.Implies(
        z3.And(diff_sign, ey > fx + (p + one), fy < ex),
        z3.Or(
            y_case(ey - one, (ey - p, ex), None, 2),
            y_case(ey, (ey - (p - one), ey - one), None, 1),
            y_case(ey, ey, True, 2),
            y_case(ey, ey, False, 1),
        ),
    )

    # # Lemma 3A
    # if diff_sign & (ex == fy + (p + 1)) & (fx < ey)
    #         push_range!(t, (sx, ex-1:ex-1, ex-(p-1):ey), (±, fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex       , ex-(p-1):ex), (±, fy:ex-(p+1), fy))
    # if diff_sign & (ey == fx + (p + 1)) & (fy < ex)
    #         push_range!(t, (sy, ey-1:ey-1, ey-(p-1):ex), (±, fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey       , ey-(p-1):ey), (±, fx:ey-(p+1), fx))
    result["TwoSum-3A-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + (p + one), fx < ey),
        z3.Or(
            x_case(ex - one, (ex - (p - one), ey), None, 1),
            x_case(ex, (ex - (p - one), ex), None, 1),
        ),
    )
    result["TwoSum-3A-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + (p + one), fy < ex),
        z3.Or(
            y_case(ey - one, (ey - (p - one), ex), None, 1),
            y_case(ey, (ey - (p - one), ey), None, 1),
        ),
    )

    # # Lemma 3B
    # if diff_sign & (ex > fy + (p + 1)) & (fx == ey)
    #         push_range!(t, (sx, ex-1:ex-1, ex-p:ey-1    ), (±  , fy:ex-(p+2), fy))
    #         push_range!(t, (sx, ex-1:ex-1, ey           ), (!sy, fy:ex-(p+2), fy))
    #         push_range!(t, (sx, ex       , ex-(p-1):ey-1), (±  , fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex       , ey           ), (!sy, fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex       , ey+1:ex-1    ), (sy , fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex       , ex           ), (sy , fy:ex-(p+2), fy))
    # if diff_sign & (ey > fx + (p + 1)) & (fy == ex)
    #         push_range!(t, (sy, ey-1:ey-1, ey-p:ex-1    ), (±  , fx:ey-(p+2), fx))
    #         push_range!(t, (sy, ey-1:ey-1, ex           ), (!sx, fx:ey-(p+2), fx))
    #         push_range!(t, (sy, ey       , ey-(p-1):ex-1), (±  , fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey       , ex           ), (!sx, fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey       , ex+1:ey-1    ), (sx , fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey       , ey           ), (sx , fx:ey-(p+2), fx))
    result["TwoSum-3B-X"] = z3.Implies(
        z3.And(diff_sign, ex > fy + (p + one), fx == ey),
        z3.Or(
            x_case(ex - one, (ex - p, ey - one), None, 2),
            x_case(ex - one, ey, False, 2),
            x_case(ex, (ex - (p - one), ey - one), None, 1),
            x_case(ex, ey, False, 1),
            x_case(ex, (ey + one, ex - one), True, 1),
            x_case(ex, ex, True, 2),
        ),
    )
    result["TwoSum-3B-Y"] = z3.Implies(
        z3.And(diff_sign, ey > fx + (p + one), fy == ex),
        z3.Or(
            y_case(ey - one, (ey - p, ex - one), None, 2),
            y_case(ey - one, ex, False, 2),
            y_case(ey, (ey - (p - one), ex - one), None, 1),
            y_case(ey, ex, False, 1),
            y_case(ey, (ex + one, ey - one), True, 1),
            y_case(ey, ey, True, 2),
        ),
    )

    # # Lemma 3C.G
    # if diff_sign & (ex == fy + p) & (fx < ey) & (ey < fy + (p - 1))
    #         push_range!(t, (sx, ex-1:ex-1, fy), pos_zero)
    #         push_range!(t, (sx, ex       , ex-(p-2):ex-1), (±  , fy:ex-p, fy))
    #         push_range!(t, (sx, ex       , ex           ), (!sy, fy:ex-p, fy))
    # if diff_sign & (ey == fx + p) & (fy < ex) & (ex < fx + (p - 1))
    #         push_range!(t, (sy, ey-1:ey-1, fx), pos_zero)
    #         push_range!(t, (sy, ey       , ey-(p-2):ey-1), (±  , fx:ey-p, fx))
    #         push_range!(t, (sy, ey       , ey           ), (!sx, fx:ey-p, fx))
    result["TwoSum-3C-G-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + p, fx < ey, ey < fy + (p - one)),
        z3.Or(
            x_case_zero(ex - one, fy),
            x_case(ex, (ex - (p - two), ex - one), None, 0),
            x_case(ex, ex, False, 0),
        ),
    )
    result["TwoSum-3C-G-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + p, fy < ex, ex < fx + (p - one)),
        z3.Or(
            y_case_zero(ey - one, fx),
            y_case(ey, (ey - (p - two), ey - one), None, 0),
            y_case(ey, ey, False, 0),
        ),
    )

    # # Lemma 3C.1
    # if diff_sign & (ex == fy + p) & (fx + 1 < ey) & (ey == fy + (p - 1))
    #         push_range!(t, (sx, fx:ex-1, fy), pos_zero)
    #         push_range!(t, (sx, ex     , ex-(p-2):ex-2), (±  , fy:ex-p, fy))
    #         push_range!(t, (sx, ex     , ex           ), (!sy, fy:ex-p, fy))
    # if diff_sign & (ey == fx + p) & (fy + 1 < ex) & (ex == fx + (p - 1))
    #         push_range!(t, (sy, fy:ey-1, fx), pos_zero)
    #         push_range!(t, (sy, ey     , ey-(p-2):ey-2), (±  , fx:ey-p, fx))
    #         push_range!(t, (sy, ey     , ey           ), (!sx, fx:ey-p, fx))
    result["TwoSum-3C-1-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + p, fx + one < ey, ey == fy + (p - one)),
        z3.Or(
            x_case_zero((fx, ex - one), fy),
            x_case(ex, (ex - (p - two), ex - two), None, 0),
            x_case(ex, ex, False, 0),
        ),
    )
    result["TwoSum-3C-1-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + p, fy + one < ex, ex == fx + (p - one)),
        z3.Or(
            y_case_zero((fy, ey - one), fx),
            y_case(ey, (ey - (p - two), ey - two), None, 0),
            y_case(ey, ey, False, 0),
        ),
    )

    # # Lemma 3C.2
    # if diff_sign & (ex == fy + p) & (fx + 1 == ey) & (ey == fy + (p - 1))
    #         push_range!(t, (sx, ex-2:ex-1, fy), pos_zero)
    #         push_range!(t, (sx, ex       , ex-(p-2):ey-2), (±  , fy:ex-p, fy))
    #         push_range!(t, (sx, ex       , ey - 1       ), (sy , fy:ex-p, fy))
    #         push_range!(t, (sx, ex       , ex           ), (!sy, fy:ex-p, fy))
    # if diff_sign & (ey == fx + p) & (fy + 1 == ex) & (ex == fx + (p - 1))
    #         push_range!(t, (sy, ey-2:ey-1, fx), pos_zero)
    #         push_range!(t, (sy, ey       , ey-(p-2):ex-2), (±  , fx:ey-p, fx))
    #         push_range!(t, (sy, ey       , ex - 1       ), (sx , fx:ey-p, fx))
    #         push_range!(t, (sy, ey       , ey           ), (!sx, fx:ey-p, fx))
    result["TwoSum-3C-2-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + p, fx + one == ey, ey == fy + (p - one)),
        z3.Or(
            x_case_zero((ex - two, ex - one), fy),
            x_case(ex, (ex - (p - two), ey - two), None, 0),
            x_case(ex, ey - one, True, 0),
            x_case(ex, ex, False, 0),
        ),
    )
    result["TwoSum-3C-2-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + p, fy + one == ex, ex == fx + (p - one)),
        z3.Or(
            y_case_zero((ey - two, ey - one), fx),
            y_case(ey, (ey - (p - two), ex - two), None, 0),
            y_case(ey, ex - one, True, 0),
            y_case(ey, ey, False, 0),
        ),
    )

    # # Lemma 3D.G
    # if diff_sign & (ex > fy + p) & (fx == ey + 1) & (ex < fx + (p - 1))
    #         push_range!(t, (sx, ex, ex-(p-1):ey-1), (±  , fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex, ey           ), (sy , fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex, ey+2:ex      ), (!sy, fy:ex-(p+1), fy))
    # if diff_sign & (ey > fx + p) & (fy == ex + 1) & (ey < fy + (p - 1))
    #         push_range!(t, (sy, ey, ey-(p-1):ex-1), (±  , fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey, ex           ), (sx , fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey, ex+2:ey      ), (!sx, fx:ey-(p+1), fx))
    result["TwoSum-3D-G-X"] = z3.Implies(
        z3.And(diff_sign, ex > fy + p, fx == ey + one, ex < fx + (p - one)),
        z3.Or(
            x_case(ex, (ex - (p - one), ey - one), None, 1),
            x_case(ex, ey, True, 1),
            x_case(ex, (ey + two, ex), False, 1),
        ),
    )
    result["TwoSum-3D-G-Y"] = z3.Implies(
        z3.And(diff_sign, ey > fx + p, fy == ex + one, ey < fy + (p - one)),
        z3.Or(
            y_case(ey, (ey - (p - one), ex - one), None, 1),
            y_case(ey, ex, True, 1),
            y_case(ey, (ex + two, ey), False, 1),
        ),
    )

    # # Lemma 3D.1
    # if diff_sign & (ex > fy + p) & (fx == ey + 1) & (ex == fx + (p - 1))
    #         push_range!(t, (sx, ex, ey+2:ex      ), (!sy, fy:ex-(p+1), fy))
    # if diff_sign & (ey > fx + p) & (fy == ex + 1) & (ey == fy + (p - 1))
    #         push_range!(t, (sy, ey, ex+2:ey      ), (!sx, fx:ey-(p+1), fx))
    result["TwoSum-3D-1-X"] = z3.Implies(
        z3.And(diff_sign, ex > fy + p, fx == ey + one, ex == fx + (p - one)),
        x_case(ex, (ey + two, ex), False, 1),
    )
    result["TwoSum-3D-1-Y"] = z3.Implies(
        z3.And(diff_sign, ey > fx + p, fy == ex + one, ey == fy + (p - one)),
        y_case(ey, (ex + two, ey), False, 1),
    )

    # # Lemma 3AB
    # if diff_sign & (ex == fy + (p + 1)) & (fx == ey)
    #         push_range!(t, (sx, ex-1:ex-1, ex-(p-1):ey-1), (±  , fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex-1:ex-1, ey           ), (!sy, fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex       , ex-(p-1):ey-1), (±  , fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex       , ey           ), (!sy, fy:ex-(p+1), fy))
    #         push_range!(t, (sx, ex       , ey+1:ex      ), (sy , fy:ex-(p+1), fy))
    # if diff_sign & (ey == fx + (p + 1)) & (fy == ex)
    #         push_range!(t, (sy, ey-1:ey-1, ey-(p-1):ex-1), (±  , fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey-1:ey-1, ex           ), (!sx, fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey       , ey-(p-1):ex-1), (±  , fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey       , ex           ), (!sx, fx:ey-(p+1), fx))
    #         push_range!(t, (sy, ey       , ex+1:ey      ), (sx , fx:ey-(p+1), fx))
    result["TwoSum-3AB-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + (p + one), fx == ey),
        z3.Or(
            x_case(ex - one, (ex - (p - one), ey - one), None, 1),
            x_case(ex - one, ey, False, 1),
            x_case(ex, (ex - (p - one), ey - one), None, 1),
            x_case(ex, ey, False, 1),
            x_case(ex, (ey + one, ex), True, 1),
        ),
    )
    result["TwoSum-3AB-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + (p + one), fy == ex),
        z3.Or(
            y_case(ey - one, (ey - (p - one), ex - one), None, 1),
            y_case(ey - one, ex, False, 1),
            y_case(ey, (ey - (p - one), ex - one), None, 1),
            y_case(ey, ex, False, 1),
            y_case(ey, (ex + one, ey), True, 1),
        ),
    )

    # # Lemma 3BC.G
    # if diff_sign & (ex == fy + p) & (fx == ey) & (ex > fx + 1) & (ey > fy + 1)
    #         push_range!(t, (sx, ex-1:ex-1, fy), pos_zero)
    #         push_range!(t, (sx, ex       , ex-(p-2):ey-1), (±  , fy:ex-p, fy))
    #         push_range!(t, (sx, ex       , ey           ), (!sy, fy:ex-p, fy))
    #         push_range!(t, (sx, ex       , ey+1:ex-1    ), (sy , fy:ex-p, fy))
    # if diff_sign & (ey == fx + p) & (fy == ex) & (ey > fy + 1) & (ex > fx + 1)
    #         push_range!(t, (sy, ey-1:ey-1, fx), pos_zero)
    #         push_range!(t, (sy, ey       , ey-(p-2):ex-1), (±  , fx:ey-p, fx))
    #         push_range!(t, (sy, ey       , ex           ), (!sx, fx:ey-p, fx))
    #         push_range!(t, (sy, ey       , ex+1:ey-1    ), (sx , fx:ey-p, fx))
    result["TwoSum-3BC-G-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + p, fx == ey, ex > fx + one, ey > fy + one),
        z3.Or(
            x_case_zero(ex - one, fy),
            x_case(ex, (ex - (p - two), ey - one), None, 0),
            x_case(ex, ey, False, 0),
            x_case(ex, (ey + one, ex - one), True, 0),
        ),
    )
    result["TwoSum-3BC-G-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + p, fy == ex, ey > fy + one, ex > fx + one),
        z3.Or(
            y_case_zero(ey - one, fx),
            y_case(ey, (ey - (p - two), ex - one), None, 0),
            y_case(ey, ex, False, 0),
            y_case(ey, (ex + one, ey - one), True, 0),
        ),
    )

    # # Lemma 3BC.1
    # if diff_sign & (ex == fy + p) & (fx == ey) & (ey == fy + 1)
    #         push_range!(t, (sx, ex-1:ex-1, fy), pos_zero)
    #         push_range!(t, (sx, ex       , ey+1:ex-1    ), (sy , fy:ex-p, fy))
    # if diff_sign & (ey == fx + p) & (fy == ex) & (ex == fx + 1)
    #         push_range!(t, (sy, ey-1:ey-1, fx), pos_zero)
    #         push_range!(t, (sy, ey       , ex+1:ey-1    ), (sx , fx:ey-p, fx))
    result["TwoSum-3BC-1-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + p, fx == ey, ey == fy + one),
        z3.Or(
            x_case_zero(ex - one, fy),
            x_case(ex, (ey + one, ex - one), True, 0),
        ),
    )
    result["TwoSum-3BC-1-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + p, fy == ex, ex == fx + one),
        z3.Or(
            y_case_zero(ey - one, fx),
            y_case(ey, (ex + one, ey - one), True, 0),
        ),
    )

    # # Lemma 3CD.G
    # if diff_sign & (ex == fy + p) & (fx == ey + 1) & (ex > fx) & (ey > fy + 1)
    #         push_range!(t, (sx, ex, ex-(p-2):ey-1), (±  , fy:ex-p, fy))
    #         push_range!(t, (sx, ex, ey           ), (sy , fy:ex-p, fy))
    #         push_range!(t, (sx, ex, ey+2:ex      ), (!sy, fy:ex-p, fy))
    # if diff_sign & (ey == fx + p) & (fy == ex + 1) & (ey > fy) & (ex > fx + 1)
    #         push_range!(t, (sy, ey, ey-(p-2):ex-1), (±  , fx:ey-p, fx))
    #         push_range!(t, (sy, ey, ex           ), (sx , fx:ey-p, fx))
    #         push_range!(t, (sy, ey, ex+2:ey      ), (!sx, fx:ey-p, fx))
    result["TwoSum-3CD-G-X"] = z3.Implies(
        z3.And(diff_sign, ex == fy + p, fx == ey + one, ex > fx, ey > fy + one),
        z3.Or(
            x_case(ex, (ex - (p - two), ey - one), None, 0),
            x_case(ex, ey, True, 0),
            x_case(ex, (ey + two, ex), False, 0),
        ),
    )
    result["TwoSum-3CD-G-Y"] = z3.Implies(
        z3.And(diff_sign, ey == fx + p, fy == ex + one, ey > fy, ex > fx + one),
        z3.Or(
            y_case(ey, (ey - (p - two), ex - one), None, 0),
            y_case(ey, ex, True, 0),
            y_case(ey, (ex + two, ey), False, 0),
        ),
    )

    # # Lemma 3CD.1
    # if diff_sign & (ex == fy + p) & (fx == ey + 1) & (ey < fy + 2)
    #         push_range!(t, (sx, ex, ey+2:ex      ), (!sy, fy:ex-p, fy))
    # if diff_sign & (ey == fx + p) & (fy == ex + 1) & (ex < fx + 2)
    #         push_range!(t, (sy, ey, ex+2:ey      ), (!sx, fx:ey-p, fx))
    result["TwoSum-3CD-1-X"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ex == fy + p, fx == ey + one, ey < fy + two),
        x_case(ex, (ey + two, ex), False, 0),
    )
    result["TwoSum-3CD-1-Y"] = z3.Implies(
        z3.And(xy_nonzero, diff_sign, ey == fx + p, fy == ex + one, ex < fx + two),
        y_case(ey, (ex + two, ey), False, 0),
    )

    ############################################################# LEMMA FAMILY 4

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

    result["TwoSum-AXS"] = z3.Implies(z3.And(sx == sy, lzx, ex > ey + one), es == ex)
    result["TwoSum-AYS"] = z3.Implies(z3.And(sx == sy, lzy, ex + one < ey), es == ey)
    result["TwoSum-AXD"] = z3.Implies(z3.And(sx != sy, lbx, ex > ey + one), es == ex)
    result["TwoSum-AYD"] = z3.Implies(z3.And(sx != sy, lby, ex + one < ey), es == ey)

    result["TwoSum-CXD"] = z3.Implies(
        z3.And(sx != sy, ex > ey + two, es == ex - one),
        z3.And(lbs, nlbs >= ex - ey - two),
    )
    result["TwoSum-CYD"] = z3.Implies(
        z3.And(sx != sy, ex + two < ey, es == ey - one),
        z3.And(lbs, nlbs >= ey - ex - two),
    )

    ############################################################################

    return result
