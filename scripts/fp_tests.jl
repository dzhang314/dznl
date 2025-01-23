#!/usr/bin/env julia

using Base.Threads
using BFloat16s
using JLD2
using ProgressMeter


const ShortFloatSummary = Tuple{Bool,Int8}
const ShortPairSummary = Tuple{ShortFloatSummary,ShortFloatSummary}
const ShortTwoSumSummary = Tuple{ShortPairSummary,ShortPairSummary}
const MediumFloatSummary = Tuple{Bool,Int8,Int16}
const MediumPairSummary = Tuple{MediumFloatSummary,MediumFloatSummary}
const MediumTwoSumSummary = Tuple{MediumPairSummary,MediumPairSummary}
const LongFloatSummary = Tuple{Bool,Bool,Bool,Int8,Int8,Int8}
const LongPairSummary = Tuple{LongFloatSummary,LongFloatSummary}
const LongTwoSumSummary = Tuple{LongPairSummary,LongPairSummary}


@inline function short_summary(x::T, ::Type{U}) where {T,U}
    BIT_SIZE = 8 * sizeof(T)
    MANTISSA_WIDTH = precision(T) - 1
    SIGN_EXPONENT_WIDTH = BIT_SIZE - MANTISSA_WIDTH
    EXPONENT_WIDTH = SIGN_EXPONENT_WIDTH - 1
    ONE_U = one(U)
    EXPONENT_MASK = ((ONE_U << EXPONENT_WIDTH) - ONE_U) << MANTISSA_WIDTH
    EXPONENT_BIAS = (1 << (EXPONENT_WIDTH - 1)) - 1
    k = reinterpret(U, x)
    return (signbit(x),
        Int8(Int((k & EXPONENT_MASK) >> MANTISSA_WIDTH) - EXPONENT_BIAS))
end


@inline function medium_summary(x::T, ::Type{U}) where {T,U}
    BIT_SIZE = 8 * sizeof(T)
    MANTISSA_WIDTH = precision(T) - 1
    SIGN_EXPONENT_WIDTH = BIT_SIZE - MANTISSA_WIDTH
    EXPONENT_WIDTH = SIGN_EXPONENT_WIDTH - 1
    ONE_U = one(U)
    EXPONENT_MASK = ((ONE_U << EXPONENT_WIDTH) - ONE_U) << MANTISSA_WIDTH
    EXPONENT_BIAS = (1 << (EXPONENT_WIDTH - 1)) - 1
    MANTISSA_MASK = (ONE_U << MANTISSA_WIDTH) - ONE_U
    k = reinterpret(U, x)
    e = Int((k & EXPONENT_MASK) >> MANTISSA_WIDTH) - EXPONENT_BIAS
    return (signbit(x), Int8(e),
        Int16(e - (MANTISSA_WIDTH - trailing_zeros(k | ~MANTISSA_MASK))))
end


@inline function long_summary(x::T, ::Type{U}) where {T,U}
    BIT_SIZE = 8 * sizeof(T)
    MANTISSA_WIDTH = precision(T) - 1
    SIGN_EXPONENT_WIDTH = BIT_SIZE - MANTISSA_WIDTH
    EXPONENT_WIDTH = SIGN_EXPONENT_WIDTH - 1
    ONE_U = one(U)
    EXPONENT_MASK = ((ONE_U << EXPONENT_WIDTH) - ONE_U) << MANTISSA_WIDTH
    EXPONENT_BIAS = (1 << (EXPONENT_WIDTH - 1)) - 1
    MANTISSA_MASK = (ONE_U << MANTISSA_WIDTH) - ONE_U
    SHIFTED_MASK = MANTISSA_MASK << SIGN_EXPONENT_WIDTH
    k = reinterpret(U, x)
    lz = leading_zeros((k << SIGN_EXPONENT_WIDTH) | ~SHIFTED_MASK)
    lo = leading_ones((k << SIGN_EXPONENT_WIDTH) & SHIFTED_MASK)
    tz = trailing_zeros(k | ~MANTISSA_MASK)
    to = trailing_ones(k & MANTISSA_MASK)
    return (signbit(x), iszero(lz), iszero(tz),
        Int8(Int((k & EXPONENT_MASK) >> MANTISSA_WIDTH) - EXPONENT_BIAS),
        Int8(max(lz, lo)), Int8(max(tz, to)))
end


struct RangePusher
    e_min::Int
    e_max::Int
    f_min::Int
    f_max::Int

    @inline RangePusher(::Type{T}) where {T} = new(
        exponent(floatmin(T)),
        exponent(floatmax(T)),
        exponent(floatmin(T)) - precision(T) + 1,
        exponent(floatmax(T)),
    )
end

@inline function _range_helper_f(
    rp::RangePusher, r::UnitRange{I}) where {I<:Integer}
    # @assert r.start <= r.stop
    return UnitRange{I}(max(I(rp.f_min), r.start), min(I(rp.f_max), r.stop))
end

function (rp::RangePusher)(
    v::AbstractVector{MediumPairSummary},
    (ss_range, es_range, fs_range), (se_range, ee_range, fe_range),
)
    for ss in _range_helper(rp, ss_range)
        for es in _range_helper_e(rp, es_range)
            for fs in _range_helper_f(rp, fs_range)
                for se in _range_helper(rp, se_range)
                    for ee in _range_helper_e(rp, ee_range)
                        for fe in _range_helper_f(rp, fe_range)
                            push!(v, ((ss, es, fs), (se, ee, fe)))
                        end
                    end
                end
            end
        end
    end
    return v
end


const ± = false:true


struct ReservoirSampler{T}
    reservoir::Vector{T}
    count::Array{Int,0}

    @inline ReservoirSampler{T}(k::Int) where {T} =
        new{T}(Vector{T}(undef, k), fill(0))
end


function Base.push!(rs::ReservoirSampler{T}, x::T) where {T}
    rs.count[] += 1
    if rs.count[] <= length(rs.reservoir)
        rs.reservoir[rs.count[]] = x
    else
        i = rand(1:rs.count[])
        if i <= length(rs.reservoir)
            rs.reservoir[i] = x
        end
    end
    return rs
end


function main(
    ::Type{T},
    pos_zero::MediumFloatSummary,
    neg_zero::MediumFloatSummary,
    summaries::AbstractVector{MediumFloatSummary},
    two_sum_summaries::AbstractVector{MediumTwoSumSummary},
) where {T}

    p = precision(T)
    push_range! = RangePusher(T)

    lemma_z_count = 0
    lemma_i_count = 0
    lemma_f_count = 0
    lemma_e_count = 0
    lemma_o_count = 0
    lemma_1_count = 0
    lemma_2_count = 0
    lemma_3_count = 0
    lemma_4_count = 0

    for rx in summaries, ry in summaries
        s = lookup_summaries(two_sum_summaries, rx, ry)
        (sx, ex, fx) = rx
        (sy, ey, fy) = ry
        same_sign = (sx == sy)
        diff_sign = (sx != sy)
        x_zero = (rx == pos_zero) | (rx == neg_zero)
        y_zero = (ry == pos_zero) | (ry == neg_zero)

        verified = 0

        if x_zero | y_zero ################################## LEMMA FAMILY Z (2)

            # Lemmas in Family Z (for "zero") apply to
            # cases where one or both addends are zero.

            # Lemma Z1: Both addends are zero.
            if (rx == pos_zero) & (ry == pos_zero)
                @assert only(s) == (pos_zero, pos_zero)
                lemma_z_count += 1
                verified += 1
            end
            if (rx == pos_zero) & (ry == neg_zero)
                @assert only(s) == (pos_zero, pos_zero)
                lemma_z_count += 1
                verified += 1
            end
            if (rx == neg_zero) & (ry == pos_zero)
                @assert only(s) == (pos_zero, pos_zero)
                lemma_z_count += 1
                verified += 1
            end
            if (rx == neg_zero) & (ry == neg_zero)
                @assert only(s) == (neg_zero, pos_zero)
                lemma_z_count += 1
                verified += 1
            end

            # Lemma Z2: One addend is zero.
            if y_zero & !x_zero
                @assert only(s) == (rx, pos_zero)
                lemma_z_count += 1
                verified += 1
            end
            if x_zero & !y_zero
                @assert only(s) == (ry, pos_zero)
                lemma_z_count += 1
                verified += 1
            end

        else #################################################### NONZERO LEMMAS

            # From this point forward, all lemma statements carry
            # an implicit assumption that both addends are nonzero.

            ################################################# LEMMA FAMILY I (1)

            # Lemmas in Family I (for "identical") apply to addends
            # that are returned unchanged by the TwoSum algorithm.

            # Lemma I
            if ((ex > ey + (p+1)) |
                ((ex == ey + (p+1)) & ((ey == fy) | same_sign | (ex > fx))) |
                ((ex == ey + p) & (ey == fy) & (same_sign | (ex > fx)) & (ex < fx + (p-1))))
                @assert only(s) == (rx, ry)
                lemma_i_count += 1
                verified += 1
            end
            if ((ey > ex + (p+1)) |
                ((ey == ex + (p+1)) & ((ex == fx) | same_sign | (ey > fy))) |
                ((ey == ex + p) & (ex == fx) & (same_sign | (ey > fy)) & (ey < fy + (p-1))))
                @assert only(s) == (ry, rx)
                lemma_i_count += 1
                verified += 1
            end

            ################################################# LEMMA FAMILY F (7)

            # Lemmas in Family F apply to addends that share
            # the same trailing exponent, i.e., (fx == fy).

            # The trailing exponent of a floating-point number x, denoted by
            # fx, is the place value of the last nonzero bit in its mantissa.

            # Lemma F1
            if same_sign & (fx == fy) & (ex == ey) & (ex == fx)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex+1:ex+1, ex + 1), pos_zero)
                    @assert s == t
                end
                lemma_f_count += 1
                verified += 1
            end

            # Lemma F2
            if same_sign & (fx == fy) & (ex == ey) & (ex > fx)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex+1:ex+1, fx+1:ex), pos_zero)
                    @assert s == t
                end
                lemma_f_count += 1
                verified += 1
            end

            # Lemma F3
            if same_sign & (fx == fy) & (ex == ey + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , fx+1:ex-2), pos_zero)
                    push_range!(t, (sx, ex+1:ex+1, fx+1:ey  ), pos_zero)
                    push_range!(t, (sx, ex+1:ex+1, ex + 1   ), pos_zero)
                    @assert s == t
                end
                lemma_f_count += 1
                verified += 1
            end
            if same_sign & (fx == fy) & (ey == ex + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , fy+1:ey-2), pos_zero)
                    push_range!(t, (sy, ey+1:ey+1, fy+1:ex  ), pos_zero)
                    push_range!(t, (sy, ey+1:ey+1, ey + 1   ), pos_zero)
                    @assert s == t
                end
                lemma_f_count += 1
                verified += 1
            end

            # Lemma F4
            if same_sign & (fx == fy) & (ex > ey + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , fx+1:ex-1), pos_zero)
                    push_range!(t, (sx, ex+1:ex+1, fx+1:ey  ), pos_zero)
                    push_range!(t, (sx, ex+1:ex+1, ex + 1   ), pos_zero)
                    @assert s == t
                end
                lemma_f_count += 1
                verified += 1
            end
            if same_sign & (fx == fy) & (ey > ex + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , fy+1:ey-1), pos_zero)
                    push_range!(t, (sy, ey+1:ey+1, fy+1:ex  ), pos_zero)
                    push_range!(t, (sy, ey+1:ey+1, ey + 1   ), pos_zero)
                    @assert s == t
                end
                lemma_f_count += 1
                verified += 1
            end

            # Lemma F5
            if diff_sign & (fx == fy) & (ex == ey)
                let t = MediumPairSummary[]
                    push!(t, (pos_zero, pos_zero))
                    for k = fx+1:ex-1
                        push_range!(t, (±, k:k, fx+1:k), pos_zero)
                    end
                    @assert s == sort!(t)
                end
                lemma_f_count += 1
                verified += 1
            end

            # Lemma F6
            if diff_sign & (fx == fy) & (ex == ey + 1)
                let t = MediumPairSummary[]
                    for k = fx+1:ex-1
                        push_range!(t, (sx, k:k, fx+1:k), pos_zero)
                    end
                    push_range!(t, (sx, ex, fx+1:ex-2), pos_zero)
                    push!(t, ((sx, ex, ex), pos_zero))
                    @assert s == t
                end
                lemma_f_count += 1
                verified += 1
            end
            if diff_sign & (fx == fy) & (ey == ex + 1)
                let t = MediumPairSummary[]
                    for k = fy+1:ey-1
                        push_range!(t, (sy, k:k, fy+1:k), pos_zero)
                    end
                    push_range!(t, (sy, ey, fy+1:ey-2), pos_zero)
                    push!(t, ((sy, ey, ey), pos_zero))
                    @assert s == t
                end
                lemma_f_count += 1
                verified += 1
            end

            # Lemma F7
            if diff_sign & (fx == fy) & (ex > ey + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, fx+1:ey), pos_zero)
                    push_range!(t, (sx, ex       , fx+1:ex), pos_zero)
                    @assert s == t
                end
                lemma_f_count += 1
                verified += 1
            end
            if diff_sign & (fx == fy) & (ey > ex + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, fy+1:ex), pos_zero)
                    push_range!(t, (sy, ey       , fy+1:ey), pos_zero)
                    @assert s == t
                end
                lemma_f_count += 1
                verified += 1
            end

            # Family F completely handles all inputs that satisfy (fx == fy).

            if (fx == fy)
                @assert isone(verified)
            end

            ############################################### LEMMA FAMILY E (7+8)

            # Lemmas in Family E (for "exact") apply to addends
            # with different trailing exponents that can be summed
            # exactly with no rounding error.

            # Lemma E1: Addends have same sign and exponent.
            if same_sign & (ex == ey) & (fx < fy) & (ex < fx + (p-1)) & (ey < fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex+1:ex+1, fx), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end
            if same_sign & (ex == ey) & (fx > fy) & (ex < fx + (p-1)) & (ey < fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex+1:ex+1, fy), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end

            # Lemma E2.G: Addends have same exponent and different signs.
            if diff_sign & (ex == ey) & (fx < fy) & (ex > fx + 1) & (ey > fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (±, fx:ex-1, fx), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end
            if diff_sign & (ex == ey) & (fx > fy) & (ex > fx + 1) & (ey > fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (±, fy:ey-1, fy), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end

            # Lemma E2.1: Boundary case of E2 where two leading bits cancel.
            if diff_sign & (ex == ey) & (ex > fx + 1) & (ey == fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (±, fx:ex-2, fx), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end
            if diff_sign & (ex == ey) & (ex == fx + 1) & (ey > fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (±, fy:ey-2, fy), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end

            # Lemma E3.G: Addends do not overlap.
            if (same_sign | (ex > fx)) & (fx > ey) & (ex < fy + p)
                @assert only(s) == ((sx, ex, fy), pos_zero)
                lemma_e_count += 1
                verified += 1
            end
            if (same_sign | (ey > fy)) & (fy > ex) & (ey < fx + p)
                @assert only(s) == ((sy, ey, fx), pos_zero)
                lemma_e_count += 1
                verified += 1
            end

            # Lemma E3.1: Boundary case of E3 where leading bits cancel.
            if diff_sign & (
                    ((ex == fx) & (fx > ey + 1) & (ex < fy + (p+1))) |
                    ((ex == fx + 1) & (fx == ey) & (ey > fy)))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, fy), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end
            if diff_sign & (
                    ((ey == fy) & (fy > ex + 1) & (ey < fx + (p+1))) |
                    ((ey == fy + 1) & (fy == ex) & (ex > fx)))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, fx), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end

            # Lemma E4.G: Addends have same sign and partially overlap.
            if same_sign & ((ex > ey > fx > fy) | (ex > ey + 1 > fx > fy)) & (ex < fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex:ex+1, fy), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end
            if same_sign & ((ey > ex > fy > fx) | (ey > ex + 1 > fy > fx)) & (ey < fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey:ey+1, fx), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end

            # Lemma E4.1: Boundary case of E4 with guaranteed carry.
            if same_sign & (ex == ey + 1) & (ey == fx > fy) & (ex < fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex+1:ex+1, fy), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end
            if same_sign & (ey == ex + 1) & (ex == fy > fx) & (ey < fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey+1:ey+1, fx), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end

            # Lemma E5.G: Addends have different signs and partially overlap.
            if diff_sign & (ex > ey + 1 > fx > fy) & (ex < fy + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex, fy), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end
            if diff_sign & (ey > ex + 1 > fy > fx) & (ey < fx + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey, fx), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end

            # Lemma E5.1: Boundary case of E5 with more possible cancellation.
            if diff_sign & (ex == ey + 1) & (ey > fx > fy) & (ex < fy + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, fx:ex, fy), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end
            if diff_sign & (ey == ex + 1) & (ex > fy > fx) & (ey < fx + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, fy:ey, fx), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end

            # Lemma E5.2: Boundary case of E5 with guaranteed cancellation.
            if diff_sign & (ex == ey + 1 == fx) & (fx > fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, fy:ex-2, fy), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end
            if diff_sign & (ey == ex + 1 == fy) & (fy > fx + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, fx:ey-2, fx), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end

            # Lemma E5.3: Boundary case of E5.2 with guaranteed cancellation.
            if diff_sign & (ex == ey + 1 == fx == fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, fy:ex-1, fy), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end
            if diff_sign & (ey == ex + 1 == fy == fx + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, fx:ey-1, fx), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end

            # Lemma E6: Addends have same sign and completely overlap.
            if same_sign & (ex > ey) & (fx < fy) & (ex < fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex:ex+1, fx), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end
            if same_sign & (ey > ex) & (fy < fx) & (ey < fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey:ey+1, fy), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end

            # Lemma E7.G: Addends have different signs and completely overlap.
            # All hypotheses are strictly necessary.
            if diff_sign & (ex > ey + 1) & (fx < fy)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex, fx), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end
            if diff_sign & (ey > ex + 1) & (fy < fx)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey, fy), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end

            # Lemma E7.1: Boundary case of E7 with more possible cancellation.
            # All hypotheses are strictly necessary.
            if diff_sign & (ex == ey + 1) & (fx < fy)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, fy:ex, fx), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end
            if diff_sign & (ey == ex + 1) & (fy < fx)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, fx:ey, fy), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end

            # Lemma E7.2: Boundary case of E7 with guaranteed cancellation.
            if diff_sign & (ex == ey == fy) & (fx < fy)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, fx:ex-1, fx), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end
            if diff_sign & (ey == ex == fx) & (fy < fx)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, fy:ey-1, fy), pos_zero)
                    @assert s == t
                end
                lemma_e_count += 1
                verified += 1
            end

            ################################################# LEMMA FAMILY O (3)

            # Lemmas in Family O (for "overlap") apply to addends
            # that completely overlap but cannot be summed exactly.

            # Lemma O1: All hypotheses are strictly necessary.
            if same_sign & (ex == fx + (p-1)) & (ex > ey > fy > fx)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , fx), pos_zero)
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-3):ey  ), (±  , fx:ex-(p-1), fx))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fx:ex-(p-1), fx))
                    @assert s == t
                end
                lemma_o_count += 1
                verified += 1
            end
            if same_sign & (ey == fy + (p-1)) & (ey > ex > fx > fy)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , fy), pos_zero)
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-3):ex  ), (±  , fy:ey-(p-1), fy))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fy:ey-(p-1), fy))
                    @assert s == t
                end
                lemma_o_count += 1
                verified += 1
            end

            # Lemma O2: All hypotheses are strictly necessary.
            if same_sign & (ex == fx + (p-1)) & (ex > ey == fy > fx + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , fx), pos_zero)
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-3):ey-1), (±  , fx:ex-(p-1), fx))
                    push_range!(t, (sx, ex+1:ex+1, ey           ), (!sy, fx:ex-(p-1), fx))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fx:ex-(p-1), fx))
                    @assert s == t
                end
                lemma_o_count += 1
                verified += 1
            end
            if same_sign & (ey == fy + (p-1)) & (ey > ex == fx > fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , fy), pos_zero)
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-3):ex-1), (±  , fy:ey-(p-1), fy))
                    push_range!(t, (sy, ey+1:ey+1, ex           ), (!sx, fy:ey-(p-1), fy))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fy:ey-(p-1), fy))
                    @assert s == t
                end
                lemma_o_count += 1
                verified += 1
            end

            # Lemma O3: All hypotheses are strictly necessary.
            if same_sign & (ex == fx + (p-1)) & (ey == fy == fx + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , fx), pos_zero)
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fx:ex-(p-1), fx))
                    @assert s == t
                end
                lemma_o_count += 1
                verified += 1
            end
            if same_sign & (ey == fy + (p-1)) & (ex == fx == fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , fy), pos_zero)
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fy:ey-(p-1), fy))
                    @assert s == t
                end
                lemma_o_count += 1
                verified += 1
            end

            ############################################## MASTER LEMMA FAMILIES

            # Lemmas 1, 2, and 3 are "Master Lemmas." Their hypotheses only
            # contain inequalities in the exponent variables (ex, fx, ey, fy).
            # This means that they apply to a full-dimensional region of the
            # input space as opposed to a lower-dimensional subspace.

            ################################################# LEMMA FAMILY 1 (4)

            # Lemma 1
            if (ex < ey + p) & (ex > fy + p) & (fx > ey + 1) & ((ex > fx) | same_sign)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ex-(p-1):ey-1), (±  , fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, ey           ), (sy , fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, ey + 1       ), (!sy, fy:ex-(p+1), fy))
                    @assert s == t
                end
                lemma_1_count += 1
                verified += 1
            end
            if (ey < ex + p) & (ey > fx + p) & (fy > ex + 1) & ((ey > fy) | same_sign)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ey-(p-1):ex-1), (±  , fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, ex           ), (sx , fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, ex + 1       ), (!sx, fx:ey-(p+1), fx))
                    @assert s == t
                end
                lemma_1_count += 1
                verified += 1
            end

            # Lemma 1A
            if (ex == ey + p) & (ex > fy + p) & (fx > ey + 1) & ((ex > fx) | same_sign)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ey + 1       ), (!sy, fy:ex-(p+1), fy))
                    @assert s == t
                end
                lemma_1_count += 1
                verified += 1
            end
            if (ey == ex + p) & (ey > fx + p) & (fy > ex + 1) & ((ey > fy) | same_sign)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ex + 1       ), (!sx, fx:ey-(p+1), fx))
                    @assert s == t
                end
                lemma_1_count += 1
                verified += 1
            end

            # Lemma 1B.G
            if (ex < ey + (p-1)) & (ex == fy + p) & (fx > ey + 1) & ((ex > fx) | same_sign)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ex-(p-2):ey-1), (±  , fy:ex-p, fy))
                    push_range!(t, (sx, ex, ey           ), (sy , fy:ex-p, fy))
                    push_range!(t, (sx, ex, ey + 1       ), (!sy, fy:ex-p, fy))
                    @assert s == t
                end
                lemma_1_count += 1
                verified += 1
            end
            if (ey < ex + (p-1)) & (ey == fx + p) & (fy > ex + 1) & ((ey > fy) | same_sign)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ey-(p-2):ex-1), (±  , fx:ey-p, fx))
                    push_range!(t, (sy, ey, ex           ), (sx , fx:ey-p, fx))
                    push_range!(t, (sy, ey, ex + 1       ), (!sx, fx:ey-p, fx))
                    @assert s == t
                end
                lemma_1_count += 1
                verified += 1
            end

            # Lemma 1B.1
            if (ex == ey + (p-1)) & (ex == fy + p) & (fx > ey + 1) & ((ex > fx) | same_sign)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ey + 1       ), (!sy, fy:ex-p, fy))
                    @assert s == t
                end
                lemma_1_count += 1
                verified += 1
            end
            if (ey == ex + (p-1)) & (ey == fx + p) & (fy > ex + 1) & ((ey > fy) | same_sign)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ex + 1       ), (!sx, fx:ey-p, fx))
                    @assert s == t
                end
                lemma_1_count += 1
                verified += 1
            end

            ################################################ LEMMA FAMILY 2 (18)

            # Lemma 2: All hypotheses are strictly necessary.
            if same_sign & (ex > fy + p) & (fx < ey)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , ex-(p-1):ex-1), (±  , fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-2):ey  ), (±  , fy:ex-p    , fy))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (!sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-p    , fy))
                    @assert s == sort!(t)
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey > fx + p) & (fy < ex)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , ey-(p-1):ey-1), (±  , fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-2):ex  ), (±  , fx:ey-p    , fx))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (!sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-p    , fx))
                    @assert s == sort!(t)
                end
                lemma_2_count += 1
                verified += 1
            end

            # Lemma 2A.G: All hypotheses are strictly necessary.
            if same_sign & (ex == fy + p) & (fx < ey) & (ey < fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , ex-(p-2):ex-1), (±, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-2):ey  ), (±, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (±, fy:ex-p, fy))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey == fx + p) & (fy < ex) & (ex < fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , ey-(p-2):ey-1), (±, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-2):ex  ), (±, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (±, fx:ey-p, fx))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end

            # Lemma 2A.1
            if same_sign & (ex == fy + p) & (fx + 1 < ey) & (ey == fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , ex-(p-2):ex-2), (±, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-2):ey  ), (±, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (±, fy:ex-p, fy))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey == fx + p) & (fy + 1 < ex) & (ex == fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , ey-(p-2):ey-2), (±, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-2):ex  ), (±, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (±, fx:ey-p, fx))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end

            # Lemma 2A.2
            if same_sign & (ex == fy + p) & (fx + 1 == ey) & (ey == fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , ex-(p-2):ey-2), (± , fy:ex-p, fy))
                    push_range!(t, (sx, ex       , ey - 1       ), (sy, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-2):ey  ), (± , fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (± , fy:ex-p, fy))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey == fx + p) & (fy + 1 == ex) & (ex == fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , ey-(p-2):ex-2), (± , fx:ey-p, fx))
                    push_range!(t, (sy, ey       , ex - 1       ), (sx, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-2):ex  ), (± , fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (± , fx:ey-p, fx))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end

            # Lemma 2B.G: All hypotheses are strictly necessary.
            if same_sign & (ex > fy + p) & (fx == ey) & (ex < fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , ex-(p-1):ey-1), (±  , fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex       , ey           ), (!sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex       , ey+1:ex-1    ), (sy , fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-2):ey-1), (±  , fy:ex-p    , fy))
                    push_range!(t, (sx, ex+1:ex+1, ey           ), (!sy, fy:ex-p    , fy))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-p    , fy))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey > fx + p) & (fy == ex) & (ey < fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , ey-(p-1):ex-1), (±  , fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey       , ex           ), (!sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey       , ex+1:ey-1    ), (sx , fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-2):ex-1), (±  , fx:ey-p    , fx))
                    push_range!(t, (sy, ey+1:ey+1, ex           ), (!sx, fx:ey-p    , fx))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-p    , fx))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end

            # Lemma 2B.1
            if same_sign & (ex > fy + p) & (fx == ey) & (ex == fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , ey           ), (!sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex       , ey+1:ex-1    ), (sy , fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-p    , fy))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey > fx + p) & (fy == ex) & (ey == fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , ex           ), (!sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey       , ex+1:ey-1    ), (sx , fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-p    , fx))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end

            # Lemma 2C.G: All hypotheses are strictly necessary.
            if same_sign & (ex == fy + (p-1)) & (fx < ey) & (ex < fx + (p-1)) & (ey < fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , fy), pos_zero)
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-3):ey), (± , fy:ex-(p-1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1     ), (sy, fy:ex-(p-1), fy))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey == fx + (p-1)) & (fy < ex) & (ey < fy + (p-1)) & (ex < fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , fx), pos_zero)
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-3):ex), (± , fx:ey-(p-1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1     ), (sx, fx:ey-(p-1), fx))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end

            # Lemma 2C.1
            if same_sign & (ex == fy + (p-1)) & (fx < ey) & (ex < fx + (p-1)) & (ey == fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-3):ey), (± , fy:ex-(p-1), fy))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey == fx + (p-1)) & (fy < ex) & (ey < fy + (p-1)) & (ex == fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-3):ex), (± , fx:ey-(p-1), fx))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end

            # Lemma 2D.G: All hypotheses are strictly necessary.
            if same_sign & (ex > fy + p) & (fx == ey + 1) & (ex < fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , ex-(p-1):ey-1), (±  , fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex       , ey           ), (sy , fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex       , ey+2:ex-1    ), (!sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (!sy, fy:ex-(p+1), fy))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey > fx + p) & (fy == ex + 1) & (ey < fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , ey-(p-1):ex-1), (±  , fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey       , ex           ), (sx , fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey       , ex+2:ey-1    ), (!sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (!sx, fx:ey-(p+1), fx))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end

            # Lemma 2D.1
            if same_sign & (ex > fy + p) & (fx == ey + 1) & (ex == fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , ey+2:ex-1    ), (!sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (!sy, fy:ex-(p+1), fy))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey > fx + p) & (fy == ex + 1) & (ey == fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , ex+2:ey-1    ), (!sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (!sx, fx:ey-(p+1), fx))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end

            # Lemma 2AB.G: All hypotheses are strictly necessary.
            if same_sign & (ex == fy + p) & (fx == ey) & (ex < fx + (p-1)) & (ey < fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , ex-(p-2):ey-1), (±  , fy:ex-p, fy))
                    push_range!(t, (sx, ex       , ey           ), (!sy, fy:ex-p, fy))
                    push_range!(t, (sx, ex       , ey+1:ex-1    ), (sy , fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-2):ey-1), (±  , fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ey           ), (!sy, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-p, fy))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey == fx + p) & (fy == ex) & (ey < fy + (p-1)) & (ex < fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , ey-(p-2):ex-1), (±  , fx:ey-p, fx))
                    push_range!(t, (sy, ey       , ex           ), (!sx, fx:ey-p, fx))
                    push_range!(t, (sy, ey       , ex+1:ey-1    ), (sx , fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-2):ex-1), (±  , fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ex           ), (!sx, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-p, fx))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end

            # Lemma 2AB.1
            if same_sign & (ex == fy + p) & (fx == ey) & (ex == fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , ey+1:ex-1    ), (sy , fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-p, fy))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey == fx + p) & (fy == ex) & (ey == fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , ex+1:ey-1    ), (sx , fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-p, fx))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end

            # Lemma 2AB.2
            if same_sign & (ex == fy + p) & (fx == ey) & (ey == fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-2):ey-1), (±  , fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ey           ), (!sy, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-p, fy))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey == fx + p) & (fy == ex) & (ex == fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-2):ex-1), (±  , fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ex           ), (!sx, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-p, fx))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end

            # Lemma 2BC.G: All hypotheses are strictly necessary.
            if same_sign & (ex == fy + (p-1)) & (fx == ey) & (ey > fy + 1) & (ey < fy + (p-2))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , fy), pos_zero)
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-3):ey-1), (±  , fy:ex-(p-1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ey           ), (!sy, fy:ex-(p-1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-(p-1), fy))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey == fx + (p-1)) & (fy == ex) & (ex > fx + 1) & (ex < fx + (p-2))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , fx), pos_zero)
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-3):ex-1), (±  , fx:ey-(p-1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ex           ), (!sx, fx:ey-(p-1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-(p-1), fx))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end

            # Lemma 2BC.1: All hypotheses are strictly necessary.
            if same_sign & (ex == fy + (p-1)) & (fx == ey) & (ey > fy + (p-3))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-3):ey-1), (±  , fy:ex-(p-1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ey           ), (!sy, fy:ex-(p-1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-(p-1), fy))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey == fx + (p-1)) & (fy == ex) & (ex > fx + (p-3))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-3):ex-1), (±  , fx:ey-(p-1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ex           ), (!sx, fx:ey-(p-1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-(p-1), fx))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end

            # Lemma 2BC.2
            if same_sign & (ex == fy + (p-1)) & (fx == ey) & (ey == fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , fy), pos_zero)
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (sy , fy:ex-(p-1), fy))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey == fx + (p-1)) & (fy == ex) & (ex == fx + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , fx), pos_zero)
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (sx , fx:ey-(p-1), fx))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end

            # Lemma 2AD.G: All hypotheses are strictly necessary.
            if same_sign & (ex == fy + p) & (fx == ey + 1) & (ex < fx + (p-2))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , ex-(p-2):ey-1), (±  , fy:ex-p, fy))
                    push_range!(t, (sx, ex       , ey           ), (sy , fy:ex-p, fy))
                    push_range!(t, (sx, ex       , ey+2:ex-1    ), (!sy, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (!sy, fy:ex-p, fy))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey == fx + p) & (fy == ex + 1) & (ey < fy + (p-2))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , ey-(p-2):ex-1), (±  , fx:ey-p, fx))
                    push_range!(t, (sy, ey       , ex           ), (sx , fx:ey-p, fx))
                    push_range!(t, (sy, ey       , ex+2:ey-1    ), (!sx, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (!sx, fx:ey-p, fx))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end

            # Lemma 2AD.1
            if same_sign & (ex == fy + p) & (fx == ey + 1) & (ex > fx + (p-3))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex       , ey+2:ex-1    ), (!sy, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex + 1       ), (!sy, fy:ex-p, fy))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end
            if same_sign & (ey == fx + p) & (fy == ex + 1) & (ey > fy + (p-3))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey       , ex+2:ey-1    ), (!sx, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey + 1       ), (!sx, fx:ey-p, fx))
                    @assert s == t
                end
                lemma_2_count += 1
                verified += 1
            end

            ################################################ LEMMA FAMILY 3 (13)

            # Lemma 3: All hypotheses are strictly necessary.
            if diff_sign & (ex > fy + (p+1)) & (fx < ey)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, ex-p:ey      ), (±  , fy:ex-(p+2), fy))
                    push_range!(t, (sx, ex       , ex-(p-1):ex-1), (±  , fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex       , ex           ), (sy , fy:ex-(p+2), fy))
                    push_range!(t, (sx, ex       , ex           ), (!sy, fy:ex-(p+1), fy))
                    @assert s == sort!(t)
                end
                lemma_3_count += 1
                verified += 1
            end
            if diff_sign & (ey > fx + (p+1)) & (fy < ex)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, ey-p:ex      ), (±  , fx:ey-(p+2), fx))
                    push_range!(t, (sy, ey       , ey-(p-1):ey-1), (±  , fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey       , ey           ), (sx , fx:ey-(p+2), fx))
                    push_range!(t, (sy, ey       , ey           ), (!sx, fx:ey-(p+1), fx))
                    @assert s == sort!(t)
                end
                lemma_3_count += 1
                verified += 1
            end

            # Lemma 3A: All hypotheses are strictly necessary.
            if diff_sign & (ex == fy + (p+1)) & (fx < ey)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, ex-(p-1):ey), (±, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex       , ex-(p-1):ex), (±, fy:ex-(p+1), fy))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end
            if diff_sign & (ey == fx + (p+1)) & (fy < ex)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, ey-(p-1):ex), (±, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey       , ey-(p-1):ey), (±, fx:ey-(p+1), fx))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end

            # Lemma 3B: All hypotheses are strictly necessary.
            if diff_sign & (ex > fy + (p+1)) & (fx == ey)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, ex-p:ey-1    ), (±  , fy:ex-(p+2), fy))
                    push_range!(t, (sx, ex-1:ex-1, ey           ), (!sy, fy:ex-(p+2), fy))
                    push_range!(t, (sx, ex       , ex-(p-1):ey-1), (±  , fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex       , ey           ), (!sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex       , ey+1:ex-1    ), (sy , fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex       , ex           ), (sy , fy:ex-(p+2), fy))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end
            if diff_sign & (ey > fx + (p+1)) & (fy == ex)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, ey-p:ex-1    ), (±  , fx:ey-(p+2), fx))
                    push_range!(t, (sy, ey-1:ey-1, ex           ), (!sx, fx:ey-(p+2), fx))
                    push_range!(t, (sy, ey       , ey-(p-1):ex-1), (±  , fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey       , ex           ), (!sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey       , ex+1:ey-1    ), (sx , fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey       , ey           ), (sx , fx:ey-(p+2), fx))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end

            # Lemma 3C.G: All hypotheses are strictly necessary.
            if diff_sign & (ex == fy + p) & (fx < ey) & (ey < fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, fy), pos_zero)
                    push_range!(t, (sx, ex       , ex-(p-2):ex-1), (±  , fy:ex-p, fy))
                    push_range!(t, (sx, ex       , ex           ), (!sy, fy:ex-p, fy))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end
            if diff_sign & (ey == fx + p) & (fy < ex) & (ex < fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, fx), pos_zero)
                    push_range!(t, (sy, ey       , ey-(p-2):ey-1), (±  , fx:ey-p, fx))
                    push_range!(t, (sy, ey       , ey           ), (!sx, fx:ey-p, fx))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end

            # Lemma 3C.1
            if diff_sign & (ex == fy + p) & (fx + 1 < ey) & (ey == fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, fx:ex-1, fy), pos_zero)
                    push_range!(t, (sx, ex     , ex-(p-2):ex-2), (±  , fy:ex-p, fy))
                    push_range!(t, (sx, ex     , ex           ), (!sy, fy:ex-p, fy))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end
            if diff_sign & (ey == fx + p) & (fy + 1 < ex) & (ex == fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, fy:ey-1, fx), pos_zero)
                    push_range!(t, (sy, ey     , ey-(p-2):ey-2), (±  , fx:ey-p, fx))
                    push_range!(t, (sy, ey     , ey           ), (!sx, fx:ey-p, fx))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end

            # Lemma 3C.2: All hypotheses are strictly necessary.
            # This lemma uniquely contains the leading exponent range ex-2:ex-1.
            if diff_sign & (ex == fy + p) & (fx + 1 == ey) & (ey == fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-2:ex-1, fy), pos_zero)
                    push_range!(t, (sx, ex       , ex-(p-2):ey-2), (±  , fy:ex-p, fy))
                    push_range!(t, (sx, ex       , ey - 1       ), (sy , fy:ex-p, fy))
                    push_range!(t, (sx, ex       , ex           ), (!sy, fy:ex-p, fy))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end
            if diff_sign & (ey == fx + p) & (fy + 1 == ex) & (ex == fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-2:ey-1, fx), pos_zero)
                    push_range!(t, (sy, ey       , ey-(p-2):ex-2), (±  , fx:ey-p, fx))
                    push_range!(t, (sy, ey       , ex - 1       ), (sx , fx:ey-p, fx))
                    push_range!(t, (sy, ey       , ey           ), (!sx, fx:ey-p, fx))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end

            # Lemma 3D.G: All hypotheses are strictly necessary.
            if diff_sign & (ex > fy + p) & (fx == ey + 1) & (ex < fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ex-(p-1):ey-1), (±  , fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, ey           ), (sy , fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, ey+2:ex      ), (!sy, fy:ex-(p+1), fy))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end
            if diff_sign & (ey > fx + p) & (fy == ex + 1) & (ey < fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ey-(p-1):ex-1), (±  , fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, ex           ), (sx , fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, ex+2:ey      ), (!sx, fx:ey-(p+1), fx))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end

            # Lemma 3D.1: All hypotheses are strictly necessary.
            if diff_sign & (ex > fy + p) & (fx == ey + 1) & (ex == fx + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ey+2:ex      ), (!sy, fy:ex-(p+1), fy))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end
            if diff_sign & (ey > fx + p) & (fy == ex + 1) & (ey == fy + (p-1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ex+2:ey      ), (!sx, fx:ey-(p+1), fx))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end

            # Lemma 3AB: All hypotheses are strictly necessary.
            if diff_sign & (ex == fy + (p+1)) & (fx == ey)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, ex-(p-1):ey-1), (±  , fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex-1:ex-1, ey           ), (!sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex       , ex-(p-1):ey-1), (±  , fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex       , ey           ), (!sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex       , ey+1:ex      ), (sy , fy:ex-(p+1), fy))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end
            if diff_sign & (ey == fx + (p+1)) & (fy == ex)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, ey-(p-1):ex-1), (±  , fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey-1:ey-1, ex           ), (!sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey       , ey-(p-1):ex-1), (±  , fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey       , ex           ), (!sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey       , ex+1:ey      ), (sx , fx:ey-(p+1), fx))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end

            # Lemma 3BC.G
            if diff_sign & (ex == fy + p) & (fx == ey) & (ex > fx + 1) & (ey > fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, fy), pos_zero)
                    push_range!(t, (sx, ex       , ex-(p-2):ey-1), (±  , fy:ex-p, fy))
                    push_range!(t, (sx, ex       , ey           ), (!sy, fy:ex-p, fy))
                    push_range!(t, (sx, ex       , ey+1:ex-1    ), (sy , fy:ex-p, fy))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end
            if diff_sign & (ey == fx + p) & (fy == ex) & (ey > fy + 1) & (ex > fx + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, fx), pos_zero)
                    push_range!(t, (sy, ey       , ey-(p-2):ex-1), (±  , fx:ey-p, fx))
                    push_range!(t, (sy, ey       , ex           ), (!sx, fx:ey-p, fx))
                    push_range!(t, (sy, ey       , ex+1:ey-1    ), (sx , fx:ey-p, fx))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end

            # Lemma 3BC.1
            if diff_sign & (ex == fy + p) & (fx == ey) & (ey == fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, fy), pos_zero)
                    push_range!(t, (sx, ex       , ey+1:ex-1    ), (sy , fy:ex-p, fy))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end
            if diff_sign & (ey == fx + p) & (fy == ex) & (ex == fx + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, fx), pos_zero)
                    push_range!(t, (sy, ey       , ex+1:ey-1    ), (sx , fx:ey-p, fx))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end

            # Lemma 3CD.G
            if diff_sign & (ex == fy + p) & (fx == ey + 1) & (ex > fx) & (ey > fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ex-(p-2):ey-1), (±  , fy:ex-p, fy))
                    push_range!(t, (sx, ex, ey           ), (sy , fy:ex-p, fy))
                    push_range!(t, (sx, ex, ey+2:ex      ), (!sy, fy:ex-p, fy))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end
            if diff_sign & (ey == fx + p) & (fy == ex + 1) & (ey > fy) & (ex > fx + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ey-(p-2):ex-1), (±  , fx:ey-p, fx))
                    push_range!(t, (sy, ey, ex           ), (sx , fx:ey-p, fx))
                    push_range!(t, (sy, ey, ex+2:ey      ), (!sx, fx:ey-p, fx))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end

            # Lemma 3CD.1
            if diff_sign & (ex == fy + p) & (fx == ey + 1) & (ey < fy + 2)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ey+2:ex      ), (!sy, fy:ex-p, fy))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end
            if diff_sign & (ey == fx + p) & (fy == ex + 1) & (ex < fx + 2)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ex+2:ey      ), (!sx, fx:ey-p, fx))
                    @assert s == t
                end
                lemma_3_count += 1
                verified += 1
            end

            ################################################# LEMMA FAMILY 4 (4)

            # Lemma 4
            if diff_sign & (ex > fy + (p+1)) & (fx < ey + (p+1)) & (ex == fx)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, ex-p:ey-1), (±  , fy:ex-(p+2), fy))
                    push_range!(t, (sx, ex-1:ex-1, ey       ), (sy , fy:ex-(p+2), fy))
                    push_range!(t, (sx, ex-1:ex-1, ey+1     ), (!sy, fy:ex-(p+2), fy))
                    @assert s == t
                end
                lemma_4_count += 1
                verified += 1
            end
            if diff_sign & (ey > fx + (p+1)) & (fy < ex + (p+1)) & (ey == fy)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, ey-p:ex-1), (±  , fx:ey-(p+2), fx))
                    push_range!(t, (sy, ey-1:ey-1, ex       ), (sx , fx:ey-(p+2), fx))
                    push_range!(t, (sy, ey-1:ey-1, ex+1     ), (!sx, fx:ey-(p+2), fx))
                    @assert s == t
                end
                lemma_4_count += 1
                verified += 1
            end

            # Lemma 4A.G
            if diff_sign & (ex == fy + (p+1)) & (fx < ey + p) & (ex == fx)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, ex-(p-1):ey-1), (±  , fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex-1:ex-1, ey           ), (sy , fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex-1:ex-1, ey+1         ), (!sy, fy:ex-(p+1), fy))
                    @assert s == t
                end
                lemma_4_count += 1
                verified += 1
            end
            if diff_sign & (ey == fx + (p+1)) & (fy < ex + p) & (ey == fy)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, ey-(p-1):ex-1), (±  , fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey-1:ey-1, ex           ), (sx , fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey-1:ey-1, ex+1         ), (!sx, fx:ey-(p+1), fx))
                    @assert s == t
                end
                lemma_4_count += 1
                verified += 1
            end

            # Lemma 4A.1
            if diff_sign & (ex == fy + (p+1)) & (fx == ey + p) & (ex == fx)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, ex-(p-1):ey+1), (!sy, fy:ex-(p+1), fy))
                    @assert s == t
                end
                lemma_4_count += 1
                verified += 1
            end
            if diff_sign & (ey == fx + (p+1)) & (fy == ex + p) & (ey == fy)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, ey-(p-1):ex+1), (!sx, fx:ey-(p+1), fx))
                    @assert s == t
                end
                lemma_4_count += 1
                verified += 1
            end

            # Lemma 4B
            if diff_sign & (ex > fy + (p+1)) & (fx == ey + (p+1)) & (ex == fx)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, ex-p:ey+1), (!sy, fy:ex-(p+2), fy))
                    @assert s == t
                end
                lemma_4_count += 1
                verified += 1
            end
            if diff_sign & (ey > fx + (p+1)) & (fy == ex + (p+1)) & (ey == fy)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, ey-p:ex+1), (!sx, fx:ey-(p+2), fx))
                    @assert s == t
                end
                lemma_4_count += 1
                verified += 1
            end

        end
        @assert isone(verified)
    end

    println("    Lemma Z: ", lemma_z_count)
    println("    Lemma I: ", lemma_i_count)
    println("    Lemma F: ", lemma_f_count)
    println("    Lemma E: ", lemma_e_count)
    println("    Lemma O: ", lemma_o_count)
    println("    Lemma 1: ", lemma_1_count)
    println("    Lemma 2: ", lemma_2_count)
    println("    Lemma 3: ", lemma_3_count)
    println("    Lemma 4: ", lemma_4_count)

    @assert (
        lemma_z_count + lemma_i_count +
        lemma_f_count + lemma_e_count + lemma_o_count +
        lemma_1_count + lemma_2_count + lemma_3_count + lemma_4_count
    ) == length(summaries)^2
end


println("\nFloat16 (sign + exponent):")
main(
    Float16,
    FLOAT16_POSITIVE_ZERO_SHORT_SUMMARY,
    FLOAT16_NEGATIVE_ZERO_SHORT_SUMMARY,
    FLOAT16_SHORT_SUMMARIES,
    FLOAT16_SHORT_TWO_SUM_SUMMARIES,
)


println("\nBFloat16 (sign + exponent):")
main(
    BFloat16,
    BFLOAT16_POSITIVE_ZERO_SHORT_SUMMARY,
    BFLOAT16_NEGATIVE_ZERO_SHORT_SUMMARY,
    BFLOAT16_SHORT_SUMMARIES,
    BFLOAT16_SHORT_TWO_SUM_SUMMARIES,
)


println("\nFloat16 (sign + exponent + trailing zeros):")
main(
    Float16,
    FLOAT16_POSITIVE_ZERO_MEDIUM_SUMMARY,
    FLOAT16_NEGATIVE_ZERO_MEDIUM_SUMMARY,
    FLOAT16_MEDIUM_SUMMARIES,
    FLOAT16_MEDIUM_TWO_SUM_SUMMARIES,
)


println("\nBFloat16 (sign + exponent + trailing zeros):")
main(
    BFloat16,
    BFLOAT16_POSITIVE_ZERO_MEDIUM_SUMMARY,
    BFLOAT16_NEGATIVE_ZERO_MEDIUM_SUMMARY,
    BFLOAT16_MEDIUM_SUMMARIES,
    BFLOAT16_MEDIUM_TWO_SUM_SUMMARIES,
)
