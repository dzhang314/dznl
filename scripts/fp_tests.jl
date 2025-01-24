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
        exponent(floatmin(T)) - (precision(T) - 1),
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
        else #################################################### NONZERO LEMMAS

            ############################################## MASTER LEMMA FAMILIES

            # Lemmas 1, 2, and 3 are "Master Lemmas." Their hypotheses only
            # contain inequalities in the exponent variables (ex, fx, ey, fy).
            # This means that they apply to a full-dimensional region of the
            # input space as opposed to a lower-dimensional subspace.

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
