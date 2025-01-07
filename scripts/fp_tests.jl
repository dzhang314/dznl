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


@inline Base.issubnormal(x::BFloat16) = issubnormal(Float32(x))
@inline isnormal(x) = isfinite(x) & ~issubnormal(x)


function all_short_summaries(::Type{T}, ::Type{U}) where {T,U}
    result = Set{ShortFloatSummary}()
    for i = typemin(U):typemax(U)
        x = reinterpret(T, i)
        if isnormal(x)
            push!(result, short_summary(x, U))
        end
    end
    return sort!(collect(result))
end


function all_medium_summaries(::Type{T}, ::Type{U}) where {T,U}
    result = Set{MediumFloatSummary}()
    for i = typemin(U):typemax(U)
        x = reinterpret(T, i)
        if isnormal(x)
            push!(result, medium_summary(x, U))
        end
    end
    return sort!(collect(result))
end


function all_long_summaries(::Type{T}, ::Type{U}) where {T,U}
    result = Set{LongFloatSummary}()
    for i = typemin(U):typemax(U)
        x = reinterpret(T, i)
        if isnormal(x)
            push!(result, long_summary(x, U))
        end
    end
    return sort!(collect(result))
end


const FLOAT16_POSITIVE_ZERO_SHORT_SUMMARY =
    short_summary(zero(Float16), UInt16)
const FLOAT16_NEGATIVE_ZERO_SHORT_SUMMARY =
    short_summary(-zero(Float16), UInt16)
const FLOAT16_SHORT_SUMMARIES = all_short_summaries(Float16, UInt16)

@assert FLOAT16_POSITIVE_ZERO_SHORT_SUMMARY in FLOAT16_SHORT_SUMMARIES
@assert FLOAT16_NEGATIVE_ZERO_SHORT_SUMMARY in FLOAT16_SHORT_SUMMARIES
@assert length(FLOAT16_SHORT_SUMMARIES) == 62
@assert issorted(FLOAT16_SHORT_SUMMARIES)


const FLOAT16_POSITIVE_ZERO_MEDIUM_SUMMARY =
    medium_summary(zero(Float16), UInt16)
const FLOAT16_NEGATIVE_ZERO_MEDIUM_SUMMARY =
    medium_summary(-zero(Float16), UInt16)
const FLOAT16_MEDIUM_SUMMARIES = all_medium_summaries(Float16, UInt16)

@assert FLOAT16_POSITIVE_ZERO_MEDIUM_SUMMARY in FLOAT16_MEDIUM_SUMMARIES
@assert FLOAT16_NEGATIVE_ZERO_MEDIUM_SUMMARY in FLOAT16_MEDIUM_SUMMARIES
@assert length(FLOAT16_MEDIUM_SUMMARIES) == 662
@assert issorted(FLOAT16_MEDIUM_SUMMARIES)


const FLOAT16_POSITIVE_ZERO_LONG_SUMMARY =
    long_summary(zero(Float16), UInt16)
const FLOAT16_NEGATIVE_ZERO_LONG_SUMMARY =
    long_summary(-zero(Float16), UInt16)
const FLOAT16_LONG_SUMMARIES = all_long_summaries(Float16, UInt16)

@assert FLOAT16_POSITIVE_ZERO_LONG_SUMMARY in FLOAT16_LONG_SUMMARIES
@assert FLOAT16_NEGATIVE_ZERO_LONG_SUMMARY in FLOAT16_LONG_SUMMARIES
@assert length(FLOAT16_LONG_SUMMARIES) == 8882
@assert issorted(FLOAT16_LONG_SUMMARIES)


const BFLOAT16_POSITIVE_ZERO_SHORT_SUMMARY =
    short_summary(zero(BFloat16), UInt16)
const BFLOAT16_NEGATIVE_ZERO_SHORT_SUMMARY =
    short_summary(-zero(BFloat16), UInt16)
const BFLOAT16_SHORT_SUMMARIES = all_short_summaries(BFloat16, UInt16)

@assert BFLOAT16_POSITIVE_ZERO_SHORT_SUMMARY in BFLOAT16_SHORT_SUMMARIES
@assert BFLOAT16_NEGATIVE_ZERO_SHORT_SUMMARY in BFLOAT16_SHORT_SUMMARIES
@assert length(BFLOAT16_SHORT_SUMMARIES) == 510
@assert issorted(BFLOAT16_SHORT_SUMMARIES)


const BFLOAT16_POSITIVE_ZERO_MEDIUM_SUMMARY =
    medium_summary(zero(BFloat16), UInt16)
const BFLOAT16_NEGATIVE_ZERO_MEDIUM_SUMMARY =
    medium_summary(-zero(BFloat16), UInt16)
const BFLOAT16_MEDIUM_SUMMARIES = all_medium_summaries(BFloat16, UInt16)

@assert BFLOAT16_POSITIVE_ZERO_MEDIUM_SUMMARY in BFLOAT16_MEDIUM_SUMMARIES
@assert BFLOAT16_NEGATIVE_ZERO_MEDIUM_SUMMARY in BFLOAT16_MEDIUM_SUMMARIES
@assert length(BFLOAT16_MEDIUM_SUMMARIES) == 4066
@assert issorted(BFLOAT16_MEDIUM_SUMMARIES)


const BFLOAT16_POSITIVE_ZERO_LONG_SUMMARY =
    long_summary(zero(BFloat16), UInt16)
const BFLOAT16_NEGATIVE_ZERO_LONG_SUMMARY =
    long_summary(-zero(BFloat16), UInt16)
const BFLOAT16_LONG_SUMMARIES = all_long_summaries(BFloat16, UInt16)

@assert BFLOAT16_POSITIVE_ZERO_LONG_SUMMARY in BFLOAT16_LONG_SUMMARIES
@assert BFLOAT16_NEGATIVE_ZERO_LONG_SUMMARY in BFLOAT16_LONG_SUMMARIES
@assert length(BFLOAT16_LONG_SUMMARIES) == 32514
@assert issorted(BFLOAT16_LONG_SUMMARIES)


function all_short_two_sum_summaries(::Type{T}, ::Type{U}) where {T,U}
    results = [Set{ShortTwoSumSummary}() for _ = 1:nthreads()]
    p = Progress(length(typemin(U):typemax(U)); showspeed=true)
    @threads for i = typemin(U):typemax(U)
        result = results[threadid()]
        x = reinterpret(T, i)
        if isnormal(x)
            for j = typemin(U):typemax(U)
                y = reinterpret(T, j)
                if isnormal(y)
                    s = x + y
                    if isnormal(s)
                        x_eff = s - y
                        y_eff = s - x_eff
                        x_err = x - x_eff
                        y_err = y - y_eff
                        e = x_err + y_err
                        if isnormal(e)
                            push!(result, (
                                (short_summary(x, U), short_summary(y, U)),
                                (short_summary(s, U), short_summary(e, U))))
                        end
                    end
                end
            end
        end
        next!(p)
    end
    finish!(p)
    return sort!(collect(union(results...)))
end


function all_medium_two_sum_summaries(::Type{T}, ::Type{U}) where {T,U}
    results = [Set{MediumTwoSumSummary}() for _ = 1:nthreads()]
    p = Progress(length(typemin(U):typemax(U)); showspeed=true)
    @threads for i = typemin(U):typemax(U)
        result = results[threadid()]
        x = reinterpret(T, i)
        if isnormal(x)
            for j = typemin(U):typemax(U)
                y = reinterpret(T, j)
                if isnormal(y)
                    s = x + y
                    if isnormal(s)
                        x_eff = s - y
                        y_eff = s - x_eff
                        x_err = x - x_eff
                        y_err = y - y_eff
                        e = x_err + y_err
                        if isnormal(e)
                            push!(result, (
                                (medium_summary(x, U), medium_summary(y, U)),
                                (medium_summary(s, U), medium_summary(e, U))))
                        end
                    end
                end
            end
        end
        next!(p)
    end
    finish!(p)
    return sort!(collect(union(results...)))
end


function all_long_two_sum_summaries(::Type{T}, ::Type{U}) where {T,U}
    results = [Set{LongTwoSumSummary}() for _ = 1:nthreads()]
    p = Progress(length(typemin(U):typemax(U)); showspeed=true)
    @threads for i = typemin(U):typemax(U)
        result = results[threadid()]
        x = reinterpret(T, i)
        if isnormal(x)
            for j = typemin(U):typemax(U)
                y = reinterpret(T, j)
                if isnormal(y)
                    s = x + y
                    if isnormal(s)
                        x_eff = s - y
                        y_eff = s - x_eff
                        x_err = x - x_eff
                        y_err = y - y_eff
                        e = x_err + y_err
                        if isnormal(e)
                            push!(result, (
                                (long_summary(x, U), long_summary(y, U)),
                                (long_summary(s, U), long_summary(e, U))))
                        end
                    end
                end
            end
        end
        next!(p)
    end
    finish!(p)
    return sort!(collect(union(results...)))
end


if !isfile("Float16ShortTwoSumSummaries.jld2")
    println("Computing Float16ShortTwoSumSummaries.jld2...")
    flush(stdout)
    save_object("Float16ShortTwoSumSummaries.jld2",
        all_short_two_sum_summaries(Float16, UInt16))
end

println("Loading Float16ShortTwoSumSummaries.jld2...")
flush(stdout)
const FLOAT16_SHORT_TWO_SUM_SUMMARIES = load_object(
    "Float16ShortTwoSumSummaries.jld2")
@assert FLOAT16_SHORT_TWO_SUM_SUMMARIES isa Vector{ShortTwoSumSummary}
@assert length(FLOAT16_SHORT_TWO_SUM_SUMMARIES) == 38_638
@assert issorted(FLOAT16_SHORT_TWO_SUM_SUMMARIES)
println("Successfully loaded Float16ShortTwoSumSummaries.jld2.")
flush(stdout)


if !isfile("Float16MediumTwoSumSummaries.jld2")
    println("Computing Float16MediumTwoSumSummaries.jld2...")
    flush(stdout)
    save_object("Float16MediumTwoSumSummaries.jld2",
        all_medium_two_sum_summaries(Float16, UInt16))
end

println("Loading Float16MediumTwoSumSummaries.jld2...")
flush(stdout)
const FLOAT16_MEDIUM_TWO_SUM_SUMMARIES = load_object(
    "Float16MediumTwoSumSummaries.jld2")
@assert FLOAT16_MEDIUM_TWO_SUM_SUMMARIES isa Vector{MediumTwoSumSummary}
@assert length(FLOAT16_MEDIUM_TWO_SUM_SUMMARIES) == 3_833_700
@assert issorted(FLOAT16_MEDIUM_TWO_SUM_SUMMARIES)
println("Successfully loaded Float16MediumTwoSumSummaries.jld2.")
flush(stdout)


if "--long-fp16" in ARGS
    if !isfile("Float16LongTwoSumSummaries.jld2")
        println("Computing Float16LongTwoSumSummaries.jld2...")
        flush(stdout)
        save_object("Float16LongTwoSumSummaries.jld2",
            all_long_two_sum_summaries(Float16, UInt16))
    end

    println("Loading Float16LongTwoSumSummaries.jld2...")
    flush(stdout)
    const FLOAT16_LONG_TWO_SUM_SUMMARIES = load_object(
        "Float16LongTwoSumSummaries.jld2")
    @assert FLOAT16_LONG_TWO_SUM_SUMMARIES isa Vector{LongTwoSumSummary}
    @assert length(FLOAT16_LONG_TWO_SUM_SUMMARIES) == 319_985_950
    @assert issorted(FLOAT16_LONG_TWO_SUM_SUMMARIES)
    println("Successfully loaded Float16LongTwoSumSummaries.jld2.")
    flush(stdout)
end


if !isfile("BFloat16ShortTwoSumSummaries.jld2")
    println("Computing BFloat16ShortTwoSumSummaries.jld2...")
    flush(stdout)
    save_object("BFloat16ShortTwoSumSummaries.jld2",
        all_short_two_sum_summaries(BFloat16, UInt16))
end

println("Loading BFloat16ShortTwoSumSummaries.jld2...")
flush(stdout)
const BFLOAT16_SHORT_TWO_SUM_SUMMARIES = load_object(
    "BFloat16ShortTwoSumSummaries.jld2")
@assert BFLOAT16_SHORT_TWO_SUM_SUMMARIES isa Vector{ShortTwoSumSummary}
@assert length(BFLOAT16_SHORT_TWO_SUM_SUMMARIES) == 548_026
@assert issorted(BFLOAT16_SHORT_TWO_SUM_SUMMARIES)
println("Successfully loaded BFloat16ShortTwoSumSummaries.jld2.")
flush(stdout)


if !isfile("BFloat16MediumTwoSumSummaries.jld2")
    println("Computing BFloat16MediumTwoSumSummaries.jld2...")
    flush(stdout)
    save_object("BFloat16MediumTwoSumSummaries.jld2",
        all_medium_two_sum_summaries(BFloat16, UInt16))
end

println("Loading BFloat16MediumTwoSumSummaries.jld2...")
flush(stdout)
const BFLOAT16_MEDIUM_TWO_SUM_SUMMARIES = load_object(
    "BFloat16MediumTwoSumSummaries.jld2")
@assert BFLOAT16_MEDIUM_TWO_SUM_SUMMARIES isa Vector{MediumTwoSumSummary}
@assert length(BFLOAT16_MEDIUM_TWO_SUM_SUMMARIES) == 26_618_866
@assert issorted(BFLOAT16_MEDIUM_TWO_SUM_SUMMARIES)
println("Successfully loaded BFloat16MediumTwoSumSummaries.jld2.")
flush(stdout)


if "--long-bf16" in ARGS
    if !isfile("BFloat16LongTwoSumSummaries.jld2")
        println("Computing BFloat16LongTwoSumSummaries.jld2...")
        flush(stdout)
        save_object("BFloat16LongTwoSumSummaries.jld2",
            all_long_two_sum_summaries(BFloat16, UInt16))
    end

    println("Loading BFloat16LongTwoSumSummaries.jld2...")
    flush(stdout)
    const BFLOAT16_LONG_TWO_SUM_SUMMARIES = load_object(
        "BFloat16LongTwoSumSummaries.jld2")
    @assert BFLOAT16_LONG_TWO_SUM_SUMMARIES isa Vector{LongTwoSumSummary}
    @assert length(BFLOAT16_LONG_TWO_SUM_SUMMARIES) == 1_172_449_766
    @assert issorted(BFLOAT16_LONG_TWO_SUM_SUMMARIES)
    println("Successfully loaded BFloat16LongTwoSumSummaries.jld2.")
    flush(stdout)
end


lookup_summaries(
    s::AbstractVector{ShortTwoSumSummary},
    rx::ShortFloatSummary,
    ry::ShortFloatSummary,
) = last.(view(s, searchsorted(s, ((rx, ry), (rx, ry)); by=first)))


lookup_summaries(
    s::AbstractVector{MediumTwoSumSummary},
    rx::MediumFloatSummary,
    ry::MediumFloatSummary,
) = last.(view(s, searchsorted(s, ((rx, ry), (rx, ry)); by=first)))


lookup_summaries(
    s::AbstractVector{LongTwoSumSummary},
    rx::LongFloatSummary,
    ry::LongFloatSummary,
) = last.(view(s, searchsorted(s, ((rx, ry), (rx, ry)); by=first)))


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


@inline _range_helper(::RangePusher, r::Bool) = r:r
@inline _range_helper_e(::RangePusher, r::Integer) = r:r
@inline _range_helper_f(::RangePusher, r::Integer) = r:r

@inline function _range_helper(::RangePusher, r::UnitRange{Bool})
    @assert r == false:true
    return r
end

@inline function _range_helper_e(
    rp::RangePusher, r::UnitRange{I}) where {I<:Integer}
    @assert r.start <= r.stop
    return UnitRange{I}(max(I(rp.e_min), r.start), min(I(rp.e_max), r.stop))
end

@inline function _range_helper_f(
    rp::RangePusher, r::UnitRange{I}) where {I<:Integer}
    @assert r.start <= r.stop
    return UnitRange{I}(max(I(rp.f_min), r.start), min(I(rp.f_max), r.stop))
end


function (rp::RangePusher)(
    v::AbstractVector{ShortPairSummary},
    (ss_range, es_range), (se_range, ee_range),
)
    for ss in _range_helper(rp, ss_range)
        for es in _range_helper_e(rp, es_range)
            for se in _range_helper(rp, se_range)
                for ee in _range_helper_e(rp, ee_range)
                    push!(v, ((ss, es), (se, ee)))
                end
            end
        end
    end
    return v
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


function main(
    ::Type{T},
    pos_zero::ShortFloatSummary,
    neg_zero::ShortFloatSummary,
    summaries::AbstractVector{ShortFloatSummary},
    two_sum_summaries::AbstractVector{ShortTwoSumSummary},
) where {T}

    p = precision(T)
    push_range! = RangePusher(T)

    case_0pp_count = 0
    case_0pn_count = 0
    case_0np_count = 0
    case_0nn_count = 0
    case_0x_count = 0
    case_0y_count = 0
    case_1x_count = 0
    case_1y_count = 0
    case_2xs_count = 0
    case_2ys_count = 0
    case_2xd_count = 0
    case_2yd_count = 0
    case_3xs_count = 0
    case_3ys_count = 0
    case_3xd_count = 0
    case_3yd_count = 0
    case_4xs_count = 0
    case_4ys_count = 0
    case_4xd_count = 0
    case_4yd_count = 0
    case_5xs_count = 0
    case_5ys_count = 0
    case_5xd_count = 0
    case_5yd_count = 0
    case_6xs_count = 0
    case_6ys_count = 0
    case_6xd_count = 0
    case_6yd_count = 0
    case_7xs_count = 0
    case_7ys_count = 0
    case_7xd_count = 0
    case_7yd_count = 0
    case_8s_count = 0
    case_8d_count = 0

    for rx in summaries
        for ry in summaries

            (sx, ex) = rx
            (sy, ey) = ry
            s = lookup_summaries(two_sum_summaries, rx, ry)

            if false

                #===========================================
                    CASE 0: One or both inputs are zero.
                ===========================================#

            elseif (rx == pos_zero) & (ry == pos_zero)
                case_0pp_count += 1
                @assert only(s) == (pos_zero, pos_zero)
            elseif (rx == pos_zero) & (ry == neg_zero)
                case_0pn_count += 1
                @assert only(s) == (pos_zero, pos_zero)
            elseif (rx == neg_zero) & (ry == pos_zero)
                case_0np_count += 1
                @assert only(s) == (pos_zero, pos_zero)
            elseif (rx == neg_zero) & (ry == neg_zero)
                case_0nn_count += 1
                @assert only(s) == (neg_zero, pos_zero)
            elseif (ry == pos_zero) | (ry == neg_zero)
                case_0x_count += 1
                @assert only(s) == (rx, pos_zero)
            elseif (rx == pos_zero) | (rx == neg_zero)
                case_0y_count += 1
                @assert only(s) == (ry, pos_zero)

                #===========================================
                    CASE 1: Both inputs are nonzero
                    and separated by at least 2 bits.
                ===========================================#

            elseif ex > ey + p + 1
                case_1x_count += 1
                @assert only(s) == (rx, ry)
            elseif ex + p + 1 < ey
                case_1y_count += 1
                @assert only(s) == (ry, rx)

                #===========================================
                    CASE 2: Both inputs are nonzero
                    and separated by exactly 1 bit.
                ===========================================#

            elseif (ex == ey + p + 1) & (sx == sy)
                case_2xs_count += 1
                @assert only(s) == (rx, ry)
            elseif (ex + p + 1 == ey) & (sx == sy)
                case_2ys_count += 1
                @assert only(s) == (ry, rx)
            elseif (ex == ey + p + 1) & (sx != sy)
                case_2xd_count += 1
                let t = ShortPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1), (!sy, ey-(p-1):ey-1))
                    push!(t, (rx, ry))
                    @assert s == t
                end
            elseif (ex + p + 1 == ey) & (sx != sy)
                case_2yd_count += 1
                let t = ShortPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1), (!sx, ex-(p-1):ex-1))
                    push!(t, (ry, rx))
                    @assert s == t
                end

                #===========================================
                    CASE 3: Both inputs are nonzero
                    and separated by exactly 0 bits.
                ===========================================#

            elseif (ex == ey + p) & (sx == sy)
                case_3xs_count += 1
                let t = [(rx, ry)]
                    push_range!(t, (sx, ex:ex+1), (!sy, ey-(p-1):ey))
                    @assert s == sort!(t)
                end
            elseif (ex + p == ey) & (sx == sy)
                case_3ys_count += 1
                let t = [(ry, rx)]
                    push_range!(t, (sy, ey:ey+1), (!sx, ex-(p-1):ex))
                    @assert s == sort!(t)
                end
            elseif (ex == ey + p) & (sx != sy)
                case_3xd_count += 1
                let t = [(rx, ry)]
                    push!(t, ((sx, ex - 1), pos_zero))
                    push_range!(t, (sx, ex - 1), (sy, ey-(p-1):ey-2))
                    push_range!(t, (sx, ex - 1), (!sy, ey-(p-1):ey-1))
                    push_range!(t, (sx, ex), (!sy, ey-(p-1):ey))
                    @assert s == sort!(t)
                end
            elseif (ex + p == ey) & (sx != sy)
                case_3yd_count += 1
                let t = [(ry, rx)]
                    push!(t, ((sy, ey - 1), pos_zero))
                    push_range!(t, (sy, ey - 1), (sx, ex-(p-1):ex-2))
                    push_range!(t, (sy, ey - 1), (!sx, ex-(p-1):ex-1))
                    push_range!(t, (sy, ey), (!sx, ex-(p-1):ex))
                    @assert s == sort!(t)
                end

                #===========================================
                    CASE 4: Both inputs are nonzero
                    and overlap by exactly 1 bit.
                ===========================================#

            elseif (ex == ey + (p - 1)) & (sx == sy)
                case_4xs_count += 1
                let t = ShortPairSummary[]
                    push_range!(t, (sx, ex:ex+1), pos_zero)
                    push_range!(t, (sx, ex:ex+1),
                        (false:true, ey-(p-1):ey-1))
                    @assert s == sort!(t)
                end
            elseif (ex + (p - 1) == ey) & (sx == sy)
                case_4ys_count += 1
                let t = ShortPairSummary[]
                    push_range!(t, (sy, ey:ey+1), pos_zero)
                    push_range!(t, (sy, ey:ey+1),
                        (false:true, ex-(p-1):ex-1))
                    @assert s == sort!(t)
                end
            elseif (ex == ey + (p - 1)) & (sx != sy)
                case_4xd_count += 1
                let t = ShortPairSummary[]
                    push_range!(t, (sx, ex-1:ex), pos_zero)
                    push_range!(t, (sx, ex-1:ex-1),
                        (false:true, ey-(p-1):ey-2))
                    push_range!(t, (sx, ex:ex),
                        (false:true, ey-(p-1):ey-1))
                    @assert s == sort!(t)
                end
            elseif (ex + (p - 1) == ey) & (sx != sy)
                case_4yd_count += 1
                let t = ShortPairSummary[]
                    push_range!(t, (sy, ey-1:ey), pos_zero)
                    push_range!(t, (sy, ey-1:ey-1),
                        (false:true, ex-(p-1):ex-2))
                    push_range!(t, (sy, ey:ey),
                        (false:true, ex-(p-1):ex-1))
                    @assert s == sort!(t)
                end

                #===========================================
                    CASE 5: Both inputs are nonzero
                    and overlap by exactly 2 bits.
                ===========================================#

            elseif (ex == ey + (p - 2)) & (sx == sy)
                case_5xs_count += 1
                let t = ShortPairSummary[]
                    push_range!(t, (sx, ex:ex+1), pos_zero)
                    push_range!(t, (sx, ex), (sy, ey-(p-1):ey-2))
                    push_range!(t, (sx, ex+1:ex+1), (sy, ey-(p-1):ey-1))
                    push_range!(t, (sx, ex:ex+1), (!sy, ey-(p-1):ey-2))
                    @assert s == sort!(t)
                end
            elseif (ex + (p - 2) == ey) & (sx == sy)
                case_5ys_count += 1
                let t = ShortPairSummary[]
                    push_range!(t, (sy, ey:ey+1), pos_zero)
                    push_range!(t, (sy, ey), (sx, ex-(p-1):ex-2))
                    push_range!(t, (sy, ey+1:ey+1), (sx, ex-(p-1):ex-1))
                    push_range!(t, (sy, ey:ey+1), (!sx, ex-(p-1):ex-2))
                    @assert s == sort!(t)
                end
            elseif (ex == ey + (p - 2)) & (sx != sy)
                case_5xd_count += 1
                let t = ShortPairSummary[]
                    push_range!(t, (sx, ex-1:ex), pos_zero)
                    push_range!(t, (sx, ex-1:ex-1),
                        (false:true, ey-(p-1):ey-3))
                    push_range!(t, (sx, ex:ex),
                        (false:true, ey-(p-1):ey-2))
                    @assert s == sort!(t)
                end
            elseif (ex + (p - 2) == ey) & (sx != sy)
                case_5yd_count += 1
                let t = ShortPairSummary[]
                    push_range!(t, (sy, ey-1:ey), pos_zero)
                    push_range!(t, (sy, ey-1:ey-1),
                        (false:true, ex-(p-1):ex-3))
                    push_range!(t, (sy, ey:ey),
                        (false:true, ex-(p-1):ex-2))
                    @assert s == sort!(t)
                end

                #===========================================
                    CASE 6: Both inputs are nonzero
                    and overlap by 3, 4, ..., p-2 bits.
                ===========================================#

            elseif (2 <= ex - ey <= p - 3) & (sx == sy)
                case_6xs_count += 1
                let t = ShortPairSummary[], k = ex - ey
                    push_range!(t, (sx, ex:ex+1), pos_zero)
                    push_range!(t, (sx, ex:ex),
                        (false:true, ey-(p-1):ey-(p-k)))
                    push_range!(t, (sx, ex+1:ex+1),
                        (false:true, ey-(p-1):ey-(p-(k+1))))
                    @assert s == sort!(t)
                end
            elseif (2 <= ey - ex <= p - 3) & (sx == sy)
                case_6ys_count += 1
                let t = ShortPairSummary[], k = ey - ex
                    push_range!(t, (sy, ey:ey+1), pos_zero)
                    push_range!(t, (sy, ey:ey),
                        (false:true, ex-(p-1):ex-(p-k)))
                    push_range!(t, (sy, ey+1:ey+1),
                        (false:true, ex-(p-1):ex-(p-(k+1))))
                    @assert s == sort!(t)
                end
            elseif (2 <= ex - ey <= p - 3) & (sx != sy)
                case_6xd_count += 1
                let t = ShortPairSummary[], k = ex - ey
                    push_range!(t, (sx, ex-1:ex), pos_zero)
                    push_range!(t, (sx, ex-1:ex-1),
                        (false:true, ey-(p-1):ey-(p-(k-1))))
                    push_range!(t, (sx, ex:ex),
                        (false:true, ey-(p-1):ey-(p-k)))
                    @assert s == sort!(t)
                end
            elseif (2 <= ey - ex <= p - 3) & (sx != sy)
                case_6yd_count += 1
                let t = ShortPairSummary[], k = ey - ex
                    push_range!(t, (sy, ey-1:ey), pos_zero)
                    push_range!(t, (sy, ey-1:ey-1),
                        (false:true, ex-(p-1):ex-(p-(k-1))))
                    push_range!(t, (sy, ey:ey),
                        (false:true, ex-(p-1):ex-(p-k)))
                    @assert s == sort!(t)
                end

                #===========================================
                    CASE 7: Both inputs are nonzero
                    and their exponents differ by 1.
                ===========================================#

            elseif (ex == ey + 1) & (sx == sy)
                case_7xs_count += 1
                let t = ShortPairSummary[]
                    push_range!(t, (sx, ex:ex+1), pos_zero)
                    push_range!(t, (sx, ex:ex),
                        (false:true, ey-(p-1):ey-(p-1)))
                    push_range!(t, (sx, ex+1:ex+1),
                        (false:true, ey-(p-1):ey-(p-2)))
                    @assert s == sort!(t)
                end
            elseif (ex + 1 == ey) & (sx == sy)
                case_7ys_count += 1
                let t = ShortPairSummary[]
                    push_range!(t, (sy, ey:ey+1), pos_zero)
                    push_range!(t, (sy, ey:ey),
                        (false:true, ex-(p-1):ex-(p-1)))
                    push_range!(t, (sy, ey+1:ey+1),
                        (false:true, ex-(p-1):ex-(p-2)))
                    @assert s == sort!(t)
                end
            elseif (ex == ey + 1) & (sx != sy)
                case_7xd_count += 1
                let t = ShortPairSummary[]
                    push_range!(t, (sx, ex-p:ex), pos_zero)
                    push_range!(t, (sx, ex:ex),
                        (false:true, ey-(p-1):ey-(p-1)))
                    @assert s == t
                end
            elseif (ex + 1 == ey) & (sx != sy)
                case_7yd_count += 1
                let t = ShortPairSummary[]
                    push_range!(t, (sy, ey-p:ey), pos_zero)
                    push_range!(t, (sy, ey:ey),
                        (false:true, ex-(p-1):ex-(p-1)))
                    @assert s == t
                end

                #===========================================
                    CASE 8: Both inputs are nonzero
                    and have the same exponent.
                ===========================================#

            elseif (ex == ey) & (sx == sy)
                case_8s_count += 1
                let t = ShortPairSummary[]
                    push_range!(t, (sx, ex+1:ex+1), pos_zero)
                    push_range!(t, (sx, ex+1:ex+1),
                        (false:true, ex-(p-1):ex-(p-1)))
                    @assert s == t
                end
            elseif (ex == ey) & (sx != sy)
                case_8d_count += 1
                let t = [(pos_zero, pos_zero)]
                    push_range!(t, (false, ex-(p-1):ex-1), pos_zero)
                    push_range!(t, (true, ex-(p-1):ex-1), pos_zero)
                    @assert s == t
                end

            else
                @assert false
            end
        end
    end

    @assert isone(case_0pp_count)
    @assert isone(case_0pn_count)
    @assert isone(case_0np_count)
    @assert isone(case_0nn_count)

    println("    Case 0: ", (case_0x_count, case_0y_count))
    println("    Case 1: ", (case_1x_count, case_1y_count))
    println("    Case 2: ",
        (case_2xs_count, case_2ys_count, case_2xd_count, case_2yd_count))
    println("    Case 3: ",
        (case_3xs_count, case_3ys_count, case_3xd_count, case_3yd_count))
    println("    Case 4: ",
        (case_4xs_count, case_4ys_count, case_4xd_count, case_4yd_count))
    println("    Case 5: ",
        (case_5xs_count, case_5ys_count, case_5xd_count, case_5yd_count))
    println("    Case 6: ",
        (case_6xs_count, case_6ys_count, case_6xd_count, case_6yd_count))
    println("    Case 7: ",
        (case_7xs_count, case_7ys_count, case_7xd_count, case_7yd_count))
    println("    Case 8: ", (case_8s_count, case_8d_count))
end


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
    reservoir = ReservoirSampler{Any}(10)
    unhandled_count = 0

    for rx in summaries, ry in summaries
        s = lookup_summaries(two_sum_summaries, rx, ry)
        (sx, ex, fx) = rx
        (sy, ey, fy) = ry
        same_sign = (sx == sy)
        diff_sign = (sx != sy)
        x_zero = (rx == pos_zero) | (rx == neg_zero)
        y_zero = (ry == pos_zero) | (ry == neg_zero)
        x_pow2 = (ex == fx) & !x_zero
        y_pow2 = (ey == fy) & !y_zero
        x_full = (ex == fx + (p - 1))
        y_full = (ey == fy + (p - 1))

        verified = 0

        if x_zero | y_zero
            if x_zero & y_zero & ((rx == pos_zero) | (ry == pos_zero))
                @assert only(s) == (pos_zero, pos_zero)
                verified += 1
            end
            if (rx == neg_zero) & (ry == neg_zero)
                @assert only(s) == (neg_zero, pos_zero)
                verified += 1
            end
            if y_zero & !x_zero
                @assert only(s) == (rx, pos_zero)
                verified += 1
            end
            if x_zero & !y_zero
                @assert only(s) == (ry, pos_zero)
                verified += 1
            end
        else

            ################################# THEOREMS WITH ONLY ONE POSSIBILITY

            if ((ex > ey + (p + 1)) |
                ((ex == ey + (p + 1)) & (same_sign | y_pow2 | !x_pow2)) |
                ((ex == ey + p) & (same_sign | !x_pow2) & y_pow2 & !x_full))
                @assert only(s) == (rx, ry)
                verified += 1
            end
            if ((ex + (p + 1) < ey) |
                ((ex + (p + 1) == ey) & (same_sign | x_pow2 | !y_pow2)) |
                ((ex + p == ey) & (same_sign | !y_pow2) & x_pow2 & !y_full))
                @assert only(s) == (ry, rx)
                verified += 1
            end

            if (ex < fy + p) & (fx > ey) & (same_sign | !x_pow2)
                @assert only(s) == ((sx, ex, fy), pos_zero)
                verified += 1
            end
            if (ey < fx + p) & (fy > ex) & (same_sign | !y_pow2)
                @assert only(s) == ((sy, ey, fx), pos_zero)
                verified += 1
            end

            if diff_sign & (ex == ey) & (fx == fy) & ((ex == fx) | (ex == fx + 1))
                @assert only(s) == (pos_zero, pos_zero)
                verified += 1
            end

            ############################################ THEOREMS WITH ONE RANGE

            # same sign, zero error

            if same_sign & (ex > ey) & (fx < fy) & !x_full
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex:ex+1, fx), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ey > ex) & (fy < fx) & !y_full
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey:ey+1, fy), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & ((ex > ey > fx > fy) | (ex > ey + 1 > fx > fy)) & (ex < fy + (p - 1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex:ex+1, fy), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & ((ey > ex > fy > fx) | (ey > ex + 1 > fy > fx)) & (ey < fx + (p - 1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey:ey+1, fx), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex == fx + 1) & (fx == ey) & (ex < fy + (p - 1)) & !y_pow2
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex+1:ex+1, fy), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ey == fy + 1) & (fy == ex) & (ey < fx + (p - 1)) & !x_pow2
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey+1:ey+1, fx), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex == ey) & (fx == fy) & !(x_pow2 | y_pow2)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex+1:ex+1, fx+1:ex), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex == ey) & (fx != fy) & !(x_full | y_full)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex+1:ex+1, min(fx, fy)), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end

            # same sign, nonzero error

            if same_sign & (ex == ey + p) & !(x_full | y_pow2)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ey+1:ey+1), (!sy, fy:ey-1, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ex + p == ey) & !(y_full | x_pow2)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ex+1:ex+1), (!sx, fx:ex-1, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            # different sign, zero error

            if diff_sign & (ex > fx == ey == fy)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, fx+1:ex), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ey > fy == ex == fx)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, fy+1:ey), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex > ey + 1) & x_pow2 & (ex < fy + (p + 1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, fy), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ey > ex + 1) & y_pow2 & (ey < fx + (p + 1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, fx), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex > ey + 1) & (
                   (fx < fy) |
                   ((fx > fy) & (ex < fy + p) & (fx < ey + 1)))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex, min(fx, fy)), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ey > ex + 1) & (
                   (fy < fx) |
                   ((fy > fx) & (ey < fx + p) & (fy < ex + 1)))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey, min(fx, fy)), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex == ey + 1) & (ey > fy > fx)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, fy:ex, fx), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ex + 1 == ey) & (ex > fx > fy)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, fx:ey, fy), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex == ey + 1) & (ey > fx > fy) & (ex < fy + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, fx:ex, fy), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ex + 1 == ey) & (ex > fy > fx) & (ey < fx + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, fy:ey, fx), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex == ey) & (fx != fy) & (fx + 1 < ex) & (fy + 1 < ey)
                let t = MediumPairSummary[]
                    push_range!(t, (false:true, min(fx, fy):ex-1, min(fx, fy)), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex == ey == fx + 1) & (fy < fx)
                let t = MediumPairSummary[]
                    push_range!(t, (false:true, fy:ex-2, fy), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ex == ey == fy + 1) & (fx < fy)
                let t = MediumPairSummary[]
                    push_range!(t, (false:true, fx:ey-2, fx), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex == fx + 1) & (fx == ey) & (fy < ey)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, fy), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ey == fy + 1) & (fy == ex) & (fx < ex)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, fx), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end

            # different sign, nonzero error

            if diff_sign & (ex == ey + p + 1) & x_pow2 & !y_pow2
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, ex-p:ex-p), (!sy, fy:ey-1, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ex + p + 1 == ey) & y_pow2 & !x_pow2
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, ey-p:ey-p), (!sx, fx:ex-1, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex == ey + p) & x_pow2 & (ey == fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, ex-(p-1):ex-(p-1)), (!sy, fy:ey-1, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ex + p == ey) & y_pow2 & (ex == fx + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, ey-(p-1):ey-(p-1)), (!sx, fx:ex-1, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex == ey + p) & !(x_pow2 | x_full | y_pow2)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ex-(p-1):ex-(p-1)), (!sy, fy:ey-1, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ex + p == ey) & !(y_pow2 | y_full | x_pow2)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ey-(p-1):ey-(p-1)), (!sx, fx:ex-1, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex == ey + p) & x_full & !y_pow2
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, fx+1:ex), (!sy, fy:ey-1, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ex + p == ey) & y_full & !x_pow2
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, fy+1:ey), (!sx, fx:ex-1, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex == ey + p) & x_full & y_pow2
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, fx+1:ex), (!sy, ey, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ex + p == ey) & y_full & x_pow2
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, fy+1:ey), (!sx, ex, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            ########################################### THEOREMS WITH TWO RANGES

            if same_sign & (ex == ey + p) & x_full & !y_pow2
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, fx+1:ex-1), (!sy, fy:ey-1, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex+1:ex+1), (!sy, fy:ey-1, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ex + p == ey) & y_full & !x_pow2
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, fy+1:ey-1), (!sx, fx:ex-1, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey+1:ey+1), (!sx, fx:ex-1, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex == ey + p) & x_full & y_pow2
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, fx+1:ex-1), (!sy, ey, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex+1:ex+1), (!sy, ey, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ex + p == ey) & y_full & x_pow2
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, fy+1:ey-1), (!sx, ex, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey+1:ey+1), (!sx, ex, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex == ey + (p - 1)) & (fx > ey + 1) & (ey > fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ey), (sy, fy:ey-2, fy))
                    push_range!(t, (sx, ex, ey+1:ey+1), (!sy, fy:ey-2, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ey == ex + (p - 1)) & (fy > ex + 1) & (ex > fx + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ex), (sx, fx:ex-2, fx))
                    push_range!(t, (sy, ey, ex + 1), (!sx, fx:ex-2, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex > ey + 1) & (fx == fy) & (ey == fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex, ey), pos_zero)
                    push_range!(t, (sx, ex, ey+1:ex), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ey > ex + 1) & (fy == fx) & (ex == fx + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey, ex), pos_zero)
                    push_range!(t, (sy, ey, ex+1:ey), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex > ey + 1) & (fx == fy) & (ey > fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, fx+1:ey), pos_zero)
                    push_range!(t, (sx, ex, fx+1:ex), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ey > ex + 1) & (fy == fx) & (ex > fx + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, fy+1:ex), pos_zero)
                    push_range!(t, (sy, ey, fy+1:ey), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex > fx > ey + 1) & (ex == ey + (p - 1)) & (ex > fy + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ey), (sy, fy:ey-2, fy))
                    push_range!(t, (sx, ex, ey + 1), (!sy, fy:ey-2, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ey > fy > ex + 1) & (ey == ex + (p - 1)) & (ey > fx + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ex), (sx, fx:ex-2, fx))
                    push_range!(t, (sy, ey, ex + 1), (!sx, fx:ex-2, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex == ey + p) & x_pow2 & (ey > fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, ex-p:ex-p), (sy, fy:ey-2, fy))
                    push_range!(t, (sx, ex-1:ex-1, ex-(p-1):ex-(p-1)), (!sy, fy:ey-2, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ex + p == ey) & y_pow2 & (ex > fx + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, ey-p:ey-p), (sx, fx:ex-2, fx))
                    push_range!(t, (sy, ey-1:ey-1, ey-(p-1):ey-(p-1)), (!sx, fx:ex-2, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex > ey > fx) & (ex == fy + (p + 1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, ex-(p-1):ey), (false:true, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, ex-(p-1):ex), (false:true, fy:ex-(p+1), fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ey > ex > fy) & (ey == fx + (p + 1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, ey-(p-1):ex), (false:true, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, ey-(p-1):ey), (false:true, fx:ey-(p+1), fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex == fx + (p - 2)) & (ex == ey + (p - 1)) & (ex > fy + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ey), (sy, fy:ey-2, fy))
                    push_range!(t, (sx, ex, ey+2:ex), (!sy, fy:ey-2, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ey == fy + (p - 2)) & (ey == ex + (p - 1)) & (ey > fx + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ex), (sx, fx:ex-2, fx))
                    push_range!(t, (sy, ey, ex+2:ey), (!sx, fx:ex-2, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            ######################################### THEOREMS WITH THREE RANGES

            if (ex < ey + (p - 1)) & (ex > fy + p) & (
                   ((ex == fx + 1) & (ex > fy + (p + 1))) |
                   ((fx > ey + 1) & !x_pow2) |
                   (same_sign & x_pow2))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ex-(p-1):ey-1), (false:true, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, ey), (sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, ey+1:ey+1), (!sy, fy:ex-(p+1), fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if (ey < ex + (p - 1)) & (ey > fx + p) & (
                   ((ey == fy + 1) & (ey > fx + (p + 1))) |
                   ((fy > ex + 1) & !y_pow2) |
                   (same_sign & y_pow2))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ey-(p-1):ex-1), (false:true, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, ex), (sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, ex+1:ex+1), (!sx, fx:ey-(p+1), fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex == fy + p) & (ey > fy + 2) & x_pow2 & !y_full
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ex-(p-2):ey-1), (false:true, fy:ex-p, fy))
                    push_range!(t, (sx, ex, ey), (sy, fy:ex-p, fy))
                    push_range!(t, (sx, ex, ey+1:ey+1), (!sy, fy:ex-p, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ey == fx + p) & (ex > fx + 2) & y_pow2 & !x_full
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ey-(p-2):ex-1), (false:true, fx:ey-p, fx))
                    push_range!(t, (sy, ey, ex), (sx, fx:ey-p, fx))
                    push_range!(t, (sy, ey, ex+1:ex+1), (!sx, fx:ey-p, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex > ey + 1) & (fx == fy) & !y_pow2
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, fx+1:ex-1), pos_zero)
                    push_range!(t, (sx, ex+1:ex+1, fx+1:ey), pos_zero)
                    push_range!(t, (sx, ex+1:ex+1, ex+1:ex+1), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ey > ex + 1) & (fx == fy) & !x_pow2
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, fy+1:ey-1), pos_zero)
                    push_range!(t, (sy, ey+1:ey+1, fy+1:ex), pos_zero)
                    push_range!(t, (sy, ey+1:ey+1, ey+1:ey+1), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex == ey + 1) & (fx == fy) & (ey > fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, fx+1:ey-1), pos_zero)
                    push_range!(t, (sx, ex+1:ex+1, fx+1:ey), pos_zero)
                    push_range!(t, (sx, ex+1:ex+1, ex+1:ex+1), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ey == ex + 1) & (fy == fx) & (ex > fx + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, fy+1:ex-1), pos_zero)
                    push_range!(t, (sy, ey+1:ey+1, fy+1:ex), pos_zero)
                    push_range!(t, (sy, ey+1:ey+1, ey+1:ey+1), pos_zero)
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex > ey > fx) & (ex == fy + (p - 1)) & !x_full
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, fy), pos_zero)
                    push_range!(t, (sx, ex+1:ex+1, fy+2:ey), (false:true, fy:ex-(p-1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ex+1:ex+1), (sy, fy:ex-(p-1), fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ey > ex > fy) & (ey == fx + (p - 1)) & !y_full
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, fx), pos_zero)
                    push_range!(t, (sy, ey+1:ey+1, fx+2:ex), (false:true, fx:ey-(p-1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ey+1:ey+1), (sx, fx:ey-(p-1), fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex > ey > fy > fx) & (ex == fx + (p - 1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, fx), pos_zero)
                    push_range!(t, (sx, ex+1:ex+1, fx+2:ey), (false:true, fx:ex-(p-1), fx))
                    push_range!(t, (sx, ex+1:ex+1, ex+1:ex+1), (sy, fx:ex-(p-1), fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ey > ex > fx > fy) & (ey == fy + (p - 1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, fy), pos_zero)
                    push_range!(t, (sy, ey+1:ey+1, fy+2:ex), (false:true, fy:ey-(p-1), fy))
                    push_range!(t, (sy, ey+1:ey+1, ey+1:ey+1), (sx, fy:ey-(p-1), fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex > ey + 1) & (ex == fy + p) & (fx < ey)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ex-(p-2):ex-1), (false:true, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-2):ey), (false:true, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex+1:ex+1), (false:true, fy:ex-p, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ey > ex + 1) & (ey == fx + p) & (fy < ex)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ey-(p-2):ey-1), (false:true, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-2):ex), (false:true, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey+1:ey+1), (false:true, fx:ey-p, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex == ey + (p - 1)) & (fx == ey) & (ey > fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, fx), (!sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, ey+1:ex-1), (sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ex+1:ex+1), (sy, fy:ex-p, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ey == ex + (p - 1)) & (fy == ex) & (ex > fx + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, fy), (!sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, ex+1:ey-1), (sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ey+1:ey+1), (sx, fx:ey-p, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex == ey + (p - 1)) & (ex == fx + (p - 2)) & (ey > fy + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, fx-1:ex-(p-1)), (sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, fx+1:ex-1), (!sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ex+1:ex+1), (!sy, fy:ex-(p+1), fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ey == ex + (p - 1)) & (ey == fy + (p - 2)) & (ex > fx + 1)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, fy-1:ey-(p-1)), (sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, fy+1:ey-1), (!sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ey+1:ey+1), (!sx, fx:ey-(p+1), fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex == fx + 1) & (fx == ey + 1) & (fy < ex - (p - 1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, fy+2:fx-2), (false:true, fy:fy, fy))
                    push_range!(t, (sx, ex, fx-1:fx-1), (sy, fy:fy, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex+1:ex+1), (!sy, fy:fy, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ey == fy + 1) & (fy == ex + 1) & (fx < ey - (p - 1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, fx+2:fy-2), (false:true, fx:fx, fx))
                    push_range!(t, (sy, ey, fy-1:fy-1), (sx, fx:fx, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey+1:ey+1), (!sx, fx:fx, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (fx + 1 < ey) & (ex == ey + 1) & (ex == fy + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ex-(p-2):ey-1), (false:true, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-2):ey), (false:true, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex+1:ex+1), (false:true, fy:ex-p, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (fy + 1 < ex) & (ey == ex + 1) & (ey == fx + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ey-(p-2):ex-1), (false:true, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-2):ex), (false:true, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey+1:ey+1), (false:true, fx:ey-p, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex < ey + p) & x_pow2 & (ex > fy + (p + 1))
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, ex-p:ey-1), (false:true, fy:ex-(p+2), fy))
                    push_range!(t, (sx, ex-1:ex-1, ey), (sy, fy:ex-(p+2), fy))
                    push_range!(t, (sx, ex-1:ex-1, ey+1:ey+1), (!sy, fy:ex-(p+2), fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ey < ex + p) & y_pow2 & (ey > fx + (p + 1))
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, ey-p:ex-1), (false:true, fx:ey-(p+2), fx))
                    push_range!(t, (sy, ey-1:ey-1, ex), (sx, fx:ey-(p+2), fx))
                    push_range!(t, (sy, ey-1:ey-1, ex+1:ex+1), (!sx, fx:ey-(p+2), fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex > ey + 1) & (fx < ey) & (ex == fy + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, fy), pos_zero)
                    push_range!(t, (sx, ex, ex-(p-2):ex-1), (false:true, fy:ex-p, fy))
                    push_range!(t, (sx, ex, ex), (!sy, fy:ex-p, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ey > ex + 1) & (fy < ex) & (ey == fx + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, fx), pos_zero)
                    push_range!(t, (sy, ey, ey-(p-2):ey-1), (false:true, fx:ey-p, fx))
                    push_range!(t, (sy, ey, ey), (!sx, fx:ey-p, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex == ey + 1) & (fx + 1 < ey) & (ex == fy + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, fx:ex-1, fy), pos_zero)
                    push_range!(t, (sx, ex, ex-(p-2):ex-2), (false:true, fy:ex-p, fy))
                    push_range!(t, (sx, ex, ex), (!sy, fy:ex-p, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ey == ex + 1) & (fy + 1 < ex) & (ey == fx + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, fy:ey-1, fx), pos_zero)
                    push_range!(t, (sy, ey, ey-(p-2):ey-2), (false:true, fx:ey-p, fx))
                    push_range!(t, (sy, ey, ey), (!sx, fx:ey-p, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex == ey + (p - 2)) & (fx == ey + 1) & (ex > fy + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ex - (p - 1)), (false:true, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, ey), (sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, fx+1:ex), (!sy, fy:ex-(p+1), fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ey == ex + (p - 2)) & (fy == ex + 1) & (ey > fx + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ey - (p - 1)), (false:true, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, ex), (sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, fy+1:ey), (!sx, fx:ey-(p+1), fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex < ey + (p - 2)) & (fx == ey + 1) & (ex > fy + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ex-(p-1):ey-1), (false:true, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, ey), (sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, fx+1:ex), (!sy, fy:ex-(p+1), fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ey < ex + (p - 2)) & (fy == ex + 1) & (ey > fx + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ey-(p-1):ex-1), (false:true, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, ex), (sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, fy+1:ey), (!sx, fx:ey-(p+1), fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex == fy + p) & (ey > fy + 2) & (fx > ey + 1) & !x_pow2
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, fy+2:ey-1), (false:true, fy:ex-p, fy))
                    push_range!(t, (sx, ex, ey), (sy, fy:ex-p, fy))
                    push_range!(t, (sx, ex, ey + 1), (!sy, fy:ex-p, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ey == fx + p) & (ex > fx + 2) & (fy > ex + 1) & !y_pow2
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, fx+2:ex-1), (false:true, fx:ey-p, fx))
                    push_range!(t, (sy, ey, ex), (sx, fx:ey-p, fx))
                    push_range!(t, (sy, ey, ex + 1), (!sx, fx:ey-p, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            ########################################## THEOREMS WITH FOUR RANGES

            if same_sign & (ex > fy + p) & (fx < ey)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ex-(p-1):ex-1), (false:true, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-2):ey), (false:true, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex+1:ex+1), (!sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ex+1:ex+1), (sy, fy:ex-p, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ey > fx + p) & (fy < ex)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ey-(p-1):ey-1), (false:true, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-2):ex), (false:true, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey+1:ey+1), (!sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ey+1:ey+1), (sx, fx:ey-p, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex > fx + 1) & (fx == ey + 1) & (ex < ey + (p - 1)) & (ex > fy + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ex-(p-1):ey-1), (false:true, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, fx-1:fx-1), (sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, fx+1:ex-1), (!sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ex+1:ex+1), (!sy, fy:ex-(p+1), fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ey > fy + 1) & (fy == ex + 1) & (ey < ex + (p - 1)) & (ey > fx + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ey-(p-1):ex-1), (false:true, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, fy-1:fy-1), (sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, fy+1:ey-1), (!sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ey+1:ey+1), (!sx, fx:ey-(p+1), fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex > ey + 2) & (fx == ey + 1) & (ex < ey + (p - 2)) & (ex == fy + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, fy+2:ey-1), (false:true, fy:ex-p, fy))
                    push_range!(t, (sx, ex, ey), (sy, fy:ex-p, fy))
                    push_range!(t, (sx, ex, fx+1:ex-1), (!sy, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex+1:ex+1), (!sy, fy:ex-p, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ey > ex + 2) & (fy == ex + 1) & (ey < ex + (p - 2)) & (ey == fx + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, fx+2:ex-1), (false:true, fx:ey-p, fx))
                    push_range!(t, (sy, ey, ex), (sx, fx:ey-p, fx))
                    push_range!(t, (sy, ey, fy+1:ey-1), (!sx, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey+1:ey+1), (!sx, fx:ey-p, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex > fy + (p + 1)) & (fx < ey)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, ex-p:ey), (false:true, fy:ex-(p+2), fy))
                    push_range!(t, (sx, ex, ex-(p-1):ex-1), (false:true, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, ex), (sy, fy:ex-(p+2), fy))
                    push_range!(t, (sx, ex, ex), (!sy, fy:ex-(p+1), fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ey > fx + (p + 1)) & (fy < ex)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, ey-p:ex), (false:true, fx:ey-(p+2), fx))
                    push_range!(t, (sy, ey, ey-(p-1):ey-1), (false:true, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, ey), (sx, fx:ey-(p+2), fx))
                    push_range!(t, (sy, ey, ey), (!sx, fx:ey-(p+1), fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            ########################################## THEOREMS WITH FIVE RANGES

            if diff_sign & x_full & (fx == ey) & (ey > fy + 2)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, fx-1:fx-1), (false:true, fy:ex-(p+2), fy))
                    push_range!(t, (sx, ex-1:ex-1, fx), (!sy, fy:ex-(p+2), fy))
                    push_range!(t, (sx, ex, fx), (!sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, fx+1:ex-1), (sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, ex), (sy, fy:ex-(p+2), fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & y_full & (fy == ex) & (ex > fx + 2)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, fy-1:fy-1), (false:true, fx:ey-(p+2), fx))
                    push_range!(t, (sy, ey-1:ey-1, fy), (!sx, fx:ey-(p+2), fx))
                    push_range!(t, (sy, ey, fy), (!sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, fy+1:ey-1), (sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, ey), (sx, fx:ey-(p+2), fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (fx == ey) & (ex == fy + (p + 1)) & !x_full
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, ex-(p-1):fx-1), (false:true, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex-1:ex-1, fx), (!sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, ex-(p-1):fx-1), (false:true, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, fx), (!sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, fx+1:ex), (sy, fy:ex-(p+1), fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (fy == ex) & (ey == fx + (p + 1)) & !y_full
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, ey-(p-1):fy-1), (false:true, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey-1:ey-1, fy), (!sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, ey-(p-1):fy-1), (false:true, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, fy), (!sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, fy+1:ey), (sx, fx:ey-(p+1), fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            ########################################### THEOREMS WITH SIX RANGES

            if diff_sign & (ex > ey) & (fx == ey) & (ex > fy + (p + 1)) & !x_full
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex-1:ex-1, ex-p:fx-1), (false:true, fy:ex-(p+2), fy))
                    push_range!(t, (sx, ex-1:ex-1, fx), (!sy, fy:ex-(p+2), fy))
                    push_range!(t, (sx, ex, ex-(p-1):fx-1), (false:true, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, fx), (!sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, fx+1:ex-1), (sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, ex), (sy, fy:ex-(p+2), fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ey > ex) & (fy == ex) & (ey > fx + (p + 1)) & !y_full
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey-1:ey-1, ey-p:fy-1), (false:true, fx:ey-(p+2), fx))
                    push_range!(t, (sy, ey-1:ey-1, fy), (!sx, fx:ey-(p+2), fx))
                    push_range!(t, (sy, ey, ey-(p-1):fy-1), (false:true, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, fy), (!sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, fy+1:ey-1), (sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, ey), (sx, fx:ey-(p+2), fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex < fx + (p - 2)) & (ex > fy + p) & (fx == ey)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ex-(p-1):fx-1), (false:true, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, fx), (!sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex, fx+1:ex-1), (sy, fy:ex-(p+1), fy))
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-2):fx-1), (false:true, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, fx), (!sy, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex+1:ex+1), (sy, fy:ex-p, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ey < fy + (p - 2)) & (ey > fx + p) & (fy == ex)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ey-(p-1):fy-1), (false:true, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, fy), (!sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey, fy+1:ey-1), (sx, fx:ey-(p+1), fx))
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-2):fy-1), (false:true, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, fy), (!sx, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey+1:ey+1), (sx, fx:ey-p, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if same_sign & (ex > ey + 1) & (ex < fx + (p - 2)) & (fx == ey) & (ex == fy + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sx, ex, ex-(p-2):fx-1), (false:true, fy:ex-p, fy))
                    push_range!(t, (sx, ex, fx), (!sy, fy:ex-p, fy))
                    push_range!(t, (sx, ex, fx+1:ex-1), (sy, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex-(p-2):fx-1), (false:true, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, fx), (!sy, fy:ex-p, fy))
                    push_range!(t, (sx, ex+1:ex+1, ex+1:ex+1), (sy, fy:ex-p, fy))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if same_sign & (ey > ex + 1) & (ey < fy + (p - 2)) & (fy == ex) & (ey == fx + p)
                let t = MediumPairSummary[]
                    push_range!(t, (sy, ey, ey-(p-2):fy-1), (false:true, fx:ey-p, fx))
                    push_range!(t, (sy, ey, fy), (!sx, fx:ey-p, fx))
                    push_range!(t, (sy, ey, fy+1:ey-1), (sx, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey-(p-2):fy-1), (false:true, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, fy), (!sx, fx:ey-p, fx))
                    push_range!(t, (sy, ey+1:ey+1, ey+1:ey+1), (sx, fx:ey-p, fx))
                    @assert s == sort!(t)
                end
                verified += 1
            end

            if diff_sign & (ex == ey + 1) & (ex > fx + 2) & (fx == fy)
                let t = MediumPairSummary[]
                    for k = max(fx + 1, exponent(floatmin(T))):ey
                        push_range!(t, (sx, k, fx+1:k), pos_zero)
                    end
                    push_range!(t, (sx, ex, fx+1:ex-2), pos_zero)
                    push!(t, ((sx, ex, ex), pos_zero))
                    @assert s == sort!(t)
                end
                verified += 1
            end
            if diff_sign & (ex + 1 == ey) & (ey > fy + 2) & (fx == fy)
                let t = MediumPairSummary[]
                    for k = max(fx + 1, exponent(floatmin(T))):ex
                        push_range!(t, (sy, k, fy+1:k), pos_zero)
                    end
                    push_range!(t, (sy, ey, fy+1:ey-2), pos_zero)
                    push!(t, ((sy, ey, ey), pos_zero))
                    @assert s == sort!(t)
                end
                verified += 1
            end
        end

        @assert iszero(verified) | isone(verified)
        if iszero(verified)
            unhandled_count += 1
            # if (ex >= -10) & (fx >= -10) & (ey >= -10) & (fy >= -10) & !isempty(s)
            #     push!(reservoir, (rx, ry, s))
            # end
        end
    end

    println("    Unhandled: ", unhandled_count)

    println()
    for i = 1:min(reservoir.count[], length(reservoir.reservoir))
        data = reservoir.reservoir[i]
        @assert data isa Tuple
        if length(data) == 3
            rx, ry, s = data
            println(rx)
            println(ry)
            for item in s
                println("    ", item)
            end
        elseif length(data) == 4
            rx, ry, s, t = data
            println(rx)
            println(ry)
            println("s:")
            for item in s
                println("    ", item)
            end
            println("t:")
            for item in t
                println("    ", item)
            end
        end
        println()
    end
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
