using Base.Threads
using BFloat16s
using JLD2
using ProgressMeter


const FloatSummary = Tuple{Bool,Int8,Int8,Int8,Int8,Int8}
const PairSummary = Tuple{FloatSummary,FloatSummary}
const ShortFloatSummary = Tuple{Bool,Int8}
const ShortPairSummary = Tuple{ShortFloatSummary,ShortFloatSummary}


@inline function summarize(x::T, ::Type{U}) where {T,U}
    _bit_size = 8 * sizeof(T)
    _mantissa_width = precision(T) - 1
    _sign_exponent_width = _bit_size - _mantissa_width
    _exponent_width = _sign_exponent_width - 1
    _one = one(U)
    _exponent_mask = ((_one << _exponent_width) - _one) << _mantissa_width
    _exponent_bias = (1 << (_exponent_width - 1)) - 1
    _mantissa_mask = (_one << _mantissa_width) - _one
    _shifted_mask = _mantissa_mask << _sign_exponent_width
    k = reinterpret(U, x)
    return (signbit(x),
        Int8(Int((k & _exponent_mask) >> _mantissa_width) - _exponent_bias),
        Int8(leading_zeros((k << _sign_exponent_width) | ~_shifted_mask)),
        Int8(leading_ones((k << _sign_exponent_width) & _shifted_mask)),
        Int8(_mantissa_width - trailing_ones(k & _mantissa_mask)),
        Int8(_mantissa_width - trailing_zeros(k | ~_mantissa_mask)))
end


@inline summarize(x::Float16) = summarize(x, UInt16)
@inline summarize(x::BFloat16) = summarize(x, UInt16)
@inline summarize(x::Float32) = summarize(x, UInt32)
@inline summarize(x::Float64) = summarize(x, UInt64)


@inline Base.issubnormal(x::BFloat16) = issubnormal(Float32(x))
@inline isnormal(x) = isfinite(x) & ~issubnormal(x)


function all_summaries(::Type{T}, ::Type{U}) where {T,U}
    result = Set{FloatSummary}()
    for i = typemin(U):typemax(U)
        x = reinterpret(T, i)
        if isnormal(x)
            push!(result, summarize(x, U))
        end
    end
    return sort!(collect(result))
end


@inline all_summaries(::Type{Float16}) = all_summaries(Float16, UInt16)
@inline all_summaries(::Type{BFloat16}) = all_summaries(BFloat16, UInt16)
@inline all_summaries(::Type{Float32}) = all_summaries(Float32, UInt32)
@inline all_summaries(::Type{Float64}) = all_summaries(Float64, UInt64)


const FLOAT16_POSITIVE_ZERO_SUMMARY = summarize(zero(Float16))
const FLOAT16_NEGATIVE_ZERO_SUMMARY = summarize(-zero(Float16))
const FLOAT16_SUMMARIES = all_summaries(Float16)
@assert FLOAT16_POSITIVE_ZERO_SUMMARY in FLOAT16_SUMMARIES
@assert FLOAT16_NEGATIVE_ZERO_SUMMARY in FLOAT16_SUMMARIES
@assert length(FLOAT16_SUMMARIES) == 8882
@assert issorted(FLOAT16_SUMMARIES)
const FLOAT16_POSITIVE_ZERO_SHORT_SUMMARY =
    FLOAT16_POSITIVE_ZERO_SUMMARY[1:2]
const FLOAT16_NEGATIVE_ZERO_SHORT_SUMMARY =
    FLOAT16_NEGATIVE_ZERO_SUMMARY[1:2]
const FLOAT16_SHORT_SUMMARIES =
    sort!(collect(Set(s[1:2] for s in FLOAT16_SUMMARIES)))
@assert FLOAT16_POSITIVE_ZERO_SHORT_SUMMARY in FLOAT16_SHORT_SUMMARIES
@assert FLOAT16_NEGATIVE_ZERO_SHORT_SUMMARY in FLOAT16_SHORT_SUMMARIES
@assert length(FLOAT16_SHORT_SUMMARIES) == 2 * (
    exponent(floatmax(Float16)) - exponent(floatmin(Float16)) + 2)
@assert issorted(FLOAT16_SHORT_SUMMARIES)


const BFLOAT16_POSITIVE_ZERO_SUMMARY = summarize(zero(BFloat16))
const BFLOAT16_NEGATIVE_ZERO_SUMMARY = summarize(-zero(BFloat16))
const BFLOAT16_SUMMARIES = all_summaries(BFloat16)
@assert BFLOAT16_POSITIVE_ZERO_SUMMARY in BFLOAT16_SUMMARIES
@assert BFLOAT16_NEGATIVE_ZERO_SUMMARY in BFLOAT16_SUMMARIES
@assert length(BFLOAT16_SUMMARIES) == 32514
@assert issorted(BFLOAT16_SUMMARIES)
const BFLOAT16_POSITIVE_ZERO_SHORT_SUMMARY =
    BFLOAT16_POSITIVE_ZERO_SUMMARY[1:2]
const BFLOAT16_NEGATIVE_ZERO_SHORT_SUMMARY =
    BFLOAT16_NEGATIVE_ZERO_SUMMARY[1:2]
const BFLOAT16_SHORT_SUMMARIES =
    sort!(collect(Set(s[1:2] for s in BFLOAT16_SUMMARIES)))
@assert BFLOAT16_POSITIVE_ZERO_SHORT_SUMMARY in BFLOAT16_SHORT_SUMMARIES
@assert BFLOAT16_NEGATIVE_ZERO_SHORT_SUMMARY in BFLOAT16_SHORT_SUMMARIES
@assert length(BFLOAT16_SHORT_SUMMARIES) == 2 * (
    exponent(floatmax(BFloat16)) - exponent(floatmin(BFloat16)) + 2)
@assert issorted(BFLOAT16_SHORT_SUMMARIES)


function summary_to_string(
    ::Type{T},
    (s, e, z, o, m, n)::FloatSummary,
) where {T}

    p = precision(T)
    e_max = exponent(floatmax(T))
    e_min = exponent(floatmin(T))
    result = ['0' for _ = 1:(e_max-e_min+p)]

    if e >= e_min
        mantissa = ['?' for _ = 1:p-1]

        # z: number of leading zeros
        for i = 1:z
            @assert (mantissa[i] == '?') || (mantissa[i] == '0')
            mantissa[i] = '0'
        end
        if z + 1 < p
            @assert (mantissa[z+1] == '?') || (mantissa[z+1] == '1')
            mantissa[z+1] = '1'
        end

        # o: number of leading ones
        for i = 1:o
            @assert (mantissa[i] == '?') || (mantissa[i] == '1')
            mantissa[i] = '1'
        end
        if o + 1 < p
            @assert (mantissa[o+1] == '?') || (mantissa[o+1] == '0')
            mantissa[o+1] = '0'
        end

        # m: index of final zero
        if m > 0
            @assert (mantissa[m] == '?') || (mantissa[m] == '0')
            mantissa[m] = '0'
        end
        for i = m+1:p-1
            @assert (mantissa[i] == '?') || (mantissa[i] == '1')
            mantissa[i] = '1'
        end

        # n: index of final one
        if n > 0
            @assert (mantissa[n] == '?') || (mantissa[n] == '1')
            mantissa[n] = '1'
        end
        for i = n+1:p-1
            @assert (mantissa[i] == '?') || (mantissa[i] == '0')
            mantissa[i] = '0'
        end

        result[e_max-e+1] = '1'
        result[e_max-e+2:e_max-e+p] .= mantissa
    end

    return (s ? '-' : '+') * String(result)
end


function all_two_sum_summaries(::Type{T}, ::Type{U}) where {T,U}
    results = [Set{Tuple{PairSummary,PairSummary}}() for _ = 1:nthreads()]
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
                                (summarize(x), summarize(y)),
                                (summarize(s), summarize(e))))
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


if !isfile("Float16TwoSumSummaries.jld2")
    println("Computing Float16TwoSumSummaries.jld2...")
    flush(stdout)
    save_object("Float16TwoSumSummaries.jld2",
        all_two_sum_summaries(Float16, UInt16))
end


println("Loading Float16TwoSumSummaries.jld2...")
flush(stdout)
const FLOAT16_TWO_SUM_SUMMARIES = load_object(
    "Float16TwoSumSummaries.jld2")
@assert FLOAT16_TWO_SUM_SUMMARIES isa Vector{
    Tuple{PairSummary,PairSummary}}
@assert length(FLOAT16_TWO_SUM_SUMMARIES) == 319_985_950
@assert issorted(FLOAT16_TWO_SUM_SUMMARIES)
const FLOAT16_SHORT_TWO_SUM_SUMMARIES = sort!(collect(Set(
    (((sx, ex), (sy, ey)), ((ss, es), (se, ee))) for (
        ((sx, ex, _, _, _, _), (sy, ey, _, _, _, _)),
        ((ss, es, _, _, _, _), (se, ee, _, _, _, _))
    ) in FLOAT16_TWO_SUM_SUMMARIES)))
@assert FLOAT16_SHORT_TWO_SUM_SUMMARIES isa Vector{
    Tuple{ShortPairSummary,ShortPairSummary}}
@assert length(FLOAT16_SHORT_TWO_SUM_SUMMARIES) == 38_638
@assert issorted(FLOAT16_SHORT_TWO_SUM_SUMMARIES)
println("Successfully loaded Float16TwoSumSummaries.jld2.")
flush(stdout)


if !isfile("BFloat16TwoSumSummaries.jld2")
    println("Computing BFloat16TwoSumSummaries.jld2...")
    flush(stdout)
    save_object("BFloat16TwoSumSummaries.jld2",
        all_two_sum_summaries(BFloat16, UInt16))
end


println("Loading BFloat16TwoSumSummaries.jld2...")
flush(stdout)
const BFLOAT16_TWO_SUM_SUMMARIES = load_object(
    "BFloat16TwoSumSummaries.jld2")
@assert BFLOAT16_TWO_SUM_SUMMARIES isa Vector{
    Tuple{PairSummary,PairSummary}}
@assert length(BFLOAT16_TWO_SUM_SUMMARIES) == 1_172_449_766
@assert issorted(BFLOAT16_TWO_SUM_SUMMARIES)
const BFLOAT16_SHORT_TWO_SUM_SUMMARIES = sort!(collect(Set(
    (((sx, ex), (sy, ey)), ((ss, es), (se, ee))) for (
        ((sx, ex, _, _, _, _), (sy, ey, _, _, _, _)),
        ((ss, es, _, _, _, _), (se, ee, _, _, _, _))
    ) in BFLOAT16_TWO_SUM_SUMMARIES)))
@assert BFLOAT16_SHORT_TWO_SUM_SUMMARIES isa Vector{
    Tuple{ShortPairSummary,ShortPairSummary}}
@assert length(BFLOAT16_SHORT_TWO_SUM_SUMMARIES) == 548_026
@assert issorted(BFLOAT16_SHORT_TWO_SUM_SUMMARIES)
println("Successfully loaded BFloat16TwoSumSummaries.jld2.")
flush(stdout)


lookup_summaries(
    s::AbstractVector{Tuple{PairSummary,PairSummary}},
    rx::FloatSummary,
    ry::FloatSummary,
) = last.(view(s, searchsorted(s, ((rx, ry), (rx, ry)); by=first)))


lookup_summaries(
    s::AbstractVector{Tuple{ShortPairSummary,ShortPairSummary}},
    rx::ShortFloatSummary,
    ry::ShortFloatSummary,
) = last.(view(s, searchsorted(s, ((rx, ry), (rx, ry)); by=first)))


struct RangePusher
    e_min::Int
    e_max::Int
end


function (rp::RangePusher)(
    v::Vector{ShortPairSummary},
    ss::Bool,
    es_range::AbstractRange,
    se::Bool,
    ee::Integer,
)
    for es in es_range
        if rp.e_min <= es <= rp.e_max
            push!(v, ((ss, es), (se, ee)))
        end
    end
    return v
end


function (rp::RangePusher)(
    v::Vector{ShortPairSummary},
    ss::Bool,
    es::Integer,
    se::Bool,
    ee_range::AbstractRange,
)
    for ee in ee_range
        if rp.e_min <= ee <= rp.e_max
            push!(v, ((ss, es), (se, ee)))
        end
    end
    return v
end


function (rp::RangePusher)(
    v::Vector{ShortPairSummary},
    ss::Bool,
    es_range::AbstractRange,
    se::Bool,
    ee_range::AbstractRange,
)
    for es in es_range
        if rp.e_min <= es <= rp.e_max
            for ee in ee_range
                if rp.e_min <= ee <= rp.e_max
                    push!(v, ((ss, es), (se, ee)))
                end
            end
        end
    end
    return v
end


@inline (rp::RangePusher)(v, (ss, es), (se, ee)) = rp(v, ss, es, se, ee)


function main(
    ::Type{T},
    pos_zero::ShortFloatSummary,
    neg_zero::ShortFloatSummary,
    summaries::Vector{ShortFloatSummary},
    two_sum_summaries::Vector{Tuple{ShortPairSummary,ShortPairSummary}},
) where {T}

    p = precision(T)
    e_min = exponent(floatmin(T))
    e_max = exponent(floatmax(T))
    push_range! = RangePusher(e_min, e_max)

    for rx in summaries
        for ry in summaries

            (sx, ex) = rx
            (sy, ey) = ry
            s = lookup_summaries(two_sum_summaries, rx, ry)

            if false

                #===============================================================
                    CASE 0: One or both inputs are (positive or negative) zero.
                ===============================================================#

            elseif (rx == pos_zero) & (ry == pos_zero)
                @assert only(s) == (pos_zero, pos_zero)
            elseif (rx == pos_zero) & (ry == neg_zero)
                @assert only(s) == (pos_zero, pos_zero)
            elseif (rx == neg_zero) & (ry == pos_zero)
                @assert only(s) == (pos_zero, pos_zero)
            elseif (rx == neg_zero) & (ry == neg_zero)
                @assert only(s) == (neg_zero, pos_zero)
            elseif (rx == pos_zero) | (rx == neg_zero)
                @assert only(s) == (ry, pos_zero)
            elseif (ry == pos_zero) | (ry == neg_zero)
                @assert only(s) == (rx, pos_zero)

                #===============================================================
                    CASE 1: Both inputs are nonzero
                    and separated by at least 2 bits.
                ===============================================================#

            elseif ex > ey + p + 1
                @assert only(s) == (rx, ry)
            elseif ex + p + 1 < ey
                @assert only(s) == (ry, rx)

                #===============================================================
                    CASE 2: Both inputs are nonzero
                    and separated by exactly 1 bit.
                ===============================================================#

            elseif (ex == ey + p + 1) & (sx == sy)
                @assert only(s) == (rx, ry)
            elseif (ex + p + 1 == ey) & (sx == sy)
                @assert only(s) == (ry, rx)
            elseif (ex == ey + p + 1) & (sx != sy)
                let t = [(rx, ry)]
                    push_range!(t, (sx, ex - 1), (!sy, ey-(p-1):ey-1))
                    @assert s == sort!(t)
                end
            elseif (ex + p + 1 == ey) & (sx != sy)
                let t = [(ry, rx)]
                    push_range!(t, (sy, ey - 1), (!sx, ex-(p-1):ex-1))
                    @assert s == sort!(t)
                end

                #===============================================================
                    CASE 3: Both inputs are nonzero
                    and separated by exactly 0 bits.
                ===============================================================#

            elseif (ex == ey + p) & (sx == sy)
                let t = [(rx, ry)]
                    push_range!(t, (sx, ex:ex+1), (!sy, ey-(p-1):ey))
                    @assert s == sort!(t)
                end
            elseif (ex + p == ey) & (sx == sy)
                let t = [(ry, rx)]
                    push_range!(t, (sy, ey:ey+1), (!sx, ex-(p-1):ex))
                    @assert s == sort!(t)
                end
            elseif (ex == ey + p) & (sx != sy)
                let t = [(rx, ry)]
                    push!(t, ((sx, ex - 1), pos_zero))
                    push_range!(t, (sx, ex - 1), (sy, ey-(p-1):ey-2))
                    push_range!(t, (sx, ex - 1), (!sy, ey-(p-1):ey-1))
                    push_range!(t, (sx, ex), (!sy, ey-(p-1):ey))
                    @assert s == sort!(t)
                end
            elseif (ex + p == ey) & (sx != sy)
                let t = [(ry, rx)]
                    push!(t, ((sy, ey - 1), pos_zero))
                    push_range!(t, (sy, ey - 1), (sx, ex-(p-1):ex-2))
                    push_range!(t, (sy, ey - 1), (!sx, ex-(p-1):ex-1))
                    push_range!(t, (sy, ey), (!sx, ex-(p-1):ex))
                    @assert s == sort!(t)
                end

                #===============================================================
                    CASE N: Both inputs are nonzero
                    and have the same exponent.
                ===============================================================#

            elseif (ex == ey) & (sx == sy)
                let t = ShortPairSummary[]
                    if ex < e_max
                        push!(t, ((sx, ex + 1), pos_zero))
                        push_range!(t, (sx, ex + 1), (false, ex-(p-1):ex-(p-1)))
                        push_range!(t, (sx, ex + 1), (true, ex-(p-1):ex-(p-1)))
                    end
                    @assert s == t
                end
            elseif (ex == ey) & (sx != sy)
                let t = [(pos_zero, pos_zero)]
                    push_range!(t, (false, ex-(p-1):ex-1), pos_zero)
                    push_range!(t, (true, ex-(p-1):ex-1), pos_zero)
                    @assert s == t
                end

            else
                println((rx, ry), " : ", length(s))
            end
        end
    end
end


main(
    Float16,
    FLOAT16_POSITIVE_ZERO_SHORT_SUMMARY,
    FLOAT16_NEGATIVE_ZERO_SHORT_SUMMARY,
    FLOAT16_SHORT_SUMMARIES,
    FLOAT16_SHORT_TWO_SUM_SUMMARIES,
)


main(
    BFloat16,
    BFLOAT16_POSITIVE_ZERO_SHORT_SUMMARY,
    BFLOAT16_NEGATIVE_ZERO_SHORT_SUMMARY,
    BFLOAT16_SHORT_SUMMARIES,
    BFLOAT16_SHORT_TWO_SUM_SUMMARIES,
)


#=


function main(
    ::Type{T},
    pos_zero::FloatSummary,
    neg_zero::FloatSummary,
    summaries::Vector{FloatSummary},
    two_sum_summaries::Vector{Tuple{PairSummary,PairSummary}},
) where {T}

    _zero = zero(Int8)
    _one = one(Int8)
    _two = _one + _one
    _three = _two + _one

    _p = Int8(precision(T))
    _e_min = exponent(floatmin(T))

    handled_zero = Atomic{Int}(0)
    handled_nonoverlapping = Atomic{Int}(0)
    handled_test_case = Atomic{Int}(0)

    unhandled_none = Atomic{Int}(0)
    unhandled_single = Atomic{Int}(0)
    unhandled_multiple = Atomic{Int}(0)

    print_lock = SpinLock()

    @threads :dynamic for rx in summaries
        for ry in summaries
            s = lookup_summaries(two_sum_summaries, rx, ry)
            (sx, ex, zx, ox, mx, nx) = rx
            (sy, ey, zy, oy, my, ny) = ry

            if (rx == pos_zero) && (ry == pos_zero)
                @assert only(s) == (pos_zero, pos_zero)
                atomic_add!(handled_zero, 1)
            elseif (rx == pos_zero) && (ry == neg_zero)
                @assert only(s) == (pos_zero, pos_zero)
                atomic_add!(handled_zero, 1)
            elseif (rx == neg_zero) && (ry == pos_zero)
                @assert only(s) == (pos_zero, pos_zero)
                atomic_add!(handled_zero, 1)
            elseif (rx == neg_zero) && (ry == neg_zero)
                @assert only(s) == (neg_zero, pos_zero)
                atomic_add!(handled_zero, 1)

            elseif ry == pos_zero
                @assert only(s) == (rx, pos_zero)
                atomic_add!(handled_zero, 1)
            elseif ry == neg_zero
                @assert only(s) == (rx, pos_zero)
                atomic_add!(handled_zero, 1)
            elseif rx == pos_zero
                @assert only(s) == (ry, pos_zero)
                atomic_add!(handled_zero, 1)
            elseif rx == neg_zero
                @assert only(s) == (ry, pos_zero)
                atomic_add!(handled_zero, 1)

            elseif ex - (_p + 1) > ey
                @assert only(s) == (rx, ry)
                atomic_add!(handled_nonoverlapping, 1)
            elseif ex < ey - (_p + 1)
                @assert only(s) == (ry, rx)
                atomic_add!(handled_nonoverlapping, 1)
            elseif (ex - (_p + 1) == ey) && ((sx == sy) || (nx != 0) ||
                                             ((nx == 0) && (ny == 0)))
                @assert only(s) == (rx, ry)
                atomic_add!(handled_nonoverlapping, 1)
            elseif (ex == ey - (_p + 1)) && ((sx == sy) || (ny != 0) ||
                                             ((nx == 0) && (ny == 0)))
                @assert only(s) == (ry, rx)
                atomic_add!(handled_nonoverlapping, 1)

            elseif ((sx == sy) &&
                    (ex - ey < _p - 1) &&
                    (ox > 0) &&
                    (ox < mx - 1) &&
                    (mx < ex - ey) &&
                    (zy >= _p - (ex - ey)) &&
                    (zy < my) &&
                    (my < _p - 1))
                rs = (sx, ex, _zero, ox, ex - ey, _p - _one)
                ee = ey - (zy + _one)
                me = _p - _one
                ne = _p - (zy + _two)
                r = PairSummary[]
                if ee >= _e_min
                    for oe = _one:my-(zy+_two)
                        push!(r, (rs, (sx, ee, _zero, oe, me, ne)))
                    end
                    for ze = _one:my-(zy+_three)
                        push!(r, (rs, (sx, ee, ze, _zero, me, ne)))
                    end
                    push!(r, (rs, (sx, ee, my - (zy + _one), _zero, me, ne)))
                end
                @assert r == s
                atomic_add!(handled_test_case, 1)

            elseif ((sx == sy) &&
                    (ey - ex < _p - 1) &&
                    (oy > 0) &&
                    (oy < my - 1) &&
                    (my < ey - ex) &&
                    (zx >= _p - (ey - ex)) &&
                    (zx < mx) &&
                    (mx < _p - 1))
                rs = (sy, ey, _zero, oy, ey - ex, _p - _one)
                ee = ex - (zx + _one)
                me = _p - _one
                ne = _p - (zx + _two)
                r = PairSummary[]
                if ee >= _e_min
                    for oe = _one:mx-(zx+_two)
                        push!(r, (rs, (sy, ee, _zero, oe, me, ne)))
                    end
                    for ze = _one:mx-(zx+_three)
                        push!(r, (rs, (sy, ee, ze, _zero, me, ne)))
                    end
                    push!(r, (rs, (sy, ee, mx - (zx + _one), _zero, me, ne)))
                end
                @assert r == s
                atomic_add!(handled_test_case, 1)

            else
                if isempty(s)
                    atomic_add!(unhandled_none, 1)
                elseif isone(length(s))
                    atomic_add!(unhandled_single, 1)
                else
                    atomic_add!(unhandled_multiple, 1)
                    # if ex >= -5 && ey >= -5
                    #     lock(print_lock) do
                    #         println(summary_to_string(T, rx), ' ', rx)
                    #         println(summary_to_string(T, ry), ' ', ry)
                    #         println()
                    #         for (rs, re) in s
                    #             println(summary_to_string(T, rs), ' ', rs)
                    #             println(summary_to_string(T, re), ' ', re)
                    #             println()
                    #         end
                    #         println('-'^80)
                    #         println()
                    #     end
                    # end
                end
            end
        end
    end

    handled = handled_zero[] + handled_nonoverlapping[] + handled_test_case[]
    unhandled = unhandled_none[] + unhandled_single[] + unhandled_multiple[]
    @assert handled + unhandled == length(summaries)^2

    println(handled, " out of ", length(summaries)^2, " cases handled.")
    println(handled_zero[], " cases with zero inputs.")
    println(handled_nonoverlapping[], " cases with non-overlapping inputs.")
    println(handled_test_case[], " test cases.")

    println(unhandled, " out of ", length(summaries)^2, " cases unhandled.")
    println(unhandled_none[], " cases with no summaries.")
    println(unhandled_single[], " cases with a single summary.")
    println(unhandled_multiple[], " cases with multiple summaries.")
end


main(
    Float16,
    FLOAT16_POSITIVE_ZERO_SUMMARY,
    FLOAT16_NEGATIVE_ZERO_SUMMARY,
    FLOAT16_SUMMARIES,
    FLOAT16_TWO_SUM_SUMMARIES,
)


# function reference_two_sum_summaries(
#     ::Type{T},
#     ::Type{U},
#     sx::FloatSummary,
#     sy::FloatSummary,
# ) where {T,U}
#     result = Set{PairSummary}()
#     for i = typemin(U):typemax(U)
#         x = reinterpret(T, i)
#         if isnormal(x) & (summarize(x) == sx)
#             for j = typemin(U):typemax(U)
#                 y = reinterpret(T, j)
#                 if isnormal(y) & (summarize(y) == sy)
#                     s = x + y
#                     if isnormal(s)
#                         x_eff = s - y
#                         y_eff = s - x_eff
#                         x_err = x - x_eff
#                         y_err = y - y_eff
#                         e = x_err + y_err
#                         if isnormal(e)
#                             push!(result, (summarize(s), summarize(e)))
#                         end
#                     end
#                 end
#             end
#         end
#     end
#     return result
# end


=#
