using JLD2


const FloatSummary = Tuple{Bool,Int8,Int8,Int8,Int8,Int8}
const PairSummary = Tuple{FloatSummary,FloatSummary}


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
@inline summarize(x::Float32) = summarize(x, UInt32)
@inline summarize(x::Float64) = summarize(x, UInt64)


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
@inline all_summaries(::Type{Float32}) = all_summaries(Float32, UInt32)
@inline all_summaries(::Type{Float64}) = all_summaries(Float64, UInt64)


const FLOAT16_POSITIVE_ZERO_SUMMARY = summarize(zero(Float16))
const FLOAT16_NEGATIVE_ZERO_SUMMARY = summarize(-zero(Float16))
const FLOAT16_SUMMARIES = all_summaries(Float16)


function all_two_sum_summaries(::Type{T}, ::Type{U}) where {T,U}
    result = Set{Tuple{PairSummary,PairSummary}}()
    for i = typemin(U):typemax(U)
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
    end
    return sort!(collect(result))
end


if !isfile("Float16TwoSumSummaries.jld2")
    save_object("Float16TwoSumSummaries.jld2",
        all_two_sum_summaries(Float16, UInt16))
end


const FLOAT16_TWO_SUM_SUMMARIES = load_object("Float16TwoSumSummaries.jld2")
@assert FLOAT16_TWO_SUM_SUMMARIES isa Vector{Tuple{PairSummary,PairSummary}}
@assert length(FLOAT16_TWO_SUM_SUMMARIES) == 319_985_950
@assert issorted(FLOAT16_TWO_SUM_SUMMARIES)


# using BFloat16s
# @inline summarize(x::BFloat16) = summarize(x, UInt16)
# @inline Base.issubnormal(x::BFloat16) = issubnormal(Float32(x))
# @inline all_summaries(::Type{BFloat16}) = all_summaries(BFloat16, UInt16)
# const BFLOAT16_SUMMARIES = all_summaries(BFloat16, UInt16)
# if !isfile("BFloat16TwoSumSummaries.jld2")
#     save_object("BFloat16TwoSumSummaries.jld2",
#         all_two_sum_summaries(BFloat16, UInt16))
# end


lookup_summaries(
    s::AbstractVector{Tuple{PairSummary,PairSummary}},
    rx::FloatSummary,
    ry::FloatSummary,
) = last.(view(s, searchsorted(s, ((rx, ry), (rx, ry)); by=first)))


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
    unhandled = 0
    p = Int8(precision(Float16))
    for rx in summaries
        for ry in summaries
            s = lookup_summaries(two_sum_summaries, rx, ry)
            (sx, ex, zx, ox, mx, nx) = rx
            (sy, ey, zy, oy, my, ny) = ry

            if (rx == pos_zero) && (ry == pos_zero)
                @assert only(s) == (pos_zero, pos_zero)
            elseif (rx == pos_zero) && (ry == neg_zero)
                @assert only(s) == (pos_zero, pos_zero)
            elseif (rx == neg_zero) && (ry == pos_zero)
                @assert only(s) == (pos_zero, pos_zero)
            elseif (rx == neg_zero) && (ry == neg_zero)
                @assert only(s) == (neg_zero, pos_zero)

            elseif ry == pos_zero
                @assert only(s) == (rx, pos_zero)
            elseif ry == neg_zero
                @assert only(s) == (rx, pos_zero)
            elseif rx == pos_zero
                @assert only(s) == (ry, pos_zero)
            elseif rx == neg_zero
                @assert only(s) == (ry, pos_zero)

            elseif ex - (p + 1) > ey
                @assert only(s) == (rx, ry)
            elseif ex < ey - (p + 1)
                @assert only(s) == (ry, rx)
            elseif (ex - (p + 1) == ey) && ((sx == sy) || (nx != 0) ||
                                            ((nx == 0) && (ny == 0)))
                @assert only(s) == (rx, ry)
            elseif (ex == ey - (p + 1)) && ((sx == sy) || (ny != 0) ||
                                            ((nx == 0) && (ny == 0)))
                @assert only(s) == (ry, rx)

            elseif ((sx == sy) &&
                    (ex - ey < p - 1) &&
                    (ox > 0) &&
                    (ox < mx - 1) &&
                    (mx < ex - ey) &&
                    (zy >= p - (ex - ey)) &&
                    (zy < my) &&
                    (my < p - 1))
                rs = (sx, ex, _zero, ox, ex - ey, p - _one)
                ee = ey - (zy + _one)
                me = p - _one
                ne = p - (zy + _two)
                result = PairSummary[]
                if ee >= exponent(floatmin(Float16))
                    for oe = _one:my-(zy+_two)
                        push!(result, (rs, (sx, ee, _zero, oe, me, ne)))
                    end
                    for ze = _one:my-(zy+_three)
                        push!(result, (rs, (sx, ee, ze, _zero, me, ne)))
                    end
                    push!(result, (rs, (sx, ee, my - (zy + _one), _zero, me, ne)))
                end
                @assert s == result

            else
                unhandled += 1
                if length(s) == 1
                    (rs, re) = only(s)
                    if (rs == rx && re == ry) || (rs == ry && re == rx)
                        @show (rx, ry)
                        @show (rs, re)
                    end
                end
            end
        end
    end

    println(unhandled, " out of ", length(summaries)^2, " cases unhandled.")
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
