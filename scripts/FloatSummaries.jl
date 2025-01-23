module FloatSummaries

using Base: uinttype, exponent_bias, exponent_mask,
    significand_bits, significand_mask
using Base.Threads: @threads

using BFloat16s: BFloat16 # needed to extend Base.issubnormal
using ProgressMeter: Progress, next!

################################################################################


export unsafe_exponent,
    mantissa_leading_bit, mantissa_leading_zeros, mantissa_leading_ones,
    mantissa_trailing_bit, mantissa_trailing_zeros, mantissa_trailing_ones


const _BITS_PER_BYTE = div(64, sizeof(UInt64))
@assert _BITS_PER_BYTE * sizeof(UInt64) == 64


@inline function unsafe_exponent(x::T) where {T}
    raw_exponent = reinterpret(Unsigned, x) & exponent_mask(T)
    raw_exponent >>= significand_bits(T)
    return Int(raw_exponent) - exponent_bias(T)
end


@inline mantissa_leading_bit(x::T) where {T} = !iszero(
    (reinterpret(Unsigned, x) >> (significand_bits(T) - 1)) & one(uinttype(T)))


@inline function mantissa_leading_zeros(x::T) where {T}
    shift = _BITS_PER_BYTE * sizeof(T) - significand_bits(T)
    shifted_mask = significand_mask(T) << shift
    return leading_zeros((reinterpret(Unsigned, x) << shift) | ~shifted_mask)
end


@inline function mantissa_leading_ones(x::T) where {T}
    shift = _BITS_PER_BYTE * sizeof(T) - significand_bits(T)
    shifted_mask = significand_mask(T) << shift
    return leading_ones((reinterpret(Unsigned, x) << shift) & shifted_mask)
end


@inline mantissa_trailing_bit(x::T) where {T} = !iszero(
    reinterpret(Unsigned, x) & one(uinttype(T)))


@inline function mantissa_trailing_zeros(x::T) where {T}
    return trailing_zeros(reinterpret(Unsigned, x) | ~significand_mask(T))
end


@inline function mantissa_trailing_ones(x::T) where {T}
    return trailing_ones(reinterpret(Unsigned, x) & significand_mask(T))
end


################################################################################


export FloatSummary, summarize_se, summarize_setz, summarize_seltzo


struct FloatSummary
    data::UInt32
end


@inline function FloatSummary(s::Bool, e::Integer)
    data = UInt32(Int16(e) % UInt16)
    data |= UInt32(s) << 31
    return FloatSummary(data)
end


@inline function summarize_se(x::T) where {T}
    data = UInt32(Int16(unsafe_exponent(x)) % UInt16)
    data |= UInt32(signbit(x)) << 31
    return FloatSummary(data)
end


@inline function summarize_setz(x::T) where {T}
    ntz = mantissa_trailing_zeros(x)
    data = UInt32(Int16(unsafe_exponent(x)) % UInt16)
    data |= UInt32(UInt8(ntz)) << 16
    data |= UInt32(signbit(x)) << 31
    return FloatSummary(data)
end


@inline function summarize_seltzo(x::T) where {T}
    lb = mantissa_leading_bit(x)
    nlb = ifelse(lb, mantissa_leading_ones(x), mantissa_leading_zeros(x))
    tb = mantissa_trailing_bit(x)
    ntb = ifelse(tb, mantissa_trailing_ones(x), mantissa_trailing_zeros(x))
    data = UInt32(Int16(unsafe_exponent(x)) % UInt16)
    data |= UInt32(UInt8(ntb)) << 16
    data |= UInt32(UInt8(nlb)) << 22
    data |= UInt32(tb) << 29
    data |= UInt32(lb) << 30
    data |= UInt32(signbit(x)) << 31
    return FloatSummary(data)
end


@inline Base.isless(a::FloatSummary, b::FloatSummary) = isless(a.data, b.data)
@inline Base.signbit(s::FloatSummary) = !iszero(s.data & 0x80000000)
@inline unsafe_exponent(s::FloatSummary) =
    Int(UInt16(s.data & 0x0000FFFF) % Int16)
@inline mantissa_leading_zeros(s::FloatSummary) =
    ifelse(iszero(s.data & 0x40000000), Int((s.data >> 22) & 0x3F), 0)
@inline mantissa_leading_ones(s::FloatSummary) =
    ifelse(iszero(s.data & 0x40000000), 0, Int((s.data >> 22) & 0x3F))
@inline mantissa_trailing_zeros(s::FloatSummary) =
    ifelse(iszero(s.data & 0x20000000), Int((s.data >> 16) & 0x3F), 0)
@inline mantissa_trailing_ones(s::FloatSummary) =
    ifelse(iszero(s.data & 0x20000000), 0, Int((s.data >> 16) & 0x3F))


################################################################################


export TwoSumSummary, find_possible_results


struct TwoSumSummary
    x::FloatSummary
    y::FloatSummary
    s::FloatSummary
    e::FloatSummary
end


@inline function _to_u64(summary::TwoSumSummary)
    result = zero(UInt64)
    result |= UInt64(summary.x.data) << 32
    result |= UInt64(summary.y.data)
    return result
end


@inline function _to_u128(summary::TwoSumSummary)
    result = zero(UInt128)
    result |= UInt128(summary.x.data) << 96
    result |= UInt128(summary.y.data) << 64
    result |= UInt128(summary.s.data) << 32
    result |= UInt128(summary.e.data)
    return result
end


@inline Base.isless(a::TwoSumSummary, b::TwoSumSummary) =
    isless(_to_u128(a), _to_u128(b))


function find_possible_results(
    summaries::AbstractVector{TwoSumSummary},
    x::FloatSummary,
    y::FloatSummary,
)
    range = searchsorted(summaries, TwoSumSummary(x, y, x, y); by=_to_u64)
    return [(summaries[i].s, summaries[i].e) for i in range]
end


################################################################################


export isnormal, normal_summaries, normal_two_sum_summaries


@inline Base.issubnormal(x::BFloat16) = issubnormal(Float32(x))
@inline isnormal(x) = isfinite(x) & !issubnormal(x)


function normal_summaries(summarize_func::F, ::Type{T}) where {F,T}
    U = uinttype(T)
    result = FloatSummary[]
    for i in zero(U):typemax(U)
        x = reinterpret(T, i)
        if isnormal(x)
            push!(result, summarize_func(x))
        end
    end
    return unique!(sort!(result))
end


function _merge_unique(vectors::Vector{Vector{T}}) where {T}
    result = T[]
    indices = firstindex.(vectors)
    while true
        min_item = nothing
        for i in eachindex(vectors)
            index = indices[i]
            vector = vectors[i]
            if index <= lastindex(vector)
                item = vector[index]
                if isnothing(min_item) || isless(item, min_item)
                    min_item = item
                end
            end
        end
        if isnothing(min_item)
            return result
        end
        push!(result, min_item)
        for i in eachindex(vectors)
            index = indices[i]
            vector = vectors[i]
            while (index <= lastindex(vector)) && (vector[index] == min_item)
                index += one(index)
            end
            indices[i] = index
        end
    end
end


function _two_sum_summary_helper(
    summarize_func::F,
    summary::FloatSummary,
    values::Vector{T},
) where {F,T}
    U = uinttype(T)
    result = Vector{TwoSumSummary}[]
    for i in eachindex(values)
        x = values[i]
        temp = TwoSumSummary[]
        for j in zero(U):typemax(U)
            y = reinterpret(T, j)
            if isnormal(y)
                sy = summarize_func(y)
                s = x + y
                if isnormal(s)
                    ss = summarize_func(s)
                    x_eff = s - y
                    y_eff = s - x_eff
                    x_err = x - x_eff
                    y_err = y - y_eff
                    e = x_err + y_err
                    if isnormal(e)
                        se = summarize_func(e)
                        push!(temp, TwoSumSummary(summary, sy, ss, se))
                    end
                end
            end
        end
        push!(result, sort!(temp))
    end
    return _merge_unique(result)
end


function normal_two_sum_summaries(summarize_func::F, ::Type{T}) where {F,T}
    U = uinttype(T)
    summary_dict = Dict{FloatSummary,Vector{T}}()
    for i in zero(U):typemax(U)
        x = reinterpret(T, i)
        if isnormal(x)
            summary = summarize_func(x)
            if haskey(summary_dict, summary)
                push!(summary_dict[summary], x)
            else
                summary_dict[summary] = T[x]
            end
        end
    end
    summaries = collect(enumerate(sort!(collect(summary_dict))))
    result = Vector{Vector{TwoSumSummary}}(undef, length(summaries))
    p = Progress(length(summaries); desc="TwoSum ($summarize_func, $T)")
    @threads :dynamic for (i, (summary, values)) in summaries
        result[i] = _two_sum_summary_helper(summarize_func, summary, values)
        next!(p)
    end
    return reduce(vcat, result)
end


################################################################################

end # module FloatSummaries
