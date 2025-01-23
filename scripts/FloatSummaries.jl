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


@inline function FloatSummary(s::Bool, e::Integer, ntz::Integer)
    data = UInt32(Int16(e) % UInt16)
    data |= UInt32(UInt8(ntz)) << 16
    data |= UInt32(s) << 31
    return FloatSummary(data)
end


@inline function FloatSummary(
    s::Bool, e::Integer,
    lb::Bool, nlb::Integer,
    tb::Bool, ntb::Integer,
)
    data = UInt32(Int16(e) % UInt16)
    data |= UInt32(UInt8(ntb)) << 16
    data |= UInt32(UInt8(nlb)) << 22
    data |= UInt32(tb) << 29
    data |= UInt32(lb) << 30
    data |= UInt32(s) << 31
    return FloatSummary(data)
end


@inline summarize_se(x::T) where {T} = FloatSummary(
    signbit(x), unsafe_exponent(x))


@inline summarize_setz(x::T) where {T} = FloatSummary(
    signbit(x), unsafe_exponent(x), mantissa_trailing_zeros(x))


@inline summarize_seltzo(x::T) where {T} = FloatSummary(
    signbit(x), unsafe_exponent(x),
    mantissa_leading_bit(x), ifelse(mantissa_leading_bit(x),
        mantissa_leading_ones(x), mantissa_leading_zeros(x)),
    mantissa_trailing_bit(x), ifelse(mantissa_trailing_bit(x),
        mantissa_trailing_ones(x), mantissa_trailing_zeros(x)))


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


export EFTSummary, find_possible_results


struct EFTSummary
    x::FloatSummary
    y::FloatSummary
    r::FloatSummary
    e::FloatSummary
end


@inline function _to_u64(summary::EFTSummary)
    result = zero(UInt64)
    result |= UInt64(summary.x.data) << 32
    result |= UInt64(summary.y.data)
    return result
end


@inline function _to_u128(summary::EFTSummary)
    result = zero(UInt128)
    result |= UInt128(summary.x.data) << 96
    result |= UInt128(summary.y.data) << 64
    result |= UInt128(summary.r.data) << 32
    result |= UInt128(summary.e.data)
    return result
end


@inline Base.isless(a::EFTSummary, b::EFTSummary) =
    isless(_to_u128(a), _to_u128(b))


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
    sx::FloatSummary,
    x_values::Vector{T},
) where {F,T}
    U = uinttype(T)
    result = Vector{EFTSummary}[]
    for x in x_values
        temp = EFTSummary[]
        for j in zero(U):typemax(U)
            y = reinterpret(T, j)
            if isnormal(y)
                sy = summarize_func(y)
                r = x + y
                if isnormal(r)
                    sr = summarize_func(r)
                    x_prime = r - y
                    y_prime = r - x_prime
                    delta_x = x - x_prime
                    delta_y = y - y_prime
                    e = delta_x + delta_y
                    if isnormal(e)
                        se = summarize_func(e)
                        push!(temp, EFTSummary(sx, sy, sr, se))
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
            sx = summarize_func(x)
            if haskey(summary_dict, sx)
                push!(summary_dict[sx], x)
            else
                summary_dict[sx] = T[x]
            end
        end
    end
    summaries = collect(enumerate(sort!(collect(summary_dict))))
    result = Vector{Vector{EFTSummary}}(undef, length(summaries))
    p = Progress(length(summaries); desc="TwoSum ($summarize_func, $T)")
    @threads :dynamic for (i, (sx, x_values)) in summaries
        result[i] = _two_sum_summary_helper(summarize_func, sx, x_values)
        next!(p)
    end
    return reduce(vcat, result)
end


################################################################################


export LemmaVerifier, LemmaHelper


function find_possible_results(
    summaries::AbstractVector{EFTSummary},
    x::FloatSummary,
    y::FloatSummary,
)
    range = searchsorted(summaries, EFTSummary(x, y, x, y); by=_to_u64)
    return [(summaries[i].r, summaries[i].e) for i in range]
end


struct LemmaVerifier
    summaries::Vector{EFTSummary}
    x::FloatSummary
    y::FloatSummary
    count::Array{Int,0}

    @inline LemmaVerifier(
        summaries::Vector{EFTSummary},
        x::FloatSummary,
        y::FloatSummary,
    ) = new(summaries, x, y, fill(0))
end


function (verifier::LemmaVerifier)(
    f!::Function,
    hypothesis::Bool,
)
    if hypothesis
        possible_results = find_possible_results(
            verifier.summaries, verifier.x, verifier.y)
        stated_results = Tuple{FloatSummary,FloatSummary}[]
        f!(stated_results)
        @assert possible_results == sort!(stated_results)
        verifier.count[] += 1
    end
    return nothing
end


struct LemmaHelper
    p::Int
    e_max::Int
    e_min::Int
    f_min::Int

    @inline LemmaHelper(::Type{T}) where {T} = new(
        precision(T), exponent(floatmax(T)), exponent(floatmin(T)),
        exponent(floatmin(T)) - (precision(T) - 1))
end


@inline _lemma_range(::LemmaHelper, r::Bool) = r:r
@inline _lemma_range(::LemmaHelper, r::UnitRange{Bool}) = r
@inline _lemma_range_e(helper::LemmaHelper, r::Integer) =
    _lemma_range_e(helper, r:r)
@inline _lemma_range_e(helper::LemmaHelper, r::UnitRange) =
    UnitRange(max(helper.e_min, r.start), min(helper.e_max, r.stop))
@inline _lemma_range_f(helper::LemmaHelper, r::Integer) =
    _lemma_range_f(helper, r:r)
@inline _lemma_range_f(helper::LemmaHelper, r::UnitRange) =
    UnitRange(max(helper.f_min, r.start), min(helper.e_max, r.stop))


const _BoolRange = Union{Bool,UnitRange{Bool}}
const _IntegerRange = Union{Integer,UnitRange{<:Integer}}
const _SETuple = Tuple{_BoolRange,_IntegerRange}
const _SETZTuple = Tuple{_BoolRange,_IntegerRange,_IntegerRange}


function (helper::LemmaHelper)(
    v::AbstractVector{Tuple{FloatSummary,FloatSummary}},
    r_summary::FloatSummary, e_summary::FloatSummary,
)
    push!(v, (r_summary, e_summary))
    return v
end


function (helper::LemmaHelper)(
    v::AbstractVector{Tuple{FloatSummary,FloatSummary}},
    (sr_range, er_range)::_SETuple,
    e_summary::FloatSummary,
)
    for sr in _lemma_range(helper, sr_range)
        for er in _lemma_range_e(helper, er_range)
            push!(v, (FloatSummary(sr, er), e_summary))
        end
    end
    return v
end


function (helper::LemmaHelper)(
    v::AbstractVector{Tuple{FloatSummary,FloatSummary}},
    (sr_range, er_range, fr_range)::_SETZTuple,
    e_summary::FloatSummary,
)
    p = helper.p
    for sr in _lemma_range(helper, sr_range)
        for er in _lemma_range_e(helper, er_range)
            for fr in _lemma_range_f(helper, fr_range)
                push!(v, (FloatSummary(sr, er, (p-1) - (er-fr)), e_summary))
            end
        end
    end
    return v
end


function (helper::LemmaHelper)(
    v::AbstractVector{Tuple{FloatSummary,FloatSummary}},
    (sr_range, er_range)::_SETuple,
    (se_range, ee_range)::_SETuple,
)
    for sr in _lemma_range(helper, sr_range)
        for er in _lemma_range_e(helper, er_range)
            for se in _lemma_range(helper, se_range)
                for ee in _lemma_range_e(helper, ee_range)
                    push!(v, (FloatSummary(sr, er), FloatSummary(se, ee)))
                end
            end
        end
    end
    return v
end


function (helper::LemmaHelper)(
    v::AbstractVector{Tuple{FloatSummary,FloatSummary}},
    (sr_range, er_range, fr_range)::_SETZTuple,
    (se_range, ee_range, fe_range)::_SETZTuple,
)
    p = helper.p
    for sr in _lemma_range(helper, sr_range)
        for er in _lemma_range_e(helper, er_range)
            for fr in _lemma_range_f(helper, fr_range)
                for se in _lemma_range(helper, se_range)
                    for ee in _lemma_range_e(helper, ee_range)
                        for fe in _lemma_range_f(helper, fe_range)
                            push!(v, (
                                FloatSummary(sr, er, (p-1) - (er-fr)),
                                FloatSummary(se, ee, (p-1) - (ee-fe))))
                        end
                    end
                end
            end
        end
    end
    return v
end


################################################################################

end # module FloatSummaries
