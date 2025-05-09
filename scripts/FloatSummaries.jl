module FloatSummaries


################################################################################


export LemmaVerifier, LemmaHelper


struct LemmaVerifier
    summaries::Vector{EFTSummary}
    x::FloatSummary
    y::FloatSummary
    lemma_dict::Dict{String,Int}
    count::Array{Int,0}

    @inline LemmaVerifier(
        summaries::Vector{EFTSummary},
        x::FloatSummary,
        y::FloatSummary,
        lemma_dict::Dict{String,Int},
    ) = new(summaries, x, y, lemma_dict, fill(0))
end


function _find_possible_results(
    summaries::AbstractVector{EFTSummary},
    x::FloatSummary,
    y::FloatSummary,
)
    range = searchsorted(summaries, EFTSummary(x, y, x, y); by=_to_u64)
    return [(summaries[i].r, summaries[i].e) for i in range]
end


function (verifier::LemmaVerifier)(
    f!::Function,
    lemma_name::String,
    hypothesis::Bool,
)
    if hypothesis
        possible_results = _find_possible_results(
            verifier.summaries, verifier.x, verifier.y)
        stated_results = Tuple{FloatSummary,FloatSummary}[]
        f!(stated_results)
        @assert possible_results == sort!(stated_results)
        if !haskey(verifier.lemma_dict, lemma_name)
            verifier.lemma_dict[lemma_name] = 0
        end
        verifier.lemma_dict[lemma_name] += 1
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
                push!(v, (FloatSummary(sr, er, (p - 1) - (er - fr)), e_summary))
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
                                FloatSummary(sr, er, (p - 1) - (er - fr)),
                                FloatSummary(se, ee, (p - 1) - (ee - fe))))
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
