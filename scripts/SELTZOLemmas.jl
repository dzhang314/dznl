#!/usr/bin/env -S julia --startup-file=no

using BFloat16s: BFloat16

push!(LOAD_PATH, @__DIR__)
using FloatSummaries


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


@inline function unpack(::Type{T}, x::FloatSummary) where {T}
    p = precision(T)
    return (signbit(x), mantissa_leading_bit(x), mantissa_trailing_bit(x),
        unsafe_exponent(x),
        unsafe_exponent(x) - (mantissa_leading_bits(x) + 1),
        unsafe_exponent(x) - ((p - 1) - mantissa_trailing_bits(x)))
end


function verify_two_sum_seltzo_lemmas(
    ::Type{T},
    summaries::Vector{EFTSummary},
) where {T}

    p = precision(T)
    pos_zero = summarize_seltzo(+zero(T))
    neg_zero = summarize_seltzo(-zero(T))
    possible_inputs = normal_summaries(summarize_seltzo, T)
    add_case! = LemmaHelper(T)
    lemma_dict = Dict{String,Int}()
    unverified_count = 0
    reservoir = ReservoirSampler{Tuple{
        FloatSummary,
        FloatSummary,
        Vector{Tuple{FloatSummary,FloatSummary}}
    }}(10)

    for x in possible_inputs, y in possible_inputs

        verifier = LemmaVerifier(summaries, x, y, lemma_dict)
        sx, lbx, tbx, ex, lx, tx = unpack(T, x)
        sy, lby, tby, ey, ly, ty = unpack(T, y)
        x_zero = (x == pos_zero) | (x == neg_zero)
        y_zero = (y == pos_zero) | (y == neg_zero)
        x_pow2 = (!tbx) & (ex == tx)
        y_pow2 = (!tby) & (ey == ty)
        same_sign = (sx == sy)
        diff_sign = (sx != sy)

        if x_zero | y_zero ########################### LEMMA FAMILY SELTZO-Z (2)

            # Lemmas in Family SELTZO-Z (for "zero") apply
            # when one or both addends are zero.

            # Lemma SELTZO-Z1: Both addends are zero.
            verifier("SELTZO-Z1-PP", (x == pos_zero) & (y == pos_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            verifier("SELTZO-Z1-PN", (x == pos_zero) & (y == neg_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            verifier("SELTZO-Z1-NP", (x == neg_zero) & (y == pos_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            verifier("SELTZO-Z1-NN", (x == neg_zero) & (y == neg_zero)) do lemma
                add_case!(lemma, neg_zero, pos_zero)
            end

            # Lemma SELTZO-Z2: One addend is zero.
            verifier("SELTZO-Z2-X", y_zero & !x_zero) do lemma
                add_case!(lemma, x, pos_zero)
            end
            verifier("SELTZO-Z2-Y", x_zero & !y_zero) do lemma
                add_case!(lemma, y, pos_zero)
            end

        else #################################################### NONZERO LEMMAS

            # From this point forward, all lemma statements carry
            # an implicit assumption that both addends are nonzero.

            ################################################# LEMMA SELTZO-I (1)

            # Lemma SELTZO-I (for "identical") applies to addends
            # returned unchanged by the TwoSum algorithm.

            verifier("SELTZO-I-X",
                (ex > ey + (p + 1)) |
                ((ex == ey + (p + 1)) & (y_pow2 | same_sign | !x_pow2)) |
                ((ex == ey + p) & y_pow2 & (same_sign | !x_pow2) & !tbx)
            ) do lemma
                add_case!(lemma, x, y)
            end
            verifier("SELTZO-I-Y",
                (ey > ex + (p + 1)) |
                ((ey == ex + (p + 1)) & (x_pow2 | same_sign | !y_pow2)) |
                ((ey == ex + p) & x_pow2 & (same_sign | !y_pow2) & !tby)
            ) do lemma
                add_case!(lemma, y, x)
            end

        end
        if iszero(verifier.count[])
            unverified_count += 1
            possible_results = FloatSummaries._find_possible_results(summaries, x, y)
            if !isempty(possible_results)
                push!(reservoir, (x, y, possible_results))
            end
        end
    end

    println(T, " TwoSum-SELTZO lemmas:")
    for (name, count) in sort!(collect(lemma_dict))
        println("    ", name, ": ", count)
    end
    println("Unverified $T cases: $unverified_count")
    for (x, y, possible_results) in reservoir.reservoir
        if unsafe_exponent(x) < unsafe_exponent(y)
            x, y = y, x
        end
        sx, lbx, tbx, ex, lx, tx = unpack(T, x)
        sy, lby, tby, ey, ly, ty = unpack(T, y)
        println("    (sx = $sx, lbx = $lbx, tbx = $tbx, ex = $ex, lx = $lx, tx = $tx)",
            " (sy = $sy, lby = $lby, tby = $tby, ey = $ey, ly = $ly, ty = $ty)")
        for (r, e) in possible_results
            sr, lbr, tbr, er, lr, tr = unpack(T, r)
            se, lbe, tbe, ee, le, te = unpack(T, e)
            println("        (sr = $sr, lbr = $lbr, tbr = $tbr, er = $er, lr = $lr, tr = $tr)",
                " (se = $se, lbe = $lbe, tbe = $tbe, ee = $ee, le = $le, te = $te)")
        end
    end

    return nothing
end


if !isfile("Float16TwoSumSELTZO.bin")
    open("Float16TwoSumSELTZO.bin", "w") do io
        write(io, normal_two_sum_summaries(summarize_seltzo, Float16))
    end
end
@assert isfile("Float16TwoSumSELTZO.bin")
@assert filesize("Float16TwoSumSELTZO.bin") == 319_985_950 * sizeof(EFTSummary)
const FLOAT16_TWO_SUM_SELTZO = Vector{EFTSummary}(undef, 319_985_950)
read!("Float16TwoSumSELTZO.bin", FLOAT16_TWO_SUM_SELTZO)
verify_two_sum_seltzo_lemmas(Float16, FLOAT16_TWO_SUM_SELTZO)
# println("Verified all Float16 TwoSum-SELTZO lemmas.")
flush(stdout)


# if !isfile("BFloat16TwoSumSELTZO.bin")
#     open("BFloat16TwoSumSELTZO.bin", "w") do io
#         write(io, normal_two_sum_summaries(summarize_seltzo, BFloat16))
#     end
# end
# @assert isfile("BFloat16TwoSumSELTZO.bin")
# @assert filesize("BFloat16TwoSumSELTZO.bin") == 1_172_449_766 * sizeof(EFTSummary)
# const BFLOAT16_TWO_SUM_SELTZO = Vector{EFTSummary}(undef, 1_172_449_766)
# read!("BFloat16TwoSumSELTZO.bin", BFLOAT16_TWO_SUM_SELTZO)
# verify_two_sum_seltzo_lemmas(BFloat16, BFLOAT16_TWO_SUM_SELTZO)
# # println("Verified all BFloat16 TwoSum-SELTZO lemmas.")
# flush(stdout)
