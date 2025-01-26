#!/usr/bin/env -S julia --startup-file=no

using BFloat16s: BFloat16

push!(LOAD_PATH, @__DIR__)
using FloatSummaries: summarize_se, unsafe_exponent,
    normal_summaries, normal_two_sum_summaries,
    EFTSummary, LemmaVerifier, LemmaHelper


const ± = false:true


function verify_two_sum_se_lemmas(
    ::Type{T},
    summaries::Vector{EFTSummary},
) where {T}

    p = precision(T)
    pos_zero = summarize_se(+zero(T))
    neg_zero = summarize_se(-zero(T))
    possible_inputs = normal_summaries(summarize_se, T)
    add_case! = LemmaHelper(T)
    lemma_dict = Dict{String,Int}()

    for x in possible_inputs, y in possible_inputs

        verifier = LemmaVerifier(summaries, x, y, lemma_dict)
        sx = signbit(x)
        ex = unsafe_exponent(x)
        sy = signbit(y)
        ey = unsafe_exponent(y)
        x_zero = (x == pos_zero) | (x == neg_zero)
        y_zero = (y == pos_zero) | (y == neg_zero)
        same_sign = (sx == sy)
        diff_sign = (sx != sy)

        if x_zero | y_zero ############################### LEMMA FAMILY SE-Z (2)

            # Lemmas in Family SE-Z (for "zero") apply
            # when one or both addends are zero.

            # Lemma SE-Z1: Both addends are zero.
            verifier("SE-Z1-PP", (x == pos_zero) & (y == pos_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            verifier("SE-Z1-PN", (x == pos_zero) & (y == neg_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            verifier("SE-Z1-NP", (x == neg_zero) & (y == pos_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            verifier("SE-Z1-NN", (x == neg_zero) & (y == neg_zero)) do lemma
                add_case!(lemma, neg_zero, pos_zero)
            end

            # Lemma SE-Z2: One addend is zero.
            verifier("SE-Z2-X", y_zero & !x_zero) do lemma
                add_case!(lemma, x, pos_zero)
            end
            verifier("SE-Z2-Y", x_zero & !y_zero) do lemma
                add_case!(lemma, y, pos_zero)
            end

        else #################################################### NONZERO LEMMAS

            # From this point forward, all lemma statements carry
            # an implicit assumption that both addends are nonzero.

            ##################################################### LEMMA SE-I (1)

            # Lemma SE-I (for "identical") applies to addends
            # returned unchanged by the TwoSum algorithm.

            verifier("SE-I-X", (ex > ey + (p+1)) | ((ex == ey + (p+1)) & same_sign)) do lemma
                add_case!(lemma, x, y)
            end
            verifier("SE-I-Y", (ey > ex + (p+1)) | ((ey == ex + (p+1)) & same_sign)) do lemma
                add_case!(lemma, y, x)
            end

            ############################################## LEMMA FAMILY SE-S (5)

            # Lemmas in Family SE-S apply to addends with the same sign.

            verifier("SE-S1-X", same_sign & (ex == ey + p)) do lemma
                add_case!(lemma, (sx, ex:ex+1), (!sy, ey-(p-1):ex-p))
                add_case!(lemma, x            , y                   )
            end
            verifier("SE-S1-Y", same_sign & (ey == ex + p)) do lemma
                add_case!(lemma, (sy, ey:ey+1), (!sx, ex-(p-1):ey-p))
                add_case!(lemma, y            , x                   )
            end

            verifier("SE-S2-X", same_sign & (ex == ey + (p-1))) do lemma
                add_case!(lemma, (sx, ex:ex+1), pos_zero          )
                add_case!(lemma, (sx, ex:ex+1), (±, ey-(p-1):ex-p))
            end
            verifier("SE-S2-Y", same_sign & (ey == ex + (p-1))) do lemma
                add_case!(lemma, (sy, ey:ey+1), pos_zero          )
                add_case!(lemma, (sy, ey:ey+1), (±, ex-(p-1):ey-p))
            end

            verifier("SE-S3-X", same_sign & (ex == ey + (p-2))) do lemma
                add_case!(lemma, (sx, ex:ex+1), pos_zero                )
                add_case!(lemma, (sx, ex:ex+1), (!sy, ey-(p-1):ex-p    ))
                add_case!(lemma, (sx, ex     ), ( sy, ey-(p-1):ex-p    ))
                add_case!(lemma, (sx, ex+1   ), ( sy, ey-(p-1):ex-(p-1)))
            end
            verifier("SE-S3-Y", same_sign & (ey == ex + (p-2))) do lemma
                add_case!(lemma, (sy, ey:ey+1), pos_zero                )
                add_case!(lemma, (sy, ey:ey+1), (!sx, ex-(p-1):ey-p    ))
                add_case!(lemma, (sy, ey     ), ( sx, ex-(p-1):ey-p    ))
                add_case!(lemma, (sy, ey+1   ), ( sx, ex-(p-1):ey-(p-1)))
            end

            verifier("SE-S4-X", same_sign & (ex > ey) & (ex < ey + (p-2))) do lemma
                add_case!(lemma, (sx, ex:ex+1), pos_zero              )
                add_case!(lemma, (sx, ex     ), (±, ey-(p-1):ex-p    ))
                add_case!(lemma, (sx, ex+1   ), (±, ey-(p-1):ex-(p-1)))
            end
            verifier("SE-S4-Y", same_sign & (ey > ex) & (ey < ex + (p-2))) do lemma
                add_case!(lemma, (sy, ey:ey+1), pos_zero              )
                add_case!(lemma, (sy, ey     ), (±, ex-(p-1):ey-p    ))
                add_case!(lemma, (sy, ey+1   ), (±, ex-(p-1):ey-(p-1)))
            end

            verifier("SE-S5", same_sign & (ex == ey)) do lemma
                add_case!(lemma, (sx, ex+1), pos_zero)
                add_case!(lemma, (sx, ex+1), (±, ex-(p-1)))
            end

            ############################################## LEMMA FAMILY SE-D (5)

            # Lemmas in Family SE-D apply to addends with different signs.

            verifier("SE-D1-X", diff_sign & (ex == ey + (p+1))) do lemma
                add_case!(lemma, (sx, ex-1), (!sy, ey-(p-1):ex-(p+2)))
                add_case!(lemma, x         , y                       )
            end
            verifier("SE-D1-Y", diff_sign & (ey == ex + (p+1))) do lemma
                add_case!(lemma, (sy, ey-1), (!sx, ex-(p-1):ey-(p+2)))
                add_case!(lemma, y         , x                       )
            end

            verifier("SE-D2-X", diff_sign & (ex == ey + p)) do lemma
                add_case!(lemma, (sx, ex-1), pos_zero                )
                add_case!(lemma, (sx, ex-1), ( sy, ey-(p-1):ex-(p+2)))
                add_case!(lemma, (sx, ex-1), (!sy, ey-(p-1):ex-(p+1)))
                add_case!(lemma, (sx, ex  ), (!sy, ey-(p-1):ex-p    ))
                add_case!(lemma, x         , y                       )
            end
            verifier("SE-D2-Y", diff_sign & (ey == ex + p)) do lemma
                add_case!(lemma, (sy, ey-1), pos_zero                )
                add_case!(lemma, (sy, ey-1), ( sx, ex-(p-1):ey-(p+2)))
                add_case!(lemma, (sy, ey-1), (!sx, ex-(p-1):ey-(p+1)))
                add_case!(lemma, (sy, ey  ), (!sx, ex-(p-1):ey-p    ))
                add_case!(lemma, y         , x                       )
            end

            verifier("SE-D3-X", diff_sign & (ex > ey + 1) & (ex < ey + p)) do lemma
                add_case!(lemma, (sx, ex-1:ex), pos_zero              )
                add_case!(lemma, (sx, ex-1   ), (±, ey-(p-1):ex-(p+1)))
                add_case!(lemma, (sx, ex     ), (±, ey-(p-1):ex-p    ))
            end
            verifier("SE-D3-Y", diff_sign & (ey > ex + 1) & (ey < ex + p)) do lemma
                add_case!(lemma, (sy, ey-1:ey), pos_zero              )
                add_case!(lemma, (sy, ey-1   ), (±, ex-(p-1):ey-(p+1)))
                add_case!(lemma, (sy, ey     ), (±, ex-(p-1):ey-p    ))
            end

            verifier("SE-D4-X", diff_sign & (ex == ey + 1)) do lemma
                add_case!(lemma, (sx, ex-p:ex), pos_zero )
                add_case!(lemma, (sx, ex     ), (±, ex-p))
            end
            verifier("SE-D4-Y", diff_sign & (ey == ex + 1)) do lemma
                add_case!(lemma, (sy, ey-p:ey), pos_zero )
                add_case!(lemma, (sy, ey     ), (±, ey-p))
            end

            verifier("SE-D5", diff_sign & (ex == ey)) do lemma
                add_case!(lemma, pos_zero          , pos_zero)
                add_case!(lemma, (±, ex-(p-1):ex-1), pos_zero)
            end

        end
        @assert isone(verifier.count[])
    end

    println(T, " TwoSum-SE lemmas:")
    for (name, count) in sort!(collect(lemma_dict))
        println("    ", name, ": ", count)
    end

    return nothing
end


if !isfile("Float16TwoSumSE.bin")
    open("Float16TwoSumSE.bin", "w") do io
        write(io, normal_two_sum_summaries(summarize_se, Float16))
    end
end
@assert isfile("Float16TwoSumSE.bin")
@assert filesize("Float16TwoSumSE.bin") == 38_638 * sizeof(EFTSummary)
const FLOAT16_TWO_SUM_SE = Vector{EFTSummary}(undef, 38_638)
read!("Float16TwoSumSE.bin", FLOAT16_TWO_SUM_SE)
verify_two_sum_se_lemmas(Float16, FLOAT16_TWO_SUM_SE)
println("Verified all Float16 TwoSum-SE lemmas.")
flush(stdout)


if !isfile("BFloat16TwoSumSE.bin")
    open("BFloat16TwoSumSE.bin", "w") do io
        write(io, normal_two_sum_summaries(summarize_se, BFloat16))
    end
end
@assert isfile("BFloat16TwoSumSE.bin")
@assert filesize("BFloat16TwoSumSE.bin") == 548_026 * sizeof(EFTSummary)
const BFLOAT16_TWO_SUM_SE = Vector{EFTSummary}(undef, 548_026)
read!("BFloat16TwoSumSE.bin", BFLOAT16_TWO_SUM_SE)
verify_two_sum_se_lemmas(BFloat16, BFLOAT16_TWO_SUM_SE)
println("Verified all BFloat16 TwoSum-SE lemmas.")
flush(stdout)
