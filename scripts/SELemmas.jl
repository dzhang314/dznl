using BFloat16s

push!(LOAD_PATH, @__DIR__)
using FloatSummaries


if !isfile("Float16TwoSumSE.bin")
    open("Float16TwoSumSE.bin", "w") do io
        write(io, normal_two_sum_summaries(summarize_se, Float16))
    end
end
@assert isfile("Float16TwoSumSE.bin")
@assert filesize("Float16TwoSumSE.bin") == 38_638 * sizeof(EFTSummary)
const FLOAT16_TWO_SUM_SE = Vector{EFTSummary}(undef, 38_638)
read!("Float16TwoSumSE.bin", FLOAT16_TWO_SUM_SE)


if !isfile("BFloat16TwoSumSE.bin")
    open("BFloat16TwoSumSE.bin", "w") do io
        write(io, normal_two_sum_summaries(summarize_se, BFloat16))
    end
end
@assert isfile("BFloat16TwoSumSE.bin")
@assert filesize("BFloat16TwoSumSE.bin") == 548_026 * sizeof(EFTSummary)
const BFLOAT16_TWO_SUM_SE = Vector{EFTSummary}(undef, 548_026)
read!("BFloat16TwoSumSE.bin", BFLOAT16_TWO_SUM_SE)


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

    for x in possible_inputs, y in possible_inputs

        verifier = LemmaVerifier(summaries, x, y)
        sx = signbit(x)
        ex = unsafe_exponent(x)
        sy = signbit(y)
        ey = unsafe_exponent(y)
        x_zero = (x == pos_zero) | (x == neg_zero)
        y_zero = (y == pos_zero) | (y == neg_zero)
        same_sign = (sx == sy)
        diff_sign = (sx != sy)

        if x_zero | y_zero ################################## LEMMA FAMILY Z (2)

            # Lemmas in Family Z (for "zero") apply to
            # cases where one or both addends are zero.

            # Lemma Z1: Both addends are zero.
            verifier((x == pos_zero) & (y == pos_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            verifier((x == pos_zero) & (y == neg_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            verifier((x == neg_zero) & (y == pos_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            verifier((x == neg_zero) & (y == neg_zero)) do lemma
                add_case!(lemma, neg_zero, pos_zero)
            end

            # Lemma Z2: One addend is zero.
            verifier(y_zero & !x_zero) do lemma
                add_case!(lemma, x, pos_zero)
            end
            verifier(x_zero & !y_zero) do lemma
                add_case!(lemma, y, pos_zero)
            end

        else #################################################### NONZERO LEMMAS

            # From this point forward, all lemma statements carry
            # an implicit assumption that both addends are nonzero.

            ######################################################## LEMMA I (1)

            # Lemma I (for "identical") applies to addends
            # returned unchanged by the TwoSum algorithm.

            verifier((ex > ey + (p+1)) | ((ex == ey + (p+1)) & same_sign)) do lemma
                add_case!(lemma, x, y)
            end
            verifier((ey > ex + (p+1)) | ((ey == ex + (p+1)) & same_sign)) do lemma
                add_case!(lemma, y, x)
            end

            ################################################# LEMMA FAMILY S (5)

            # Lemmas in Family S apply to addends with the same sign.

            # Lemma S1
            verifier(same_sign & (ex == ey + p)) do lemma
                add_case!(lemma, (sx, ex:ex+1), (!sy, ey-(p-1):ey))
                add_case!(lemma, (sx, ex     ), ( sy, ey         ))
            end
            verifier(same_sign & (ey == ex + p)) do lemma
                add_case!(lemma, (sy, ey:ey+1), (!sx, ex-(p-1):ex))
                add_case!(lemma, (sy, ey     ), ( sx, ex         ))
            end

            # Lemma S2
            verifier(same_sign & (ex == ey + (p-1))) do lemma
                add_case!(lemma, (sx, ex:ex+1), pos_zero          )
                add_case!(lemma, (sx, ex:ex+1), (±, ey-(p-1):ey-1))
            end
            verifier(same_sign & (ey == ex + (p-1))) do lemma
                add_case!(lemma, (sy, ey:ey+1), pos_zero          )
                add_case!(lemma, (sy, ey:ey+1), (±, ex-(p-1):ex-1))
            end

            # Lemma S3
            verifier(same_sign & (ex == ey + (p-2))) do lemma
                add_case!(lemma, (sx, ex:ex+1), pos_zero            )
                add_case!(lemma, (sx, ex:ex+1), (!sy, ey-(p-1):ey-2))
                add_case!(lemma, (sx, ex     ), ( sy, ey-(p-1):ey-2))
                add_case!(lemma, (sx, ex+1   ), ( sy, ey-(p-1):ey-1))
            end
            verifier(same_sign & (ey == ex + (p-2))) do lemma
                add_case!(lemma, (sy, ey:ey+1), pos_zero            )
                add_case!(lemma, (sy, ey:ey+1), (!sx, ex-(p-1):ex-2))
                add_case!(lemma, (sy, ey     ), ( sx, ex-(p-1):ex-2))
                add_case!(lemma, (sy, ey+1   ), ( sx, ex-(p-1):ex-1))
            end

            # Lemma S4
            verifier(same_sign & (ex > ey) & (ex < ey + (p-2))) do lemma
                k = ex - ey
                add_case!(lemma, (sx, ex:ex+1), pos_zero                  )
                add_case!(lemma, (sx, ex     ), (±, ey-(p-1):ey-(p-k)    ))
                add_case!(lemma, (sx, ex+1   ), (±, ey-(p-1):ey-(p-(k+1))))
            end
            verifier(same_sign & (ey > ex) & (ey < ex + (p-2))) do lemma
                k = ey - ex
                add_case!(lemma, (sy, ey:ey+1), pos_zero                  )
                add_case!(lemma, (sy, ey     ), (±, ex-(p-1):ex-(p-k)    ))
                add_case!(lemma, (sy, ey+1   ), (±, ex-(p-1):ex-(p-(k+1))))
            end

            # Lemma S5
            verifier(same_sign & (ex == ey)) do lemma
                add_case!(lemma, (sx, ex+1), pos_zero)
                add_case!(lemma, (sx, ex+1), (±, ex-(p-1)))
            end

            ################################################# LEMMA FAMILY D (5)

            # Lemmas in Family D apply to addends with different signs.

            # Lemma D1
            verifier(diff_sign & (ex == ey + (p+1))) do lemma
                add_case!(lemma, (sx, ex-1), (!sy, ey-(p-1):ey-1))
                add_case!(lemma, (sx, ex  ), ( sy, ey           ))
            end
            verifier(diff_sign & (ey == ex + (p+1))) do lemma
                add_case!(lemma, (sy, ey-1), (!sx, ex-(p-1):ex-1))
                add_case!(lemma, (sy, ey  ), ( sx, ex           ))
            end

            # Lemma D2
            verifier(diff_sign & (ex == ey + p)) do lemma
                add_case!(lemma, (sx, ex-1), pos_zero            )
                add_case!(lemma, (sx, ex-1), ( sy, ey-(p-1):ey-2))
                add_case!(lemma, (sx, ex-1), (!sy, ey-(p-1):ey-1))
                add_case!(lemma, (sx, ex  ), (!sy, ey-(p-1):ey  ))
                add_case!(lemma, (sx, ex  ), ( sy, ey           ))
            end
            verifier(diff_sign & (ey == ex + p)) do lemma
                add_case!(lemma, (sy, ey-1), pos_zero            )
                add_case!(lemma, (sy, ey-1), ( sx, ex-(p-1):ex-2))
                add_case!(lemma, (sy, ey-1), (!sx, ex-(p-1):ex-1))
                add_case!(lemma, (sy, ey  ), (!sx, ex-(p-1):ex  ))
                add_case!(lemma, (sy, ey  ), ( sx, ex           ))
            end

            # Lemma D3
            verifier(diff_sign & (ex > ey + 1) & (ex < ey + p)) do lemma
                k = ex - ey
                add_case!(lemma, (sx, ex-1:ex), pos_zero                  )
                add_case!(lemma, (sx, ex-1   ), (±, ey-(p-1):ey-(p-(k-1))))
                add_case!(lemma, (sx, ex     ), (±, ey-(p-1):ey-(p-k)    ))
            end
            verifier(diff_sign & (ey > ex + 1) & (ey < ex + p)) do lemma
                k = ey - ex
                add_case!(lemma, (sy, ey-1:ey), pos_zero                  )
                add_case!(lemma, (sy, ey-1   ), (±, ex-(p-1):ex-(p-(k-1))))
                add_case!(lemma, (sy, ey     ), (±, ex-(p-1):ex-(p-k)    ))
            end

            # Lemma D4
            verifier(diff_sign & (ex == ey + 1)) do lemma
                add_case!(lemma, (sx, ex-p:ex), pos_zero     )
                add_case!(lemma, (sx, ex     ), (±, ey-(p-1)))
            end
            verifier(diff_sign & (ey == ex + 1)) do lemma
                add_case!(lemma, (sy, ey-p:ey), pos_zero     )
                add_case!(lemma, (sy, ey     ), (±, ex-(p-1)))
            end

            # Lemma D5
            verifier(diff_sign & (ex == ey)) do lemma
                add_case!(lemma, pos_zero          , pos_zero)
                add_case!(lemma, (±, ex-(p-1):ex-1), pos_zero)
            end

        end
        @assert isone(verifier.count[])
    end
    return nothing
end


verify_two_sum_se_lemmas(Float16, FLOAT16_TWO_SUM_SE)
println("Verified all TwoSum-SE lemmas for Float16.")
flush(stdout)


verify_two_sum_se_lemmas(BFloat16, BFLOAT16_TWO_SUM_SE)
println("Verified all TwoSum-SE lemmas for BFloat16.")
flush(stdout)
