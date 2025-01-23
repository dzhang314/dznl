using BFloat16s

push!(LOAD_PATH, @__DIR__)
using FloatSummaries


const ± = false:true


function verify_two_sum_setz_lemmas(
    ::Type{T},
    summaries::Vector{EFTSummary},
) where {T}

    p = precision(T)
    pos_zero = summarize_setz(+zero(T))
    neg_zero = summarize_setz(-zero(T))
    possible_inputs = normal_summaries(summarize_setz, T)
    add_case! = LemmaHelper(T)
    unverified_count = 0

    for x in possible_inputs, y in possible_inputs

        verifier = LemmaVerifier(summaries, x, y)
        sx = signbit(x)
        ex = unsafe_exponent(x)
        fx = unsafe_exponent(x) - ((p-1) - mantissa_trailing_zeros(x))
        sy = signbit(y)
        ey = unsafe_exponent(y)
        fy = unsafe_exponent(y) - ((p-1) - mantissa_trailing_zeros(y))
        x_zero = (x == pos_zero) | (x == neg_zero)
        y_zero = (y == pos_zero) | (y == neg_zero)
        same_sign = (sx == sy)
        diff_sign = (sx != sy)

        if x_zero | y_zero ################################## LEMMA FAMILY Z (2)

            # Lemmas in Family Z (for "zero") apply
            # when one or both addends are zero.

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

            verifier(
                (ex > ey + (p+1)) |
                ((ex == ey + (p+1)) & ((ey == fy) | same_sign | (ex > fx))) |
                ((ex == ey + p) & (ey == fy) & (same_sign | (ex > fx)) & (ex < fx + (p-1)))
            ) do lemma
                add_case!(lemma, x, y)
            end
            verifier(
                (ey > ex + (p+1)) |
                ((ey == ex + (p+1)) & ((ex == fx) | same_sign | (ey > fy))) |
                ((ey == ex + p) & (ex == fx) & (same_sign | (ey > fy)) & (ey < fy + (p-1)))
            ) do lemma
                add_case!(lemma, y, x)
            end

        end
        if iszero(verifier.count[])
            unverified_count += 1
        end
    end
    println("Unverified $T lemmas: $unverified_count of ",
        length(possible_inputs)^2)
    return nothing
end


if !isfile("Float16TwoSumSETZ.bin")
    open("Float16TwoSumSETZ.bin", "w") do io
        write(io, normal_two_sum_summaries(summarize_setz, Float16))
    end
end
@assert isfile("Float16TwoSumSETZ.bin")
@assert filesize("Float16TwoSumSETZ.bin") == 3_833_700 * sizeof(EFTSummary)
const FLOAT16_TWO_SUM_SETZ = Vector{EFTSummary}(undef, 3_833_700)
read!("Float16TwoSumSETZ.bin", FLOAT16_TWO_SUM_SETZ)
verify_two_sum_setz_lemmas(Float16, FLOAT16_TWO_SUM_SETZ)
# println("Verified all TwoSum-SETZ lemmas for Float16.")
flush(stdout)


if !isfile("BFloat16TwoSumSETZ.bin")
    open("BFloat16TwoSumSETZ.bin", "w") do io
        write(io, normal_two_sum_summaries(summarize_setz, BFloat16))
    end
end
@assert isfile("BFloat16TwoSumSETZ.bin")
@assert filesize("BFloat16TwoSumSETZ.bin") == 26_618_866 * sizeof(EFTSummary)
const BFLOAT16_TWO_SUM_SETZ = Vector{EFTSummary}(undef, 26_618_866)
read!("BFloat16TwoSumSETZ.bin", BFLOAT16_TWO_SUM_SETZ)
verify_two_sum_setz_lemmas(BFloat16, BFLOAT16_TWO_SUM_SETZ)
# println("Verified all TwoSum-SETZ lemmas for BFloat16.")
flush(stdout)
