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
    lemma_dict = Dict{String,Int}()
    unverified_count = 0

    for x in possible_inputs, y in possible_inputs

        verifier = LemmaVerifier(summaries, x, y, lemma_dict)
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

        if x_zero | y_zero ############################# LEMMA FAMILY SETZ-Z (2)

            # Lemmas in Family SETZ-Z (for "zero") apply
            # when one or both addends are zero.

            # Lemma SETZ-Z1: Both addends are zero.
            verifier("SETZ-Z1-PP", (x == pos_zero) & (y == pos_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            verifier("SETZ-Z1-PN", (x == pos_zero) & (y == neg_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            verifier("SETZ-Z1-NP", (x == neg_zero) & (y == pos_zero)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
            end
            verifier("SETZ-Z1-NN", (x == neg_zero) & (y == neg_zero)) do lemma
                add_case!(lemma, neg_zero, pos_zero)
            end

            # Lemma SETZ-Z2: One addend is zero.
            verifier("SETZ-Z2-X", y_zero & !x_zero) do lemma
                add_case!(lemma, x, pos_zero)
            end
            verifier("SETZ-Z2-Y", x_zero & !y_zero) do lemma
                add_case!(lemma, y, pos_zero)
            end

        else #################################################### NONZERO LEMMAS

            # From this point forward, all lemma statements carry
            # an implicit assumption that both addends are nonzero.

            ################################################### LEMMA SETZ-I (1)

            # Lemma SETZ-I (for "identical") applies to addends
            # returned unchanged by the TwoSum algorithm.

            verifier("SETZ-I-X",
                (ex > ey + (p+1)) |
                ((ex == ey + (p+1)) & ((ey == fy) | same_sign | (ex > fx))) |
                ((ex == ey + p) & (ey == fy) & (same_sign | (ex > fx)) & (ex < fx + (p-1)))
            ) do lemma
                add_case!(lemma, x, y)
            end
            verifier("SETZ-I-Y",
                (ey > ex + (p+1)) |
                ((ey == ex + (p+1)) & ((ex == fx) | same_sign | (ey > fy))) |
                ((ey == ex + p) & (ex == fx) & (same_sign | (ey > fy)) & (ey < fy + (p-1)))
            ) do lemma
                add_case!(lemma, y, x)
            end

            ############################################ LEMMA FAMILY SETZ-F (7)

            # Lemmas in Family SETZ-F apply to addends
            # with the same trailing exponent (fx == fy).

            # The trailing exponent of a floating-point number x, denoted by
            # fx, is the place value of the last nonzero bit in its mantissa.

            verifier("SETZ-FS0-X", same_sign & (fx == fy) & (ex > ey + 1)) do lemma
                add_case!(lemma, (sx, ex  , fx+1:ex-1), pos_zero)
                add_case!(lemma, (sx, ex+1, fx+1:ey  ), pos_zero)
                add_case!(lemma, (sx, ex+1, ex+1     ), pos_zero)
            end
            verifier("SETZ-FS0-Y", same_sign & (fx == fy) & (ey > ex + 1)) do lemma
                add_case!(lemma, (sy, ey  , fy+1:ey-1), pos_zero)
                add_case!(lemma, (sy, ey+1, fy+1:ex  ), pos_zero)
                add_case!(lemma, (sy, ey+1, ey+1     ), pos_zero)
            end

            verifier("SETZ-FS1-X", same_sign & (fx == fy) & (ex == ey + 1)) do lemma
                add_case!(lemma, (sx, ex  , fx+1:ex-2), pos_zero)
                add_case!(lemma, (sx, ex+1, fx+1:ey  ), pos_zero)
                add_case!(lemma, (sx, ex+1, ex+1     ), pos_zero)
            end
            verifier("SETZ-FS1-Y", same_sign & (fx == fy) & (ey == ex + 1)) do lemma
                add_case!(lemma, (sy, ey  , fy+1:ey-2), pos_zero)
                add_case!(lemma, (sy, ey+1, fy+1:ex  ), pos_zero)
                add_case!(lemma, (sy, ey+1, ey+1     ), pos_zero)
            end

            verifier("SETZ-FS2", same_sign & (fx == fy) & (ex == ey) & (ex > fx)) do lemma
                add_case!(lemma, (sx, ex+1, fx+1:ex), pos_zero)
            end

            verifier("SETZ-FS3", same_sign & (fx == fy) & (ex == ey) & (ex == fx)) do lemma
                add_case!(lemma, (sx, ex+1, ex+1), pos_zero)
            end

            verifier("SETZ-FD0-X", diff_sign & (fx == fy) & (ex > ey + 1)) do lemma
                add_case!(lemma, (sx, ex-1, fx+1:ey), pos_zero)
                add_case!(lemma, (sx, ex  , fx+1:ex), pos_zero)
            end
            verifier("SETZ-FD0-Y", diff_sign & (fx == fy) & (ey > ex + 1)) do lemma
                add_case!(lemma, (sy, ey-1, fy+1:ex), pos_zero)
                add_case!(lemma, (sy, ey  , fy+1:ey), pos_zero)
            end

            verifier("SETZ-FD1-X", diff_sign & (fx == fy) & (ex == ey + 1)) do lemma
                for k = fx+1:ex-1
                    add_case!(lemma, (sx, k, fx+1:k), pos_zero)
                end
                add_case!(lemma, (sx, ex, fx+1:ex-2), pos_zero)
                add_case!(lemma, (sx, ex, ex       ), pos_zero)
            end
            verifier("SETZ-FD1-Y", diff_sign & (fx == fy) & (ey == ex + 1)) do lemma
                for k = fy+1:ey-1
                    add_case!(lemma, (sy, k, fy+1:k), pos_zero)
                end
                add_case!(lemma, (sy, ey, fy+1:ey-2), pos_zero)
                add_case!(lemma, (sy, ey, ey       ), pos_zero)
            end

            verifier("SETZ-FD2", diff_sign & (fx == fy) & (ex == ey)) do lemma
                add_case!(lemma, pos_zero, pos_zero)
                for k = fx+1:ex-1
                    add_case!(lemma, (±, k, fx+1:k), pos_zero)
                end
            end

            ############################################### LEMMA FAMILY E (7+8)

            # Lemmas in Family E (for "exact") apply to addends with
            # different trailing exponents whose floating-point sum is exact.

            # Lemma SETZ-EN0: Addends do not overlap.
            verifier("SETZ-EN0-X", (same_sign | (ex > fx)) & (fx > ey) & (ex < fy + p)) do lemma
                add_case!(lemma, (sx, ex, fy), pos_zero)
            end
            verifier("SETZ-EN0-Y", (same_sign | (ey > fy)) & (fy > ex) & (ey < fx + p)) do lemma
                add_case!(lemma, (sy, ey, fx), pos_zero)
            end

            # Lemma SETZ-EN1: Boundary case of SETZ-EN0.
            verifier("SETZ-EN1-X", diff_sign & (
                ((ex == fx) & (fx > ey + 1) & (ex < fy + (p+1))) |
                ((ex == fx + 1) & (fx == ey) & (ey > fy))
            )) do lemma
                add_case!(lemma, (sx, ex-1, fy), pos_zero)
            end
            verifier("SETZ-EN1-Y", diff_sign & (
                ((ey == fy) & (fy > ex + 1) & (ey < fx + (p+1))) |
                ((ey == fy + 1) & (fy == ex) & (ex > fx))
            )) do lemma
                add_case!(lemma, (sy, ey-1, fx), pos_zero)
            end

            # Lemma SETZ-ESP0: Addends have same sign and partially overlap.
            verifier("SETZ-ESP0-X", same_sign & ((ex > ey > fx > fy) | (ex > ey + 1 > fx > fy)) & (ex < fy + (p-1))) do lemma
                add_case!(lemma, (sx, ex:ex+1, fy), pos_zero)
            end
            verifier("SETZ-ESP0-Y", same_sign & ((ey > ex > fy > fx) | (ey > ex + 1 > fy > fx)) & (ey < fx + (p-1))) do lemma
                add_case!(lemma, (sy, ey:ey+1, fx), pos_zero)
            end

            # Lemma SETZ-ESP1: Boundary case of SETZ-ESP0 with guaranteed carry.
            verifier("SETZ-ESP1-X", same_sign & (ex == ey + 1) & (ey == fx > fy) & (ex < fy + (p-1))) do lemma
                add_case!(lemma, (sx, ex+1, fy), pos_zero)
            end
            verifier("SETZ-ESP1-Y", same_sign & (ey == ex + 1) & (ex == fy > fx) & (ey < fx + (p-1))) do lemma
                add_case!(lemma, (sy, ey+1, fx), pos_zero)
            end

            # Lemma SETZ-ESC: Addends have same sign and completely overlap.
            verifier("SETZ-ESC-X", same_sign & (ex > ey) & (fx < fy) & (ex < fx + (p-1))) do lemma
                add_case!(lemma, (sx, ex:ex+1, fx), pos_zero)
            end
            verifier("SETZ-ESC-Y", same_sign & (ey > ex) & (fy < fx) & (ey < fy + (p-1))) do lemma
                add_case!(lemma, (sy, ey:ey+1, fy), pos_zero)
            end

            # Lemma SETZ-ESS: Addends have same sign and exponent.
            verifier("SETZ-ESS-X", same_sign & (ex == ey) & (fx < fy) & (ex < fx + (p-1)) & (ey < fy + (p-1))) do lemma
                add_case!(lemma, (sx, ex+1, fx), pos_zero)
            end
            verifier("SETZ-ESS-Y", same_sign & (ex == ey) & (fx > fy) & (ex < fx + (p-1)) & (ey < fy + (p-1))) do lemma
                add_case!(lemma, (sx, ex+1, fy), pos_zero)
            end

            # Lemma SETZ-EDP0: Addends have different signs and partially overlap.
            verifier("SETZ-EDP0-X", diff_sign & (ex > ey + 1 > fx > fy) & (ex < fy + p)) do lemma
                add_case!(lemma, (sx, ex-1:ex, fy), pos_zero)
            end
            verifier("SETZ-EDP0-Y", diff_sign & (ey > ex + 1 > fy > fx) & (ey < fx + p)) do lemma
                add_case!(lemma, (sy, ey-1:ey, fx), pos_zero)
            end

            # Lemma SETZ-EDP1: Boundary case of SETZ-EDP0 with more possible cancellation.
            verifier("SETZ-EDP1-X", diff_sign & (ex == ey + 1) & (ey > fx > fy) & (ex < fy + p)) do lemma
                add_case!(lemma, (sx, fx:ex, fy), pos_zero)
            end
            verifier("SETZ-EDP1-Y", diff_sign & (ey == ex + 1) & (ex > fy > fx) & (ey < fx + p)) do lemma
                add_case!(lemma, (sy, fy:ey, fx), pos_zero)
            end

            # Lemma SETZ-EDP2: Boundary case of SETZ-EDP1 with guaranteed cancellation.
            verifier("SETZ-EDP2-X", diff_sign & (ex == ey + 1 == fx) & (fx > fy + 1)) do lemma
                add_case!(lemma, (sx, fy:ex-2, fy), pos_zero)
            end
            verifier("SETZ-EDP2-Y", diff_sign & (ey == ex + 1 == fy) & (fy > fx + 1)) do lemma
                add_case!(lemma, (sy, fx:ey-2, fx), pos_zero)
            end

            # Lemma SETZ-EDP3: Boundary case of SETZ-EDP2 with less guaranteed cancellation.
            verifier("SETZ-EDP3-X", diff_sign & (ex == ey + 1 == fx == fy + 1)) do lemma
                add_case!(lemma, (sx, fy:ex-1, fy), pos_zero)
            end
            verifier("SETZ-EDP3-Y", diff_sign & (ey == ex + 1 == fy == fx + 1)) do lemma
                add_case!(lemma, (sy, fx:ey-1, fx), pos_zero)
            end

            # Lemma SETZ-EDC0: Addends have different signs and completely overlap.
            verifier("SETZ-EDC0-X", diff_sign & (ex > ey + 1) & (fx < fy)) do lemma
                add_case!(lemma, (sx, ex-1:ex, fx), pos_zero)
            end
            verifier("SETZ-EDC0-Y", diff_sign & (ey > ex + 1) & (fy < fx)) do lemma
                add_case!(lemma, (sy, ey-1:ey, fy), pos_zero)
            end

            # Lemma SETZ-EDC1: Boundary case of SETZ-EDC0 with more possible cancellation.
            verifier("SETZ-EDC1-X", diff_sign & (ex == ey + 1) & (fx < fy)) do lemma
                add_case!(lemma, (sx, fy:ex, fx), pos_zero)
            end
            verifier("SETZ-EDC1-Y", diff_sign & (ey == ex + 1) & (fy < fx)) do lemma
                add_case!(lemma, (sy, fx:ey, fy), pos_zero)
            end

            # Lemma SETZ-EDC2: Boundary case of SETZ-EDC0 with guaranteed cancellation.
            verifier("SETZ-EDC2-X", diff_sign & (ex == ey == fy) & (fx < fy)) do lemma
                add_case!(lemma, (sx, fx:ex-1, fx), pos_zero)
            end
            verifier("SETZ-EDC2-Y", diff_sign & (ey == ex == fx) & (fy < fx)) do lemma
                add_case!(lemma, (sy, fy:ey-1, fy), pos_zero)
            end

            # Lemma SETZ-EDS0: Addends have same exponent and different signs.
            verifier("SETZ-EDS0-X", diff_sign & (ex == ey) & (fx < fy) & (ex > fx + 1) & (ey > fy + 1)) do lemma
                add_case!(lemma, (±, fx:ex-1, fx), pos_zero)
            end
            verifier("SETZ-EDS0-Y", diff_sign & (ex == ey) & (fx > fy) & (ex > fx + 1) & (ey > fy + 1)) do lemma
                add_case!(lemma, (±, fy:ey-1, fy), pos_zero)
            end

            # Lemma SETZ-EDS1: Boundary case of SETZ-EDS0 where two leading bits cancel.
            verifier("SETZ-EDS1-X", diff_sign & (ex == ey) & (ex > fx + 1) & (ey == fy + 1)) do lemma
                add_case!(lemma, (±, fx:ex-2, fx), pos_zero)
            end
            verifier("SETZ-EDS1-Y", diff_sign & (ex == ey) & (ex == fx + 1) & (ey > fy + 1)) do lemma
                add_case!(lemma, (±, fy:ey-2, fy), pos_zero)
            end

        end
        if iszero(verifier.count[])
            unverified_count += 1
        end
    end

    println(T, " TwoSum-SETZ lemmas:")
    for (name, count) in sort!(collect(lemma_dict))
        println("    ", name, ": ", count)
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
# println("Verified all Float16 TwoSum-SETZ lemmas.")
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
# println("Verified all BFloat16 TwoSum-SETZ lemmas.")
flush(stdout)
