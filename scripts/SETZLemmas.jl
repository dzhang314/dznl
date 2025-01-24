using BFloat16s: BFloat16

push!(LOAD_PATH, @__DIR__)
using FloatSummaries: summarize_setz, unsafe_exponent, mantissa_trailing_zeros,
    normal_summaries, normal_two_sum_summaries,
    EFTSummary, LemmaVerifier, LemmaHelper


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

            ########################################### LEMMA FAMILY SETZ-E (15)

            # Lemmas in Family SETZ-E (for "exact") apply to addends with
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

            ############################################ LEMMA FAMILY SETZ-O (3)

            # Lemmas in Family SETZ-O (for "overlap") apply to addends
            # that completely overlap but cannot be summed exactly.

            # All hypotheses are strictly necessary.
            verifier("SETZ-O0-X", same_sign & (ex == fx + (p-1)) & (ex > ey > fy > fx)) do lemma
                add_case!(lemma, (sx, ex  , fx         ), pos_zero             )
                add_case!(lemma, (sx, ex+1, ex-(p-3):ey), (± , fx:ex-(p-1), fx))
                add_case!(lemma, (sx, ex+1, ex+1       ), (sy, fx:ex-(p-1), fx))
            end
            verifier("SETZ-O0-Y", same_sign & (ey == fy + (p-1)) & (ey > ex > fx > fy)) do lemma
                add_case!(lemma, (sy, ey  , fy         ), pos_zero             )
                add_case!(lemma, (sy, ey+1, ey-(p-3):ex), (± , fy:ey-(p-1), fy))
                add_case!(lemma, (sy, ey+1, ey+1       ), (sx, fy:ey-(p-1), fy))
            end

            # All hypotheses are strictly necessary.
            verifier("SETZ-O1-X", same_sign & (ex == fx + (p-1)) & (ex > ey == fy > fx + 1)) do lemma
                add_case!(lemma, (sx, ex  , fx           ), pos_zero              )
                add_case!(lemma, (sx, ex+1, ex-(p-3):ey-1), ( ± , fx:ex-(p-1), fx))
                add_case!(lemma, (sx, ex+1, ey           ), (!sy, fx:ex-(p-1), fx))
                add_case!(lemma, (sx, ex+1, ex+1         ), ( sy, fx:ex-(p-1), fx))
            end
            verifier("SETZ-O1-Y", same_sign & (ey == fy + (p-1)) & (ey > ex == fx > fy + 1)) do lemma
                add_case!(lemma, (sy, ey  , fy           ), pos_zero              )
                add_case!(lemma, (sy, ey+1, ey-(p-3):ex-1), ( ± , fy:ey-(p-1), fy))
                add_case!(lemma, (sy, ey+1, ex           ), (!sx, fy:ey-(p-1), fy))
                add_case!(lemma, (sy, ey+1, ey+1         ), ( sx, fy:ey-(p-1), fy))
            end

            # All hypotheses are strictly necessary.
            verifier("SETZ-O2-X", same_sign & (ex == fx + (p-1)) & (ey == fy == fx + 1)) do lemma
                add_case!(lemma, (sx, ex  , fx  ), pos_zero             )
                add_case!(lemma, (sx, ex+1, ex+1), (sy, fx:ex-(p-1), fx))
            end
            verifier("SETZ-O2-Y", same_sign & (ey == fy + (p-1)) & (ex == fx == fy + 1)) do lemma
                add_case!(lemma, (sy, ey  , fy  ), pos_zero             )
                add_case!(lemma, (sy, ey+1, ey+1), (sx, fy:ey-(p-1), fy))
            end

            ############################################ LEMMA FAMILY SETZ-1 (4)

            verifier("SETZ-1-X", (ex < ey + p) & (ex > fy + p) & (fx > ey + 1) & ((ex > fx) | same_sign)) do lemma
                add_case!(lemma, (sx, ex, ex-(p-1):ey-1), ( ± , fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex, ey           ), ( sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex, ey+1         ), (!sy, fy:ex-(p+1), fy))
            end
            verifier("SETZ-1-Y", (ey < ex + p) & (ey > fx + p) & (fy > ex + 1) & ((ey > fy) | same_sign)) do lemma
                add_case!(lemma, (sy, ey, ey-(p-1):ex-1), ( ± , fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey, ex           ), ( sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey, ex+1         ), (!sx, fx:ey-(p+1), fx))
            end

            verifier("SETZ-1A-X", (ex == ey + p) & (ex > fy + p) & (fx > ey + 1) & ((ex > fx) | same_sign)) do lemma
                add_case!(lemma, (sx, ex, ey+1), (!sy, fy:ex-(p+1), fy))
            end
            verifier("SETZ-1A-Y", (ey == ex + p) & (ey > fx + p) & (fy > ex + 1) & ((ey > fy) | same_sign)) do lemma
                add_case!(lemma, (sy, ey, ex+1), (!sx, fx:ey-(p+1), fx))
            end

            verifier("SETZ-1B0-X", (ex < ey + (p-1)) & (ex == fy + p) & (fx > ey + 1) & ((ex > fx) | same_sign)) do lemma
                add_case!(lemma, (sx, ex, ex-(p-2):ey-1), ( ± , fy:ex-p, fy))
                add_case!(lemma, (sx, ex, ey           ), ( sy, fy:ex-p, fy))
                add_case!(lemma, (sx, ex, ey+1         ), (!sy, fy:ex-p, fy))
            end
            verifier("SETZ-1B0-Y", (ey < ex + (p-1)) & (ey == fx + p) & (fy > ex + 1) & ((ey > fy) | same_sign)) do lemma
                add_case!(lemma, (sy, ey, ey-(p-2):ex-1), ( ± , fx:ey-p, fx))
                add_case!(lemma, (sy, ey, ex           ), ( sx, fx:ey-p, fx))
                add_case!(lemma, (sy, ey, ex+1         ), (!sx, fx:ey-p, fx))
            end

            verifier("SETZ-1B1-X", (ex == ey + (p-1)) & (ex == fy + p) & (fx > ey + 1) & ((ex > fx) | same_sign)) do lemma
                add_case!(lemma, (sx, ex, ey+1), (!sy, fy:ex-p, fy))
            end
            verifier("SETZ-1B1-Y", (ey == ex + (p-1)) & (ey == fx + p) & (fy > ex + 1) & ((ey > fy) | same_sign)) do lemma
                add_case!(lemma, (sy, ey, ex+1), (!sx, fx:ey-p, fx))
            end

            ########################################### LEMMA FAMILY SETZ-2 (18)

            # All hypotheses are strictly necessary.
            verifier("SETZ-2-X", same_sign & (ex > fy + p) & (fx < ey)) do lemma
                add_case!(lemma, (sx, ex  , ex-(p-1):ex-1), ( ± , fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex+1, ex-(p-2):ey  ), ( ± , fy:ex-p    , fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), (!sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), ( sy, fy:ex-p    , fy))
            end
            verifier("SETZ-2-Y", same_sign & (ey > fx + p) & (fy < ex)) do lemma
                add_case!(lemma, (sy, ey  , ey-(p-1):ey-1), ( ± , fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey+1, ey-(p-2):ex  ), ( ± , fx:ey-p    , fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), (!sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), ( sx, fx:ey-p    , fx))
            end

            # All hypotheses are strictly necessary.
            verifier("SETZ-2A0-X", same_sign & (ex == fy + p) & (fx < ey) & (ey < fy + (p-1))) do lemma
                add_case!(lemma, (sx, ex  , ex-(p-2):ex-1), (±, fy:ex-p, fy))
                add_case!(lemma, (sx, ex+1, ex-(p-2):ey  ), (±, fy:ex-p, fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), (±, fy:ex-p, fy))
            end
            verifier("SETZ-2A0-Y", same_sign & (ey == fx + p) & (fy < ex) & (ex < fx + (p-1))) do lemma
                add_case!(lemma, (sy, ey  , ey-(p-2):ey-1), (±, fx:ey-p, fx))
                add_case!(lemma, (sy, ey+1, ey-(p-2):ex  ), (±, fx:ey-p, fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), (±, fx:ey-p, fx))
            end

            verifier("SETZ-2A1-X", same_sign & (ex == fy + p) & (fx + 1 < ey) & (ey == fy + (p-1))) do lemma
                add_case!(lemma, (sx, ex  , ex-(p-2):ex-2), (±, fy:ex-p, fy))
                add_case!(lemma, (sx, ex+1, ex-(p-2):ey  ), (±, fy:ex-p, fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), (±, fy:ex-p, fy))
            end
            verifier("SETZ-2A1-Y", same_sign & (ey == fx + p) & (fy + 1 < ex) & (ex == fx + (p-1))) do lemma
                add_case!(lemma, (sy, ey  , ey-(p-2):ey-2), (±, fx:ey-p, fx))
                add_case!(lemma, (sy, ey+1, ey-(p-2):ex  ), (±, fx:ey-p, fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), (±, fx:ey-p, fx))
            end

            verifier("SETZ-2A2-X", same_sign & (ex == fy + p) & (fx + 1 == ey) & (ey == fy + (p-1))) do lemma
                add_case!(lemma, (sx, ex  , ex-(p-2):ey-2), (± , fy:ex-p, fy))
                add_case!(lemma, (sx, ex  , ey-1         ), (sy, fy:ex-p, fy))
                add_case!(lemma, (sx, ex+1, ex-(p-2):ey  ), (± , fy:ex-p, fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), (± , fy:ex-p, fy))
            end
            verifier("SETZ-2A2-Y", same_sign & (ey == fx + p) & (fy + 1 == ex) & (ex == fx + (p-1))) do lemma
                add_case!(lemma, (sy, ey  , ey-(p-2):ex-2), (± , fx:ey-p, fx))
                add_case!(lemma, (sy, ey  , ex-1         ), (sx, fx:ey-p, fx))
                add_case!(lemma, (sy, ey+1, ey-(p-2):ex  ), (± , fx:ey-p, fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), (± , fx:ey-p, fx))
            end

            # All hypotheses are strictly necessary.
            verifier("SETZ-2B0-X", same_sign & (ex > fy + p) & (fx == ey) & (ex < fx + (p-1))) do lemma
                add_case!(lemma, (sx, ex  , ex-(p-1):ey-1), ( ± , fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  , ey           ), (!sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  , ey+1:ex-1    ), ( sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex+1, ex-(p-2):ey-1), ( ± , fy:ex-p    , fy))
                add_case!(lemma, (sx, ex+1, ey           ), (!sy, fy:ex-p    , fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), ( sy, fy:ex-p    , fy))
            end
            verifier("SETZ-2B0-Y", same_sign & (ey > fx + p) & (fy == ex) & (ey < fy + (p-1))) do lemma
                add_case!(lemma, (sy, ey  , ey-(p-1):ex-1), ( ± , fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  , ex           ), (!sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  , ex+1:ey-1    ), ( sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey+1, ey-(p-2):ex-1), ( ± , fx:ey-p    , fx))
                add_case!(lemma, (sy, ey+1, ex           ), (!sx, fx:ey-p    , fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), ( sx, fx:ey-p    , fx))
            end

            verifier("SETZ-2B1-X", same_sign & (ex > fy + p) & (fx == ey) & (ex == fx + (p-1))) do lemma
                add_case!(lemma, (sx, ex  , ey       ), (!sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  , ey+1:ex-1), ( sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex+1, ex+1     ), ( sy, fy:ex-p    , fy))
            end
            verifier("SETZ-2B1-Y", same_sign & (ey > fx + p) & (fy == ex) & (ey == fy + (p-1))) do lemma
                add_case!(lemma, (sy, ey  , ex       ), (!sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  , ex+1:ey-1), ( sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey+1, ey+1     ), ( sx, fx:ey-p    , fx))
            end

            # All hypotheses are strictly necessary.
            verifier("SETZ-2C0-X", same_sign & (ex == fy + (p-1)) & (fx < ey) & (ex < fx + (p-1)) & (ey < fy + (p-1))) do lemma
                add_case!(lemma, (sx, ex  , fy         ), pos_zero             )
                add_case!(lemma, (sx, ex+1, ex-(p-3):ey), (± , fy:ex-(p-1), fy))
                add_case!(lemma, (sx, ex+1, ex+1       ), (sy, fy:ex-(p-1), fy))
            end
            verifier("SETZ-2C0-Y", same_sign & (ey == fx + (p-1)) & (fy < ex) & (ey < fy + (p-1)) & (ex < fx + (p-1))) do lemma
                add_case!(lemma, (sy, ey  , fx         ), pos_zero             )
                add_case!(lemma, (sy, ey+1, ey-(p-3):ex), (± , fx:ey-(p-1), fx))
                add_case!(lemma, (sy, ey+1, ey+1       ), (sx, fx:ey-(p-1), fx))
            end

            verifier("SETZ-2C1-X", same_sign & (ex == fy + (p-1)) & (fx < ey) & (ex < fx + (p-1)) & (ey == fy + (p-1))) do lemma
                add_case!(lemma, (sx, ex+1, ex-(p-3):ey), (±, fy:ex-(p-1), fy))
            end
            verifier("SETZ-2C1-Y", same_sign & (ey == fx + (p-1)) & (fy < ex) & (ey < fy + (p-1)) & (ex == fx + (p-1))) do lemma
                add_case!(lemma, (sy, ey+1, ey-(p-3):ex), (±, fx:ey-(p-1), fx))
            end

            # All hypotheses are strictly necessary.
            verifier("SETZ-2D0-X", same_sign & (ex > fy + p) & (fx == ey + 1) & (ex < fx + (p-1))) do lemma
                add_case!(lemma, (sx, ex  , ex-(p-1):ey-1), ( ± , fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  , ey           ), ( sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  , ey+2:ex-1    ), (!sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), (!sy, fy:ex-(p+1), fy))
            end
            verifier("SETZ-2D0-Y", same_sign & (ey > fx + p) & (fy == ex + 1) & (ey < fy + (p-1))) do lemma
                add_case!(lemma, (sy, ey  , ey-(p-1):ex-1), ( ± , fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  , ex           ), ( sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  , ex+2:ey-1    ), (!sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), (!sx, fx:ey-(p+1), fx))
            end

            verifier("SETZ-2D1-X", same_sign & (ex > fy + p) & (fx == ey + 1) & (ex == fx + (p-1))) do lemma
                add_case!(lemma, (sx, ex  , ey+2:ex-1), (!sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex+1, ex+1     ), (!sy, fy:ex-(p+1), fy))
            end
            verifier("SETZ-2D1-Y", same_sign & (ey > fx + p) & (fy == ex + 1) & (ey == fy + (p-1))) do lemma
                add_case!(lemma, (sy, ey  , ex+2:ey-1), (!sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey+1, ey+1     ), (!sx, fx:ey-(p+1), fx))
            end

            # All hypotheses are strictly necessary.
            verifier("SETZ-2AB0-X", same_sign & (ex == fy + p) & (fx == ey) & (ex < fx + (p-1)) & (ey < fy + (p-1))) do lemma
                add_case!(lemma, (sx, ex  , ex-(p-2):ey-1), ( ± , fy:ex-p, fy))
                add_case!(lemma, (sx, ex  , ey           ), (!sy, fy:ex-p, fy))
                add_case!(lemma, (sx, ex  , ey+1:ex-1    ), ( sy, fy:ex-p, fy))
                add_case!(lemma, (sx, ex+1, ex-(p-2):ey-1), ( ± , fy:ex-p, fy))
                add_case!(lemma, (sx, ex+1, ey           ), (!sy, fy:ex-p, fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), ( sy, fy:ex-p, fy))
            end
            verifier("SETZ-2AB0-Y", same_sign & (ey == fx + p) & (fy == ex) & (ey < fy + (p-1)) & (ex < fx + (p-1))) do lemma
                add_case!(lemma, (sy, ey  , ey-(p-2):ex-1), ( ± , fx:ey-p, fx))
                add_case!(lemma, (sy, ey  , ex           ), (!sx, fx:ey-p, fx))
                add_case!(lemma, (sy, ey  , ex+1:ey-1    ), ( sx, fx:ey-p, fx))
                add_case!(lemma, (sy, ey+1, ey-(p-2):ex-1), ( ± , fx:ey-p, fx))
                add_case!(lemma, (sy, ey+1, ex           ), (!sx, fx:ey-p, fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), ( sx, fx:ey-p, fx))
            end

            verifier("SETZ-2AB1-X", same_sign & (ex == fy + p) & (fx == ey) & (ex == fx + (p-1))) do lemma
                add_case!(lemma, (sx, ex  , ey+1:ex-1), (sy, fy:ex-p, fy))
                add_case!(lemma, (sx, ex+1, ex+1     ), (sy, fy:ex-p, fy))
            end
            verifier("SETZ-2AB1-Y", same_sign & (ey == fx + p) & (fy == ex) & (ey == fy + (p-1))) do lemma
                add_case!(lemma, (sy, ey  , ex+1:ey-1), (sx, fx:ey-p, fx))
                add_case!(lemma, (sy, ey+1, ey+1     ), (sx, fx:ey-p, fx))
            end

            verifier("SETZ-2AB2-X", same_sign & (ex == fy + p) & (fx == ey) & (ey == fy + (p-1))) do lemma
                add_case!(lemma, (sx, ex+1, ex-(p-2):ey-1), ( ± , fy:ex-p, fy))
                add_case!(lemma, (sx, ex+1, ey           ), (!sy, fy:ex-p, fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), ( sy, fy:ex-p, fy))
            end
            verifier("SETZ-2AB2-Y", same_sign & (ey == fx + p) & (fy == ex) & (ex == fx + (p-1))) do lemma
                add_case!(lemma, (sy, ey+1, ey-(p-2):ex-1), ( ± , fx:ey-p, fx))
                add_case!(lemma, (sy, ey+1, ex           ), (!sx, fx:ey-p, fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), ( sx, fx:ey-p, fx))
            end

            # All hypotheses are strictly necessary.
            verifier("SETZ-2BC0-X", same_sign & (ex == fy + (p-1)) & (fx == ey) & (ey > fy + 1) & (ey < fy + (p-2))) do lemma
                add_case!(lemma, (sx, ex  , fy           ), pos_zero              )
                add_case!(lemma, (sx, ex+1, ex-(p-3):ey-1), ( ± , fy:ex-(p-1), fy))
                add_case!(lemma, (sx, ex+1, ey           ), (!sy, fy:ex-(p-1), fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), ( sy, fy:ex-(p-1), fy))
            end
            verifier("SETZ-2BC0-Y", same_sign & (ey == fx + (p-1)) & (fy == ex) & (ex > fx + 1) & (ex < fx + (p-2))) do lemma
                add_case!(lemma, (sy, ey  , fx           ), pos_zero              )
                add_case!(lemma, (sy, ey+1, ey-(p-3):ex-1), ( ± , fx:ey-(p-1), fx))
                add_case!(lemma, (sy, ey+1, ex           ), (!sx, fx:ey-(p-1), fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), ( sx, fx:ey-(p-1), fx))
            end

            # All hypotheses are strictly necessary.
            verifier("SETZ-2BC1-X", same_sign & (ex == fy + (p-1)) & (fx == ey) & (ey > fy + (p-3))) do lemma
                add_case!(lemma, (sx, ex+1, ex-(p-3):ey-1), ( ± , fy:ex-(p-1), fy))
                add_case!(lemma, (sx, ex+1, ey           ), (!sy, fy:ex-(p-1), fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), ( sy, fy:ex-(p-1), fy))
            end
            verifier("SETZ-2BC1-Y", same_sign & (ey == fx + (p-1)) & (fy == ex) & (ex > fx + (p-3))) do lemma
                add_case!(lemma, (sy, ey+1, ey-(p-3):ex-1), ( ± , fx:ey-(p-1), fx))
                add_case!(lemma, (sy, ey+1, ex           ), (!sx, fx:ey-(p-1), fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), ( sx, fx:ey-(p-1), fx))
            end

            verifier("SETZ-2BC2-X", same_sign & (ex == fy + (p-1)) & (fx == ey) & (ey == fy + 1)) do lemma
                add_case!(lemma, (sx, ex  , fy  ), pos_zero             )
                add_case!(lemma, (sx, ex+1, ex+1), (sy, fy:ex-(p-1), fy))
            end
            verifier("SETZ-2BC2-Y", same_sign & (ey == fx + (p-1)) & (fy == ex) & (ex == fx + 1)) do lemma
                add_case!(lemma, (sy, ey  , fx  ), pos_zero             )
                add_case!(lemma, (sy, ey+1, ey+1), (sx, fx:ey-(p-1), fx))
            end

            # All hypotheses are strictly necessary.
            verifier("SETZ-2AD0-X", same_sign & (ex == fy + p) & (fx == ey + 1) & (ex < fx + (p-2))) do lemma
                add_case!(lemma, (sx, ex  , ex-(p-2):ey-1), ( ± , fy:ex-p, fy))
                add_case!(lemma, (sx, ex  , ey           ), ( sy, fy:ex-p, fy))
                add_case!(lemma, (sx, ex  , ey+2:ex-1    ), (!sy, fy:ex-p, fy))
                add_case!(lemma, (sx, ex+1, ex+1         ), (!sy, fy:ex-p, fy))
            end
            verifier("SETZ-2AD0-Y", same_sign & (ey == fx + p) & (fy == ex + 1) & (ey < fy + (p-2))) do lemma
                add_case!(lemma, (sy, ey  , ey-(p-2):ex-1), ( ± , fx:ey-p, fx))
                add_case!(lemma, (sy, ey  , ex           ), ( sx, fx:ey-p, fx))
                add_case!(lemma, (sy, ey  , ex+2:ey-1    ), (!sx, fx:ey-p, fx))
                add_case!(lemma, (sy, ey+1, ey+1         ), (!sx, fx:ey-p, fx))
            end

            verifier("SETZ-2AD1-X", same_sign & (ex == fy + p) & (fx == ey + 1) & (ex > fx + (p-3))) do lemma
                add_case!(lemma, (sx, ex  , ey+2:ex-1), (!sy, fy:ex-p, fy))
                add_case!(lemma, (sx, ex+1, ex+1     ), (!sy, fy:ex-p, fy))
            end
            verifier("SETZ-2AD1-Y", same_sign & (ey == fx + p) & (fy == ex + 1) & (ey > fy + (p-3))) do lemma
                add_case!(lemma, (sy, ey  , ex+2:ey-1), (!sx, fx:ey-p, fx))
                add_case!(lemma, (sy, ey+1, ey+1     ), (!sx, fx:ey-p, fx))
            end

            ########################################### LEMMA FAMILY SETZ-3 (13)

            # All hypotheses are strictly necessary.
            verifier("SETZ-3-X", diff_sign & (ex > fy + (p+1)) & (fx < ey)) do lemma
                add_case!(lemma, (sx, ex-1, ex-p:ey      ), ( ± , fy:ex-(p+2), fy))
                add_case!(lemma, (sx, ex  , ex-(p-1):ex-1), ( ± , fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  , ex           ), ( sy, fy:ex-(p+2), fy))
                add_case!(lemma, (sx, ex  , ex           ), (!sy, fy:ex-(p+1), fy))
            end
            verifier("SETZ-3-Y", diff_sign & (ey > fx + (p+1)) & (fy < ex)) do lemma
                add_case!(lemma, (sy, ey-1, ey-p:ex      ), ( ± , fx:ey-(p+2), fx))
                add_case!(lemma, (sy, ey  , ey-(p-1):ey-1), ( ± , fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  , ey           ), ( sx, fx:ey-(p+2), fx))
                add_case!(lemma, (sy, ey  , ey           ), (!sx, fx:ey-(p+1), fx))
            end

            # All hypotheses are strictly necessary.
            verifier("SETZ-3A-X", diff_sign & (ex == fy + (p+1)) & (fx < ey)) do lemma
                add_case!(lemma, (sx, ex-1, ex-(p-1):ey), (±, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  , ex-(p-1):ex), (±, fy:ex-(p+1), fy))
            end
            verifier("SETZ-3A-Y", diff_sign & (ey == fx + (p+1)) & (fy < ex)) do lemma
                add_case!(lemma, (sy, ey-1, ey-(p-1):ex), (±, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  , ey-(p-1):ey), (±, fx:ey-(p+1), fx))
            end

            # All hypotheses are strictly necessary.
            verifier("SETZ-3B-X", diff_sign & (ex > fy + (p+1)) & (fx == ey)) do lemma
                add_case!(lemma, (sx, ex-1, ex-p:ey-1    ), ( ± , fy:ex-(p+2), fy))
                add_case!(lemma, (sx, ex-1, ey           ), (!sy, fy:ex-(p+2), fy))
                add_case!(lemma, (sx, ex  , ex-(p-1):ey-1), ( ± , fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  , ey           ), (!sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  , ey+1:ex-1    ), ( sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  , ex           ), ( sy, fy:ex-(p+2), fy))
            end
            verifier("SETZ-3B-Y", diff_sign & (ey > fx + (p+1)) & (fy == ex)) do lemma
                add_case!(lemma, (sy, ey-1, ey-p:ex-1    ), ( ± , fx:ey-(p+2), fx))
                add_case!(lemma, (sy, ey-1, ex           ), (!sx, fx:ey-(p+2), fx))
                add_case!(lemma, (sy, ey  , ey-(p-1):ex-1), ( ± , fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  , ex           ), (!sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  , ex+1:ey-1    ), ( sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  , ey           ), ( sx, fx:ey-(p+2), fx))
            end

            # All hypotheses are strictly necessary.
            verifier("SETZ-3C0-X", diff_sign & (ex == fy + p) & (fx < ey) & (ey < fy + (p-1))) do lemma
                add_case!(lemma, (sx, ex-1, fy           ), pos_zero          )
                add_case!(lemma, (sx, ex  , ex-(p-2):ex-1), ( ± , fy:ex-p, fy))
                add_case!(lemma, (sx, ex  , ex           ), (!sy, fy:ex-p, fy))
            end
            verifier("SETZ-3C0-Y", diff_sign & (ey == fx + p) & (fy < ex) & (ex < fx + (p-1))) do lemma
                add_case!(lemma, (sy, ey-1, fx           ), pos_zero          )
                add_case!(lemma, (sy, ey  , ey-(p-2):ey-1), ( ± , fx:ey-p, fx))
                add_case!(lemma, (sy, ey  , ey           ), (!sx, fx:ey-p, fx))
            end

            verifier("SETZ-3C1-X", diff_sign & (ex == fy + p) & (fx + 1 < ey) & (ey == fy + (p-1))) do lemma
                add_case!(lemma, (sx, fx:ex-1, fy           ), pos_zero          )
                add_case!(lemma, (sx, ex     , ex-(p-2):ex-2), ( ± , fy:ex-p, fy))
                add_case!(lemma, (sx, ex     , ex           ), (!sy, fy:ex-p, fy))
            end
            verifier("SETZ-3C1-Y", diff_sign & (ey == fx + p) & (fy + 1 < ex) & (ex == fx + (p-1))) do lemma
                add_case!(lemma, (sy, fy:ey-1, fx           ), pos_zero          )
                add_case!(lemma, (sy, ey     , ey-(p-2):ey-2), ( ± , fx:ey-p, fx))
                add_case!(lemma, (sy, ey     , ey           ), (!sx, fx:ey-p, fx))
            end

            # All hypotheses are strictly necessary.
            verifier("SETZ-3C2-X", diff_sign & (ex == fy + p) & (fx + 1 == ey) & (ey == fy + (p-1))) do lemma
                add_case!(lemma, (sx, ex-2:ex-1, fy           ), pos_zero          )
                add_case!(lemma, (sx, ex       , ex-(p-2):ey-2), ( ± , fy:ex-p, fy))
                add_case!(lemma, (sx, ex       , ey-1         ), ( sy, fy:ex-p, fy))
                add_case!(lemma, (sx, ex       , ex           ), (!sy, fy:ex-p, fy))
            end
            verifier("SETZ-3C2-Y", diff_sign & (ey == fx + p) & (fy + 1 == ex) & (ex == fx + (p-1))) do lemma
                add_case!(lemma, (sy, ey-2:ey-1, fx           ), pos_zero          )
                add_case!(lemma, (sy, ey       , ey-(p-2):ex-2), ( ± , fx:ey-p, fx))
                add_case!(lemma, (sy, ey       , ex-1         ), ( sx, fx:ey-p, fx))
                add_case!(lemma, (sy, ey       , ey           ), (!sx, fx:ey-p, fx))
            end

            # All hypotheses are strictly necessary.
            verifier("SETZ-3D0-X", diff_sign & (ex > fy + p) & (fx == ey + 1) & (ex < fx + (p-1))) do lemma
                add_case!(lemma, (sx, ex, ex-(p-1):ey-1), ( ± , fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex, ey           ), ( sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex, ey+2:ex      ), (!sy, fy:ex-(p+1), fy))
            end
            verifier("SETZ-3D0-Y", diff_sign & (ey > fx + p) & (fy == ex + 1) & (ey < fy + (p-1))) do lemma
                add_case!(lemma, (sy, ey, ey-(p-1):ex-1), ( ± , fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey, ex           ), ( sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey, ex+2:ey      ), (!sx, fx:ey-(p+1), fx))
            end

            # All hypotheses are strictly necessary.
            verifier("SETZ-3D1-X", diff_sign & (ex > fy + p) & (fx == ey + 1) & (ex == fx + (p-1))) do lemma
                add_case!(lemma, (sx, ex, ey+2:ex), (!sy, fy:ex-(p+1), fy))
            end
            verifier("SETZ-3D1-Y", diff_sign & (ey > fx + p) & (fy == ex + 1) & (ey == fy + (p-1))) do lemma
                add_case!(lemma, (sy, ey, ex+2:ey), (!sx, fx:ey-(p+1), fx))
            end

            # All hypotheses are strictly necessary.
            verifier("SETZ-3AB-X", diff_sign & (ex == fy + (p+1)) & (fx == ey)) do lemma
                add_case!(lemma, (sx, ex-1, ex-(p-1):ey-1), ( ± , fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex-1, ey           ), (!sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  , ex-(p-1):ey-1), ( ± , fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  , ey           ), (!sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex  , ey+1:ex      ), ( sy, fy:ex-(p+1), fy))
            end
            verifier("SETZ-3AB-Y", diff_sign & (ey == fx + (p+1)) & (fy == ex)) do lemma
                add_case!(lemma, (sy, ey-1, ey-(p-1):ex-1), ( ± , fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey-1, ex           ), (!sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  , ey-(p-1):ex-1), ( ± , fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  , ex           ), (!sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey  , ex+1:ey      ), ( sx, fx:ey-(p+1), fx))
            end

            verifier("SETZ-3BC0-X", diff_sign & (ex == fy + p) & (fx == ey) & (ex > fx + 1) & (ey > fy + 1)) do lemma
                add_case!(lemma, (sx, ex-1, fy           ), pos_zero          )
                add_case!(lemma, (sx, ex  , ex-(p-2):ey-1), ( ± , fy:ex-p, fy))
                add_case!(lemma, (sx, ex  , ey           ), (!sy, fy:ex-p, fy))
                add_case!(lemma, (sx, ex  , ey+1:ex-1    ), ( sy, fy:ex-p, fy))
            end
            verifier("SETZ-3BC0-Y", diff_sign & (ey == fx + p) & (fy == ex) & (ey > fy + 1) & (ex > fx + 1)) do lemma
                add_case!(lemma, (sy, ey-1, fx           ), pos_zero          )
                add_case!(lemma, (sy, ey  , ey-(p-2):ex-1), ( ± , fx:ey-p, fx))
                add_case!(lemma, (sy, ey  , ex           ), (!sx, fx:ey-p, fx))
                add_case!(lemma, (sy, ey  , ex+1:ey-1    ), ( sx, fx:ey-p, fx))
            end

            verifier("SETZ-3BC1-X", diff_sign & (ex == fy + p) & (fx == ey) & (ey == fy + 1)) do lemma
                add_case!(lemma, (sx, ex-1, fy       ), pos_zero         )
                add_case!(lemma, (sx, ex  , ey+1:ex-1), (sy, fy:ex-p, fy))
            end
            verifier("SETZ-3BC1-Y", diff_sign & (ey == fx + p) & (fy == ex) & (ex == fx + 1)) do lemma
                add_case!(lemma, (sy, ey-1, fx       ), pos_zero         )
                add_case!(lemma, (sy, ey  , ex+1:ey-1), (sx, fx:ey-p, fx))
            end

            verifier("SETZ-3CD0-X", diff_sign & (ex == fy + p) & (fx == ey + 1) & (ex > fx) & (ey > fy + 1)) do lemma
                add_case!(lemma, (sx, ex, ex-(p-2):ey-1), ( ± , fy:ex-p, fy))
                add_case!(lemma, (sx, ex, ey           ), ( sy, fy:ex-p, fy))
                add_case!(lemma, (sx, ex, ey+2:ex      ), (!sy, fy:ex-p, fy))
            end
            verifier("SETZ-3CD0-Y", diff_sign & (ey == fx + p) & (fy == ex + 1) & (ey > fy) & (ex > fx + 1)) do lemma
                add_case!(lemma, (sy, ey, ey-(p-2):ex-1), ( ± , fx:ey-p, fx))
                add_case!(lemma, (sy, ey, ex           ), ( sx, fx:ey-p, fx))
                add_case!(lemma, (sy, ey, ex+2:ey      ), (!sx, fx:ey-p, fx))
            end

            verifier("SETZ-3CD1-X", diff_sign & (ex == fy + p) & (fx == ey + 1) & (ey < fy + 2)) do lemma
                add_case!(lemma, (sx, ex, ey+2:ex), (!sy, fy:ex-p, fy))
            end
            verifier("SETZ-3CD1-Y", diff_sign & (ey == fx + p) & (fy == ex + 1) & (ex < fx + 2)) do lemma
                add_case!(lemma, (sy, ey, ex+2:ey), (!sx, fx:ey-p, fx))
            end

            ############################################ LEMMA FAMILY SETZ-4 (4)

            verifier("SETZ-4-X", diff_sign & (ex > fy + (p+1)) & (fx < ey + (p+1)) & (ex == fx)) do lemma
                add_case!(lemma, (sx, ex-1, ex-p:ey-1), ( ± , fy:ex-(p+2), fy))
                add_case!(lemma, (sx, ex-1, ey       ), ( sy, fy:ex-(p+2), fy))
                add_case!(lemma, (sx, ex-1, ey+1     ), (!sy, fy:ex-(p+2), fy))
            end
            verifier("SETZ-4-Y", diff_sign & (ey > fx + (p+1)) & (fy < ex + (p+1)) & (ey == fy)) do lemma
                add_case!(lemma, (sy, ey-1, ey-p:ex-1), ( ± , fx:ey-(p+2), fx))
                add_case!(lemma, (sy, ey-1, ex       ), ( sx, fx:ey-(p+2), fx))
                add_case!(lemma, (sy, ey-1, ex+1     ), (!sx, fx:ey-(p+2), fx))
            end

            verifier("SETZ-4A0-X", diff_sign & (ex == fy + (p+1)) & (fx < ey + p) & (ex == fx)) do lemma
                add_case!(lemma, (sx, ex-1, ex-(p-1):ey-1), ( ± , fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex-1, ey           ), ( sy, fy:ex-(p+1), fy))
                add_case!(lemma, (sx, ex-1, ey+1         ), (!sy, fy:ex-(p+1), fy))
            end
            verifier("SETZ-4A0-Y", diff_sign & (ey == fx + (p+1)) & (fy < ex + p) & (ey == fy)) do lemma
                add_case!(lemma, (sy, ey-1, ey-(p-1):ex-1), ( ± , fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey-1, ex           ), ( sx, fx:ey-(p+1), fx))
                add_case!(lemma, (sy, ey-1, ex+1         ), (!sx, fx:ey-(p+1), fx))
            end

            verifier("SETZ-4A1-X", diff_sign & (ex == fy + (p+1)) & (fx == ey + p) & (ex == fx)) do lemma
                add_case!(lemma, (sx, ex-1, ex-(p-1):ey+1), (!sy, fy:ex-(p+1), fy))
            end
            verifier("SETZ-4A1-Y", diff_sign & (ey == fx + (p+1)) & (fy == ex + p) & (ey == fy)) do lemma
                add_case!(lemma, (sy, ey-1, ey-(p-1):ex+1), (!sx, fx:ey-(p+1), fx))
            end

            verifier("SETZ-4B-X", diff_sign & (ex > fy + (p+1)) & (fx == ey + (p+1)) & (ex == fx)) do lemma
                add_case!(lemma, (sx, ex-1, ex-p:ey+1), (!sy, fy:ex-(p+2), fy))
            end
            verifier("SETZ-4B-Y", diff_sign & (ey > fx + (p+1)) & (fy == ex + (p+1)) & (ey == fy)) do lemma
                add_case!(lemma, (sy, ey-1, ey-p:ex+1), (!sx, fx:ey-(p+2), fx))
            end

        end
        @assert isone(verifier.count[])
    end

    println(T, " TwoSum-SETZ lemmas:")
    for (name, count) in sort!(collect(lemma_dict))
        println("    ", name, ": ", count)
    end

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
println("Verified all Float16 TwoSum-SETZ lemmas.")
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
println("Verified all BFloat16 TwoSum-SETZ lemmas.")
flush(stdout)
