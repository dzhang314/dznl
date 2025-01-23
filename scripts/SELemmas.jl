using BFloat16s

push!(LOAD_PATH, @__DIR__)
using FloatSummaries


if !isfile("Float16TwoSumSE.bin")
    open("Float16TwoSumSE.bin", "w") do io
        write(io, normal_two_sum_summaries(summarize_se, Float16))
    end
end
@assert isfile("Float16TwoSumSE.bin")
@assert filesize("Float16TwoSumSE.bin") == 38_638 * sizeof(TwoSumSummary)
const FLOAT16_TWO_SUM_SE = Vector{TwoSumSummary}(undef, 38_638)
read!("Float16TwoSumSE.bin", FLOAT16_TWO_SUM_SE)


if !isfile("BFloat16TwoSumSE.bin")
    open("BFloat16TwoSumSE.bin", "w") do io
        write(io, normal_two_sum_summaries(summarize_se, BFloat16))
    end
end
@assert isfile("BFloat16TwoSumSE.bin")
@assert filesize("BFloat16TwoSumSE.bin") == 548_026 * sizeof(TwoSumSummary)
const BFLOAT16_TWO_SUM_SE = Vector{TwoSumSummary}(undef, 548_026)
read!("BFloat16TwoSumSE.bin", BFLOAT16_TWO_SUM_SE)


function main(::Type{T}, two_sum_summaries::Vector{TwoSumSummary}) where {T}

    p = precision(T)
    pos_zero = summarize_se(+zero(T))
    neg_zero = summarize_se(-zero(T))
    possible_inputs = normal_summaries(summarize_se, T)
    unverified_count = 0

    for x in possible_inputs, y in possible_inputs

        possible_results = find_possible_results(two_sum_summaries, x, y)
        sx = signbit(x)
        ex = unsafe_exponent(x)
        sy = signbit(y)
        ey = unsafe_exponent(y)
        x_zero = (x == pos_zero) | (x == neg_zero)
        y_zero = (y == pos_zero) | (y == neg_zero)
        same_sign = (sx == sy)
        diff_sign = (sx != sy)
        verified = 0

        if x_zero | y_zero ################################## LEMMA FAMILY Z (2)

            # Lemmas in Family Z (for "zero") apply to
            # cases where one or both addends are zero.

            # Lemma Z1: Both addends are zero.
            if (x == pos_zero) & (y == pos_zero)
                @assert only(possible_results) == (pos_zero, pos_zero)
                verified += 1
            end
            if (x == pos_zero) & (y == neg_zero)
                @assert only(possible_results) == (pos_zero, pos_zero)
                verified += 1
            end
            if (x == neg_zero) & (y == pos_zero)
                @assert only(possible_results) == (pos_zero, pos_zero)
                verified += 1
            end
            if (x == neg_zero) & (y == neg_zero)
                @assert only(possible_results) == (neg_zero, pos_zero)
                verified += 1
            end

            # Lemma Z2: One addend is zero.
            if y_zero & !x_zero
                @assert only(possible_results) == (x, pos_zero)
                verified += 1
            end
            if x_zero & !y_zero
                @assert only(possible_results) == (y, pos_zero)
                verified += 1
            end

        else #################################################### NONZERO LEMMAS

            # From this point forward, all lemma statements carry
            # an implicit assumption that both addends are nonzero.

            if (ex > ey + (p+1)) | ((ex == ey + (p+1)) & same_sign)
                @assert only(possible_results) == (x, y)
                verified += 1
            end
            if (ey > ex + (p+1)) | ((ey == ex + (p+1)) & same_sign)
                @assert only(possible_results) == (y, x)
                verified += 1
            end

        end

        if iszero(verified)
            unverified_count += 1
        end

    end
    println(T, ": ", unverified_count, " out of ",
        length(possible_inputs)^2, " unverified.")

end


main(Float16, FLOAT16_TWO_SUM_SE)
main(BFloat16, BFLOAT16_TWO_SUM_SE)
