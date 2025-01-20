using BFloat16s
using InteractiveUtils: code_native

push!(LOAD_PATH, @__DIR__)
using FloatSummaries

################################################################################


for i = typemin(UInt16):typemax(UInt16)
    x = reinterpret(Float16, i)
    if isnormal(x)
        s = summarize_se(x)
        @assert signbit(s) == signbit(x)
        @assert unsafe_exponent(s) == unsafe_exponent(x)
        @assert mantissa_leading_zeros(s) == 0
        @assert mantissa_leading_ones(s) == 0
        @assert mantissa_trailing_zeros(s) == 0
        @assert mantissa_trailing_ones(s) == 0
    end
end


for i = typemin(UInt16):typemax(UInt16)
    x = reinterpret(BFloat16, i)
    if isnormal(x)
        s = summarize_se(x)
        @assert signbit(s) == signbit(x)
        @assert unsafe_exponent(s) == unsafe_exponent(x)
        @assert mantissa_leading_zeros(s) == 0
        @assert mantissa_leading_ones(s) == 0
        @assert mantissa_trailing_zeros(s) == 0
        @assert mantissa_trailing_ones(s) == 0
    end
end


for _ = 1:10^6
    x = reinterpret(Float32, rand(UInt32))
    if isnormal(x)
        s = summarize_se(x)
        @assert signbit(s) == signbit(x)
        @assert unsafe_exponent(s) == unsafe_exponent(x)
        @assert mantissa_leading_zeros(s) == 0
        @assert mantissa_leading_ones(s) == 0
        @assert mantissa_trailing_zeros(s) == 0
        @assert mantissa_trailing_ones(s) == 0
    end
end


for _ = 1:10^6
    x = reinterpret(Float64, rand(UInt64))
    if isnormal(x)
        s = summarize_se(x)
        @assert signbit(s) == signbit(x)
        @assert unsafe_exponent(s) == unsafe_exponent(x)
        @assert mantissa_leading_zeros(s) == 0
        @assert mantissa_leading_ones(s) == 0
        @assert mantissa_trailing_zeros(s) == 0
        @assert mantissa_trailing_ones(s) == 0
    end
end


################################################################################


for i = typemin(UInt16):typemax(UInt16)
    x = reinterpret(Float16, i)
    if isnormal(x)
        s = summarize_setz(x)
        @assert signbit(s) == signbit(x)
        @assert unsafe_exponent(s) == unsafe_exponent(x)
        @assert mantissa_leading_zeros(s) == 0
        @assert mantissa_leading_ones(s) == 0
        @assert mantissa_trailing_zeros(s) == mantissa_trailing_zeros(x)
        @assert mantissa_trailing_ones(s) == 0
    end
end


for i = typemin(UInt16):typemax(UInt16)
    x = reinterpret(BFloat16, i)
    if isnormal(x)
        s = summarize_setz(x)
        @assert signbit(s) == signbit(x)
        @assert unsafe_exponent(s) == unsafe_exponent(x)
        @assert mantissa_leading_zeros(s) == 0
        @assert mantissa_leading_ones(s) == 0
        @assert mantissa_trailing_zeros(s) == mantissa_trailing_zeros(x)
        @assert mantissa_trailing_ones(s) == 0
    end
end


for _ = 1:10^6
    x = reinterpret(Float32, rand(UInt32))
    if isnormal(x)
        s = summarize_setz(x)
        @assert signbit(s) == signbit(x)
        @assert unsafe_exponent(s) == unsafe_exponent(x)
        @assert mantissa_leading_zeros(s) == 0
        @assert mantissa_leading_ones(s) == 0
        @assert mantissa_trailing_zeros(s) == mantissa_trailing_zeros(x)
        @assert mantissa_trailing_ones(s) == 0
    end
end


for _ = 1:10^6
    x = reinterpret(Float64, rand(UInt64))
    if isnormal(x)
        s = summarize_setz(x)
        @assert signbit(s) == signbit(x)
        @assert unsafe_exponent(s) == unsafe_exponent(x)
        @assert mantissa_leading_zeros(s) == 0
        @assert mantissa_leading_ones(s) == 0
        @assert mantissa_trailing_zeros(s) == mantissa_trailing_zeros(x)
        @assert mantissa_trailing_ones(s) == 0
    end
end


################################################################################


for i = typemin(UInt16):typemax(UInt16)
    x = reinterpret(Float16, i)
    if isnormal(x)
        s = summarize_seltzo(x)
        @assert signbit(s) == signbit(x)
        @assert unsafe_exponent(s) == unsafe_exponent(x)
        @assert mantissa_leading_zeros(s) == mantissa_leading_zeros(x)
        @assert mantissa_leading_ones(s) == mantissa_leading_ones(x)
        @assert mantissa_trailing_zeros(s) == mantissa_trailing_zeros(x)
        @assert mantissa_trailing_ones(s) == mantissa_trailing_ones(x)
    end
end


for i = typemin(UInt16):typemax(UInt16)
    x = reinterpret(BFloat16, i)
    if isnormal(x)
        s = summarize_seltzo(x)
        @assert signbit(s) == signbit(x)
        @assert unsafe_exponent(s) == unsafe_exponent(x)
        @assert mantissa_leading_zeros(s) == mantissa_leading_zeros(x)
        @assert mantissa_leading_ones(s) == mantissa_leading_ones(x)
        @assert mantissa_trailing_zeros(s) == mantissa_trailing_zeros(x)
        @assert mantissa_trailing_ones(s) == mantissa_trailing_ones(x)
    end
end


for _ = 1:10^6
    x = reinterpret(Float32, rand(UInt32))
    if isnormal(x)
        s = summarize_seltzo(x)
        @assert signbit(s) == signbit(x)
        @assert unsafe_exponent(s) == unsafe_exponent(x)
        @assert mantissa_leading_zeros(s) == mantissa_leading_zeros(x)
        @assert mantissa_leading_ones(s) == mantissa_leading_ones(x)
        @assert mantissa_trailing_zeros(s) == mantissa_trailing_zeros(x)
        @assert mantissa_trailing_ones(s) == mantissa_trailing_ones(x)
    end
end


for _ = 1:10^6
    x = reinterpret(Float64, rand(UInt64))
    if isnormal(x)
        s = summarize_seltzo(x)
        @assert signbit(s) == signbit(x)
        @assert unsafe_exponent(s) == unsafe_exponent(x)
        @assert mantissa_leading_zeros(s) == mantissa_leading_zeros(x)
        @assert mantissa_leading_ones(s) == mantissa_leading_ones(x)
        @assert mantissa_trailing_zeros(s) == mantissa_trailing_zeros(x)
        @assert mantissa_trailing_ones(s) == mantissa_trailing_ones(x)
    end
end


################################################################################


@assert length(normal_summaries(summarize_se, Float16)) == 62
@assert length(normal_summaries(summarize_setz, Float16)) == 662
@assert length(normal_summaries(summarize_seltzo, Float16)) == 8_882


@assert length(normal_summaries(summarize_se, BFloat16)) == 510
@assert length(normal_summaries(summarize_setz, BFloat16)) == 4_066
@assert length(normal_summaries(summarize_seltzo, BFloat16)) == 32_514


@assert length(normal_two_sum_summaries(summarize_se, Float16)) == 38_638
@assert length(normal_two_sum_summaries(summarize_setz, Float16)) == 3_833_700
@assert length(normal_two_sum_summaries(summarize_seltzo, Float16)) == 319_985_950


@assert length(normal_two_sum_summaries(summarize_se, BFloat16)) == 548_026
@assert length(normal_two_sum_summaries(summarize_setz, BFloat16)) == 26_618_866
@assert length(normal_two_sum_summaries(summarize_seltzo, BFloat16)) == 1_172_449_766


################################################################################


function view_asm(@nospecialize(f), @nospecialize(types...))
    println(string(f), "(", join(string.(types), ", "), "):")
    code_native(f, types; debuginfo=:none, dump_module=false)
    println()
end


view_asm(summarize_se, Float16)
view_asm(summarize_setz, Float16)
view_asm(summarize_seltzo, Float16)
view_asm(signbit, FloatSummary)
view_asm(unsafe_exponent, FloatSummary)
view_asm(mantissa_leading_zeros, FloatSummary)
view_asm(mantissa_leading_ones, FloatSummary)
view_asm(mantissa_trailing_zeros, FloatSummary)
view_asm(mantissa_trailing_ones, FloatSummary)
