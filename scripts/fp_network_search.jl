using Base.Threads
using Random


################################################################################


@inline function two_sum(a::T, b::T) where {T}
    s = a + b
    a_prime = s - b
    b_prime = s - a_prime
    a_err = a - a_prime
    b_err = b - b_prime
    e = a_err + b_err
    return (s, e)
end


@inline deflate_range(i::UInt16) =
    ((i << 5) + (i << 4) + (i << 2) + 0x0038) >> 6


@inline function _modify_low_bits(x::UInt64, i::UInt16)
    _one = one(UInt64)
    bit = (_one << i)
    mask = bit - _one
    value = bit - (x & _one)
    return (x & ~mask) | (value & mask)
end


@inline function _modify_high_bits(x::UInt64, j::UInt16)
    _one = one(UInt64)
    _high_bit = _one << 51
    _past_bit = _one << 52
    _full_mask = _past_bit - _one
    mask = (_full_mask >> j) << j
    value = _past_bit - ((x & _high_bit) >> 51)
    return (x & ~mask) | (value & mask)
end


function generate_test_float()
    # Generate random data for sign bit and exponent.
    r = rand(UInt16)
    exponent = r & 0x03FF
    if iszero(exponent)
        return 0.0
    end
    exponent += 0x01FF
    # Generate random data for mantissa.
    m = rand(UInt64)
    i, j = minmax(
        deflate_range(UInt16((m & 0xFC00000000000000) >> 58)),
        deflate_range(UInt16((m & 0x03F0000000000000) >> 52)))
    m &= 0x000FFFFFFFFFFFFF
    m = _modify_low_bits(m, i)
    m = _modify_high_bits(m, j)
    return reinterpret(Float64, ((UInt64(r) << 48) & 0x8000000000000000) |
                                (UInt64(exponent) << 52) | m)
end


@inline _overlapping_bits(x::T, y::T) where {T} =
    iszero(y) ? 0 : iszero(x) ? precision(T) :
    max(0, precision(T) - (exponent(x) - exponent(y)))


@inline _exponent_gap(x::T, y::T) where {T} =
    iszero(y) ? exponent(floatmax(T)) - exponent(floatmin(T)) :
    iszero(x) ? 0 : exponent(x) - exponent(y)


################################################################################


const NUM_LIMBS = parse(Int, ARGS[1])
const IDEAL_OVERLAP_SCORE = 0
const IDEAL_ERROR_SCORE = NUM_LIMBS * precision(Float64) + (NUM_LIMBS - 1)


function renormalize!(v::AbstractVector{T}) where {T}
    @assert axes(v) == (Base.OneTo(NUM_LIMBS),)
    while true
        changed = false
        for i = 1:NUM_LIMBS-1
            @inbounds x, y = v[i], v[i+1]
            (s, e) = two_sum(x, y)
            changed |= (s != x) | (e != y)
            @inbounds v[i], v[i+1] = s, e
        end
        if !changed
            return v
        end
    end
end


function riffle!(
    v::AbstractVector{T},
    x::AbstractVector{T},
    y::AbstractVector{T},
) where {T}
    @assert axes(v) == (Base.OneTo(NUM_LIMBS + NUM_LIMBS),)
    @assert axes(x) == (Base.OneTo(NUM_LIMBS),)
    @assert axes(y) == (Base.OneTo(NUM_LIMBS),)
    for i = 1:NUM_LIMBS
        _2i = i + i
        @inbounds v[_2i-1] = x[i]
        @inbounds v[_2i] = y[i]
    end
    return v
end


function test_sum_network!(
    v::AbstractVector{T},
    network::AbstractVector{Tuple{Int,Int}},
) where {T}
    @assert axes(v) == (Base.OneTo(NUM_LIMBS + NUM_LIMBS),)
    for (i, j) in network
        v[i], v[j] = two_sum(v[i], v[j])
    end
    overlap_score = IDEAL_OVERLAP_SCORE
    for i = 1:NUM_LIMBS-1
        @inbounds overlap_score = max(overlap_score,
            _overlapping_bits(v[i], v[i+1]))
    end
    error_score = IDEAL_ERROR_SCORE
    for i = 1:NUM_LIMBS
        @inbounds error_score = min(error_score,
            _exponent_gap(v[1], v[NUM_LIMBS+i]))
    end
    return (overlap_score, error_score)
end


const EvaluationResult = Tuple{Int,Int,Vector{Float64},Vector{Float64},Int}


function evaluate_sum_network(
    network::AbstractVector{Tuple{Int,Int}},
    duration_ns::UInt64,
)
    start = time_ns()
    x = Vector{Float64}(undef, NUM_LIMBS)
    y = Vector{Float64}(undef, NUM_LIMBS)
    v = Vector{Float64}(undef, NUM_LIMBS + NUM_LIMBS)
    v_overlap = Vector{Float64}(undef, NUM_LIMBS + NUM_LIMBS)
    v_error = Vector{Float64}(undef, NUM_LIMBS + NUM_LIMBS)
    overlap_score = IDEAL_OVERLAP_SCORE
    error_score = IDEAL_ERROR_SCORE
    num_tests = 0
    while true
        # Generate random (but renormalized) input data.
        for i = 1:NUM_LIMBS
            @inbounds x[i] = generate_test_float()
        end
        renormalize!(x)

        for i = 1:NUM_LIMBS
            @inbounds y[i] = generate_test_float()
        end
        renormalize!(y)

        # Combine input data and execute sum network.
        riffle!(v, x, y)
        new_overlap_score, new_error_score = test_sum_network!(v, network)

        # Update scores.
        if new_overlap_score > overlap_score
            overlap_score = new_overlap_score
            riffle!(v_overlap, x, y)
        end
        if new_error_score < error_score
            error_score = new_error_score
            riffle!(v_error, x, y)
        end

        # Check for termination.
        num_tests += 1
        if time_ns() >= start + duration_ns
            if overlap_score == IDEAL_OVERLAP_SCORE
                empty!(v_overlap)
            end
            if error_score == IDEAL_ERROR_SCORE
                empty!(v_error)
            end
            return (overlap_score, error_score, v_overlap, v_error, num_tests)
        end
    end
end


function parallel_evaluate_sum_network(
    network::AbstractVector{Tuple{Int,Int}},
    duration_ns::UInt64,
)
    N = nthreads()
    results = Vector{EvaluationResult}(undef, N)
    @threads for i = 1:N
        @inbounds results[i] = evaluate_sum_network(network, duration_ns)
    end
    final_overlap_score = IDEAL_OVERLAP_SCORE
    final_error_score = IDEAL_ERROR_SCORE
    final_v_overlap = Vector{Float64}(undef, 0)
    final_v_error = Vector{Float64}(undef, 0)
    final_num_tests = 0
    for (overlap_score, error_score, v_overlap, v_error, num_tests) in results
        if overlap_score > final_overlap_score
            final_overlap_score = overlap_score
            final_v_overlap = v_overlap
        end
        if error_score < final_error_score
            final_error_score = error_score
            final_v_error = v_error
        end
        final_num_tests += num_tests
    end
    return (final_overlap_score, final_error_score,
        final_v_overlap, final_v_error, final_num_tests)
end


################################################################################


const CHALLENGING_TEST_CASES = Vector{Float64}[]
const PASSING_NETWORKS = Vector{Tuple{Int,Int}}[]
const OVERLAP_THRESHOLD = parse(Int, ARGS[2])
const ERROR_THRESHOLD = parse(Int, ARGS[3])
@assert OVERLAP_THRESHOLD >= IDEAL_OVERLAP_SCORE
@assert ERROR_THRESHOLD <= IDEAL_ERROR_SCORE


function screen_sum_network(network::AbstractVector{Tuple{Int,Int}})
    v = Vector{Float64}(undef, NUM_LIMBS + NUM_LIMBS)
    for test_case in CHALLENGING_TEST_CASES
        copy!(v, test_case)
        overlap_score, error_score = test_sum_network!(v, network)
        if overlap_score > OVERLAP_THRESHOLD
            return false
        end
        if error_score < ERROR_THRESHOLD
            return false
        end
    end
    return true
end


function base_sum_network(k::Int)
    result = Tuple{Int,Int}[]
    for _ = 1:k
        for i = 1:NUM_LIMBS
            _2i = i + i
            push!(result, (_2i - 1, _2i))
        end
        for i = 1:NUM_LIMBS-1
            _2i = i + i
            push!(result, (_2i, _2i + 1))
        end
    end
    return result
end


function main()
    network = base_sum_network(10)
    while true
        indices = shuffle(1:length(network))
        found_improvement = false
        for i in indices
            new_network = deleteat!(copy(network), i)
            if screen_sum_network(new_network)
                deleteat!(network, i)
                found_improvement = true
                break
            end
        end
        if !found_improvement
            break
        end
    end
    println("Candidate network: ", network)
    flush(stdout)
    start = time_ns()
    overlap_score, error_score, v_overlap, v_error, num_tests =
        parallel_evaluate_sum_network(network, UInt64(1_000_000_000))
    stop = time_ns()
    elapsed = (stop - start) / 1.0e9
    println("Performed ", num_tests, " tests in ", elapsed,
        " seconds (", num_tests / elapsed, " tests per second).")
    println("Scores: ", (overlap_score, error_score))
    if overlap_score != IDEAL_OVERLAP_SCORE
        @assert !isempty(v_overlap)
        println("Adding new overlap test case: ", v_overlap)
        push!(CHALLENGING_TEST_CASES, v_overlap)
    end
    if error_score != IDEAL_ERROR_SCORE
        @assert !isempty(v_error)
        println("Adding new error test case: ", v_error)
        push!(CHALLENGING_TEST_CASES, v_error)
    end
    if (overlap_score <= OVERLAP_THRESHOLD) & (error_score >= ERROR_THRESHOLD)
        println("Candidate network passed final testing.")
        println("Final network: ", network)
        push!(PASSING_NETWORKS, network)
    else
        println("Candidate network failed final testing.")
    end
    println()
    flush(stdout)

    failures = (!).(screen_sum_network.(PASSING_NETWORKS))
    if any(failures)
        println("New test cases eliminated ", sum(failures), " networks.")
    end
    deleteat!(PASSING_NETWORKS, failures)
    println.(PASSING_NETWORKS)
    println()
    flush(stdout)
end


while true
    main()
end
