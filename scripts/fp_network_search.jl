using Base.Threads
using Random


@inline function two_sum(a::T, b::T) where {T}
    s = a + b
    a_prime = s - b
    b_prime = s - a_prime
    a_err = a - a_prime
    b_err = b - b_prime
    e = a_err + b_err
    return (s, e)
end


function renormalize!(v::AbstractVector{T}) where {T}
    Base.require_one_based_indexing(v)
    while true
        changed = false
        for i = 1 : length(v) - 1
            @inbounds x = v[i]
            @inbounds y = v[i+1]
            (s, e) = two_sum(x, y)
            changed |= (s != x) | (e != y)
            @inbounds v[i] = s
            @inbounds v[i+1] = e
        end
        if !changed
            return v
        end
    end
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
    r = rand(UInt16)
    exponent = r & 0x03FF
    if iszero(exponent)
        return 0.0
    end
    exponent += 0x01FF
    s = rand(UInt64)
    s & 0xFC00000000000000
    i, j = minmax(
        deflate_range(UInt16((s & 0xFC00000000000000) >> 58)),
        deflate_range(UInt16((s & 0x03F0000000000000) >> 52)))
    m = s & 0x000FFFFFFFFFFFFF
    m = _modify_low_bits(m, i)
    m = _modify_high_bits(m, j)
    x = (UInt64(r) << 48) & 0x8000000000000000
    x |= UInt64(exponent) << 52
    x |= m
    return reinterpret(Float64, x)
end


function run_sum_network!(
    v::AbstractVector{T},
    network::AbstractVector{Tuple{Int,Int}},
) where {T}
    for (i, j) in network
        v[i], v[j] = two_sum(v[i], v[j])
    end
    return v
end


function riffle!(
    v::AbstractVector{T},
    x::AbstractVector{T},
    y::AbstractVector{T},
) where {T}
    Base.require_one_based_indexing(v, x, y)
    @assert length(x) == length(y)
    @assert length(v) == length(x) + length(y)
    for i = 1 : length(x)
        _2i = i + i
        @inbounds v[_2i-1] = x[i]
        @inbounds v[_2i] = y[i]
    end
    return v
end


@inline function _overlapping_bits(x::T, y::T) where {T}
    if iszero(y)
        return 0
    elseif iszero(x)
        return precision(T)
    else
        return max(0, precision(T) - (exponent(x) - exponent(y)))
    end
end


@inline function _exponent_gap(x::T, y::T) where {T}
    if iszero(y)
        return exponent(floatmax(T)) - exponent(floatmin(T))
    elseif iszero(x)
        return 0
    else
        return exponent(x) - exponent(y)
    end
end


function evaluate_sum_network(
    network::AbstractVector{Tuple{Int,Int}},
    num_limbs::Int,
    duration_ns::UInt64,
)
    start = time_ns()
    x = Vector{Float64}(undef, num_limbs)
    y = Vector{Float64}(undef, num_limbs)
    v = Vector{Float64}(undef, num_limbs + num_limbs)
    overlap_score = 0
    error_score = typemax(Int)
    while true
        # Generate random (but renormalized) input data.
        for i = 1:num_limbs
            @inbounds x[i] = generate_test_float()
        end
        renormalize!(x)

        for i = 1:num_limbs
            @inbounds y[i] = generate_test_float()
        end
        renormalize!(y)

        # Combine input data and execute sum network.
        riffle!(v, x, y)
        run_sum_network!(v, network)

        # Update scores.
        for i = 1:num_limbs-1
            @inbounds overlap_score = max(overlap_score,
                _overlapping_bits(v[i], v[i+1]))
        end
        for i = 1:num_limbs
            @inbounds error_score = min(error_score,
                _exponent_gap(v[1], v[num_limbs+i]))
        end

        if time_ns() >= start + duration_ns
            return (overlap_score, error_score)
        end
    end
end


function parallel_evaluate_sum_network(
    network::AbstractVector{Tuple{Int,Int}},
    num_limbs::Int,
    duration_ns::UInt64,
)
    N = nthreads()
    results = Vector{Tuple{Int,Int}}(undef, N)
    @threads for i = 1:N
        @inbounds results[i] = evaluate_sum_network(
            network, num_limbs, duration_ns)
    end
    return (maximum(overlap_score for (overlap_score, _) in results),
            minimum(error_score for (_, error_score) in results))
end


function base_sum_network(num_limbs::Int, n::Int)
    result = Tuple{Int,Int}[]
    for _ = 1:n
        for i = 1:num_limbs
            _2i = i + i
            push!(result, (_2i - 1, _2i))
        end
        for i = 1:num_limbs-1
            _2i = i + i
            push!(result, (_2i, _2i + 1))
        end
    end
    return result
end


base_sum_network(num_limbs::Int) =
    base_sum_network(num_limbs, num_limbs)


function main(num_limbs::Int, overlap_threshold::Int, error_threshold::Int)
    network = base_sum_network(num_limbs, num_limbs + num_limbs)
    while true
        indices = shuffle(1:length(network))
        found_improvement = false
        for i in indices
            new_network = deleteat!(copy(network), i)
            println("Evaluating: ", new_network)
            flush(stdout)
            (overlap_score, error_score) = parallel_evaluate_sum_network(network, num_limbs, UInt64(1_000_000_000))
            println("Initial scores: ", (overlap_score, error_score))
            flush(stdout)
            if (overlap_score <= overlap_threshold) && (error_score >= error_threshold)
                println("Passed initial evaluation.")
                flush(stdout)
                (overlap_score, error_score) = parallel_evaluate_sum_network(network, num_limbs, UInt64(10_000_000_000))
                println("Final scores: ", (overlap_score, error_score))
                flush(stdout)
                if (overlap_score <= overlap_threshold) && (error_score >= error_threshold)
                    println("Passed final evaluation. Accepted new network.")
                    flush(stdout)
                    network = new_network
                    found_improvement = true
                    break
                else
                    println("Failed final evaluation.")
                    flush(stdout)
                end
            else
                println("Failed initial evaluation.")
                flush(stdout)
            end
        end
        if !found_improvement
            break
        end
    end
    println("Final network: ", network)
    println()
    flush(stdout)
end


while true
    main(parse(Int, ARGS[1]), parse(Int, ARGS[2]), parse(Int, ARGS[3]))
end
