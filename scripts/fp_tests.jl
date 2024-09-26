@inline expnt(x::Float16) = Int((reinterpret(UInt16, x) >> 10) & 0x1F) - 15
@inline expnt(x::Float32) = Int((reinterpret(UInt32, x) >> 23) & 0xFF) - 127
@inline expnt(x::Float64) = Int((reinterpret(UInt64, x) >> 52) & 0x7FF) - 1023


@assert iszero(expnt(one(Float16)))
@assert iszero(expnt(one(Float32)))
@assert iszero(expnt(one(Float64)))


function generate_test_values(
    ::Type{T},
    num_random_values::Int,
    exponent_min::Int,
    exponent_max::Int,
) where {T}

    result = T[]
    _zero = zero(T)
    push!(result, +_zero)
    push!(result, -_zero)

    _one = one(T)
    _one_plus_eps = nextfloat(_one)
    _one_plus_2eps = nextfloat(_one_plus_eps)
    _two = _one + _one
    _two_minus_eps = prevfloat(_two)
    _two_minus_2eps = prevfloat(_two_minus_eps)
    @assert iszero(expnt(_one))
    @assert iszero(expnt(_one_plus_eps))
    @assert iszero(expnt(_one_plus_2eps))
    @assert iszero(expnt(_two_minus_eps))
    @assert iszero(expnt(_two_minus_2eps))

    for e = exponent_min:exponent_max
        push!(result, +ldexp(_one, e))
        push!(result, -ldexp(_one, e))
        push!(result, +ldexp(_one_plus_eps, e))
        push!(result, -ldexp(_one_plus_eps, e))
        push!(result, +ldexp(_one_plus_2eps, e))
        push!(result, -ldexp(_one_plus_2eps, e))
        push!(result, +ldexp(_two_minus_eps, e))
        push!(result, -ldexp(_two_minus_eps, e))
        push!(result, +ldexp(_two_minus_2eps, e))
        push!(result, -ldexp(_two_minus_2eps, e))
    end

    for _ = 1:num_random_values
        e = rand(exponent_min:exponent_max)
        x = rand(T)
        push!(result, +ldexp(x, e))
        push!(result, -ldexp(x, e))
    end

    return result
end


@inline ispositive(x::T) where {T} = x > zero(T)
@inline isnegative(x::T) where {T} = x < zero(T)
@inline has_same_sign(x::T, y::T) where {T} =
    (iszero(x) & iszero(y)) |
    (ispositive(x) & ispositive(y)) |
    (isnegative(x) & isnegative(y))


function test_fp_sum(x::T, y::T) where {T}

    s = x + y

    # If both addends are zero, the sum is zero.
    (iszero(x) && iszero(y)) && @assert iszero(s)

    # If both addends have the same sign, the sum has the same sign.
    (ispositive(x) && ispositive(y)) && @assert ispositive(s)
    (isnegative(x) && isnegative(y)) && @assert isnegative(s)

    # If either addend is zero, the sum equals the other addend.
    iszero(x) && @assert s == y
    iszero(y) && @assert s == x

    # If the addends have different exponents, the sum is
    # nonzero and has the same sign as the larger addend.
    (expnt(x) != expnt(y)) && @assert !iszero(s)
    (expnt(x) > expnt(y)) && @assert has_same_sign(s, x)
    (expnt(x) < expnt(y)) && @assert has_same_sign(s, y)

    # The exponent of the sum is at most one
    # plus the exponent of the larger addend.
    @assert (expnt(s) <= expnt(x) + 1) || (expnt(s) <= expnt(y) + 1)

    # If the addends have the same sign, the exponent of
    # the sum is at least the exponent of the larger addend.
    has_same_sign(x, y) && @assert expnt(s) >= expnt(x)
    has_same_sign(x, y) && @assert expnt(s) >= expnt(y)

    # If the addends have different signs, the exponent of
    # the sum is at most the exponent of the larger addend.
    @assert has_same_sign(x, y) ||
            (expnt(s) <= expnt(x)) ||
            (expnt(s) <= expnt(y))

    # If the exponents of the addends are non-adjacent, the
    # exponent of the sum is adjacent to the larger addend.
    (expnt(x) > expnt(y) + 1) && @assert expnt(s) >= expnt(x) - 1
    (expnt(x) + 1 < expnt(y)) && @assert expnt(s) >= expnt(y) - 1

    # If the sum is nonzero, then it is at least as large
    # as the least significant bit of the larger addend.
    @assert iszero(s) || (expnt(s) >= expnt(x) - precision(T))
    @assert iszero(s) || (expnt(s) >= expnt(y) - precision(T))

    return nothing
end


@inline function two_sum(x::T, y::T) where {T}
    s = x + y
    x_prime = s - y
    y_prime = s - x_prime
    x_err = x - x_prime
    y_err = y - y_prime
    e = x_err + y_err
    return (s, e)
end


function test_fp_two_sum(x::T, y::T) where {T}

    (s, e) = two_sum(x, y)

    @assert s == x + y

    # If either addend is zero, the error term is zero.
    iszero(x) && @assert iszero(e)
    iszero(y) && @assert iszero(e)

    if isfinite(e) && !issubnormal(e)

        # If the error term is nonzero, it is smaller
        # than the least significant bit of the sum.
        @assert iszero(e) || (expnt(e) <= expnt(s) - precision(T))

        # If the error term is nonzero, it is larger than
        # the least significant bit of the smaller addend.
        @assert iszero(e) ||
                (expnt(e) > expnt(x) - precision(T)) ||
                (expnt(e) > expnt(y) - precision(T))
    end

    return nothing
end


function main()

    num_random_values = 2000

    test_values_16 = generate_test_values(Float16,
        num_random_values, -14, +15)
    for x in test_values_16
        for y in test_values_16
            test_fp_sum(x, y)
            test_fp_two_sum(x, y)
        end
    end
    println("Float16 tests passed.")

    test_values_32 = generate_test_values(Float32,
        num_random_values, -126, +127)
    for x in test_values_32
        for y in test_values_32
            test_fp_sum(x, y)
            test_fp_two_sum(x, y)
        end
    end
    println("Float32 tests passed.")

    test_values_64 = generate_test_values(Float64,
        num_random_values, -1022, +1023)
    for x in test_values_64
        for y in test_values_64
            test_fp_sum(x, y)
            test_fp_two_sum(x, y)
        end
    end
    println("Float64 tests passed.")

    return nothing
end


main()
