module ExtensionFields

import Base: +, -, *, /, //, ^, inv, ==
import Base: numerator, denominator
import Base: zero, one, iszero
import Base: promote_rule, convert
import Base: @pure, power_by_squaring, literal_pow
import Base: deepcopy
import Base: rand
import Base: show

import Random: AbstractRNG, SamplerType

import InPlace: @inplace, inclusiveinplace!, inplace!

import ..Constants: One
import PolynomialRings: polynomial_ring, integers

struct MinPolyId{ID} end
const minpolys = Dict()
minpoly(::MinPolyId{ID}) where ID = minpolys[ID][]

"""
    F = ExtensionField{F <: AbstractGaloisField, N, α, MinPoly}

Algebraic extension of a finite field ``F`` of degree ``N``.
"""
struct ExtensionField{Num <: Number, N, Denom <: Number, MinPoly} <: Number
    nums    :: NTuple{N, Num}
    denom   :: Denom
end

numeratortype(::Type{ExtensionField{Num, N, Denom, MinPoly}}) where {Num, N, Denom, MinPoly} = Num
denominatortype(::Type{ExtensionField{Num, N, Denom, MinPoly}}) where {Num, N, Denom, MinPoly} = Denom
degree(::Type{ExtensionField{Num, N, Denom, MinPoly}}) where {Num, N, Denom, MinPoly} = N

minpoly(::Type{ExtensionField{Num, N, Denom, MinPoly}}) where {Num, N, Denom, MinPoly} = minpoly(MinPoly()) :: NTuple{N + 1, Num}

function reducefraction(F, nums, denom)
    x = deepcopy(denom)
    for n in nums
        @inplace x = gcd(x, n)
    end
    @inplace x = flipsign(x, denom)
    nums = inclusiveinplace!.(÷, nums, x)
    @inplace denom ÷= x
    F(nums, denom)
end
reducefraction(F, nums, ::One) = F(nums, One())

numeratortype(T::Type) = T
denominatortype(T::Type) = One
numeratortype(T::Type{Rational{I}}) where I = I
denominatortype(T::Type{Rational{I}}) where I = I
basefield(T::Type{<:ExtensionField}) = Rational{promote_type(numeratortype(T), denominatortype(T))}

numeratortype(x) = numeratortype(typeof(x))
denominatortype(x) = denominatortype(typeof(x))
basefield(x::ExtensionField) = basefield(typeof(x))

numerator(a::ExtensionField) = error("not implemented")
denominator(a::ExtensionField) = a.denom

integers(T::Type{<:ExtensionField}) = ExtensionField{numeratortype(T), degree(T), One, MinPoly}

# -----------------------------------------------------------------------------
#
# Addition and substraction
#
# -----------------------------------------------------------------------------
zero(T::Type{<:ExtensionField}) =
    T(ntuple(i -> zero(numeratortype(T)), degree(T)), one(denominatortype(T)))
one( T::Type{<:ExtensionField}) =
    T(ntuple(i -> i == 1 ? one(numeratortype(T)) : zero(numeratortype(T)), degree(T)), one(denominatortype(T)))
gen( T::Type{<:ExtensionField}) =
    T(ntuple(i -> i == 2 ? one(numeratortype(T)) : zero(numeratortype(T)), degree(T)), one(denominatortype(T)))

function linearcombination(op, a, b)
    T = promote_type(typeof(a), typeof(b))
    D = lcm(a.denom, b.denom)
    c, d = D ÷ a.denom, D ÷ b.denom
    reducefraction(T, op.(c .* a.nums, d .* b.nums), D)
end

+(a::F, b::F) where F<:ExtensionField = linearcombination(+, a, b)
-(a::F, b::F) where F<:ExtensionField = linearcombination(-, a, b)

+(a::ExtensionField) = deepcopy(a)
-(a::ExtensionField) = typeof(a)(.-a.nums, a.denom)

iszero(a::ExtensionField) = all(iszero, a.nums)

==(a::F, b::F) where F <: ExtensionField = a.nums == b.nums && a.denom == b.denom

# -----------------------------------------------------------------------------
#
# The interesting extension field operations: multiplication and division
#
# -----------------------------------------------------------------------------
function _xrem!(a::AbstractVector{C}, b::AbstractVector{C}) where C <: Integer
    len_a = findlast(!iszero, a)
    len_b = findlast(!iszero, b)
    isnothing(len_b) && throw(DivideError())
    k = one(C)
    while !isnothing(len_a) && len_a >= len_b
        D = lcm(a[len_a], b[len_b])
        c, d = D ÷ a[len_a], D ÷ b[len_b]

        a .*= c; k *= c
        a[len_a-len_b+1:len_a] .-= d .* b[1:len_b]

        len_a = findprev(!iszero, a, len_a - 1)
    end
    D = gcd(k, gcd(a))
    return k ÷ D, a .÷ D
end

function _rem(a::AbstractVector{C}, b::AbstractVector{C}) where C
    a = copy(a)
    len_a = findlast(!iszero, a)
    len_b = findlast(!iszero, b)
    while len_a !== nothing && len_a >= len_b
        q = a[len_a] // b[len_b]
        a[len_a-len_b+1:len_a] .-= q .* b[1:len_b]
        len_a = findprev(!iszero, a, len_a - 1)
    end
    a
end

distinctzeros(T, n) = T[zero(T) for _ in 1:n]

function _gcdx(a::AbstractVector{C}, b::AbstractVector{C}) where C
    a = deepcopy(a)
    b = deepcopy(b)
    len_a = something(findlast(!iszero, a), 0)
    len_b = something(findlast(!iszero, b), 0)
    m = max(len_a, len_b)
    s0, s1 = distinctzeros(C, m), distinctzeros(C, m)
    t0, t1 = distinctzeros(C, m), distinctzeros(C, m)
    @inplace s0[1] += 1
    @inplace t1[1] += 1
    # The loop invariants are: s0*a0 + t0*b0 == a
    #                          s1*a0 + t1*b0 == b
    while len_b != 0
        while len_a >= len_b
            deg_diff = len_a - len_b
            D = lcm(a[len_a], b[len_b])
            c, d = D ÷ a[len_a], D ÷ b[len_b]

            @inplace a .*= c
            @inplace a[deg_diff + 1 : len_a] .-= d .* b[1 : len_b]

            # (c*s0 - d*s1)*a0 + (c*t0 - d*t1)*b0 = c*a - d*b

            @inplace s0 .*= c
            @inplace s0[deg_diff+1:end] .-= d .* s1[1:end-deg_diff]
            @inplace t0 .*= c
            @inplace t0[deg_diff+1:end] .-= d .* t1[1:end-deg_diff]

            len_a = something(findprev(!iszero, a, len_a-1), 0)
        end
        a, b = b, a
        len_a, len_b = len_b, len_a
        s0, s1 = s1, s0
        t0, t1 = t1, t0
    end
    return (a, s0, t0)
end

@pure @generated function _pow_of_generator_rem(::Type{F}, m) where F <: ExtensionField
    N = degree(F)
    pows = map(N : 2N - 2) do i
        pow_of_generator = zeros(numeratortype(F), 2N - 1)
        pow_of_generator[i + 1] = one(numeratortype(F))
        c, pow_of_generator_rem = _xrem!(pow_of_generator, collect(minpoly(F)))
        (i, reducefraction(F, tuple(pow_of_generator_rem[1:N]...), c))
    end
    quote
        $(
        map(pows) do p
            :( m == $(p[1]) && return $(p[2]) )
        end...
        )
        error("_pow_of_generator_rem: m (=$m) should be between $(degree(F)) and $(2degree(F) - 1)")
    end
end

*(a::F, b::F) where F <: ExtensionField = _mul_generated!(zero(F), a.denom * b.denom, a.nums, b.nums)

literal_pow(::typeof(^), a::F, ::Val{2}) where F <: ExtensionField = _mul_generated!(zero(F), a.denom^2, a.nums)

function inv(a::F) where F <: ExtensionField
    iszero(a) && throw(DivideError())
    N = degree(F)
    nums = collect(a.nums)
    d, u, v = _gcdx(nums, collect(minpoly(F)))
    @assert !iszero(d[1]) && all(iszero, @view d[2:end])
    return reducefraction(F, ntuple(i -> a.denom * u[i], N), d[1])
end

/(a::Number, b::ExtensionField) = a * inv(b)
//(a::Number, b::ExtensionField) = a * inv(b)

# resolve ambiguity
/(a::ExtensionField, b::ExtensionField) = a * inv(b)
//(a::ExtensionField, b::ExtensionField) = a * inv(b)

^(a::F, n::Integer) where F <: ExtensionField = power_by_squaring(a, n)

function power_by_squaring(a::F, n::Integer) where F <: ExtensionField
    iszero(a) && return iszero(n) ? one(a) : zero(a)
    n == 0 && return one(a)

    t = trailing_zeros(n) + 1
    n >>= t
    while (t -= 1) > 0
        a = a^2
    end
    b = a
    while n > 0
        t = trailing_zeros(n) + 1
        n >>= t
        while (t -= 1) >= 0
            a = a^2
        end
        b *= a
    end
    return b
end

@inline function _convolution!(q, tmp, N, lo, hi, vec1, vec2)
    for i in lo : hi
        @inplace tmp = vec1[i] * vec2[N - i + 1]
        @inplace q += tmp
    end
    return q
end

@inline _convolution!(q, tmp, N, lo, hi, vec) = _convolution!(q, tmp, N, lo, hi, vec, vec)

# in case of length(operands) == 1: compute its square
# in case of length(operands) == 2: compute their product
# (ugly interface, but reduces code duplication)
@generated function _mul_generated!(res::F, denom, operands...) where F <: ExtensionField
    N = degree(F)
    coeffs = [Symbol(:coeff, i) for i in 1:N]
    code = quote
        q = zero(numeratortype(F))
        tmp = zero(numeratortype(F))
    end

    pows_of_generator = [_pow_of_generator_rem(F, i) for i in N : 2N - 2]
    D = lcm(denominator.(pows_of_generator))
    lcm_multipliers = D .÷ denominator.(pows_of_generator)

    for j in 1:N
        push!(code.args, quote
            $(coeffs[j]) = res.nums[$j]
            @inplace $(coeffs[j]) = 0
            $(coeffs[j]) = _convolution!($(coeffs[j]), tmp, $j, 1, $j, operands...)
            @inplace $(coeffs[j]) *= $D
        end)
    end

    for i in N + 1 : 2N - 1
        c = :( if (q = _convolution!(q, tmp, $i, $(i + 1 - N), $N, operands...)) |> !iszero
        end )
        coeffs_to_add = pows_of_generator[i - N].nums
        multiplier = lcm_multipliers[i - N]

        for j in 1 : N
            if !iszero(coeffs_to_add[j])
                push!(c.args[2].args, quote
                    @inplace tmp = q * $(multiplier * coeffs_to_add[j])
                    @inplace $(coeffs[j]) += tmp
                end)
            end
        end
        push!(code.args, c)
        push!(code.args, :( @inplace q = 0 ))
    end

    push!(code.args, quote
        nums = tuple($(coeffs...))
        @inplace denom *= $D
        return reducefraction(F, nums, denom)
    end)

    code
end

# -----------------------------------------------------------------------------
#
# Base field operations
#
# -----------------------------------------------------------------------------
function *(a::Number, b::ExtensionField)
    # FIXME: should allow for promote_type(typeof(a), numeratortype(b)) different
    # from numeratortype(b)
    reducefraction(typeof(b), numerator(a) .* b.nums, denominator(a) * b.denom)
end

function *(a::ExtensionField, b::Number)
    # FIXME: see above
    reducefraction(typeof(a), a.nums .* numerator(b), a.denom * denominator(b))
end

function /(a::ExtensionField, b::Number)
    # FIXME: see above
    reducefraction(typeof(a), a.nums .* denominator(b), a.denom * numerator(b))
end

function //(a::ExtensionField, b::Number)
    # FIXME: see above
    reducefraction(typeof(a), a.nums .* denominator(b), a.denom * numerator(b))
end

*(a::Complex, b::ExtensionField) = error("not implemented")
*(a::ExtensionField, b::ExtensionField) = error("not implemented")
*(a::ExtensionField, b::Complex) = error("not implemented")

# -----------------------------------------------------------------------------
#
# Constructors and promotion
#
# -----------------------------------------------------------------------------
promote_rule(F::Type{<:ExtensionField}, ::Type{<:Number}) = F
function convert(F::Type{<:ExtensionField}, x::Number)
    a = convert(numeratortype(F), numerator(x))
    d = convert(denominatortype(F), denominator(x))
    nums = ntuple(i -> i == 1 ? a : zero(a), degree(F))
    F(nums, d)
end

convert(::Type{F}, x::F) where F <: ExtensionField = x

(::Type{F})(a::F) where F<:ExtensionField = deepcopy(a)
(::Type{F})(a::Number) where F<:ExtensionField = convert(F, a)

deepcopy(x::ExtensionField) = typeof(x)(map(deepcopy, x.nums), deepcopy(x.denom))

# -----------------------------------------------------------------------------
#
# Random number
#
# -----------------------------------------------------------------------------
function rand(rng::AbstractRNG, ::SamplerType{F}) where F <: ExtensionField
    nums = ntuple(i -> rand(rng, numeratortype(F)), degree(F))
    d = rand(rng, denominatortype(F))
    reducefraction(F, nums, d)
end

# -----------------------------------------------------------------------------
#
# Display
#
# -----------------------------------------------------------------------------
function show(io::IO, x::ExtensionField)
    _, (α,) = polynomial_ring(:α, basering = basefield(x))
    xx = sum(x.nums[n] // x.denom * α^(n-1) for n in 1:degree(typeof(x)))
    show(io, xx)
end

# -----------------------------------------------------------------------------
#
# In-place operations
#
# -----------------------------------------------------------------------------
const PlusMinus = Union{typeof(+), typeof(-)}
function inplace!(op::PlusMinus, a::F, b::F, c::F) where F <: ExtensionField{BigInt, N, BigInt} where N
    D = lcm(b.denom, c.denom)
    u, v = D ÷ b.denom, D ÷ c.denom

    tmp = zero(BigInt)
    for i in 1 : degree(F)
        inplace!(*, a.nums[i], u, b.nums[i])
        inplace!(*, tmp, v, c.nums[i])
        inclusiveinplace!(op, a.nums[i], tmp)
    end

    return reducefraction(F, a.nums, D)
end

# -----------------------------------------------------------------------------
#
# Construct an extension field
#
# -----------------------------------------------------------------------------

function ExtensionField(BaseField::Type, minpoly::Pair{Symbol, <:AbstractVector{<:Number}})
    sym, minpoly_coeffs = minpoly

    # FIXME: lookup existing minimum polynomials by equality
    mp = Ref(tuple(map(numeratortype(BaseField), minpoly_coeffs)...))
    minpolys[objectid(mp)] = mp
    MinPoly = MinPolyId{objectid(mp)}

    N = length(minpoly_coeffs) - 1

    return ExtensionField{numeratortype(BaseField), N, denominatortype(BaseField), MinPoly}
end

end
