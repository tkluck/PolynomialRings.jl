module NumberFields

import Base: @pure, power_by_squaring, literal_pow
import Base: +, -, *, /, //, ^, inv, ==
import Base: deepcopy
import Base: numerator, denominator
import Base: promote_rule, convert
import Base: rand
import Base: show
import Base: zero, one, iszero, inv, copy
import LinearAlgebra: nullspace
import LinearAlgebra: tr, norm
import Random: AbstractRNG, SamplerType

import InPlace: @inplace, inclusiveinplace!, inplace!

import ..Constants: Constant, One, MinusOne, Zero
import ..Ideals: ring
import ..Monomials: AbstractMonomial
import ..NamedValues: type_with_named_values, knownvalue, knownnames, knownvalues
import ..NamingSchemes: boundnames, fullboundnames, namingscheme, Named
import ..Polynomials: Polynomial, PolynomialOver, basering, variablesymbols
import ..QuotientRings: QuotientRing, monomial_basis
import ..QuotientRings: _ideal
import ..Terms: coefficient
import PolynomialRings: allvariablesymbols, fraction_field, basering
import PolynomialRings: integers, polynomial_ring, generators

# -----------------------------------------------------------------------------
#
# Type and type information
#
# -----------------------------------------------------------------------------

const minpolys = Dict()

"""
    F = NumberField{Num <: Number, N, Denom <: Number, NamedValues}} <: Number

Algebraic extension of a field ``Num//Denom`` of degree ``N``.
"""
struct NumberField{Num <: Number, N, Denom <: Number, NamedValues} <: Number
    nums    :: NTuple{N, Num}
    denom   :: Denom
end

numeratortype(::Type{NumberField{Num, N, Denom, NamedValues}}) where {Num, N, Denom, NamedValues} = Num
denominatortype(::Type{NumberField{Num, N, Denom, NamedValues}}) where {Num, N, Denom, NamedValues} = Denom
degree(::Type{NumberField{Num, N, Denom, NamedValues}}) where {Num, N, Denom, NamedValues} = N
minpoly(F::Type{NumberField{Num, N, Denom, NamedValues}}) where {Num, N, Denom, NamedValues} = minpolys[F] :: NTuple{N + 1, Num}
@pure @generated boundnames(::Type{F})         where F <: NumberField = Named{knownnames(F),}()
@pure @generated fullboundnames(::Type{F})     where F <: NumberField = Named{knownnames(F),}()
@pure @generated variablesymbols(::Type{F})    where F <: NumberField = knownnames(F)
@pure @generated allvariablesymbols(::Type{F}) where F <: NumberField = knownnames(F)

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
basefield(T::Type{<:NumberField}) = Rational{promote_type(numeratortype(T), denominatortype(T))}

numeratortype(x) = numeratortype(typeof(x))
denominatortype(x) = denominatortype(typeof(x))
basefield(x::NumberField) = basefield(typeof(x))

numerator(a::NumberField) = error("not implemented") # TODO: have denominatortype=One
denominator(a::NumberField) = a.denom

# FIXME: this should be the one with Denom=One. But for now, I just want the
# groebner basis algorithms not to choke.
integers(T::Type{<:NumberField}) = T

# -----------------------------------------------------------------------------
#
# Addition and substraction
#
# -----------------------------------------------------------------------------
zero(T::Type{<:NumberField}) =
    T(ntuple(i -> zero(numeratortype(T)), degree(T)), one(denominatortype(T)))
one( T::Type{<:NumberField}) =
    T(ntuple(i -> i == 1 ? one(numeratortype(T)) : zero(numeratortype(T)), degree(T)), one(denominatortype(T)))
gen( T::Type{<:NumberField}) =
    T(ntuple(i -> i == 2 ? one(numeratortype(T)) : zero(numeratortype(T)), degree(T)), one(denominatortype(T)))

function linearcombination(op, a, b)
    T = promote_type(typeof(a), typeof(b))
    D = lcm(a.denom, b.denom)
    c, d = D ÷ a.denom, D ÷ b.denom
    reducefraction(T, op.(c .* a.nums, d .* b.nums), D)
end

+(a::F, b::F) where F<:NumberField = linearcombination(+, a, b)
-(a::F, b::F) where F<:NumberField = linearcombination(-, a, b)

+(a::NumberField) = deepcopy(a)
-(a::NumberField) = typeof(a)(.-a.nums, a.denom)

iszero(a::NumberField) = all(iszero, a.nums)

==(a::F, b::F) where F <: NumberField = a.nums == b.nums && a.denom == b.denom

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

@pure @generated function _pow_of_generator_rem(::Type{F}, m) where F <: NumberField
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

*(a::F, b::F) where F <: NumberField = _mul_generated!(zero(F), a.denom * b.denom, a.nums, b.nums)

literal_pow(::typeof(^), a::F, ::Val{2}) where F <: NumberField = _mul_generated!(zero(F), a.denom^2, a.nums)

function inv(a::F) where F <: NumberField
    iszero(a) && throw(DivideError())
    N = degree(F)
    nums = collect(a.nums)
    d, u, v = _gcdx(nums, collect(minpoly(F)))
    @assert !iszero(d[1]) && all(iszero, @view d[2:end])
    return reducefraction(F, ntuple(i -> a.denom * u[i], N), d[1])
end

/(a::Number, b::NumberField) = a * inv(b)
//(a::Number, b::NumberField) = a * inv(b)

# resolve ambiguity
/(a::NumberField, b::NumberField) = a * inv(b)
//(a::NumberField, b::NumberField) = a * inv(b)

^(a::F, n::Integer) where F <: NumberField = power_by_squaring(a, n)

function power_by_squaring(a::F, n::Integer) where F <: NumberField
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
@generated function _mul_generated!(res::F, denom, operands...) where F <: NumberField
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
function *(a::Number, b::NumberField)
    # FIXME: should allow for promote_type(typeof(a), numeratortype(b)) different
    # from numeratortype(b)
    reducefraction(typeof(b), numerator(a) .* b.nums, denominator(a) * b.denom)
end

function *(a::NumberField, b::Number)
    # FIXME: see above
    reducefraction(typeof(a), a.nums .* numerator(b), a.denom * denominator(b))
end

function /(a::NumberField, b::Number)
    # FIXME: see above
    reducefraction(typeof(a), a.nums .* denominator(b), a.denom * numerator(b))
end

function //(a::NumberField, b::Number)
    # FIXME: see above
    reducefraction(typeof(a), a.nums .* denominator(b), a.denom * numerator(b))
end

*(a::Complex, b::NumberField) = error("not implemented")
*(a::NumberField, b::NumberField) = error("not implemented")
*(a::NumberField, b::Complex) = error("not implemented")

# -----------------------------------------------------------------------------
#
# Random number
#
# -----------------------------------------------------------------------------
function rand(rng::AbstractRNG, ::SamplerType{F}) where F <: NumberField
    nums = ntuple(i -> rand(rng, numeratortype(F)), degree(F))
    d = rand(rng, denominatortype(F))
    reducefraction(F, nums, d)
end

# -----------------------------------------------------------------------------
#
# In-place operations
#
# -----------------------------------------------------------------------------
const PlusMinus = Union{typeof(+), typeof(-)}
function inplace!(op::PlusMinus, a::F, b::F, c::F) where F <: NumberField{BigInt, N, BigInt} where N
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

convert(::Type{N}, c::N) where N <: NumberField = c
convert(N::Type{<:NumberField}, c::Polynomial) = _convert(N, c)
convert(::Type{N}, c::PolynomialOver{N}) where N <: NumberField = _convert(N, c)
convert(N::Type{<:NumberField}, c::Number) = _convert(N, c)
convert(::Type{F}, c) where F <: NumberField = _convert(F, c)

function _convert(::Type{F}, c) where F <: NumberField
    #=
    We use a switch statement instead of many methods because there is too
    much possibility of method ambiguity
    =#
    if c isa F
        return c
    elseif c isa basefield(F) || c isa Number
        a = convert(numeratortype(F), numerator(c))
        d = convert(denominatortype(F), denominator(c))
        nums = ntuple(i -> i == 1 ? a : zero(a), degree(F))
        return F(nums, d)
    elseif c isa PolynomialOver{F}
        # TODO: assert it is constant
        return iszero(c) ? zero(basering(c)) : c.coeffs[1]
    elseif c isa Symbol
        return knownvalue(F, c)
    elseif namingscheme(typeof(c)) ⊆ boundnames(F)
        return c(;knownvalues(F)...)
    else
        error("Do not know how to convert an element of type $(typeof(c)) to $F")
    end
end

# -----------------------------------------------------------------------------
#
# Constructor-style conversions
#
# -----------------------------------------------------------------------------
(::Type{F})(a::F) where F<:NumberField = deepcopy(a)
(::Type{F})(a) where F<:NumberField = convert(F, a)

promote_rule(F::Type{<:NumberField}, ::Type{<:Number}) = F
deepcopy(x::NumberField) = typeof(x)(map(deepcopy, x.nums), deepcopy(x.denom))

# -----------------------------------------------------------------------------
#
# Resolve ambiguities for number fields over number fields
#
# -----------------------------------------------------------------------------
NumberFieldOver{C} = NumberField{P,C} where P<:Polynomial

+(a::NumberFieldOver{C}, b::C) where C<:NumberField = +(promote(a,b)...)
+(a::C, b::NumberFieldOver{C}) where C<:NumberField = +(promote(a,b)...)
-(a::NumberFieldOver{C}, b::C) where C<:NumberField = -(promote(a,b)...)
-(a::C, b::NumberFieldOver{C}) where C<:NumberField = -(promote(a,b)...)
*(a::NumberFieldOver{C}, b::C) where C<:NumberField = *(promote(a,b)...)
*(a::C, b::NumberFieldOver{C}) where C<:NumberField = *(promote(a,b)...)
//(a::NumberFieldOver{C}, b::C) where C<:NumberField = //(promote(a,b)...)
//(a::C, b::NumberFieldOver{C}) where C<:NumberField = //(promote(a,b)...)
==(a::NumberFieldOver{C}, b::C) where C<:NumberField = ==(promote(a,b)...)
==(a::C, b::NumberFieldOver{C}) where C<:NumberField = ==(promote(a,b)...)

# -----------------------------------------------------------------------------
#
# Algebraic functions
#
# -----------------------------------------------------------------------------
function tr(a::NumberField)
    N = degree(typeof(a))
    minpoly = _minimal_polynomial(typeof(a))

    N*a.coeffs[1] + minpoly[end-1]//minpoly[end] + xxx
end

# -----------------------------------------------------------------------------
#
# Friendly display name macro
#
# -----------------------------------------------------------------------------
macro ringname(ring, name)
    quote
        begin
            import Base: show
            $(esc(:show))(io::IO, ::Type{$(esc(ring))}) = print(io, $name)
            $(esc(ring))
        end
    end
end

function show(io::IO, x::NumberField)
    # TODO: use an expression in the quotient ring, instead.
    _, (α,) = polynomial_ring(:α, basering = basefield(x))
    xx = sum(x.nums[n] // x.denom * α^(n-1) for n in 1:degree(typeof(x)))
    show(io, xx)
end

# -----------------------------------------------------------------------------
#
# Resolve method ambiguity
#
# -----------------------------------------------------------------------------
for N = [QuotientRing, NumberField]
    @eval begin
        promote_rule(::Type{T}, ::Type{C}) where {T<:$N, C <: Constant} = T

        convert(::Type{T}, ::One)      where T<:$N = one(T)
        convert(::Type{T}, ::Zero)     where T<:$N = zero(T)
        convert(::Type{T}, ::MinusOne) where T<:$N = -one(T)

        # fix method ambiguities
        *(x::$N, ::One) = deepcopy(x)
        *(::One, x::$N) = deepcopy(x)
        *(x::$N, ::MinusOne) = -x
        *(::MinusOne, x::$N) = -x

        +(x::$N, ::Zero) = deepcopy(x)
        -(x::$N, ::Zero) = deepcopy(x)
        *(x::$N, ::Zero) = zero(x)
        +(::Zero, x::$N) = deepcopy(x)
        -(::Zero, x::$N) = -x
        *(::Zero, x::$N) = zero(x)
    end
end

# -----------------------------------------------------------------------------
#
# The constructor and verification logic
#
# -----------------------------------------------------------------------------
"""
    S = NumberField(R)

Assert that R is a number field, and return a new data type `S`
such that `S <: Number` and such that computations are more
efficient than those happening in a QuotientRing.

Note: currently, this function does not fully prove that
`Q` is a number field. If it isn't, arithmetic in the resulting
ring will not give meaningful results.
"""
function NumberField(Q::Type{<:QuotientRing})
    P = ring(Q)
    C = basering(P)
    if fraction_field(C) != C
        throw(ArgumentError("$Q is not a numberfield, as its coefficient ring is not even a field"))
    end

    monomials = monomial_basis(Q)

    coeffs(f) = (ff = rem(f,_ideal(Q)); [coefficient(ff,m,variablesymbols(P)...) for m in monomials])
    N = length(monomials)

    K = Vector{C}()
    # let's hope one of these is a primitive element
    possible_α = collect(generators(P))
    append!(possible_α, α*β for (α,β) in zip(generators(P)[2:end], generators(P)[1:end-1]))
    append!(possible_α, α+β for (α,β) in zip(generators(P)[2:end], generators(P)[1:end-1]))
    push!(possible_α, sum(generators(P)))
    push!(possible_α, prod(generators(P)))
    α = zero(P)
    possible_K = []
    for α in possible_α
        M = hcat((coeffs(α^n) for n=0:N)...)

        K = nullspace(M)
        if size(K,2) == 1 && !iszero(K[end,1])
            # TODO: check that the polynomial is irreducible.
            push!(possible_K, (K[:, 1], α, M))
        end
    end
    isempty(possible_K) && error("OOPS! My naive guesses for a primitive element all didn't work. Maybe this is not a number field?")

    sort!(possible_K, by=((K, α, M),)->count(!iszero, K))
    K, α, M = first(possible_K)

    if eltype(K) <: Rational
        D = lcm(denominator.(K))
        K = Integer.(D .* K)
    end
    K .÷= gcd(K)

    F = NumberField{numeratortype(C), length(K) - 1, denominatortype(C)}
    F = type_with_named_values(F) do F, named_values
        for β in variablesymbols(P)
            MM = copy(M)
            MM[:,end] = coeffs(P(β))
            KK = nullspace(MM)

            D = lcm(denominator.(KK))
            KK = Integer.(D .* KK)

            named_values[β] = reducefraction(F, tuple(KK[1:end-1]...), -KK[end] * D)
        end
    end

    # FIXME: lookup existing minimum polynomials by equality
    minpolys[F] = tuple(map(numeratortype(C), K)...)

    # FIXME: do something with this representation of the primitive element,
    # e.g. store it so we can lift + display.
    primitive_element  = Q(α)

    return F
end

end
