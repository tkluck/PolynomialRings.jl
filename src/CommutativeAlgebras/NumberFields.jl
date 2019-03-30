module NumberFields

using PolynomialRings
import Base: +,-,*,/,//,==,!=
import Base: promote_rule, convert
import Base: show
import Base: zero, one, inv, copy
import LinearAlgebra: nullspace
import LinearAlgebra: tr, norm

import ..Constants: Constant, One, MinusOne, Zero
import ..Ideals: ring
import ..Monomials: AbstractMonomial
import ..NamingSchemes: boundnames, fullboundnames
import ..Polynomials: Polynomial, PolynomialOver, basering, variablesymbols
import ..QuotientRings: QuotientRing, monomial_basis
import ..QuotientRings: _ideal
import ..Terms: Term, monomial, coefficient
import ..Util.LinAlgUtil: AbstractExactNumber
import PolynomialRings: allvariablesymbols, fraction_field, basering

# -----------------------------------------------------------------------------
#
# Type and type information
#
# -----------------------------------------------------------------------------

struct NumberField{P<:Polynomial,C,Q} <: AbstractExactNumber
    coeffs::Vector{C}
    NumberField{P,C,Q}(coeffs::Vector{C}) where {P<:Polynomial,C,Q} = new(coeffs)
end
ring(::Type{<:NumberField{P}}) where P = P
basering(::Type{<:NumberField{P}}) where P = basering(P)
quotientring(::Type{<:NumberField{P,C,Q}}) where {P,C,Q} = Q

_values = Dict()
_primitive_element(N) = _values[N].primitive_element
_minimal_polynomial(N) = _values[N].minimal_polynomial
_extension_degree(N) = _values[N].extension_degree
_named_values(N) = _values[N].named_values

# -----------------------------------------------------------------------------
#
# The constructor and verification logic
#
# -----------------------------------------------------------------------------
const PRIMITIVE_ELEMENT_TRIES = 10
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

    F = NumberField{P, C, Q}

    K = Vector{C}()
    # let's hope one of these is a primitive element
    possible_α = collect(generators(P))
    append!(possible_α, α+β for (α,β) in zip(generators(P)[2:end], generators(P)[1:end-1]))
    append!(possible_α, α*β for (α,β) in zip(generators(P)[2:end], generators(P)[1:end-1]))
    push!(possible_α, sum(generators(P)))
    found = false
    α = zero(P)
    M = Matrix{C}(undef,0,0)
    for α₁ in possible_α
        M = hcat((coeffs(α₁^n) for n=0:N)...)

        K = nullspace(M)
        if size(K,2) == 1 && !iszero(K[end,1])
            # TODO: check that the polynomial is irreducible.
            K = K[:,1]
            α = α₁
            found = true
            break
        end
    end
    if !found
        throw(AssertionError("OOPS! My naive guesses for a primitive element all didn't work. Maybe this is not a number field?"))
    end

    named_values = Dict{Symbol, F}()
    _values[F] = (
        primitive_element  = Q(α),
        extension_degree   = N,
        minimal_polynomial = K,
        named_values       = named_values,
    )

    for β in variablesymbols(P)
        MM = copy(M)
        MM[:,end] = coeffs(P(β))
        KK = nullspace(MM)
        named_values[β] = F( KK[1:end-1] // -KK[end] )
    end

    return F
end

function convert(::Type{F}, c::C) where F<:NumberField{P, C} where {P<:Polynomial, C}
    coeffs = zeros(C, _extension_degree(F))
    coeffs[1] = c
    F(coeffs)
end

function convert(::Type{F}, c::C) where F<:NumberField{P, C} where {P<:Polynomial, C<:Number}
    coeffs = zeros(C, _extension_degree(F))
    coeffs[1] = c
    F(coeffs)
end

convert(::Type{F}, f::P) where F<:NumberField{P, C} where {P<:Polynomial, C} =
    f(;_named_values(F)...)

convert(::Type{F}, f::Q) where F<:NumberField{P, C, Q} where {P<:Polynomial, C, Q} =
    f.f(;_named_values(F)...)

# -----------------------------------------------------------------------------
#
# Constructor-style conversions
#
# -----------------------------------------------------------------------------
(::Type{F})(a::F) where F<:NumberField = a
(::Type{F})(a) where F<:NumberField = convert(F, a)

# -----------------------------------------------------------------------------
#
# Operations for NumberFields (mostly pass-through)
#
# -----------------------------------------------------------------------------
zero(::Type{Q}) where Q<:NumberField{P} where P<:Polynomial = Q(zero(basering(P)))
one(::Type{Q})  where Q<:NumberField{P} where P<:Polynomial = Q(one(basering(P)))
zero(a::NumberField) = zero(typeof(a))
one(a::NumberField)  = one(typeof(a))
copy(a::NumberField) = a

+(a::NumberField) = a
-(a::Q) where Q<:NumberField = Q(-a.coeffs)
+(a::Q, b::Q)  where Q<:NumberField = Q(a.coeffs.+b.coeffs)
-(a::Q, b::Q)  where Q<:NumberField = Q(a.coeffs.-b.coeffs)
==(a::Q, b::Q) where Q<:NumberField = a.coeffs == b.coeffs
!=(a::Q, b::Q) where Q<:NumberField = a.coeffs != b.coeffs
allvariablesymbols(::Type{Q}) where Q<:NumberField = allvariablesymbols(ring(Q))
boundnames(::Type{Q})         where Q<:NumberField = boundnames(quotientring(Q))
fullboundnames(::Type{Q})     where Q<:NumberField = fullboundnames(quotientring(Q))

fraction_field(::Type{N}) where N<:NumberField = N

# -----------------------------------------------------------------------------
#
# The only interesting NumberFields operations: multiplication and division
#
# -----------------------------------------------------------------------------
function _rem(a::AbstractVector{C}, b::AbstractVector{C}) where C
    a = copy(a)
    len_a = findlast(!iszero, a)
    len_b = findlast(!iszero, b)
    while !isnothing(len_a) && len_a >= len_b
        q = a[len_a] // b[len_b]
        a[len_a-len_b+1:len_a] .-= q .* b[1:len_b]
        len_a = findprev(!iszero, a, len_a-1)
    end
    a
end

function _gcdx(a::AbstractVector{C}, b::AbstractVector{C}) where C
    a = copy(a)
    b = copy(b)
    len_a = findlast(!iszero, a)
    len_b = findlast(!iszero, b)
    len_a === nothing && (len_a = 0)
    len_b === nothing && (len_b = 0)
    m = max(len_a, len_b)
    s0, s1 = zeros(C, m), zeros(C, m)
    t0, t1 = zeros(C, m), zeros(C, m)
    s0[1] = one(C)
    t1[1] = one(C)
    # The loop invariant is: s0*a0 + t0*b0 == a
    while len_b != 0
        s2 = copy(s0)
        t2 = copy(t0)
        while len_a >= len_b
            q = a[len_a] // b[len_b]
            a[len_a-len_b+1:len_a] .-= q .* b[1:len_b]

            deg_diff = len_a - len_b
            s2[deg_diff+1:end] .-= q .* s1[1:end-deg_diff]
            t2[deg_diff+1:end] .-= q .* t1[1:end-deg_diff]

            len_a = findprev(!iszero, a, len_a-1)
            len_a == nothing && (len_a = 0)
        end
        a, b = b, a
        len_a, len_b = len_b, len_a
        s0, s1 = s1, s2
        t0, t1 = t1, t2
    end
    return (a, s0, t0)
end

_gcd(a, b) = ( (d,u,v) = _gcdx(a, b); d )

function *(a::Q, b::Q) where Q<:NumberField
    N = _extension_degree(Q)
    coeffs = zeros(basering(Q), 2N-1)

    for (i, a_i) in enumerate(a.coeffs)
        for (j, b_j) in enumerate(b.coeffs)
            coeffs[i+j-1] += a_i*b_j
        end
    end

    return Q(_rem(coeffs, _minimal_polynomial(Q))[1:N])
end

function inv(a::Q) where Q<:NumberField
    N = _extension_degree(Q)
    d,u,v = _gcdx(a.coeffs, _minimal_polynomial(Q))
    if iszero(d[1]) || any(!iszero(d[2:end]))
        throw(DivideError("$a is not invertible"))
    end
    return Q( u[1:N] // d[1] )
end

//(a::Q, b::Q) where Q<:NumberField = a * inv(b)
/(a::Q, b::Q) where Q<:NumberField = a * inv(b)

# -----------------------------------------------------------------------------
#
# Operations through promotion
#
# -----------------------------------------------------------------------------
function promote_rule(::Type{N}, ::Type{C}) where N<:NumberField where C
    Q = quotientring(N)
    rule_for_Q = promote_rule(Q, C)
    if rule_for_Q === Q
        return N
    else
        return rule_for_Q
    end
end

function convert(::Type{N}, c::C) where N<:NumberField{P} where {P<:Polynomial,C}
    N(convert(P, c))
end

function convert(::Type{N}, c::C) where N<:NumberField{P} where {P<:Polynomial,C<:Number}
    N(convert(quotientring(N), c))
end

function convert(::Type{Q}, x::NumberField) where Q <: QuotientRing{P} where P<:Polynomial
    N = typeof(x)
    M = _extension_degree(N)
    α = _primitive_element(N)
    q = sum(c * α.f^n for (n, c) in zip(0:(M-1), x.coeffs))
    return convert(Q, q)
end

# resolve ambiguity
function convert(::Type{N}, x::Polynomial) where N <: NumberField
    N(convert(quotientring(N), x))
end

convert(::Type{N}, q::N) where N<:NumberField{P} where P<:Polynomial = q

promote_rule(::Type{C}, ::Type{N}) where {P<:Polynomial,N<:NumberField{P},C<:PolynomialOver{N}} = C
# -----------------------------------------------------------------------------
#
# Operations through promotion
#
# -----------------------------------------------------------------------------
+(a::NumberField, b::Number) = +(promote(a,b)...)
+(a::Number, b::NumberField) = +(promote(a,b)...)
-(a::NumberField, b::Number) = -(promote(a,b)...)
-(a::Number, b::NumberField) = -(promote(a,b)...)
*(a::NumberField, b::Number) = *(promote(a,b)...)
*(a::Number, b::NumberField) = *(promote(a,b)...)
//(a::NumberField, b::Number) = //(promote(a,b)...)
//(a::Number, b::NumberField) = //(promote(a,b)...)
==(a::NumberField, b::Number) = ==(promote(a,b)...)
==(a::Number, b::NumberField) = ==(promote(a,b)...)
!=(a::NumberField, b::Number) = !=(promote(a,b)...)
!=(a::Number, b::NumberField) = !=(promote(a,b)...)

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
!=(a::NumberFieldOver{C}, b::C) where C<:NumberField = !=(promote(a,b)...)
!=(a::C, b::NumberFieldOver{C}) where C<:NumberField = !=(promote(a,b)...)

# -----------------------------------------------------------------------------
#
# Algebraic functions
#
# -----------------------------------------------------------------------------
function tr(a::NumberField)
    N = _extension_degree(Q)
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
    f = convert(quotientring(typeof(x)), x)
    print(io, f)
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


end
