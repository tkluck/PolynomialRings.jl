module NumberFields

using PolynomialRings
using PolynomialRings.Polynomials: Polynomial, basering, variablesymbols
using PolynomialRings.Monomials: AbstractMonomial
using PolynomialRings.Terms: Term, monomial, coefficient
using PolynomialRings.QuotientRings: QuotientRing, monomial_basis
if VERSION >= v"0.7-"
    using LinearAlgebra: nullspace
end

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: promote_rule, convert
import Base: zero, one, inv, copy
import Base: +,-,*,/,//,==,!=
import Base: show
import PolynomialRings: allvariablesymbols, fraction_field, basering
import PolynomialRings.Ideals: ring
import PolynomialRings.QuotientRings: _ideal
import PolynomialRings.Util.LinAlgUtil: AbstractExactNumber
if VERSION >= v"0.7-"
    import LinearAlgebra: tr, norm
else
    import Base: norm
end

# -----------------------------------------------------------------------------
#
# Type and type information
#
# -----------------------------------------------------------------------------

struct NumberField{P<:Polynomial,C,Q} <: AbstractExactNumber
    coeffs::Vector{C}
    NumberField{P,C,Q}(coeffs::Vector{C}) where {P,C,Q} = new(coeffs)
end
ring(::Type{F}) where F<:NumberField{P} where P = P
basering(::Type{F}) where F<:NumberField{P} where P = basering(P)

function _primitive_element end
function _minimal_polynomial end
function _extension_degree end
function _named_values end

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
function NumberField(::Type{Q}) where Q<:QuotientRing
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
    M = Matrix{C}(0,0)
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

    @eval _primitive_element(::Type{$F}) = $(Q(α))
    @eval _extension_degree(::Type{$F}) = $N
    @eval _minimal_polynomial(::Type{$F}) = $K

    named_values = Dict{Symbol, F}()
    for β in variablesymbols(P)
        MM = copy(M)
        MM[:,end] = coeffs(P(β))
        KK = nullspace(MM)
        named_values[β] = F( KK[1:end-1] // -KK[end] )
    end

    @eval _named_values(::Type{$F}) = $named_values

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
    while len_a >= len_b
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
    if VERSION >= v"0.7-"
        len_a == nothing && (len_a = 0)
        len_b == nothing && (len_b = 0)
    end
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
            VERSION >= v"0.7-" && len_a == nothing && (len_a = 0)
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
function promote_rule(::Type{N}, ::Type{C}) where N<:NumberField{P} where {P<:Polynomial,C}
    rule_for_P = typejoin( promote_rule(P,C), promote_rule(C,P) )
    if rule_for_P === P
        return N
    else
        return Union{}
    end
end

function convert(::Type{N}, c::C) where N<:NumberField{P} where {P<:Polynomial,C}
    N(convert(P, c))
end

function convert(::Type{N}, c::C) where N<:NumberField{P} where {P<:Polynomial,C<:Number}
    N(convert(P, c))
end

convert(::Type{N}, q::N) where N<:NumberField{P} where P<:Polynomial = q

# resolve an ambiguity for expansion() to work
promote_rule(::Type{N}, ::Type{C}) where {N<:NumberField,C<:PolynomialRings.Constants.Constant} = N

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
    N = _extension_degree(typeof(x))
    α = _primitive_element(typeof(x))
    f = typeof(α)(sum(c * α.f^n for (n, c) in zip(0:(N-1), x.coeffs)))
    print(io, f)
end

end
