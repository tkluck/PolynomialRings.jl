module Conversions

import PolynomialRings.NamedPolynomials: NamedPolynomial, polynomialtype
import PolynomialRings.Polynomials: Polynomial, termtype, monomialtype, basering, terms
import PolynomialRings.Terms: Term, monomial, coefficient
import PolynomialRings.Monomials: AbstractMonomial
import PolynomialRings: fraction_field, base_extend

_P = Union{Polynomial, NamedPolynomial}

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: promote_rule, convert
import Base: +,*,-,==,/,//
import PolynomialRings: ⊗, base_extend
import PolynomialRings.Groebner: red

# -----------------------------------------------------------------------------
#
# No-op promotions
#
# -----------------------------------------------------------------------------
convert(::Type{P}, x::P) where P <: _P = x

# -----------------------------------------------------------------------------
#
# Promoting coefficients to polynomials
#
# -----------------------------------------------------------------------------

promote_rule(::Type{Polynomial{V,O}}, ::Type{C}) where V <: AbstractVector{T} where T <: Term{M,C} where {O,M,C} = Polynomial{V,O}

function convert(::Type{P}, a::C) where P<:Polynomial{V,O} where V <: AbstractVector{T} where T <: Term{M,C} where {O,M,C}
    if iszero(a)
        return zero(P)
    else
        return P([T(one(M),a)])
    end
end

function convert(::Type{NP}, a::C) where {NP<:NamedPolynomial,C<:Number}
    NP( convert(polynomialtype(NP), a) )
end

# -----------------------------------------------------------------------------
#
# Base extension
#
# -----------------------------------------------------------------------------
base_extend(::Type{Term{M,C1}}, ::Type{C2}) where {M,C1,C2} = Term{M, base_extend(C1,C2)}
base_extend(::Type{Polynomial{V,O}}, ::Type{C}) where V<:AbstractVector{T} where {O,T,C} = Polynomial{Vector{base_extend(T,C)}, O}
base_extend(::Type{NamedPolynomial{P,Names}}, ::Type{C}) where {P,Names,C} = NamedPolynomial{base_extend(P,C),Names}

function base_extend(p::P, ::Type{C}) where P<:Polynomial where C
    PP = base_extend(P, C)
    CC = basering(PP)
    return PP([ Term(monomial(t), CC(coefficient(t))) for t in terms(p) ])
end

base_extend(p::P)      where P <: Union{Term,Polynomial,NamedPolynomial} = base_extend(p, fraction_field(basering(p)))
base_extend(::Type{P}) where P <: Union{Term,Polynomial,NamedPolynomial} = base_extend(P, fraction_field(basering(P)))

# -----------------------------------------------------------------------------
#
# Operations (potentially) needing base extension
#
# -----------------------------------------------------------------------------
/(a::T,b::Number)   where T <: Term = base_extend(T,    float(typeof(b)))(a.m, a.c/b)
//(a::T,b::Number)  where T <: Term = base_extend(T, Rational{typeof(b)})(a.m, a.c//b)
/(a::P,b::Number)   where P <: Polynomial = base_extend(P,   float(typeof(b)))([t/b  for t in terms(a)])
//(a::P,b::Number)  where P <: Polynomial = base_extend(P,Rational{typeof(b)})([t//b for t in terms(a)])
/(a::NP,b::Number)  where NP <: NamedPolynomial = base_extend(NP,   float(typeof(b)))(a.p/b)
//(a::NP,b::Number) where NP <: NamedPolynomial = base_extend(NP,Rational{typeof(b)})(a.p//b)

# -----------------------------------------------------------------------------
#
# Promoting numbers to polynomials (possibly using base extension)
#
# -----------------------------------------------------------------------------
promote_rule(::Type{P}, ::Type{C}) where {P <: Polynomial, C<:Number} = base_extend(P,C)
convert(::Type{P}, a::C) where {P <: Polynomial, C<:Number} = P(basering(P)(a))

# resolve ambiguity between C a coefficient and C a number
promote_rule(::Type{Polynomial{V,O}}, ::Type{C}) where V <: AbstractVector{T} where T <: Term{M,C} where {O,M,C<:Number} = Polynomial{V,O}
function convert(::Type{P}, a::C) where P<:Polynomial{V,O} where V <: AbstractVector{T} where T <: Term{M,C} where {O,M,C<:Number}
    if iszero(a)
        return zero(P)
    else
        return P([T(one(M),a)])
    end
end

# -----------------------------------------------------------------------------
#
# Promoting scalars to terms
#
# -----------------------------------------------------------------------------

promote_rule(::Type{T}, ::Type{C}) where T <: Term where C<:Number = base_extend(T,C)

convert(::Type{T}, a::C) where T <: Term{M} where M where C<:Number = base_extend(T,C)(one(M), a)

# -----------------------------------------------------------------------------
#
# Promoting terms to polynomials
#
# -----------------------------------------------------------------------------

promote_rule(::Type{P}, ::Type{T}) where P <: Polynomial{<:AbstractArray{T}} where T <: Term = P

convert(::Type{P}, a::T) where P <: Polynomial{<:AbstractArray{T}} where T <: Term = iszero(a) ? zero(P) : P([a])

# -----------------------------------------------------------------------------
#
# Implicit typecasts (like what we'd get if Polynomial <: Number)
#
# TODO: certain exclusions for ambigious situations where we have a
# Polynomial with polynomial coefficients on one side, but not the
# other. In that case, should the 'bare' polynomial f be regarded as
# f⊗1 or 1⊗f ? (I'd rather not make a choice, but wait until I implement
# a version of polynomials with named variables.)
#
# -----------------------------------------------------------------------------
+(a::P1,b::P2) where {P1<:_P,P2<:_P} = +(promote(a,b)...)
*(a::P1,b::P2) where {P1<:_P,P2<:_P} = *(promote(a,b)...)
-(a::P1,b::P2) where {P1<:_P,P2<:_P} = -(promote(a,b)...)
==(a::P1,b::P2) where {P1<:_P,P2<:_P} = ==(promote(a,b)...)

_C = Union{Number, AbstractMonomial, Term}
+(a::C,b::P) where P<:_P where C<:_C = +(promote(a,b)...)
+(a::P,b::C) where P<:_P where C<:_C = +(promote(a,b)...)
*(a::C,b::P) where P<:_P where C<:_C = *(promote(a,b)...)
*(a::P,b::C) where P<:_P where C<:_C = *(promote(a,b)...)
-(a::C,b::P) where P<:_P where C<:_C = -(promote(a,b)...)
-(a::P,b::C) where P<:_P where C<:_C = -(promote(a,b)...)
==(a::P,b::C) where P<:_P where C<:_C = ==(promote(a,b)...)
==(a::C,b::P) where P<:_P where C<:_C = ==(promote(a,b)...)

# -----------------------------------------------------------------------------
#
# Polynomials with polynomial coefficients
#
# -----------------------------------------------------------------------------
"""
    ⊗(a::Polynomial, b::Polynomial)

Construct a polynomial with polynomial coefficients, by promoting a with the type of the coefficients of b.
"""

function ⊗(a::P1, b::P2) where P1 <: Polynomial where P2 <: Polynomial
    P = P1⊗P2
    assert(basering(P) === P1)
    l = P(a)
    r = base_extend(b, P1)
    assert(typeof(l) === typeof(r))
    l * r
end

⊗(::Type{P1}, ::Type{P2}) where P1 <: _P where P2 <: Polynomial{<:AbstractVector{T}} where T = base_extend(P2, P1)

# -----------------------------------------------------------------------------
#
# Use Term as a polynomial
#
# -----------------------------------------------------------------------------
promote_rule(::Type{P}, ::Type{T}) where P <: Polynomial{V} where V <: AbstractVector{T} where T <: Term = P
convert(::Type{P}, a::T) where P <: Polynomial{V} where V <: AbstractVector{T} where T <: Term = P([a])


# -----------------------------------------------------------------------------
#
# Promotions for more complicated functions
#
# -----------------------------------------------------------------------------
function red(a::S,b::AbstractVector{T}) where {S,T}
    U = typejoin(promote_rule(S,T), promote_rule(T,S))
    if U === Union{}
        throw(TypeError())
    else
        return red(U(a), map(U,b))
    end
end

end
