module Conversions

import PolynomialRings.Polynomials: Polynomial, termtype, monomialtype, basering, terms
import PolynomialRings.Terms: Term, monomial, coefficient
import PolynomialRings.Monomials: AbstractMonomial
import PolynomialRings: fraction_field, base_extend, namestype

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: promote_rule, convert
import Base: +,*,-,==,/,//
import PolynomialRings: ⊗, base_extend
import Base: divrem

# -----------------------------------------------------------------------------
#
# No-op promotions
#
# -----------------------------------------------------------------------------
(::Type{P})(a::P) where P <: Polynomial = a
convert(::Type{P}, x::P) where P <: Polynomial = x

# -----------------------------------------------------------------------------
#
# Promoting coefficients to polynomials
#
# -----------------------------------------------------------------------------

promote_rule(::Type{Polynomial{V,O}}, ::Type{C}) where V <: AbstractVector{T} where T <: Term{M,C} where {O,M,C} = Polynomial{V,O}

function convert(::Type{P}, a::C) where P<:Polynomial{V} where V <: AbstractVector{T} where T <: Term{M,C} where {M,C}
    if iszero(a)
        return zero(P)
    else
        return P([T(one(M),a)])
    end
end

# -----------------------------------------------------------------------------
#
# Base extension
#
# -----------------------------------------------------------------------------
base_extend(::Type{Term{M,C1}}, ::Type{C2}) where {M,C1,C2} = Term{M, base_extend(C1,C2)}
base_extend(::Type{Polynomial{V,O}}, ::Type{C}) where V<:AbstractVector{T} where {O,T,C} = Polynomial{Vector{base_extend(T,C)}, O}

function base_extend(t::T, ::Type{C}) where T<:Term where C
    TT = base_extend(T, C)
    CC = basering(TT)
    return TT(monomial(t), CC(coefficient(t)))
end

function base_extend(p::P, ::Type{C}) where P<:Polynomial where C
    PP = base_extend(P, C)
    T = termtype(PP)
    return PP(T[ base_extend(t, C) for t in terms(p) ])
end

base_extend(p::P)      where P <: Union{Term,Polynomial} = base_extend(p, fraction_field(basering(p)))
base_extend(::Type{P}) where P <: Union{Term,Polynomial} = base_extend(P, fraction_field(basering(P)))

# -----------------------------------------------------------------------------
#
# Operations (potentially) needing base extension
#
# -----------------------------------------------------------------------------
/(a::T,b::Number)   where T <: Term = base_extend(T,    float(typeof(b)))(a.m, a.c/b)
//(a::T,b::Number)  where T <: Term = base_extend(T, fraction_field(typeof(b)))(a.m, a.c//b)
/(a::P,b::Number)   where P <: Polynomial = base_extend(P,   float(typeof(b)))([t/b  for t in terms(a)])
//(a::P,b::Number)  where P <: Polynomial = base_extend(P,fraction_field(typeof(b)))([t//b for t in terms(a)])

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
# Promoting monomials to polynomials
#
# -----------------------------------------------------------------------------

promote_rule(::Type{P}, ::Type{M}) where P <: Polynomial{<:AbstractArray{T}} where T <: Term{M,C} where {M<:AbstractMonomial,C} = P
#
convert(::Type{P}, a::M) where P <: Polynomial{<:AbstractArray{T}} where T <: Term{M,C} where {M<:AbstractMonomial,C} = P([T(a,one(C))])

# -----------------------------------------------------------------------------
#
# Implicit typecasts (like what we'd get if Polynomial <: Number)
#
# -----------------------------------------------------------------------------
+(a::P1,b::P2) where {P1<:Polynomial,P2<:Polynomial} = +(promote(a,b)...)
*(a::P1,b::P2) where {P1<:Polynomial,P2<:Polynomial} = *(promote(a,b)...)
-(a::P1,b::P2) where {P1<:Polynomial,P2<:Polynomial} = -(promote(a,b)...)
==(a::P1,b::P2) where {P1<:Polynomial,P2<:Polynomial} = ==(promote(a,b)...)

_C = Union{Number, AbstractMonomial, Term}
+(a::C,b::P) where P<:Polynomial where C<:_C = +(promote(a,b)...)
+(a::P,b::C) where P<:Polynomial where C<:_C = +(promote(a,b)...)
*(a::C,b::P) where P<:Polynomial where C<:_C = *(promote(a,b)...)
*(a::P,b::C) where P<:Polynomial where C<:_C = *(promote(a,b)...)
-(a::C,b::P) where P<:Polynomial where C<:_C = -(promote(a,b)...)
-(a::P,b::C) where P<:Polynomial where C<:_C = -(promote(a,b)...)
==(a::P,b::C) where P<:Polynomial where C<:_C = ==(promote(a,b)...)
==(a::C,b::P) where P<:Polynomial where C<:_C = ==(promote(a,b)...)

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
    @assert basering(P) === base_extend(P1, basering(P2))
    l = P(base_extend(a, basering(P2)))
    r = base_extend(b, P1)
    @assert typeof(l) === typeof(r)
    l * r
end

⊗(::Type{P1}, ::Type{P2}) where P1 <: Polynomial where P2 <: Polynomial{<:AbstractVector{T}} where T = base_extend(P2, P1)

# -----------------------------------------------------------------------------
#
# Polynomials with polynomial coefficients: resolve ambiguities
#
# -----------------------------------------------------------------------------

# Resolve ambiguity with the convert method that takes care of canonical mappings
# between polynomial rings
function convert(::Type{P}, a::C) where P<:Polynomial{V} where V <: AbstractVector{T} where T <: Term{M,C} where {M,C<:Polynomial}
    if iszero(a)
        return zero(P)
    else
        return P([T(one(M),a)])
    end
end

# Don't duplicate variable names as a result of base_extend
function base_extend(::Type{Term{M,C1}}, ::Type{C2}) where {M,C1,C2<:Polynomial}
    if namestype(C2) == namestype(M)
        Term{M, base_extend(C1,basering(C2))}
    else
        Term{M, base_extend(C1,C2)}
    end
end


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
function divrem(a::S,b::AbstractVector{T}) where {S<:Number,T<:Polynomial}
    U = typejoin(promote_rule(S,T), promote_rule(T,S))
    if U === Union{}
        throw(TypeError())
    else
        return divrem(U(a), map(U,b))
    end
end

end
