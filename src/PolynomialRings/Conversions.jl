module Conversions

import PolynomialRings.Polynomials: Polynomial, termtype, monomialtype
import PolynomialRings.Terms: Term
import PolynomialRings.Monomials: AbstractMonomial

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: promote_rule, convert
import Base: +,*,-
import PolynomialRings: iszero

# -----------------------------------------------------------------------------
#
# Promoting scalars to polynomials
#
# -----------------------------------------------------------------------------

promote_rule(::Type{P}, ::Type{C2}) where P <: Polynomial{V,O} where V <: AbstractVector{T} where T <: Term{M,C1} where {M,O,C1,C2} = Polynomial{Vector{Term{M, promote_type(C1,C2)}}, O}

convert(::Type{P}, a::C2) where P <: Polynomial{V,O} where V <: AbstractVector{T} where T <: Term{M,C1} where {M,O,C1,C2} = promote_type(P, C2)([termtype(P)(a)])

# -----------------------------------------------------------------------------
#
# Promoting scalars to terms
#
# -----------------------------------------------------------------------------

promote_rule(::Type{T}, ::Type{C2}) where T <: Term{M,C1} where {M,C1,C2} = Term{M, promote_type(C1,C2)}

convert(::Type{T}, a::C2) where T <: Term{M,C1} where {M,C1,C2} = T(one(M), promote_type(C1,C2)(a))

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
+(a::C,b::Polynomial) where C = +(promote(a,b)...)
+(a::Polynomial,b::C) where C = +(promote(a,b)...)
*(a::C,b::Polynomial) where C = *(promote(a,b)...)
*(a::Polynomial,b::C) where C = *(promote(a,b)...)
-(a::C,b::Polynomial) where C = -(promote(a,b)...)
-(a::Polynomial,b::C) where C = -(promote(a,b)...)

# -----------------------------------------------------------------------------
#
# Polynomials with polynomial coefficients
#
# -----------------------------------------------------------------------------
*(a::P1, b::P2) where P1 <: Polynomial{V,O} where V <: AbstractVector{T} where T <: Term{M, P2} where P2 <: Polynomial where {O,M} = a * Polynomial([Term(one(M), b)])
*(a::P1, b::P2) where P2 <: Polynomial{V,O} where V <: AbstractVector{T} where T <: Term{M, P1} where P1 <: Polynomial where {O,M} = Polynomial([Term(one(M), a)])* b

"""
    ⊗(a::Polynomial, b::Polynomial)

Construct a polynomial with polynomial coefficients, by promoting a with the coefficients of b.
"""

⊗(a::P1, b::P2) where P1 <: Polynomial where P2 <: Polynomial = Polynomial([Term(one(monomialtype(P1)), a)]) * b


end
