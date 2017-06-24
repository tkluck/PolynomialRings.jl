module Conversions

import PolynomialRings.Polynomials: Polynomial, termtype
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
# -----------------------------------------------------------------------------
+(a::C,b::Polynomial) where C = +(promote(a,b)...)
+(a::Polynomial,b::C) where C = +(promote(a,b)...)
*(a::C,b::Polynomial) where C = *(promote(a,b)...)
*(a::Polynomial,b::C) where C = *(promote(a,b)...)
-(a::C,b::Polynomial) where C = -(promote(a,b)...)
-(a::Polynomial,b::C) where C = -(promote(a,b)...)



end
