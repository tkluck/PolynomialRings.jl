module Polynomials

import PolynomialRings.Terms: Term
import PolynomialRings: generators

# -----------------------------------------------------------------------------
#
# Polynomial
#
# -----------------------------------------------------------------------------

"""
    Polynomial{A, Order} where A <: AbstractVector{T} where T <: Term where Order <: Val

This type represents a polynomial as a vector of terms. All methods guarantee and assume
that the vector is sorted by increasing monomial order, according to `Order` (see
`PolynomialRings.MonomialOrderings`).
"""
struct Polynomial{A, Order}
    terms::A
    Polynomial{A, Order}(terms::A) where A <: AbstractVector{T} where T <: Term where Order <: Val = new(terms)
end

Polynomial(terms::AbstractVector{<:Term}) = Polynomial{typeof(terms), Val{:degrevlex}}(terms)

# -----------------------------------------------------------------------------
#
# Type information
#
# -----------------------------------------------------------------------------

terms(p::Polynomial) = p.terms

termtype(::Type{Polynomial{A, Order}}) where {A,Order} = eltype(A)
basering(::Type{Polynomial{A, Order}}) where {A,Order} = basering(termtype(A))

generators(::Type{P}) where P <: Polynomial = [
    Polynomial([g]) for g in generators(termtype(P))
]


end
