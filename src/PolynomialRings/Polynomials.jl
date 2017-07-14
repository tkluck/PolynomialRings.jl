module Polynomials

import PolynomialRings.Monomials: TupleMonomial
import PolynomialRings.Terms: Term

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import PolynomialRings: generators, to_dense_monomials, max_variable_index, basering, monomialtype, deg
import PolynomialRings: leading_term, termtype, monomialorder, terms, exptype
import Base: copy

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
    Polynomial{A, Order}(terms::A) where A <: AbstractVector{T} where T <: Term where Order = new(terms)
end

# -----------------------------------------------------------------------------
#
# Type information
#
# -----------------------------------------------------------------------------

terms(p::Polynomial) = p.terms

termtype(::Type{Polynomial{A, Order}}) where {A,Order} = eltype(A)
exptype(::Type{P}) where P<:Polynomial = exptype(termtype(P))
monomialorder(::Type{Polynomial{A, Order}}) where {A,Order} = Order
basering(::Type{P}) where P <: Polynomial = basering(termtype(P))
monomialtype(::Type{P}) where P <: Polynomial = monomialtype(termtype(P))

import PolynomialRings.Util: lazymap
generators(::Type{P}) where P <: Polynomial = lazymap(
    g->P([g]), generators(termtype(P))
)

function to_dense_monomials(n, p::Polynomial)
    T = Term{TupleMonomial{n,exptype(p)},basering(p)}
    P = Polynomial{Vector{T},monomialorder(p)}
    P(T[ to_dense_monomials(n, t) for t in terms(p) ])
end

max_variable_index(p::Polynomial) = maximum(max_variable_index(t) for t in terms(p))

deg(p::Polynomial) = iszero(p) ? -1 : deg(last(terms(p)))
leading_term(p::Polynomial) = last(terms(p))

copy(p::Polynomial) = typeof(p)(copy(p.terms))

end
