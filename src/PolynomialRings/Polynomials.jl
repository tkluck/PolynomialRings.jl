module Polynomials

import PolynomialRings.Monomials: TupleMonomial
import PolynomialRings.Terms: Term

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import PolynomialRings: generators, to_dense_monomials, max_variable_index, basering, monomialtype, deg

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
monomialorder(::Type{Polynomial{A, Order}}) where {A,Order} = Order
basering(::Type{P}) where P <: Polynomial = basering(termtype(P))
monomialtype(::Type{P}) where P <: Polynomial = monomialtype(termtype(P))

monomialorder(p::P) where P <: Polynomial = monomialorder(typeof(p))
basering(p::P) where P <: Polynomial = basering(typeof(p))

import PolynomialRings.Util: lazymap
generators(::Type{P}) where P <: Polynomial = lazymap(
    g->P([g]), generators(termtype(P))
)


# TODO: take right integer type for TupleMonomial exponents
to_dense_monomials(n, p::Polynomial) = Polynomial{Vector{Term{TupleMonomial{n,Int},basering(p)}},monomialorder(p)}([ to_dense_monomials(n, t) for t in terms(p) ])
max_variable_index(p::Polynomial) = maximum(max_variable_index(t) for t in terms(p))

deg(p::Polynomial) = deg(last(terms(p)))

end
