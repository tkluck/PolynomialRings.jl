module Terms

import PolynomialRings.Monomials: AbstractMonomial

"""
    Term{M, C} where M <: AbstractMonomial where C

This type represents a single term of a multivariate polynomial:
that is, it represents the combination of a coefficient and a
monomial.

"""
struct Term{M <: AbstractMonomial, C}
    m::M
    c::C
end

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: *, -, one
import PolynomialRings: generators, iszero

# -----------------------------------------------------------------------------
#
# Type information
#
# -----------------------------------------------------------------------------
monomialtype(::Type{Term{M,C}}) where {M,C} = M
basering(::Type{Term{M,C}}) where {M,C} = C

# -----------------------------------------------------------------------------
#
# Term functions
#
# -----------------------------------------------------------------------------
*(a::Term{M, C1}, b::Term{M, C2}) where M <: AbstractMonomial where {C1,C2} = Term(a.m*b.m, a.c*b.c)
-(a::T) where T <: Term = T(a.m, -a.c)

one(::Type{Term{M,C}}) where {M, C} = Term{M,C}(one(M), one(C))

monomial(a::Term) = a.m
coefficient(a::Term) = a.c

import PolynomialRings.Util: lazymap
generators(::Type{Term{M,C}}) where {M, C} = lazymap(g -> Term{M,C}(g, one(C)), generators(M))

iszero(a::Term) = coefficient(a) == 0


end
