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
import Base: *


# -----------------------------------------------------------------------------
#
# Term functions
#
# -----------------------------------------------------------------------------
*(a::T, b::T) where T <: Term = T(a.m + b.m, a.c*b.c)


end
