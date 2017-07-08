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
import Base: *, +, -, one, ==, iszero
import PolynomialRings: generators, to_dense_monomials, max_variable_index, deg, basering
import PolynomialRings: maybe_div, lcm_multipliers, monomialtype

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
+(a::T)            where T <: Term = a
-(a::T)            where T <: Term = T(a.m, -a.c)
==(a::T,b::T)      where T <: Term = a.m == b.m && a.c == b.c

one(::Type{Term{M,C}}) where {M, C} = Term{M,C}(one(M), one(C))

monomial(a::Term) = a.m
coefficient(a::Term) = a.c

import PolynomialRings.Util: lazymap
generators(::Type{Term{M,C}}) where {M, C} = lazymap(g -> Term{M,C}(g, one(C)), generators(M))

iszero(a::Term) = coefficient(a) == 0

to_dense_monomials(n, a::Term) = Term( to_dense_monomials(n, monomial(a)), coefficient(a) )
max_variable_index(a::Term) = max_variable_index(monomial(a))

deg(a::Term) = deg(monomial(a))


function maybe_div(a::T, b::T)::Nullable{T} where T<:Term
    maybe_q = maybe_div(monomial(a), monomial(b))
    if isnull(maybe_q)
        return nothing
    else
        return T(get(maybe_q), coefficient(a) // coefficient(b))
    end
end

function lcm_multipliers(a::T, b::T)::Tuple{T,T} where T<:Term
    m_a,m_b = lcm_multipliers(monomial(a), monomial(b))
    return T(m_a, coefficient(b)), T(m_b, coefficient(a))
end

(t::Term)(args...) = coefficient(t) * monomial(t)(args...)

end
