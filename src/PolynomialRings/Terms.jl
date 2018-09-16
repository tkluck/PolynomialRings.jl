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
import Base: *, ^, +, -, one, ==, iszero, diff
import Base: hash
import PolynomialRings: generators, to_dense_monomials, max_variable_index, basering
import PolynomialRings: maybe_div, lcm_multipliers, monomialtype, exptype, lcm_degree, namestype, monomialorder
import Base.Order: lt
import PolynomialRings.MonomialOrderings: MonomialOrder
import PolynomialRings.Monomials: total_degree

# -----------------------------------------------------------------------------
#
# Type information
#
# -----------------------------------------------------------------------------
monomialtype(::Type{Term{M,C}}) where {M,C} = M
basering(::Type{Term{M,C}}) where {M,C} = C
exptype(::Type{T}) where T<:Term = exptype(monomialtype(T))
namestype(::Type{T}) where T<:Term = namestype(monomialtype(T))
monomialorder(::Type{T}) where T <: Term = monomialorder(monomialtype(T))

# -----------------------------------------------------------------------------
#
# Term functions
#
# -----------------------------------------------------------------------------
*(a::Term{M, C1}, b::Term{M, C2}) where M <: AbstractMonomial where {C1,C2} = Term(a.m*b.m, a.c*b.c)
*(a::Term{M, C}, b::C) where M <: AbstractMonomial where C = Term(a.m, a.c*b)
*(a::C, b::Term{M, C}) where M <: AbstractMonomial where C = Term(b.m, a*b.c)
+(a::T)                where T <: Term = a
-(a::T)                where T <: Term = T(a.m, -a.c)
==(a::T,b::T)          where T <: Term = a.m == b.m && a.c == b.c
^(a::T, n::Integer)    where T <: Term = T(a.m^n, a.c^n)

one(::Type{Term{M,C}}) where {M, C} = Term{M,C}(one(M), one(C))
one(t::T) where T <: Term = one(typeof(t))

monomial(a::Term) = a.m
coefficient(a::Term) = a.c

hash(a::Term, h::UInt) = hash(a.m, hash(a.c, h))

generators(::Type{Term{M,C}}) where {M, C} = (
    Term{M,C}(g, one(C)) for g in generators(M)
)

iszero(a::Term) = coefficient(a) == 0

to_dense_monomials(n, a::Term) = Term( to_dense_monomials(n, monomial(a)), coefficient(a) )
max_variable_index(a::Term) = max_variable_index(monomial(a))

function maybe_div(a::T, b::T) where T<:Term
    q = maybe_div(monomial(a), monomial(b))
    if q === nothing || iszero(coefficient(b))
        return nothing
    else
        return T(q, coefficient(a) // coefficient(b))
    end
end

function lcm_multipliers(a::T, b::T)::Tuple{T,T} where T<:Term
    m_a,m_b = lcm_multipliers(monomial(a), monomial(b))
    return T(m_a, coefficient(b)), T(m_b, coefficient(a))
end

(t::Term)(args...) = coefficient(t) * monomial(t)(args...)

function diff(t::T, i::Integer) where T <: Term
    n,m = diff(monomial(t),i)
    return T(m, n*coefficient(t))
end

total_degree(a::Term) = total_degree(monomial(a))
lcm_degree(a::T, b::T) where T<:Term = lcm_degree(monomial(a), monomial(b))

lt(o::MonomialOrder, a::T,b::T) where T <: Term = lt(o, monomial(a), monomial(b))

end
