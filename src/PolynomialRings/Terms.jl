module Terms

import Base: *, ^, +, -, one, ==, iszero, diff
import Base: hash

import ..MonomialOrderings: MonomialOrder
import ..Monomials: AbstractMonomial
import ..Monomials: total_degree
import ..NamingSchemes: NamingScheme
import ..Util: lazymap
import PolynomialRings: generators, to_dense_monomials, max_variable_index, basering
import PolynomialRings: maybe_div, divides, lcm_multipliers, monomialtype, exptype, lcm_degree, namingscheme, monomialorder

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
# Type information
#
# -----------------------------------------------------------------------------
monomialtype(::Type{Term{M,C}}) where {M,C} = M
basering(::Type{Term{M,C}}) where {M,C} = C
exptype(::Type{T}) where T<:Term = exptype(monomialtype(T))
namingscheme(::Type{T}) where T<:Term = namingscheme(monomialtype(T))
monomialorder(::Type{T}) where T <: Term = monomialorder(monomialtype(T))
exptype(::Type, scheme::NamingScheme) = Union{}
function exptype(::Type{T}, scheme::NamingScheme) where T <: Term
    return promote_type(exptype(basering(T), scheme), exptype(monomialtype(T), scheme))
end

# -----------------------------------------------------------------------------
#
# Term functions
#
# -----------------------------------------------------------------------------
*(a::Term{M, C1}, b::Term{M, C2}) where M <: AbstractMonomial where {C1,C2} = Term(a.m*b.m, a.c*b.c)
*(a::Term{M, C}, b::C) where M <: AbstractMonomial where C = Term(a.m, a.c*b)
*(a::C, b::Term{M, C}) where M <: AbstractMonomial where C = Term(b.m, a*b.c)
+(a::T)                where T <: Term = deepcopy(a)
-(a::T)                where T <: Term = T(a.m, -a.c)
==(a::T,b::T)          where T <: Term = a.m == b.m && a.c == b.c
^(a::T, n::Integer)    where T <: Term = T(a.m^n, a.c^n)

# resolve ambiguity if C is also a Number
*(a::Term{M, C}, b::C) where M <: AbstractMonomial where C<:Number = Term(a.m, a.c*b)
*(a::C, b::Term{M, C}) where M <: AbstractMonomial where C<:Number = Term(b.m, a*b.c)

one(::Type{Term{M,C}}) where {M, C} = Term{M,C}(one(M), one(C))
one(t::T) where T <: Term = one(typeof(t))

monomial(a::Term) = a.m
coefficient(a::Term) = a.c

hash(a::Term, h::UInt) = hash(a.m, hash(a.c, h))

generators(::Type{Term{M,C}}) where {M, C} = lazymap(g -> Term{M,C}(g, one(C)), generators(M))

iszero(a::Term) = iszero(coefficient(a))

to_dense_monomials(n, a::Term) = Term( to_dense_monomials(n, monomial(a)), deepcopy(coefficient(a)) )
max_variable_index(a::Term) = max_variable_index(monomial(a))

function maybe_div(a::T, b::T) where T<:Term
    q = maybe_div(monomial(a), monomial(b))
    if q === nothing || iszero(coefficient(b))
        return nothing
    else
        return T(q, coefficient(a) // coefficient(b))
    end
end

divides(a::T, b::T) where T <: Term = divides(monomial(a), monomial(b))

function lcm_multipliers(a::T, b::T)::Tuple{T,T} where T<:Term
    m_a,m_b = lcm_multipliers(monomial(a), monomial(b))
    c_a,c_b = lcm_multipliers(coefficient(a), coefficient(b))
    return T(m_a, c_a), T(m_b, c_b)
end

(t::Term)(args...) = coefficient(t) * monomial(t)(args...)

function diff(t::T, i::Integer) where T <: Term
    n,m = diff(monomial(t),i)
    return T(m, n*coefficient(t))
end

total_degree(a::Term) = total_degree(monomial(a))
lcm_degree(a::T, b::T) where T<:Term = lcm_degree(monomial(a), monomial(b))

Base.Order.lt(o::MonomialOrder, a::T,b::T) where T <: Term = Base.Order.lt(o, monomial(a), monomial(b))

end
