module Terms

import Base: *, ^, +, -, one, ==, iszero, zero, diff
import Base: hash, exp

import ..AbstractMonomials: AbstractMonomial
import ..MonomialOrderings: MonomialOrder, monomialorderkey
import ..NamingSchemes: NamingScheme, InfiniteScheme, Variable
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
    m :: M
    c :: C
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
# De-construct through (m, c) = Term(...)
#
# -----------------------------------------------------------------------------
Base.indexed_iterate(t::Term, i) = (monomial(t), nothing)
Base.indexed_iterate(t::Term, i, state) = (i == 2 || throw(BoundsError()); (coefficient(t), nothing))

# -----------------------------------------------------------------------------
#
# Term functions
#
# -----------------------------------------------------------------------------
*(a::Term{M, C1}, b::Term{M, C2}) where M <: AbstractMonomial where {C1,C2} = Term(a.m*b.m, a.c*b.c)
*(a::Term{M, C}, b::C) where M <: AbstractMonomial where C = Term(a.m, a.c*b)
*(a::C, b::Term{M, C}) where M <: AbstractMonomial where C = Term(b.m, a*b.c)
*(a::Term{M, C}, b::M) where M <: AbstractMonomial where C = Term(a.m*b, deepcopy(a.c))
*(a::M, b::Term{M, C}) where M <: AbstractMonomial where C = Term(a*b.m, deepcopy(b.c))
+(a::T)                where T <: Term = deepcopy(a)
-(a::T)                where T <: Term = T(a.m, -a.c)
==(a::T,b::T)          where T <: Term = a.m == b.m && a.c == b.c
^(a::T, n::Integer)    where T <: Term = T(a.m^n, a.c^n)

# resolve ambiguity if C is also a Number
*(a::Term{M, C}, b::C) where M <: AbstractMonomial where C<:Number = Term(a.m, a.c*b)
*(a::C, b::Term{M, C}) where M <: AbstractMonomial where C<:Number = Term(b.m, a*b.c)

one(::Type{Term{M,C}}) where {M, C} = Term{M,C}(one(M), one(C))
one(t::T) where T <: Term = one(typeof(t))

zero(::Type{Term{M,C}}) where {M, C} = error("Using zero(::Term) is indicative of faulty logic")
zero(t::T) where T <: Term = zero(typeof(t))

monomial(a::Term) = a.m
coefficient(a::Term) = a.c

monomialorderkey(order, a::Term) = (monomialorder(a) == order || error("Not implemented!"); monomial(a))

hash(a::Term, h::UInt) = hash(a.m, hash(a.c, h))

generators(::Type{Term{M,C}}) where {M, C} = lazymap(g -> Term{M,C}(g, one(C)), generators(M))

iszero(a::Term) = iszero(coefficient(a))

function max_variable_index(scheme::InfiniteScheme, a::Term)
    m = max_variable_index(scheme, coefficient(a))
    n = max_variable_index(scheme, monomial(a))
    return max(m, n)
end

function to_dense_monomials(scheme::InfiniteScheme, a::Term, max_variable_index)
    m = to_dense_monomials(scheme, monomial(a), max_variable_index)
    c = to_dense_monomials(scheme, coefficient(a), max_variable_index)
    return Term(m, c)
end

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

diff(a, x::Variable) = zero(a)

function diff(t::T, x::Variable) where T <: Term
    if isnothing(indexin(x, namingscheme(t)))
        return Term(monomial(t), diff(coefficient(t), x))
    else
        n, m = diff(monomial(t), x)
        return Term(m, n * coefficient(t))
    end
end

lcm_degree(a::T, b::T) where T<:Term = lcm_degree(monomial(a), monomial(b))

Base.Order.lt(o::MonomialOrder, a::T,b::T) where T <: Term = Base.Order.lt(o, monomial(a), monomial(b))

Base.deepcopy(t::Term) = Term(deepcopy(monomial(t)), deepcopy(coefficient(t)))

exp(T::Type{<:Term}, exps) = T(exp(monomialtype(T), exps), one(basering(T)))

end
