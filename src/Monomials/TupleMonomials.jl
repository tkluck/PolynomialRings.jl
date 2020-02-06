module TupleMonomials

import Base: exp

import ...AbstractMonomials: AbstractMonomial, _construct, num_variables, nzindices, maybe_div
import PolynomialRings: exptype

# -----------------------------------------------------------------------------
#
# TupleMonomial
#
# -----------------------------------------------------------------------------

"""
    TupleMonomial{N, I, Order} <: AbstractMonomial where I <: Integer where Order

An implementation of AbstractMonomial that stores exponents as a tuple
of integers. This is a dense representation.
"""
struct TupleMonomial{N, I <: Integer, Order} <: AbstractMonomial{Order}
    e   :: NTuple{N, I}
    deg :: I
end


num_variables(::Type{TupleMonomial{N,I,Order}}) where {N,I,Order} = N
exptype(::Type{TupleMonomial{N,I,Order}}) where I <: Integer where {N,Order} = I
expstype(::Type{TupleMonomial{N,I,Order}}) where I <: Integer where {N,Order} = NTuple{N,I}

exp(::Type{M}, exps::NTuple, deg=sum(exps)) where M <: TupleMonomial = M(exps, deg)
exp(::Type{M}, exps, deg=sum(exps)) where M <: TupleMonomial = M(ntuple(i -> exps[i], num_variables(M)), deg)

@inline exponent(m::TupleMonomial, i::Integer) = m.e[i]

generators(::Type{TupleMonomial{N, I, Order}}) where {N, I, Order} = [
    _construct(TupleMonomial{N, I, Order}, i->i==j ? one(I) : zero(I), 1:N)
    for j in 1:N
]

nzindices(a::TupleMonomial{N,I,Order}) where {N,I,Order} = 1:N

# -----------------------------------------------------------------------------
#
# TupleMonomial: overloads for speedup
#
# -----------------------------------------------------------------------------
total_degree(a::TupleMonomial) = a.deg

==(a::M, b::M) where M <: TupleMonomial = a.e == b.e


end
