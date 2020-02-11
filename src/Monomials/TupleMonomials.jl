module TupleMonomials

import Base: exp, rand

import Random: AbstractRNG, SamplerType

import ...AbstractMonomials: AbstractMonomial, MonomialIn, num_variables, maybe_div
import ...MonomialOrderings: MonomialOrder
import ...NamingSchemes: NamingScheme, InfiniteScheme
import PolynomialRings: exptype, deg, max_variable_index

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

exp(::Type{M}, exps::NTuple, deg=sum(exps)) where M <: TupleMonomial = M(exps, deg)
exp(::Type{M}, exps, deg=sum(exps)) where M <: TupleMonomial = M(ntuple(i -> get(exps, i, 0), num_variables(M)), deg)

function max_variable_index(scheme::InfiniteScheme{Name},
                            m::TupleMonomial{N, I, <: MonomialOrder{Scheme}}) where
                            {N, I, Name, Scheme <: InfiniteScheme{Name}}
    return N
end


max_variable_index(scheme::InfiniteScheme{Name}, m::TupleMonomial)  where Name = 0

# -----------------------------------------------------------------------------
#
# TupleMonomial: overloads for speedup
#
# -----------------------------------------------------------------------------
deg(a::typeintersect(TupleMonomial, MonomialIn{Scheme}), ::Scheme) where Scheme <: NamingScheme = a.deg

==(a::M, b::M) where M <: TupleMonomial = a.e == b.e

function rand(rng::AbstractRNG, ::SamplerType{M}) where M <: TupleMonomial
    maxexp = 2 ^ (leading_zeros(zero(exptype(M))) ÷ 2)
    exps = ntuple(i -> rand(rng, 1:maxexp), num_variables(M))
    return exp(M, exps)
end


end
