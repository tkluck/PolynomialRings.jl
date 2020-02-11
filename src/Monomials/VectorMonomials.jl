module VectorMonomials

import Base: exp, rand

import Random: AbstractRNG, SamplerType, randsubseq
import SparseArrays: SparseVector, sparsevec, sparse, spzeros
import SparseArrays: nonzeroinds

import ...AbstractMonomials: AbstractMonomial, MonomialIn, exponents
import ...MonomialOrderings: MonomialOrder
import ...NamingSchemes: NamingScheme, Numbered, InfiniteScheme
import PolynomialRings: exptype, max_variable_index, deg, generators

# -----------------------------------------------------------------------------
#
# VectorMonomial
#
# -----------------------------------------------------------------------------

"""
    VectorMonomial{V,I,Order} <: AbstractMonomial where V <: AbstractVector{I} where I <: Integer where Order

An implementation of AbstractMonomial that stores exponents as a vector
of integers. This can be a sparse or dense representation, depending on the
type specialization.

This representation is intended for the case when the number of variables
is unbounded. In particular, the indexing operation `m[i]` returns `0` when `i`
is out-of-bounds, instead of throwing an exception.
"""
struct VectorMonomial{V,I,Order} <: AbstractMonomial{Order}
    e   :: V
    deg :: I
    VectorMonomial{V,I,Order}(e, deg) where V<:AbstractVector{I} where {I<:Integer,Order} = new(e, deg)
end

SparseVectorMonomial{I, Order} = VectorMonomial{<:SparseVector, I, Order}

exp(::Type{M}, exps::V, deg=sum(exps)) where M <: VectorMonomial{V} where V = M(exps, deg)
exp(::Type{M}, exps::Tuple, deg=sum(exps)) where M <: VectorMonomial = exp(M, collect(exps), deg)
exp(::Type{M}, exps::AbstractVector, deg=sum(exps)) where M <: SparseVectorMonomial = M(sparse(exps), deg)

exptype(::Type{VectorMonomial{V,I,Order}}) where {V,I,Order} = I

# special case for sparsevectors; for some reason, SparseVector{Int,Int}() does not give
# an empty vector by default.
(::Type{V})() where V <: SparseVector{A,B} where {A,B} = sparsevec(B[],A[])

generators(::Type{VectorMonomial{V,I,Order}}) where {V,I,Order} = (
    # bla
    (x = spzeros(I, j); x[j] = one(I); VectorMonomial{V,I,Order}(x, one(I)))
    for j in 1:typemax(Int)
)

function max_variable_index(scheme::InfiniteScheme{Name},
                            m::VectorMonomial{V, I, <: MonomialOrder{Scheme}}) where
                            {V, I, Name, Scheme <: InfiniteScheme{Name}}
    return something(findlast(!iszero, m.e), 0)
end

max_variable_index(scheme::InfiniteScheme{Name}, m::VectorMonomial) where Name = 0

function exponents(m::VectorMonomial{<:SparseVector}, scheme::Numbered{Name, Inf}; max_variable_index=max_variable_index(scheme, m)) where Name
    return SparseVector(max_variable_index, m.e.nzind, m.e.nzval)
end

# -----------------------------------------------------------------------------
#
# VectorMonomial: overloads for speedup
#
# -----------------------------------------------------------------------------
deg(a::typeintersect(VectorMonomial, MonomialIn{Scheme}), ::Scheme) where Scheme <: NamingScheme = a.deg

#= TODO
function iterate(enz::EnumerateNZ{<:VectorMonomial{<:SparseVector}}, state=1)
    state > length(enz.a.e.nzind) && return nothing
    (enz.a.e.nzind[state], enz.a.e.nzval[state]), state + 1
end
=#

function ==(a::M, b::M) where M <: VectorMonomial{<:SparseVector}
    m = min(length(a.e), length(b.e))
    @views begin
        iszero(a.e[m+1:end]) && iszero(b.e[m+1:end]) && a.e[1:m] == b.e[1:m]
    end
end

function rand(rng::AbstractRNG, ::SamplerType{M}) where M <: VectorMonomial{<:SparseVector}
    maxexp = 2 ^ (leading_zeros(zero(exptype(M))) ÷ 2)
    numvars = rand(1:100)
    nzind = randsubseq(1:numvars, 1/sqrt(numvars))
    exps = rand(1:maxexp, length(nzind))
    return exp(M, SparseVector(numvars, nzind, exps))
end


end
