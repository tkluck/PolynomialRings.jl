module VectorMonomials

import Base: exp, rand

import Random: AbstractRNG, SamplerType, randsubseq
import SparseArrays: SparseVector, sparsevec, sparse
import SparseArrays: nonzeroinds

import ...AbstractMonomials: AbstractMonomial, MonomialIn, nzindices, exponents
import ...NamingSchemes: Numbered
import PolynomialRings: exptype, max_variable_index

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

function _construct(::Type{M}, f::Function, nonzero_indices, deg) where M <: VectorMonomial{V,I,Order} where V <: AbstractVector{I} where I <: Integer where Order
    if findlast(nonzero_indices) == 0
        return M(V(), deg)
    else
        e = zeros(I, last(nonzero_indices))
        for i in nonzero_indices
            e[i] = f(i)
        end
        return M(e, deg)
    end
end

function _construct(::Type{M}, f::Function, nonzero_indices, deg) where M <: VectorMonomial{V,I,Order} where V <: SparseVector{I,J} where I <: Integer where J <: Integer where Order
    indices = collect(J, nonzero_indices)
    len = !isempty(indices) ? last(indices) : 0
    e = V(len, indices, map(i->I(f(i)), indices))
    return M(e, deg)
end

exptype(::Type{VectorMonomial{V,I,Order}}) where {V,I,Order} = I
expstype(::Type{VectorMonomial{V,I,Order}}) where {V,I,Order} = V
@inline exponent(m::VectorMonomial, i::Integer) = i <= length(m.e) ? m.e[i] : zero(exptype(m))

# special case for sparsevectors; for some reason, SparseVector{Int,Int}() does not give
# an empty vector by default.
(::Type{V})() where V <: SparseVector{A,B} where {A,B} = sparsevec(B[],A[])

generators(::Type{VectorMonomial{V,I,Order}}) where {V,I,Order} = Channel(ctype=VectorMonomial{V,I,Order}) do ch
    for j in 1:typemax(Int)
        x = spzeros(I, j)
        x[j] = one(I)
        push!(ch, VectorMonomial{V,I,Order}(x))
    end
    throw(AssertionError("typemax exhausted"))
end

nzindices(a::VectorMonomial) = 1:length(a.e)

function max_variable_index(scheme::Scheme, m::typeintersect(VectorMonomial, MonomialIn{Scheme})) where Scheme <: Numbered{Name, Inf} where Name
    return something(findlast(!iszero, m.e), 0)
end

function exponents(m::VectorMonomial{<:SparseVector}, scheme::Numbered{Name, Inf}; max_variable_index=max_variable_index(scheme, m)) where Name
    return SparseVector(max_variable_index, m.e.nzind, m.e.nzval)
end

# -----------------------------------------------------------------------------
#
# VectorMonomial: overloads for speedup
#
# -----------------------------------------------------------------------------
total_degree(a::VectorMonomial) = a.deg

nzindices(a::VectorMonomial{V,I,Order}) where {V <: SparseVector,I,Order} = nonzeroinds(a.e)

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
