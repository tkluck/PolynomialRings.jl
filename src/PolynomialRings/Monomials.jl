module Monomials

using Nulls

"""
    AbstractMonomial{Nm}

The abstract base type for multi-variate monomials.

Specifying a monomial is equivalent to specifying the exponents for all variables.
The concrete type decides whether this happens as a tuple or as a (sparse or dense)
array.

The variables may or may not have names at this abstraction level; they can
always be identified by a number (e.g. the index in the array/tuple) but the type
may choose to support having a symbolic name for each as well. In the former case,
namestype(::Type{M}) returns Numbered; otherwise, it returns Named{Names}. This
is also the value of Nm.

Each concrete implementation should implement:
    m[i]
    nzindices(m)
    _construct(M, i -> exponent, nonzero_indices, [total_degree])
    exptype(M)
    namestype(M)

and optionally:
    *(a,b)
    total_degree(a)
    lcm(a,b)
    gcd(a,b)
    enumeratenz(m)

These latter function have fallbacks in terms of the functions above.
"""
abstract type AbstractMonomial{Nm} end

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: getindex, gcd, lcm, one, *, ^, ==, diff
import PolynomialRings: generators, to_dense_monomials, max_variable_index
import PolynomialRings: maybe_div, lcm_multipliers, exptype, lcm_degree, namestype

# -----------------------------------------------------------------------------
#
# Utility: iterate over the union of two index sets
#
# -----------------------------------------------------------------------------
import Base: start, done, next, last, findlast
struct IndexUnion{I,J,lt}
    left::I
    right::J
end

start(i::IndexUnion) = (start(i.left), start(i.right))
function next(i::IndexUnion{I,J,lt}, state) where {I,J,lt}
    lstate, rstate = state
    ldone = done(i.left, lstate)
    rdone = done(i.right, rstate)

    if !ldone
        (litem, lnextstate) = next(i.left, lstate)
    end
    if !rdone
        (ritem, rnextstate) = next(i.right, rstate)
    end
    if rdone || (!ldone && lt(litem, ritem))
        return (litem, (lnextstate, rstate))
    elseif ldone || (!rdone && lt(ritem, litem))
        return (ritem, (lstate, rnextstate))
    elseif litem == ritem
        return (litem, (lnextstate, rnextstate))
    else
        @assert(false) # unreachable?
    end
end
done(i::IndexUnion, state) = done(i.left, state[1]) && done(i.right, state[2])

findlast(i::IndexUnion) = max(findlast(i.left), findlast(i.right))

function last(i::IndexUnion)
    l = findlast(i.left)
    r = findlast(i.right)
    if l == 0
        return i.right[r]
    elseif r == 0
        return i.left[l]
    else
        return max(i.left[l], i.right[r])
    end
end

function index_union(a::AbstractMonomial, b::AbstractMonomial)
    l = nzindices(a)
    r = nzindices(b)
    IndexUnion{typeof(l),typeof(r),<}(l,r)
end

function rev_index_union(a::AbstractMonomial, b::AbstractMonomial)
    l = reverse(nzindices(a))
    r = reverse(nzindices(b))
    IndexUnion{typeof(l),typeof(r),>}(l,r)
end

# -----------------------------------------------------------------------------
#
# Abstract fallbacks
#
# -----------------------------------------------------------------------------
@inline _construct(::Type{M}, f, nzindices, deg) where M <: AbstractMonomial = _construct(M, f, nzindices)
@inline _construct(::Type{M}, f, nzindices) where M <: AbstractMonomial = _construct(M, f, nzindices, mapreduce(f, +, zero(exptype(M)), nzindices))

one(::Type{M}) where M <: AbstractMonomial = _construct(M, i->0, 1:0)
one(::M) where M <: AbstractMonomial = one(M)

*(a::M, b::M) where M <: AbstractMonomial = _construct(M,i -> a[i] + b[i], index_union(a,b), total_degree(a) + total_degree(b))
^(a::M, n::Integer) where M <: AbstractMonomial = _construct(M,i -> a[i]*n, nzindices(a), total_degree(a)*n)

total_degree(a::A) where A <: AbstractMonomial = (ix = nzindices(a); length(ix)==0 ? zero(exptype(a)) : sum( a[i] for i in nzindices(a) ) )

lcm(a::M, b::M) where M <: AbstractMonomial = _construct(M,i -> max(a[i], b[i]), index_union(a,b))
gcd(a::M, b::M) where M <: AbstractMonomial = _construct(M,i -> min(a[i], b[i]), index_union(a,b))
enumeratenz(a::M) where M <: AbstractMonomial = Channel(ctype=Tuple{Int,exptype(M)}) do ch
    for i in nzindices(a)
        push!(ch, (i, a[i]))
    end
end

exptype(a::AbstractMonomial) = exptype(typeof(a))

function maybe_div(a::M, b::M) where M <: AbstractMonomial
    if all(a[i] >= b[i] for i in index_union(a,b))
        return _construct(M,i -> a[i] - b[i], index_union(a,b))
    else
        return null
    end
end

function lcm_multipliers(a::M, b::M)::Tuple{M,M} where M <: AbstractMonomial
    return (
        _construct(M, i -> max(a[i], b[i]) - a[i], index_union(a,b)),
        _construct(M, i -> max(a[i], b[i]) - b[i], index_union(a,b)),
    )
end

function diff(a::M, i::Integer) where M <: AbstractMonomial
    n = a[i]
    if iszero(n)
        return (n, one(M))
    else
        return (n, _construct(M, j -> (j==i ? a[j]-one(exptype(M)) : a[j]), nzindices(a)))
    end
end

function lcm_degree(a::M, b::M) where M <: AbstractMonomial
    return sum(max(a[i],b[i]) for i in index_union(a,b))
end

# -----------------------------------------------------------------------------
#
# TupleMonomial
#
# -----------------------------------------------------------------------------

"""
    TupleMonomial{N, I, Nm} <: AbstractMonomial where I <: Integer where Nm

An implementation of AbstractMonomial that stores exponents as a tuple
of integers. This is a dense representation.
"""
struct TupleMonomial{N, I, Nm} <: AbstractMonomial{Nm}
    e::NTuple{N, I}
    deg::I
    TupleMonomial{N,I,Nm}(e,deg) where I <: Integer where {N,Nm} = new(e,deg)
end

@generated function _construct(::Type{typ}, f::Function, nonzero_indices, deg) where typ <: TupleMonomial{N,I,Nm} where {N,I,Nm}
    result = :( tuple() )
    for i in 1:N
        push!(result.args, :( I(f($i)) ))
    end
    return quote
        t = $result
        typ(t, deg)
    end
end

num_variables(::Type{TupleMonomial{N,I,Nm}}) where {N,I,Nm} = N
namestype(::Type{TupleMonomial{N,I,Nm}}) where {N,I,Nm} = Nm
exptype(::Type{TupleMonomial{N,I,Nm}}) where I <: Integer where {N,Nm} = I
expstype(::Type{TupleMonomial{N,I,Nm}}) where I <: Integer where {N,Nm} = NTuple{N,I}
@inline getindex(m::TupleMonomial, i::Integer) = m.e[i]

generators(::Type{TupleMonomial{N, I, Nm}}) where {N, I, Nm} = [
    _construct(TupleMonomial{N, I, Nm}, i->i==j ? one(I) : zero(I), 1:N)
    for j in 1:N
]

nzindices(a::TupleMonomial{N,I,Nm}) where {N,I,Nm} = 1:N
@inline index_union(::T, ::T) where T<:TupleMonomial{N,I,Nm} where {N,I,Nm} = 1:N
@inline rev_index_union(::T, ::T) where T<:TupleMonomial{N,I,Nm} where {N,I,Nm} = N:-1:1

# -----------------------------------------------------------------------------
#
# VectorMonomial
#
# -----------------------------------------------------------------------------

"""
    VectorMonomial{V,Nm} <: AbstractMonomial where V <: AbstractVector{I} where I <: Integer where Nm

An implementation of AbstractMonomial that stores exponents as a vector
of integers. This can be a sparse or dense representation, depending on the
type specialization.

This representation is intended for the case when the number of variables
is unbounded. In particular, the indexing operation `m[i]` returns `0` when `i`
is out-of-bounds, instead of throwing an exception.
"""
struct VectorMonomial{V,Nm} <: AbstractMonomial{Nm}
    e::V
    VectorMonomial{V,Nm}(e) where V<: AbstractVector{<:Integer} where Nm = new(e)
end

function _construct(::Type{M}, f::Function, nonzero_indices) where M <: VectorMonomial{V,Nm} where V <: AbstractVector{I} where I <: Integer where Nm
    if findlast(nonzero_indices) == 0
        return M(V())
    else
        e = zeros(I, last(nonzero_indices))
        for i in nonzero_indices
            e[i] = f(i)
        end
        return M(e)
    end
end

namestype(::Type{VectorMonomial{V,Nm}}) where {V,Nm} = Nm
exptype(::Type{VectorMonomial{V,Nm}}) where {V,Nm} = eltype(V)
expstype(::Type{VectorMonomial{V,Nm}}) where {V,Nm} = V
@inline getindex(m::VectorMonomial, i::Integer) = i <= length(m.e) ? m.e[i] : zero(exptype(m))

# special case for sparsevectors; for some reason, SparseVector{Int,Int}() does not give
# an empty vector by default.
(::Type{V})() where V <: SparseVector{A,B} where {A,B} = sparsevec(B[],A[])

#
# workaround: for some reason, comparison does't fall through the struct
# for VectorMonomial (???)
==(a::M,b::M) where M<:VectorMonomial = a.e == b.e

generators(::Type{VectorMonomial{V,Nm}}) where {V,Nm} = Channel(ctype=VectorMonomial{V}) do ch
    for j in 1:typemax(Int)
        x = spzeros(eltype(V), j)
        x[j] = one(eltype(V))
        push!(ch, VectorMonomial{V,Nm}(x))
    end
    throw(AssertionError("typemax exhausted"))
end

nzindices(a::VectorMonomial) = 1:length(a.e)

# -----------------------------------------------------------------------------
#
# TupleMonomial: overloads for speedup
#
# -----------------------------------------------------------------------------
total_degree(a::TupleMonomial) = a.deg

# -----------------------------------------------------------------------------
#
# VectorMonomial: overloads for speedup
#
# -----------------------------------------------------------------------------
import Base.SparseArrays: nonzeroinds
nzindices(a::VectorMonomial{V,Nm}) where {V <: SparseVector,Nm} = nonzeroinds(a.e)

# -----------------------------------------------------------------------------
#
# Conversion from Vector to tuple (sparse to dense)
#
# -----------------------------------------------------------------------------

max_variable_index(m::TupleMonomial{N}) where N = N
max_variable_index(m::VectorMonomial{V,Nm}) where {V,Nm} = length(m.e)

import PolynomialRings: variablesymbols
import PolynomialRings.VariableNames: Named, Numbered
_densenames(n::Integer, ::Type{Numbered{Name}}) where Name = (g = variablesymbols(Numbered{Name}); Named{ tuple([take!(g) for _ = 1:n]...) })
to_dense_monomials(n::Integer, m::AbstractMonomial) = _construct(TupleMonomial{n,exptype(m),_densenames(n, namestype(m))}, i->m[i], 1:n)

# -----------------------------------------------------------------------------
#
# User-facing interface
#
# -----------------------------------------------------------------------------
(m::TupleMonomial)(args...)  = prod(args[i]^e for (i,e) in enumeratenz(m))
(m::VectorMonomial)(args...) = prod(args[i]^e for (i,e) in enumeratenz(m))


end
