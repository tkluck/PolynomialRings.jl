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
import Base: hash
import Base: promote_rule
import PolynomialRings: generators, to_dense_monomials, max_variable_index
import PolynomialRings: maybe_div, lcm_multipliers, exptype, lcm_degree, namestype

# -----------------------------------------------------------------------------
#
# Utility: iterate over the union of two index sets
#
# -----------------------------------------------------------------------------
import Base: start, done, next, last, findlast, length
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

length(i::IndexUnion) = (len=0; for _ in i; len += 1; end; len)

function index_union(a::AbstractMonomial, b::AbstractMonomial)
    l = nzindices(a)
    r = nzindices(b)
    IndexUnion{typeof(l),typeof(r),<}(l,r)
end

# part of julia 0.7; doing a poor-man's version here as it is a significant
# performance win (monomial comparisons being part of many inner loops)
struct ReversedVector{A<:AbstractVector}
    a::A
end
start(r::ReversedVector) = length(r.a)
done(r::ReversedVector, state) = state == 0
next(r::ReversedVector, state) = r.a[state], state-1
reverseview(a) = reverse(a)
reverseview(a::AbstractVector) = ReversedVector(a)
function rev_index_union(a::AbstractMonomial, b::AbstractMonomial)
    l = reverseview(nzindices(a))
    r = reverseview(nzindices(b))
    IndexUnion{typeof(l),typeof(r),>}(l,r)
end

struct EnumerateNZ{M<:AbstractMonomial}
    a::M
end
start(enz::EnumerateNZ) = start(nzindices(enz.a))
done(enz::EnumerateNZ, state) = done(nzindices(enz.a), state)
next(enz::EnumerateNZ, state) = ((i,next_state) = next(nzindices(enz.a), state); ((i,enz.a[i]), next_state))
length(enz::EnumerateNZ) = length(nzindices(enz.a))

# -----------------------------------------------------------------------------
#
# Abstract fallbacks
#
# -----------------------------------------------------------------------------
@inline _construct(::Type{M}, f, nzindices, deg) where M <: AbstractMonomial = _construct(M, f, nzindices)
@inline _construct(::Type{M}, f, nzindices) where M <: AbstractMonomial = _construct(M, f, nzindices, exptype(M)(mapreduce(f, +, zero(exptype(M)), nzindices)))

one(::Type{M}) where M <: AbstractMonomial = _construct(M, i->0, 1:0)
one(::M) where M <: AbstractMonomial = one(M)

*(a::AbstractMonomial{Nm}, b::AbstractMonomial{Nm}) where Nm = _construct(promote_type(typeof(a), typeof(b)),i -> a[i] + b[i], index_union(a,b), total_degree(a) + total_degree(b))
^(a::M, n::Integer) where M <: AbstractMonomial = _construct(M,i -> a[i]*n, nzindices(a), total_degree(a)*n)

total_degree(a::A) where A <: AbstractMonomial = (ix = nzindices(a); length(ix)==0 ? zero(exptype(a)) : sum( a[i] for i in nzindices(a) ) )

lcm(a::AbstractMonomial{Nm}, b::AbstractMonomial{Nm}) where Nm = _construct(promote_type(typeof(a), typeof(b)),i -> max(a[i], b[i]), index_union(a,b))
gcd(a::AbstractMonomial{Nm}, b::AbstractMonomial{Nm}) where Nm = _construct(promote_type(typeof(a), typeof(b)),i -> min(a[i], b[i]), index_union(a,b))

enumeratenz(a::M) where M <: AbstractMonomial = EnumerateNZ(a)

exptype(a::AbstractMonomial) = exptype(typeof(a))

function hash(a::AbstractMonomial, h::UInt)
    h = hash(1)
    for (i,e) in enumeratenz(a)
        if !iszero(e)
            h = hash((i,e), h)
        end
    end
    h
end

==(a::AbstractMonomial{Names}, b::AbstractMonomial{Names}) where Names = all(i->a[i]==b[i], index_union(a,b))

function maybe_div(a::AbstractMonomial{Nm}, b::AbstractMonomial{Nm}) where Nm
    M = promote_type(typeof(a), typeof(b))
    if all(i->a[i]>=b[i], index_union(a,b))
        return _construct(M,i -> a[i] - b[i], index_union(a,b))
    else
        return null
    end
end

function lcm_multipliers(a::AbstractMonomial{Nm}, b::AbstractMonomial{Nm}) where Nm
    M = promote_type(typeof(a), typeof(b))
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

function lcm_degree(a::AbstractMonomial{Nm}, b::AbstractMonomial{Nm}) where Nm
    # avoid summing empty iterator
    iszero(total_degree(a)) && iszero(total_degree(b)) && return zero(exptype(M))
    return sum(max(a[i],b[i]) for i in index_union(a,b))
end

function any_divisor(f::Function, a::M) where M <: AbstractMonomial
    if length(nzindices(a)) == 0
        return
    end

    e = zeros(exptype(M), last(nzindices(a)))
    nonzeros = [j for (j,_) in enumeratenz(a)]

    N = VectorMonomial{typeof(e),exptype(M), namestype(M)}

    while true
        m = N(e, sum(e))
        if f(m)
            return true
        end
        carry = 1
        for j = 1:length(nonzeros)
            if (e[nonzeros[j]] += carry) > a[nonzeros[j]]
                e[nonzeros[j]] = 0
                carry = 1
            else
                carry = 0
            end
        end
        if carry == 1
            return false
        end
    end
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
    VectorMonomial{V,I,Nm} <: AbstractMonomial where V <: AbstractVector{I} where I <: Integer where Nm

An implementation of AbstractMonomial that stores exponents as a vector
of integers. This can be a sparse or dense representation, depending on the
type specialization.

This representation is intended for the case when the number of variables
is unbounded. In particular, the indexing operation `m[i]` returns `0` when `i`
is out-of-bounds, instead of throwing an exception.
"""
struct VectorMonomial{V,I,Nm} <: AbstractMonomial{Nm}
    e::V
    deg::I
    VectorMonomial{V,I,Nm}(e, deg) where V<:AbstractVector{I} where {I<:Integer,Nm} = new(e, deg)
end

function _construct(::Type{M}, f::Function, nonzero_indices, deg) where M <: VectorMonomial{V,I,Nm} where V <: AbstractVector{I} where I <: Integer where Nm
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

function _construct(::Type{M}, f::Function, nonzero_indices, deg) where M <: VectorMonomial{V,I,Nm} where V <: SparseVector{I,J} where I <: Integer where J <: Integer where Nm
    indices = collect(J, nonzero_indices)
    len = length(indices) > 0 ? last(indices) : 0
    e = V(len, indices, map(i->I(f(i)), indices))
    return M(e, deg)
end

namestype(::Type{VectorMonomial{V,I,Nm}}) where {V,I,Nm} = Nm
exptype(::Type{VectorMonomial{V,I,Nm}}) where {V,I,Nm} = I
expstype(::Type{VectorMonomial{V,I,Nm}}) where {V,I,Nm} = V
@inline getindex(m::VectorMonomial, i::Integer) = i <= length(m.e) ? m.e[i] : zero(exptype(m))

# special case for sparsevectors; for some reason, SparseVector{Int,Int}() does not give
# an empty vector by default.
(::Type{V})() where V <: SparseVector{A,B} where {A,B} = sparsevec(B[],A[])

generators(::Type{VectorMonomial{V,I,Nm}}) where {V,I,Nm} = Channel(ctype=VectorMonomial{V,I,Nm}) do ch
    for j in 1:typemax(Int)
        x = spzeros(I, j)
        x[j] = one(I)
        push!(ch, VectorMonomial{V,I,Nm}(x))
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
total_degree(a::VectorMonomial) = a.deg

import Base.SparseArrays: nonzeroinds
nzindices(a::VectorMonomial{V,I,Nm}) where {V <: SparseVector,I,Nm} = nonzeroinds(a.e)

# -----------------------------------------------------------------------------
#
# Conversion from Vector to tuple (sparse to dense)
#
# -----------------------------------------------------------------------------

max_variable_index(m::TupleMonomial{N}) where N = N
max_variable_index(m::VectorMonomial{V,I,Nm}) where {V,I,Nm} = length(m.e)

import PolynomialRings.VariableNames: Named, Numbered, flatvariablesymbols
_densenames(n::Integer, ::Type{Numbered{Name}}) where Name = (g = flatvariablesymbols(Numbered{Name}); Named{ tuple([take!(g) for _ = 1:n]...) })
to_dense_monomials(n::Integer, m::AbstractMonomial) = _construct(TupleMonomial{n,exptype(m),_densenames(n, namestype(m))}, i->m[i], 1:n)

promote_rule(::Type{<:TupleMonomial{N,I,Nm}}, ::Type{<:VectorMonomial{V,J,Nm}}) where {N,V,I,J,Nm} = TupleMonomial{N,promote_type(I,J),Nm}

# -----------------------------------------------------------------------------
#
# User-facing interface
#
# -----------------------------------------------------------------------------
(m::TupleMonomial)(args...)  = prod(args[i]^e for (i,e) in enumeratenz(m))
(m::VectorMonomial)(args...) = prod(args[i]^e for (i,e) in enumeratenz(m))


end
