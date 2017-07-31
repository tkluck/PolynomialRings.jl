module Monomials

using Nulls

"""
    AbstractMonomial{Order}

The abstract base type for multi-variate monomials.

Specifying a monomial is equivalent to specifying the exponents for all variables.
The concrete type decides whether this happens as a tuple or as a (sparse or dense)
array.

The variables do not have names at this abstraction level; they are identified
by a number (e.g. the index in the array/tuple).

Each concrete implementation should implement:
    m[i]
    num_variables(m)
    _construct(M, i -> exponent, num_variables)
    exptype(M)

and optionally:
    *(a,b)
    total_degree(a)
    lcm(a,b)
    gcd(a,b)
    enumerate(m)

These latter function have fallbacks in terms of the functions above.
"""
abstract type AbstractMonomial end

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: getindex, gcd, lcm, one, *, ^, enumerate, ==, diff
import PolynomialRings: generators, to_dense_monomials, max_variable_index, deg
import PolynomialRings: maybe_div, lcm_multipliers, exptype, lcm_degree


# -----------------------------------------------------------------------------
#
# Abstract fallbacks
#
# -----------------------------------------------------------------------------

*(a::M, b::M) where M <: AbstractMonomial = _construct(M,i -> a[i] + b[i], max(num_variables(a), num_variables(b)))
^(a::M, n::Integer) where M <: AbstractMonomial = _construct(M,i -> a[i]*n, num_variables(a))

total_degree(a::A) where A <: AbstractMonomial = sum( a[i] for i in 1:num_variables(a) )

lcm(a::M, b::M) where M <: AbstractMonomial = _construct(M,i -> max(a[i], b[i]), max(num_variables(a), num_variables(b)))
gcd(a::M, b::M) where M <: AbstractMonomial = _construct(M,i -> min(a[i], b[i]), max(num_variables(a), num_variables(b)))
enumerate(a::M) where M <: AbstractMonomial = Channel(ctype=Tuple{Int,exptype(M)}) do ch
    for i = 1:num_variables(a)
        push!(ch, (i, a[i]))
    end
end

exptype(a::AbstractMonomial) = exptype(typeof(a))
num_variables(a::A) where A <: AbstractMonomial = num_variables(A)

function maybe_div(a::M, b::M) where M <: AbstractMonomial
    if all(a[i] >= b[i] for i=1:max(num_variables(a), num_variables(b)))
        return _construct(M,i -> a[i] - b[i], max(num_variables(a), num_variables(b)))
    else
        return null
    end
end

function lcm_multipliers(a::M, b::M)::Tuple{M,M} where M <: AbstractMonomial
    N = max(num_variables(a), num_variables(b))
    return (
        _construct(M, i -> max(a[i], b[i]) - a[i], N),
        _construct(M, i -> max(a[i], b[i]) - b[i], N),
    )
end

function diff(a::M, i::Integer) where M <: AbstractMonomial
    n = a[i]
    if iszero(n)
        return (n, one(M))
    else
        return (n, _construct(M, j -> (j==i ? a[j]-one(exptype(M)) : a[j]), num_variables(a)))
    end
end

function lcm_degree(a::M, b::M) where M <: AbstractMonomial
    N = max(num_variables(a), num_variables(b))
    return sum(max(a[i],b[i]) for i=1:N)
end

# -----------------------------------------------------------------------------
#
# TupleMonomial
#
# -----------------------------------------------------------------------------

"""
    TupleMonomial{N, I} <: AbstractMonomial where I <: Integer

An implementation of AbstractMonomial that stores exponents as a tuple
of integers. This is a dense representation.
"""
struct TupleMonomial{N, I} <: AbstractMonomial
    e::NTuple{N, I}
    deg::I
    TupleMonomial{N,I}(e,deg) where I <: Integer where N = new(e,deg)
end

@generated function _construct(::Type{TupleMonomial{N,I}}, f::Function, num_variables::Type{Val{N}}) where {N,I}
    result = :( tuple() )
    for i in 1:N
        push!(result.args, :( I(f($i)) ))
    end
    return quote
        t = $result
        TupleMonomial{N, eltype(t)}(t, sum(t))
    end
end

_construct(::Type{T}, f::Function, num_variables::Int) where T <: TupleMonomial= _construct(T, f, Val{num_variables})

TupleMonomial(e::NTuple{N,I}) where I <: Integer where N = TupleMonomial{N,I}(e,sum(e))

num_variables(::Type{TupleMonomial{N,I}}) where {N,I} = N
exptype(::Type{TupleMonomial{N,I}}) where I <: Integer where N = I
@inline getindex(m::TupleMonomial, i::Integer) = m.e[i]

one(::Type{T}) where T<:TupleMonomial = _construct(T, i->zero(exptype(T)), Val{num_variables(T)})

generators(::Type{TupleMonomial{N, I}}) where {N, I} = [
    _construct(TupleMonomial{N, I}, i->i==j?one(I):zero(I), Val{N})
    for j in 1:N
]

# -----------------------------------------------------------------------------
#
# VectorMonomial
#
# -----------------------------------------------------------------------------

"""
    VectorMonomial{V} <: AbstractMonomial where V <: AbstractVector{I} where I <: Integer

An implementation of AbstractMonomial that stores exponents as a vector
of integers. This can be a sparse or dense representation, depending on the
type specialization.

This representation is intended for the case when the number of variables
is unbounded. In particular, the indexing operation `m[i]` returns `0` when `i`
is out-of-bounds, instead of throwing an exception.
"""
struct VectorMonomial{V} <: AbstractMonomial
    e::V
    VectorMonomial{V}(e) where V <: AbstractVector{<:Integer} = new(e)
end

function _construct(::Type{M}, f::Function, num_variables::Int) where M <: VectorMonomial{V} where V <: AbstractVector{I} where I <: Integer
    e = [f(i) for i in 1:num_variables]
    M(e)
end

num_variables(m::VectorMonomial) = length(m.e)
exptype(::Type{VectorMonomial{V}}) where V = eltype(V)
@inline getindex(m::VectorMonomial, i::Integer) = i <= length(m.e) ? m.e[i] : zero(exptype(m))

# the empty vector corresponds to all exponents equal to zero
one(::Type{VectorMonomial{V}}) where V = VectorMonomial{V}( V() )
# special case for sparsevectors; for some reason, SparseVector{Int,Int}() does not give
# an empty vector.
one(::Type{VectorMonomial{V}}) where V <: SparseVector{A,B} where {A,B} = VectorMonomial{V}( sparsevec(B[],A[]) )

#
# workaround: for some reason, comparison does't fall through the struct
# for VectorMonomial (???)
==(a::M,b::M) where M<:VectorMonomial = a.e == b.e

generators(::Type{VectorMonomial{V}}) where V = Channel(ctype=VectorMonomial{V}) do ch
    for j in 1:typemax(Int)
        x = spzeros(eltype(V), j)
        x[j] = one(eltype(V))
        push!(ch, VectorMonomial{V}(x))
    end
    throw(AssertionError("typemax exhausted"))
end

# -----------------------------------------------------------------------------
#
# TupleMonomial: overloads for speedup
#
# -----------------------------------------------------------------------------
@generated function *(a::M, b::M) where M <: TupleMonomial{N} where N
    result = :( tuple() )
    for i in 1:N
        push!(result.args, :( a[$i] + b[$i] ))
    end
    return quote
        M($result, a.deg + b.deg)
    end
end

total_degree(a::TupleMonomial) = a.deg

@generated function _div(a::M, b::M) where M <: TupleMonomial{N} where N
    result = :( tuple() )
    for i=1:N
        push!(result.args, :( a[$i] - b[$i] ))
    end
    return quote
        M($result, a.deg - b.deg)
    end
end

function maybe_div(a::M, b::M) where M <: TupleMonomial{N} where N
    if all(a[i] >= b[i] for i=1:N)
        return _div(a,b)
    else
        return null
    end
end


# -----------------------------------------------------------------------------
#
# VectorMonomial: overloads for speedup
#
# -----------------------------------------------------------------------------
function *(a::M, b::M) where M <: VectorMonomial
    if length(a.e) >= length(b.e)
        res = copy(a.e)
        res[1:length(b.e)] += b.e
        return M(res)
    else
        res = copy(b.e)
        res[1:length(a.e)] += a.e
        return M(res)
    end
end

total_degree(a::VectorMonomial{V}) where V <: SparseVector = sum(nonzeros(a.e))
enumerate(a::M) where M <: VectorMonomial{V} where V <: SparseVector = Channel(ctype=Tuple{Int,exptype(M)}) do ch
    for i in find(a.e)
        push!(ch, (i, a.e[i]))
    end
end

function *(a::M, b::M) where M <: VectorMonomial{V} where V<:SparseVector
    if length(a.e) >= length(b.e)
        res = copy(a.e)
        res[find(b.e)] += nonzeros(b.e)
        return M(res)
    else
        res = copy(b.e)
        res[find(a.e)] += nonzeros(a.e)
        return M(res)
    end
end

function maybe_div(a::M, b::M) where M <: VectorMonomial{V} where V<:Vector
    if length(a.e) >= length(b.e)
        res = copy(a.e)
        res[find(b.e)] -= nonzeros(b.e)
        if all(r>=0 for r in res)
            return M(res)
        else
            return null
        end
    else
        res = copy(b.e)
        res[find(a.e)] -= nonzeros(a.e)
        if all(r>=0 for r in res)
            return M(res)
        else
            return null
        end
    end
end

import Base.SparseArrays: nonzeroinds
function maybe_div(a::M, b::M) where M <: VectorMonomial{V} where V<:SparseVector
    for (ib,exp) in zip(nonzeroinds(b.e), nonzeros(b.e))
        if a[ib] < exp
            return null
        end
    end
    res = spzeros(exptype(M), max(num_variables(a), num_variables(b)))
    ia = findfirst(a.e)
    ib = findfirst(b.e)
    while (i = min(ia, ib)) > 0
        res[i] = a.e[i] - b.e[i]

        ia = findnext(a.e,i+1)
        ib = findnext(b.e,i+1)
    end
    if ia != 0
        res[ia] = a.e[ia]
        while (ia = findnext(a.e,ia+1))>0
            res[ia] = a.e[ia]
        end
    end
    return M(res)
end

function ^(a::M, n::Integer) where M <: VectorMonomial
    return M(broadcast(*,a.e,n))
end

# -----------------------------------------------------------------------------
#
# Conversion from Vector to tuple (sparse to dense)
#
# -----------------------------------------------------------------------------

max_variable_index(m::TupleMonomial{N}) where N = N
max_variable_index(m::VectorMonomial{V}) where V = length(m.e)

to_dense_monomials(n::Integer, m::AbstractMonomial) = _construct(TupleMonomial{n,exptype(m)}, i->m[i], n)

# -----------------------------------------------------------------------------
#
# User-facing interface
#
# -----------------------------------------------------------------------------
deg(m::AbstractMonomial) = total_degree(m)

(m::TupleMonomial)(args...)  = prod(args[i]^e for (i,e) in enumerate(m))
(m::VectorMonomial)(args...) = prod(args[i]^e for (i,e) in enumerate(m))


end
