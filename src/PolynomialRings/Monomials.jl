module Monomials

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
    M(i -> exponent, num_variables)
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
import Base: getindex, gcd, lcm, one, *, enumerate
import PolynomialRings: generators


# -----------------------------------------------------------------------------
#
# Abstract fallbacks
#
# -----------------------------------------------------------------------------

*(a::M, b::M) where M <: AbstractMonomial = M(i -> a[i] + b[i], max(num_variables(a), num_variables(b)))

total_degree(a::A) where A <: AbstractMonomial = sum( a[i] for i in 1:num_variables(a) )

lcm(a::M, b::M) where M <: AbstractMonomial = M(i -> max(a[i], b[i]), max(num_variables(a), num_variables(b)))
gcd(a::M, b::M) where M <: AbstractMonomial = M(i -> min(a[i], b[i]), max(num_variables(a), num_variables(b)))
enumerate(a::M) where M <: AbstractMonomial = Channel(ctype=Tuple{Int,exptype(M)}) do ch
    for i = 1:num_variables(a)
        push!(ch, (i, a[i]))
    end
end

exptype(a::AbstractMonomial) = exptype(typeof(a))
num_variables(a::A) where A <: AbstractMonomial = num_variables(A)

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

function TupleMonomial(f::Function, num_variables::Type{Val{N}}) where N
    t = ntuple(f, Val{N})
    TupleMonomial{N, eltype(t)}(t, sum(t))
end

TupleMonomial(f::Function, num_variables::Int) = TupleMonomial(f, Val{num_variables})

TupleMonomial(e::NTuple{N,I}) where I <: Integer where N = TupleMonomial{N,I}(e,sum(e))

num_variables(::Type{TupleMonomial{N,I}}) where {N,I} = N
exptype(::Type{TupleMonomial{N,I}}) where I <: Integer where N = I
getindex(m::TupleMonomial, i::Integer) = m.e[i]

one(::Type{TupleMonomial{N, I}}) where {N, I} = TupleMonomial(i->zero(I), Val{N})

generators(::Type{TupleMonomial{N, I}}) where {N, I} = [
    TupleMonomial(i->i==j?one(I):zero(I), Val{N})
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

function VectorMonomial(f::Function, num_variables::Int)
    e = [f(i) for i in 1:num_variables]
    VectorMonomial(e)
end

num_variables(m::VectorMonomial) = length(m.e)
exptype(::Type{VectorMonomial{V}}) where V = eltype(V)
getindex(m::VectorMonomial, i::Integer) = i <= length(m.e) ? m.e[i] : zero(exptype(m))

# the empty vector corresponds to all exponents equal to zero
one(::Type{VectorMonomial{V}}) where V = VectorMonomial{V}( V() )
# special case for sparsevectors; for some reason, SparseVector{Int,Int}() does not give
# an empty vector.
one(::Type{VectorMonomial{V}}) where V <: SparseVector{A,B} where {A,B} = VectorMonomial{V}( sparsevec(B[],A[]) )

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


end
