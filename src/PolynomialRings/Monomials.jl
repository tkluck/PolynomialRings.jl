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
    +(a,b)
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
import Base: getindex, gcd, lcm


# -----------------------------------------------------------------------------
#
# Abstract fallbacks
#
# -----------------------------------------------------------------------------

+(a::M, b::M) where M <: AbstractMonomial = M(i -> a[i] + b[i], max(num_variables(a), num_variables(b)))

total_degree(a::AbstractMonomial) = sum( a[i] for i in 1:num_variables(a) )

lcm(a::M, b::M) where M <: AbstractMonomial = M(i -> max(a[i], b[i]), max(num_variables(a), num_variables(b)))
gcd(a::M, b::M) where M <: AbstractMonomial = M(i -> min(a[i], b[i]), max(num_variables(a), num_variables(b)))
enumerate(a::M) where M <: AbstractMonomial = Channel(chtype=Tuple{Int,exptype(M)}) do ch
    for i = 1:num_variables(a)
        push!(ch, (i, a[i]))
    end
end

exptype(a::AbstractMonomial) = exptype(typeof(a))
num_variables(a::AbstractMonomial) = num_variables(typeof(a))

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

function TupleMonomial(f::Function, num_variables::Int)
    t = ntuple(f, num_variables)
    TupleMonomial{num_variables, eltype(t)}(t, sum(t))
end

num_variables(::Type{TupleMonomial{N}}) where N = N
exptype(::Type{TupleMonomial{N,I}}) where I <: Integer where N = I
getindex(m::TupleMonomial, i::Integer) = m.e[i]

# -----------------------------------------------------------------------------
#
# VectorMonomial
#
# -----------------------------------------------------------------------------

"""
    Vector{V, I} <: AbstractMonomial where V <: AbstractVector{I} where I <: Integer

An implementation of AbstractMonomial that stores exponents as a vector
of integers. This can be a sparse or dense representation, depending on the
type specialization.

This representation is intended for the case when the number of variables
is unbounded. In particular, the indexing operation `m[i]` returns `0` when `i`
is out-of-bounds, instead of throwing an exception.
"""
struct VectorMonomial{V, I} <: AbstractMonomial
    e::V
    deg::I
    VectorMonomial{V, I}(e, deg) where V <: AbstractVector{I} where I <: Integer = new(e, deg)
end

function VectorMonomial(f::Function, num_variables::Int)
    e = [f(i) for i in 1:num_variables]
    VectorMonomial(e, sum(e))
end

num_variables(m::VectorMonomial) = length(m.e)
exptype(::Type{VectorMonomial{V,I}}) where I <: Integer where V = I
getindex(m::VectorMonomial, i::Integer) = i <= length(m.e) ? m.e[i] : zero(exptype(m))

# -----------------------------------------------------------------------------
#
# TupleMonomial: overloads for speedup
#
# -----------------------------------------------------------------------------
@generated function +(a::M, b::M) where M <: TupleMonomial{N} where N
    result = :( tuple() )
    for i in 1:N
        push!(result.args, :( a[$i] + b[$i] ))
    end
    return quote
        M($result, a.deg + b.deg)
    end
end


end
