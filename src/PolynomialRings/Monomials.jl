module Monomials

import Base: getindex, gcd, lcm, one, *, ^, ==, diff, isless, iszero
import Base: hash
import Base: iterate
import Base: last, findlast, length
import Base: promote_rule
import SparseArrays: SparseVector, sparsevec
import SparseArrays: nonzeroinds

import ..NamingSchemes: Named, Numbered, NamingScheme, isdisjoint
import PolynomialRings: generators, to_dense_monomials, max_variable_index, monomialtype, num_variables
import PolynomialRings: maybe_div, lcm_multipliers, exptype, lcm_degree, namingscheme, monomialorder
import PolynomialRings: divides

"""
    AbstractMonomial{Order}

The abstract base type for multi-variate monomials.

Specifying a monomial is equivalent to specifying the exponents for all variables.
The concrete type decides whether this happens as a tuple or as a (sparse or dense)
array.

The type also encodes the monomial order, and as part of that, the names
of the variables.

Each concrete implementation `M` should implement for elements `m`:

    m[i]
    nzindices(m)
    _construct(M, i -> exponent, nonzero_indices, [total_degree])
    exptype(M)

In addition, one may choose to add specific optimizations by overloading
other functions, as well.
"""
abstract type AbstractMonomial{Order} end

# -----------------------------------------------------------------------------
#
# Utility: iterate over the union of two index sets
#
# -----------------------------------------------------------------------------
struct IndexUnion{I,J,lt}
    left::I
    right::J
end

struct Start end
iterate(a, b::Start) = iterate(a)
iterate(a::Array, b::Start) = iterate(a)
iterate(a::OrdinalRange, b::Start) = iterate(a)
iterate(i::IndexUnion) = iterate(i, (Start(), Start()))
@inline function iterate(i::IndexUnion{I,J,lt}, state) where {I,J,lt}
    lstate, rstate = state
    liter = iterate(i.left, lstate)
    riter = iterate(i.right, rstate)
    if liter === nothing && riter === nothing
        return nothing
    elseif liter === nothing || (riter !== nothing && lt(riter[1], liter[1]))
        return riter[1], (lstate, riter[2])
    elseif riter === nothing || (liter !== nothing && lt(liter[1], riter[1]))
        return liter[1], (liter[2], rstate)
    elseif liter[1] == riter[1]
        return liter[1], (liter[2], riter[2])
    else
        @assert(false) # unreachable?
    end
end

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
iterate(r::ReversedVector) = iterate(r, Start())
iterate(r::ReversedVector, ::Start) = isempty(r.a) ? nothing : (r.a[end], 1)
iterate(r::ReversedVector, state) = length(r.a) <= state ? nothing : (r.a[end-state], state+1)
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
function iterate(enz::EnumerateNZ)
    it = iterate(nzindices(enz.a))
    it === nothing && return nothing
    i, next_state = it
    (i,enz.a[i]), next_state
end
function iterate(enz::EnumerateNZ, state)
    it = iterate(nzindices(enz.a), state)
    it === nothing && return nothing
    i, next_state = it
    (i,enz.a[i]), next_state
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
@inline _construct(::Type{M}, f, nzindices) where M <: AbstractMonomial = _construct(M, f, nzindices, exptype(M)(mapreduce(f, +, nzindices, init=zero(exptype(M)))))

one(::Type{M}) where M <: AbstractMonomial = _construct(M, i->0, 1:0)
one(::M) where M <: AbstractMonomial = one(M)

*(a::AbstractMonomial{Order}, b::AbstractMonomial{Order}) where Order = _construct(promote_type(typeof(a), typeof(b)),i -> a[i] + b[i], index_union(a,b), total_degree(a) + total_degree(b))
^(a::M, n::Integer) where M <: AbstractMonomial = _construct(M,i -> a[i]*n, nzindices(a), total_degree(a)*n)

total_degree(a::A) where A <: AbstractMonomial = mapreduce(i->a[i], +, nzindices(a), init=zero(exptype(a)))

lcm(a::AbstractMonomial{Order}, b::AbstractMonomial{Order}) where Order = _construct(promote_type(typeof(a), typeof(b)),i -> max(a[i], b[i]), index_union(a,b))
gcd(a::AbstractMonomial{Order}, b::AbstractMonomial{Order}) where Order = _construct(promote_type(typeof(a), typeof(b)),i -> min(a[i], b[i]), index_union(a,b))

monomialorder(::Type{M}) where M <: AbstractMonomial{Order} where Order = Order()
namingscheme(::Type{M}) where M <: AbstractMonomial = namingscheme(monomialorder(M))
isless(a::M, b::M) where M <: AbstractMonomial = Base.Order.lt(monomialorder(M), a, b)
iszero(a::AbstractMonomial) = false

function exptype(::Type{M}, scheme::NamingScheme) where M <: AbstractMonomial
    return isdisjoint(namingscheme(M), scheme) ? Int8 : exptype(M)
end

num_variables(::Type{M}) where M <: AbstractMonomial = num_variables(namingscheme(M))

"""
    enumeratenz(monomial)

Enumerate (i.e. return an iterator) for `(variable index, exponent)` tuples for `monomial`,
where `exponent` is a structural nonzero (hence `nz`).

This means that, depending on implementation details, the variable indices with
zero exponent *may* be skipped, but this is not guaranteed. In practice, this
only happens if the storage format is sparse.
"""
enumeratenz(a::M) where M <: AbstractMonomial = EnumerateNZ(a)

exptype(a::AbstractMonomial) = exptype(typeof(a))

"""
    hash(monomial)

This hash function is carefully designed to give the same answer
for sparse and dense representations. This is necessary for a
typical `any_divisor` use-case: `any_divisor` loops over the
possible divisors in-place in an array, but its function `f` might
operate on tuple monomials. They should compare equal and hash
equal.

TODO: add test cases for that!
"""
@generated function hash(a::M, h::UInt) where M <: AbstractMonomial
    N = 8sizeof(UInt)
    n = 8sizeof(exptype(M))
    k = N÷n
    q = num_variables(M)÷k

    res = quote
    end
    for i in 0:q
        push!(res.args, quote
            accum = zero(UInt)
        end)
        for j in 1:k
            if (ix = k*i + j) <= num_variables(M)
                push!(res.args, quote
                    accum |= UInt(a[$ix]) << $(8j)
                end)
            end
        end
        push!(res.args, quote
            h = hash(accum, h)
        end)
    end
    push!(res.args, quote
        h
    end)
    res
end

==(a::AbstractMonomial{Order}, b::AbstractMonomial{Order}) where Order = all(i->a[i]==b[i], index_union(a,b))

divides(a::AbstractMonomial{Order}, b::AbstractMonomial{Order}) where Order = all(i->a[i]<=b[i], index_union(a,b))

function maybe_div(a::AbstractMonomial{Order}, b::AbstractMonomial{Order}) where Order
    M = promote_type(typeof(a), typeof(b))
    if all(i->a[i]>=b[i], index_union(a,b))
        return _construct(M,i -> a[i] - b[i], index_union(a,b))
    else
        return nothing
    end
end

function lcm_multipliers(a::AbstractMonomial{Order}, b::AbstractMonomial{Order}) where Order
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

function lcm_degree(a::AbstractMonomial{Order}, b::AbstractMonomial{Order}) where Order
    # avoid summing empty iterator
    iszero(total_degree(a)) && iszero(total_degree(b)) && return zero(exptype(M))
    return sum(max(a[i],b[i]) for i in index_union(a,b))
end

function any_divisor(f::Function, a::M) where M <: AbstractMonomial
    if isempty(nzindices(a))
        return f(a)
    end


    n = last(nzindices(a))
    nzinds = collect(nzindices(a))
    nonzeros_a = map(i->a[i], nzinds)
    nonzeros = copy(nonzeros_a)
    e = SparseVector{Int16, Int}(n, nzinds, nonzeros)

    N = VectorMonomial{typeof(e), Int16, typeof(monomialorder(M))}

    while true
        m = N(e, sum(e))
        if f(m)
            return true
        end
        carry = 1
        for j = 1:length(nonzeros)
            if iszero(nonzeros[j]) && !iszero(carry)
                nonzeros[j] = nonzeros_a[j]
                carry = 1
            else
                nonzeros[j] -= carry
                carry = 0
            end
        end
        if !iszero(carry)
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
    TupleMonomial{N, I, Order} <: AbstractMonomial where I <: Integer where Order

An implementation of AbstractMonomial that stores exponents as a tuple
of integers. This is a dense representation.
"""
struct TupleMonomial{N, I, Order} <: AbstractMonomial{Order}
    e::NTuple{N, I}
    deg::I
    TupleMonomial{N,I,Order}(e,deg) where I <: Integer where {N,Order} = new(e,deg)
end

@generated function _construct(::Type{typ}, f::Function, nonzero_indices, deg) where typ <: TupleMonomial{N,I,Order} where {N,I,Order}
    result = :( tuple() )
    for i in 1:N
        push!(result.args, :( I(f($i)) ))
    end
    return quote
        t = $result
        typ(t, deg)
    end
end

num_variables(::Type{TupleMonomial{N,I,Order}}) where {N,I,Order} = N
exptype(::Type{TupleMonomial{N,I,Order}}) where I <: Integer where {N,Order} = I
expstype(::Type{TupleMonomial{N,I,Order}}) where I <: Integer where {N,Order} = NTuple{N,I}
@inline getindex(m::TupleMonomial, i::Integer) = m.e[i]

generators(::Type{TupleMonomial{N, I, Order}}) where {N, I, Order} = [
    _construct(TupleMonomial{N, I, Order}, i->i==j ? one(I) : zero(I), 1:N)
    for j in 1:N
]

nzindices(a::TupleMonomial{N,I,Order}) where {N,I,Order} = 1:N
@inline index_union(::T, ::T) where T<:TupleMonomial{N,I,Order} where {N,I,Order} = 1:N
@inline rev_index_union(::T, ::T) where T<:TupleMonomial{N,I,Order} where {N,I,Order} = N:-1:1

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
    e::V
    deg::I
    VectorMonomial{V,I,Order}(e, deg) where V<:AbstractVector{I} where {I<:Integer,Order} = new(e, deg)
end

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
@inline getindex(m::VectorMonomial, i::Integer) = i <= length(m.e) ? m.e[i] : zero(exptype(m))

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

nzindices(a::VectorMonomial{V,I,Order}) where {V <: SparseVector,I,Order} = nonzeroinds(a.e)

# -----------------------------------------------------------------------------
#
# Conversion from Vector to tuple (sparse to dense)
#
# -----------------------------------------------------------------------------

max_variable_index(m::TupleMonomial{N}) where N = N
max_variable_index(m::VectorMonomial{V,I,Order}) where {V,I,Order} = length(m.e)

to_dense_monomials(n::Integer, scheme::Numbered{Name}) where Name = (@assert n <= num_variables(scheme); Numbered{Name, n}())
function to_dense_monomials(n::Integer, m::AbstractMonomial)
    Order = to_dense_monomials(n, monomialorder(m))
    M = TupleMonomial{n, exptype(m), typeof(Order)}
    _construct(M, i->m[i], 1:n)
end

promote_rule(::Type{<:TupleMonomial{N,I,Order}}, ::Type{<:VectorMonomial{V,J,Order}}) where {N,V,I,J,Order} = TupleMonomial{N,promote_type(I,J),Order}

# -----------------------------------------------------------------------------
#
# User-facing interface
#
# -----------------------------------------------------------------------------
(m::TupleMonomial)(args...)  = prod(args[i]^e for (i,e) in enumeratenz(m))
(m::VectorMonomial)(args...) = prod(args[i]^e for (i,e) in enumeratenz(m))


end
