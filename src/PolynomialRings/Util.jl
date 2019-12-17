module Util

import Base: delete!, similar
import Base: iterate
import Base: length, isempty
import Base: length, iterate
import Base: filter, filter!
import Base: pairs

import SparseArrays: SparseVector, SparseMatrixCSC

import Transducers: Transducer, R_, inner, wrap, xform
import Transducers: wrapping, unwrap
import Transducers: start, next, complete, outtype

import DataStructures: PriorityQueue, SortedSet, OrderedSet, OrderedDict
import DataStructures: percolate_down!, percolate_up!, enqueue!, dequeue!, peek
import OrderedCollections: ht_keyindex, rehash!
import ProgressMeter
import ProgressMeter: Progress, next!, finish!

# -----------------------------------------------------------------------------
#
# Bounded heap
#
# -----------------------------------------------------------------------------
mutable struct BoundedHeap{T, O<:Base.Order.Ordering}
    values::Vector{T}
    cur_length::Int
    max_length::Int
    order::O
    BoundedHeap{T, O}(max_length::Int, order::O) where {T, O} = new(resize!(T[], max_length+1), 0, max_length, order)
end

BoundedHeap(T::Type, max_length::Int, order::Base.Order.Ordering) = BoundedHeap{T, typeof(order)}(max_length, order)


function enqueue!(x::BoundedHeap{T, O}, v::T) where {T,O}
    x.values[x.cur_length+1] = v
    if(x.cur_length < x.max_length)
        x.cur_length +=1
    end
    percolate_up!(x.values, x.cur_length, x.order)
end

function dequeue!(x::BoundedHeap{T, O})::T where {T,O}
    if x.cur_length < 1
        throw(BoundsError())
    end
    v = x.values[1]
    x.values[1] = x.values[x.cur_length]
    x.cur_length -= 1
    percolate_down!(x.values, 1, x.order, x.cur_length)
    return v
end

function peek(x::BoundedHeap{T,O})::T where {T,O}
    if x.cur_length < 1
        throw(BoundsError())
    end
    return x.values[1]
end

length(x::BoundedHeap) = x.cur_length
isempty(x::BoundedHeap) = iszero(x.cur_length)


lazymap(f::Function, c) = map(f,c)
lazymap(f::Function, c::C) where C<:Channel = Channel() do ch
    for x in c
        push!(ch, f(x))
    end
end

# -----------------------------------------------------------------------------
#
# make filter! work for priority queues
#
# -----------------------------------------------------------------------------
delete!(pq::PriorityQueue{K}, k::K) where K = dequeue!(pq, k)
similar(pq::PriorityQueue{K, V, O}) where {K, V, O} = PriorityQueue{K, V}(O())

# -----------------------------------------------------------------------------
#
# make filter! work for SortedSets
#
# -----------------------------------------------------------------------------
function filter!(f::Function, s::SortedSet)
    for x in s
        if !f(x)
            delete!(s, x)
        end
    end
    return s
end
filter(f::Function, s::SortedSet) = filter!(f, copy(s))

# -----------------------------------------------------------------------------
#
# speed up iteration over pairs(::PriorityQueue)
#
# -----------------------------------------------------------------------------
pairs(x::PriorityQueue) = x.xs

# -----------------------------------------------------------------------------
#
# iterate over subsets of OrderedSet
#
# -----------------------------------------------------------------------------
function interval(x::OrderedDict, lower; lo)
    δ = lo == :exclusive ? 1 : lo == :inclusive ? 0 : error("lo needs to be :inclusive or :exclusive; not $lo")
    # XXX rehash is only needed for deletions, which we don't do
    #rehash!(x)
    index = ht_keyindex(x, lower, true)
    return (index<0) ? throw(KeyError(lower)) : @views zip(x.keys[index + δ : end], x.vals[index + δ : end])
end

function last_(x::OrderedDict)
    # XXX rehash is only needed for deletions, which we don't do
    #rehash!(x)
    return x.keys[end]
end

interval(x::OrderedSet, lower; lo) = interval(x.dict, lower; lo=lo).is[1]
last_(x::OrderedSet) = last_(x.dict)

# -----------------------------------------------------------------------------
#
# One-element iterator
#
# -----------------------------------------------------------------------------
struct SingleItemIter{X}
    item::X
end
length(::SingleItemIter) = 1
iterate(i::SingleItemIter) = (i.item, nothing)
iterate(i::SingleItemIter, ::Nothing) = nothing

include("LinAlgUtil.jl")

isstrictlysorted(itr; lt) = issorted(itr; lt = (a, b) -> !lt(b, a))

# -----------------------------------------------------------------------------
#
# Utility for showing progress on Gröbner basis computations
#
# -----------------------------------------------------------------------------
_length(x) = length(x)
_length(x::AbstractDict{K, <: AbstractDict}) where K = sum(length, values(x))
_length(x::AbstractDict{K, <: AbstractVector}) where K = sum(length, values(x))
macro showprogress(desc, exprs...)
    infos = exprs[1:end-1]
    expr = last(exprs)

    ourpattern = expr.head == :while && expr.args[1].head == :call &&
        expr.args[1].args[1] == :! && expr.args[1].args[2].head == :call &&
        expr.args[1].args[2].args[1] == :isempty
    if !ourpattern
        return esc(:(
            $ProgressMeter.@showprogress $desc $expr
        ))
    end
    P = expr.args[1].args[2].args[2]
    condition = expr.args[1]
    body = expr.args[2]

    function infoval(L)
        sym = QuoteNode(Symbol("|$L|"))
        :( ($sym, _length($(esc(L)))) )
    end
    infovals = map(infoval, infos)

    quote
        progress = $Progress($length($(esc(P))), $desc)
        loops = 0
        while $(esc(condition))
            $(esc(body))

            loops += 1
            progress.n = $length($(esc(P))) + loops
            $next!(progress, showvalues = [$(infovals...)])
        end
        $finish!(progress)
    end
end

# -----------------------------------------------------------------------------
#
# Readable alternative for Iterators.flatten
#
# -----------------------------------------------------------------------------
chain(iters...) = Iterators.flatten(iters)

# -----------------------------------------------------------------------------
#
# Helper for iteration over nonzeros in arrays
#
# -----------------------------------------------------------------------------
nzpairs(iter) = ((i, x) for (i, x) in pairs(iter) if !iszero(x))

nzpairs(iter::SparseVector) = (
    (iter.nzind[j], iter.nzval[j])
    for j in eachindex(iter.nzind) if !iszero(iter.nzval[j])
)

nzpairs(iter::SparseMatrixCSC) = ((i, iter[i]) for i in findall(!iszero, iter))

isnonzero(array, ix...) = !iszero(array[ix...])
function isnonzero(array::SparseVector, ix::Integer)
    r = searchsorted(array.nzind, ix)
    isempty(r) && return false
    return !iszero(array.nzval[first(r)])
end

# -----------------------------------------------------------------------------
#
# A transducer that merges two iterables like a zipper
#
# -----------------------------------------------------------------------------
struct MergingTransducer{Iter, Order, LeftOp, RightOp, MergeOp, Key, Value} <: Transducer
    iter      :: Iter
    order     :: Order
    leftop    :: LeftOp
    rightop   :: RightOp
    mergeop   :: MergeOp
    key       :: Key
    value     :: Value
end

function start(rf::R_{<:MergingTransducer}, result)
    outeriter = iterate(xform(rf).iter)
    return wrap(rf, outeriter, start(inner(rf), result))
end

function next(rf::R_{<:MergingTransducer}, result, input)
    ≺(a, b) = Base.Order.lt(xform(rf).order, a, b)

    leftop = xform(rf).leftop
    rightop = xform(rf).rightop
    mergeop = xform(rf).mergeop
    key = xform(rf).key
    value = xform(rf).value

    wrapping(rf, result) do outeriter, res
        while !isnothing(outeriter)
            outerinput, state = outeriter
            if key(input) ≺ key(outerinput)
                t = rightop(value(input))
                res = next(inner(rf), res, t)
                return outeriter, res
            elseif key(input) == key(outerinput)
                t = mergeop(value(outerinput), value(input))
                res = next(inner(rf), res, t)
                outeriter = iterate(xform(rf).iter, state)
                return outeriter, res
            else
                t = leftop(value(outerinput))
                res = next(inner(rf), res, t)
                outeriter = iterate(xform(rf).iter, state)
            end
        end
        res = next(inner(rf), res, rightop(value(input)))
        return outeriter, res
    end
end

function complete(rf::R_{<:MergingTransducer}, result)
    leftop = xform(rf).leftop
    value = xform(rf).value

    outeriter, res = unwrap(rf, result)
    while !isnothing(outeriter)
        outerinput, state = outeriter
        res = next(inner(rf), res, leftop(value(outerinput)))
        outeriter = iterate(xform(rf).iter, state)
    end
    complete(inner(rf), res)
end

outtype(xf::MergingTransducer, Q) = Base._return_type((a, b) -> xf.mergeop(xf.value(a), xf.value(b)), Tuple{eltype(xf.iter), Q})

"""
    _Map{Op} <: Transducer

The same thing as Transducers.Map, except using Base._return_type for determining
the outtype. This is not API-stable but gives much better performance. Moreover,
it means we can use it in @generated functions as well.
"""
struct _Map{Op} <: Transducer
    f  :: Op
end

next(rf::R_{<:_Map}, result, input) = next(inner(rf), result, xform(rf).f(input))
outtype(xf::_Map, intype) = Base._return_type(xf.f, Tuple{intype})
isexpansive(xf::_Map) = false

Base.deepcopy(x::BigInt) = return Base.GMP.MPZ.set(x)
function Base.deepcopy(x::Rational)
    T = typeof(x)
    n = deepcopy(numerator(x))
    d = numerator(x) === denominator(x) ? n : deepcopy(denominator(x))
    y = ccall(:jl_new_struct_uninit, Any, (Any,), T)
    ccall(:jl_set_nth_field, Cvoid, (Any, Csize_t, Any), y, 0, n)
    ccall(:jl_set_nth_field, Cvoid, (Any, Csize_t, Any), y, 1, d)
    return y::T
end

_debugassertions() = false

macro assertvalid(p)
    if _debugassertions()
        quote
            res = $(esc(p))
            @assert length(res.monomials) == length(res.coeffs)
            @assert all(!iszero, res.coeffs)
            @assert issorted(res.monomials)
            res
        end
    else
        esc(p)
    end
end

end
