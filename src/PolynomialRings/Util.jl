module Util

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

import DataStructures: percolate_down!, percolate_up!, enqueue!, dequeue!, peek

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
end

function peek(x::BoundedHeap{T,O})::T where {T,O}
    if x.cur_length < 1
        throw(BoundsError())
    end
    return x.values[1]
end

import Base: length
length(x::BoundedHeap) = x.cur_length


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
import Base: delete!
import DataStructures: PriorityQueue
delete!(pq::PriorityQueue{K}, k::K) where K = dequeue!(pq, k)

# -----------------------------------------------------------------------------
#
# One-element iterator
#
# -----------------------------------------------------------------------------
struct TrivialIter{X}
    item::X
end
import Base: length, iterate
start(::TrivialIter) = false
done(::TrivialIter, state) = state
next(t::TrivialIter, state) = (t.item, true)
length(::TrivialIter) = 1
iterate(i::TrivialIter) = (i.item, nothing)
iterate(i::TrivialIter, ::Nothing) = nothing

include("LinAlgUtil.jl")

# -----------------------------------------------------------------------------
#
# Parallel iteration of two iterators
#
# -----------------------------------------------------------------------------
import Base: iterate, last, findlast, length
struct ParallelIter{I,J,key,value,lt,l0,r0}
    left::I
    right::J
end

struct Start end
iterate(a, b::Start) = iterate(a)
iterate(a::Array, b::Start) = iterate(a)
iterate(i::ParallelIter) = iterate(i, (Start(), Start()))
function iterate(i::ParallelIter{I,J,key,value,lt,l0,r0}, state) where {I,J,key,value,lt,l0,r0}
    lstate, rstate = state
    liter = iterate(i.left, lstate)
    riter = iterate(i.right, rstate)
    if liter === nothing && riter === nothing
        return nothing
    elseif liter === nothing || (riter !== nothing && lt(key(riter[1]), key(liter[1])))
        return (key(riter[1]), l0, value(riter[1])), (lstate, riter[2])
    elseif riter === nothing || (liter !== nothing && lt(key(liter[1]), key(riter[1])))
        return (key(liter[1]), value(liter[1]), r0), (liter[2], rstate)
    elseif key(liter[1]) == key(riter[1])
        return (key(liter[1]), value(liter[1]), value(riter[1])), (liter[2], riter[2])
    else
        @assert(false) # unreachable?
    end
end


end
