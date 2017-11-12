module Util

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

import Base: findnext
function findnext(v::SparseVector, i::Int)
    n = searchsortedfirst(v.nzind, i)
    if n > length(v.nzind)
        return 0
    else
        return v.nzind[n]
    end
end

function findnext(m::SparseMatrixCSC, i::Int)
   if i > length(m)
       return 0
   end
   row, col = ind2sub(m, i)
   lo, hi = m.colptr[col], m.colptr[col+1]
   n = searchsortedfirst(m.rowval[lo:hi-1], row)
   if n == 0
       return sub2ind(m, m.rowval[lo], col)
   end
   if n <= hi-lo
       return sub2ind(m, m.rowval[lo+n-1], col)
   end
   nextcol = findnext(c->(c>hi), m.colptr, col+1)
   if nextcol == 0
       return 0
   end
   nextlo = m.colptr[nextcol-1]
   return sub2ind(m, m.rowval[nextlo], nextcol-1)
end


# -----------------------------------------------------------------------------
#
# Read/write locks
#
# -----------------------------------------------------------------------------

using Base.Threads: lock, unlock

mutable struct ReadWriteLock{L}
    readers::Int
    read_lock::L
    write_lock::L
    ReadWriteLock{L}() where L = new(0, L(), L())
end

function read_lock!(l::ReadWriteLock)
    lock(l.read_lock)
    l.readers += 1
    unlock(l.read_lock)
end

function read_unlock!(l::ReadWriteLock)
    lock(l.read_lock)
    @assert l.readers > 0
    l.readers -= 1
    unlock(l.read_lock)
end

function write_lock!(l::ReadWriteLock)
    lock(l.write_lock)
    lock(l.read_lock)
    while l.readers > 0
        unlock(l.read_lock)
        # this unlock+lock thing, hoping that another thread can lock it in the
        # mean time, works better or worse based on the exact semantics of the
        # lock. I'm guessing a SpinLock is terrible and an OS mutex is fine.
        lock(l.read_lock)
    end
end

function write_unlock!(l::ReadWriteLock)
    unlock(l.read_lock)
    unlock(l.write_lock)
end


# -----------------------------------------------------------------------------
#
# One-element iterator
#
# -----------------------------------------------------------------------------
struct TrivialIter{X}
    item::X
end
import Base: start, done, next, length
start(::TrivialIter) = false
done(::TrivialIter, state) = state
next(t::TrivialIter, state) = (t.item, true)
length(::TrivialIter) = 1

include("LinAlgUtil.jl")


end
