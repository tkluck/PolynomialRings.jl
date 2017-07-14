module Util

type BoundedHeap{T, O} #O<:Base.Order.Ordering}
    values::Vector{T}
    cur_length::Int
    max_length::Int
    BoundedHeap{T, O}(max_length::Int) where {T, O} = new(resize!(T[], max_length+1), 0, max_length)
end

import DataStructures: percolate_down!, percolate_up!, enqueue!, dequeue!, peek

function enqueue!(x::BoundedHeap{T, O}, v::T) where {T,O}
    x.values[x.cur_length+1] = v
    if(x.cur_length < x.max_length)
        x.cur_length +=1
    end
    percolate_up!(x.values, x.cur_length, O)
end

function dequeue!(x::BoundedHeap{T, O})::T where {T,O}
    if x.cur_length < 1
        throw(BoundsError())
    end
    v = x.values[1]
    x.values[1] = x.values[x.cur_length]
    x.cur_length -= 1
    percolate_down!(x.values, 1, O, x.cur_length)
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
function findnext{S <: SparseVector}(v::S, i::Int)
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


end
