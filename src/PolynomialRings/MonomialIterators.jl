module MonomialIterators

import Base: *, ==, //, +, -
import Base: iszero, zero
import Base: hash, convert, getindex, iterate
import Base: lcm

import ProgressMeter: @showprogress

import ..IndexedMonomials: IndexedMonomial, ByIndex
import ..Monomials: AbstractMonomial, _construct, num_variables, nzindices, maybe_div
import ..MonomialOrderings: MonomialOrder, NamedMonomialOrder, NumberedMonomialOrder
import ..NamingSchemes: NamingScheme
import PolynomialRings: monomialtype, exptype, basering, monomialorder, tail, divides

function hilbert(n, k)
    n < 0 && return 0
    k < 0 && return 0
    k == 0 && return 1
    n == 0 && return 0
    return binomial(n + k - 1, n - 1)
end

function degrevlex_index(exponents)
    ret = 1
    degree_seen = 0
    for (i, e) in enumerate(exponents)
        degree_seen += e
        ret += hilbert(i + 1, degree_seen - 1)
    end
    return ret
end

function revlex_exponents(::Val{n}, total_degree, index) where n
    n == 0 && return ()
    deg = 0
    while index > (h = hilbert(n - 1, deg))
        index -= h
        deg += 1
    end
    return tuple(revlex_exponents(Val(n - 1), deg, index)..., total_degree - deg)
end

function degrevlex_exponents(::Val{n}, index) where n
    n == 0 && return ()
    total_degree = 0
    while index > (h = hilbert(n, total_degree))
        index -= h
        total_degree += 1
    end
    return revlex_exponents(Val(n), total_degree, index)
end

@inline degrevlex_exponents(n, index) = degrevlex_exponents(Val(n), index)
@inline revlex_exponents(n, total_degree, index) = revlex_exponents(Val(n), total_degree, index)

struct MonomialIter{M<:AbstractMonomial, P} end
monomialtype(::MonomialIter{M}) where M <: AbstractMonomial = M
Base.eltype(::MonomialIter{M, P}) where M <: AbstractMonomial where P = P
Base.copy(it::MonomialIter{M, P}) where M <: AbstractMonomial where P = it

monomialiter(P) = MonomialIter{monomialtype(P), P}()

const IterBy{sym} = MonomialIter{<:AbstractMonomial{<:MonomialOrder{sym}}}
const IndexedIter{sym} = MonomialIter{<:IndexedMonomial{<:MonomialOrder{sym}}}

function Base.iterate(it::IndexedIter, state...)
    M = monomialtype(it)
    P = eltype(it)
    ix, newstate = iterate(1:typemax(Int), state...)
    P(M(ByIndex(), ix)), newstate
end

# resolve ambiguity
function Base.iterate(it::IndexedIter{:degrevlex}, state...)
    M = monomialtype(it)
    P = eltype(it)
    ix, newstate = iterate(1:typemax(Int), state...)
    P(M(ByIndex(), ix)), newstate
end


function Base.iterate(it::IterBy{:degrevlex})
    M = monomialtype(it)
    P = eltype(it)
    state = zeros(exptype(M), num_variables(M))
    return one(P), state
end

function Base.iterate(it::IterBy{:degrevlex}, state)
    M = monomialtype(it)
    P = eltype(it)
    if length(state) == 1
        state[1] += 1
        return convert(P, _construct(M, i -> i <= length(state) ? state[i] : zero(eltype(state)), eachindex(state))), state
    end
    curdeg = sum(state)
    substate = @view state[1:end-1]
    subdeg = sum(substate)
    _, substate = iterate(it, substate)
    if sum(substate) > subdeg
        if state[end] > 0
            state[end] -= 1
            state[end-1] = curdeg - state[end]
            state[1:end-2] .= 0
        else
            state[end] = curdeg + 1
            state[1:end-1] .= 0
        end
    else
        #state[1:end-1] = substate
    end

    return convert(P, _construct(M, i -> i <= length(state) ? state[i] : zero(eltype(state)), eachindex(state))), state
end

Base.IteratorSize(::MonomialIter) = Base.IsInfinite()

const MATERIALIZE_SIZE = 3_000_000

@generated function Base.getindex(::Iter, ix::Integer) where Iter <: MonomialIter
    To = monomialtype(Iter())
    lookup = Vector{To}()
    #@showprogress 1 "pre-computing..."
    for (i, to) in zip(1:MATERIALIZE_SIZE, Iter())
        push!(lookup, to)
        @assert length(lookup) == i
    end
    :( $lookup[ix] )
end

# TODO: ensure order congruence
function Base.searchsorted(mi::IterBy{:degrevlex}, m::AbstractMonomial)
    return degrevlex_index(m.e)
end

# TODO: ensure order congruence
function Base.searchsorted(mi::IterBy{:degrevlex}, m::IndexedMonomial)
    return m.ix
end

Base.lastindex(::MonomialIter) = typemax(Int)
Base.getindex(mi::MonomialIter, ix::UnitRange) = (@assert first(ix) == 1; copy(mi))

for SpecificOrder in [NamedMonomialOrder, NumberedMonomialOrder]; @eval begin
    function convert(::Type{To}, m::From) where To <: IndexedMonomial{Order} where From <: AbstractMonomial{Order} where Order <: $SpecificOrder
        ix = degrevlex_index(m.e)
        To(ByIndex(), ix)
    end

    @generated function convert(::Type{To}, m::From) where To <: AbstractMonomial{Order} where From <: IndexedMonomial{Order} where Order <: $SpecificOrder
        lookup = Vector{To}()
        #@showprogress 1 "pre-computing $From->$To"
        for (ix, to) in zip(1:MATERIALIZE_SIZE, MonomialIter{To, To}())
            push!(lookup, to)
            @assert length(lookup) == ix
        end
        :( $lookup[m.ix] )
    end

    convert(::Type{M}, m::M) where M <: IndexedMonomial{Order} where Order <: $SpecificOrder = m
end end



end
