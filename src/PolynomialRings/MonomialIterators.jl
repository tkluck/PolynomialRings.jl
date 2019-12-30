module MonomialIterators

import Base: *, ==, //, +, -
import Base: iszero, zero
import Base: hash, convert, getindex, iterate
import Base: lcm

import ProgressMeter: @showprogress

import ..IndexedMonomials: IndexedMonomial, ByIndex
import ..Monomials: TupleMonomial, AbstractMonomial, _construct, num_variables, nzindices, maybe_div
import ..MonomialOrderings: MonomialOrder, NamedMonomialOrder, NumberedMonomialOrder, rulesymbol
import ..NamingSchemes: NamingScheme
import PolynomialRings: monomialtype, exptype, basering, monomialorder, tail, divides

const _hilbertfunction = Vector{Vector{Int}}()
function hilbert(n, k)
    n < 0 && return 0
    k < 0 && return 0
    k == 0 && return 1
    n == 0 && return 0
    while length(_hilbertfunction) < n
        push!(_hilbertfunction, Vector{Int}())
    end
    hf_n = _hilbertfunction[n]
    while length(hf_n) < k
        k′ = length(hf_n) + 1
        push!(hf_n, binomial(n + k′ - 1, n - 1))
    end
    return hf_n[k]
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

struct MonomialIter{M<:AbstractMonomial, P, Length} end
monomialtype(::MonomialIter{M}) where M <: AbstractMonomial = M
Base.eltype(::MonomialIter{M, P, Length}) where M <: AbstractMonomial where {Length, P} = P
Base.copy(it::MonomialIter{M, P, Length}) where M <: AbstractMonomial where {Length, P} = it
Base.length(it::MonomialIter{M, P, Length}) where M <: AbstractMonomial where {Length, P} = Length

monomialiter(P, len=Inf) = MonomialIter{monomialtype(P), P, len}()

const IterBy{Rule} = MonomialIter{<:AbstractMonomial{<:MonomialOrder{Rule}}}
const IndexedIterBy{Rule} = MonomialIter{<:IndexedMonomial{<:MonomialOrder{Rule}}}

function Base.iterate(it::IndexedIterBy, state...)
    M = monomialtype(it)
    P = eltype(it)
    ix, newstate = iterate(1:typemax(Int), state...)
    P(M(ByIndex(), ix)), newstate
end

# resolve ambiguity
function Base.iterate(it::IndexedIterBy{:degrevlex}, state...)
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

function next_degrevlex!(exponents, n=lastindex(exponents), totaldeg=sum(exponents[i] for i in 1:n))
    if n == 1
        exponents[1] += 1
        return true
    end
    if next_degrevlex!(exponents, n - 1, totaldeg - exponents[n])
        if exponents[n] > 0
            exponents[n] -= 1
            exponents[n - 1] = totaldeg - exponents[n]
            exponents[1:n - 2] .= 0
            return false
        else
            exponents[n] = totaldeg + 1
            exponents[1:n - 1] .= 0
            return true
        end
    end
    return false
end

function Base.iterate(it::IterBy{:degrevlex}, state)
    M = monomialtype(it)
    P = eltype(it)

    next_degrevlex!(state)
    return convert(P, _construct(M, i -> i <= length(state) ? state[i] : zero(eltype(state)), eachindex(state))), state
end

Base.IteratorSize(it::MonomialIter) = length(it) == Inf ? Base.IsInfinite() : Base.HasLength()

function _byindex(M::Type{<:TupleMonomial}, ix)
    @assert rulesymbol(monomialorder(M)) == :degrevlex
    nv = Val(num_variables(M))
    exps = degrevlex_exponents(nv, ix)
    M(exps, sum(exps))
end

function _byindex(M::Type{<:IndexedMonomial}, ix)
    M(ByIndex(), ix)
end

function Base.getindex(it::MonomialIter, ix::Integer)
    IteratorSize(it) == Base.IsInfinite() || ix <= length(it) || error("Index out of range")
    M = monomialtype(it)
    P = eltype(it)
    IxM = IndexedMonomial{typeof(monomialorder(M)), typeof(ix)}
    return P(convert(M, IxM(ByIndex(), ix)))
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

    @generated function convert(::Type{To}, m::From)::To where To <: AbstractMonomial{Order} where From <: IndexedMonomial{Order} where Order <: $SpecificOrder
        lookup = Vector{To}()
        quote
            if 1 <= m.ix <= length($lookup)
                return @inbounds $lookup[m.ix]::$To
            else
                newsize = length($lookup) + m.ix # Fibonacci growth
                while length($lookup) < newsize
                    k = length($lookup) + 1
                    val = _byindex($To, k)
                    push!($lookup, val)
                end
                return $lookup[m.ix]::$To
            end
        end
    end

    convert(::Type{M}, m::M) where M <: IndexedMonomial{Order} where Order <: $SpecificOrder = m
end end



end
