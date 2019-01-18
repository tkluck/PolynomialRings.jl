module DensePolynomials

import Base: *, ==, //, +, -
import Base: iszero, zero
import Base: hash, convert, getindex, iterate
import Base: lcm

import ProgressMeter: @showprogress


import ..Monomials: AbstractMonomial, _construct, num_variables, nzindices, maybe_div
import ..MonomialOrderings: MonomialOrder, NamedMonomialOrder, NumberedMonomialOrder
import ..NamingSchemes: NamingScheme
import ..Polynomials: Polynomial, basering, terms
import ..Polynomials: PolynomialBy
import ..Terms: monomial, coefficient, Term
import PolynomialRings: leading_monomial, leading_coefficient, leading_term
import PolynomialRings: monomialtype, exptype, monomialorder, tail, divides

@generated function hilbert(n::I,k::I) where I <: Integer
    lookup = Matrix{Int}(undef, 20, 20)
    for N = axes(lookup, 1), K = axes(lookup, 2)
        lookup[N, K] = binomial(N + K - 1, N - 1)
    end
    quote
        n < 0 && return 0
        k < 0 && return 0
        k == 0 && return 1
        n == 0 && return 0
        $lookup[n, k]
    end
end

function degrevlex_index(exponents)
    ret = 1
    degree_seen = 0
    for (i,e) in enumerate(exponents)
        degree_seen += e
        ret += hilbert(i + 1, degree_seen - 1)
    end
    return ret
end

struct MonomialIter{M<:AbstractMonomial, P} end
monomialtype(::MonomialIter{M}) where M <: AbstractMonomial = M
targettype(::MonomialIter{M, P}) where M <: AbstractMonomial where P = P
monomialiter(P) = MonomialIter{monomialtype(P), P}()

const IterBy{sym} = MonomialIter{<:AbstractMonomial{<:MonomialOrder{sym}}}

function Base.iterate(it::IterBy{:degrevlex})
    M = monomialtype(it)
    P = targettype(it)
    state = zeros(exptype(M), num_variables(M))
    return one(P), state
end

function Base.iterate(it::IterBy{:degrevlex}, state)
    M = monomialtype(it)
    P = targettype(it)
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

const MATERIALIZE_SIZE = 3000000

struct ByIndex end

struct IndexedMonomial{Order <: MonomialOrder, I <: Integer} <: AbstractMonomial{Order}
    ix::I
    IndexedMonomial{Order, I}(::ByIndex, ix::I) where {Order, I}= new(ix)
end

monomialorder(::Type{IndexedMonomial{Order, I}}) where {Order, I} = Order()
exptype(::Type{IndexedMonomial{Order, I}}) where {Order, I} = I

densetype(::Type{IndexedMonomial{Order, I}}) where {Order, I} = monomialtype(Order(), Int8)

==(a::M, b::M) where M <: IndexedMonomial = a.ix == b.ix
hash(m::IndexedMonomial, h::UInt) = hash(m.ix, h)

function nzindices(m::IndexedMonomial)
    N = densetype(typeof(m))
    nzindices(convert(N, m))
end

function Base.getindex(m::IndexedMonomial, ix)
    N = densetype(typeof(m))
    getindex(convert(N, m), ix)
end

Base.lt(::Order, a::M, b::M) where M <: IndexedMonomial{Order} where Order <: MonomialOrder{:degrevlex} = a.ix < b.ix

for SpecificOrder in [NamedMonomialOrder, NumberedMonomialOrder]; @eval begin
    #@generated function convert(::Type{To}, m::From) where To <: IndexedMonomial{Order} where From <: AbstractMonomial{Order} where Order <: $SpecificOrder
    #    lookup = Dict{From, To}()
    #    @showprogress 1 "pre-computing $From->$To" for (ix, from) in zip(1:MATERIALIZE_SIZE, MonomialIter{From, From}())
    #        to = To(ByIndex(), ix)
    #        lookup[from] = to
    #    end
    #    :( $lookup[m] )
    #end

    function convert(::Type{To}, m::From) where To <: IndexedMonomial{Order} where From <: AbstractMonomial{Order} where Order <: $SpecificOrder
        ix = degrevlex_index(m.e)
        To(ByIndex(), ix)
    end

    @generated function convert(::Type{To}, m::From) where To <: AbstractMonomial{Order} where From <: IndexedMonomial{Order} where Order <: $SpecificOrder
        lookup = Vector{To}()
        @showprogress 1 "pre-computing $From->$To" for (ix, to) in zip(1:MATERIALIZE_SIZE, MonomialIter{To, To}())
            push!(lookup, to)
            @assert length(lookup) == ix
        end
        :( $lookup[m.ix] )
    end

    convert(::Type{M}, m::M) where M <: IndexedMonomial{Order} where Order <: $SpecificOrder = m
end end

function _construct(::Type{M}, f, nz) where M <: IndexedMonomial
    N = densetype(M)
    convert(M, _construct(N, f, nz))
end

function *(a::M, b::M) where M <: IndexedMonomial
    N = densetype(M)
    res = convert(N, a) * convert(N, b)
    return convert(M, res)
end

_convertres(M, res) = convert(M, res)
_convertres(M, res::Nothing) = nothing
function maybe_div(a::M, b::M) where M <: IndexedMonomial
    N = densetype(M)
    res = maybe_div(convert(N, a), convert(N, b))
    return _convertres(M, res)
end

function lcm(a::M, b::M) where M <: IndexedMonomial
    N = densetype(M)
    res = lcm(convert(N, a), convert(N, b))
    return _convertres(M, res)
end

function divides(a::M, b::M) where M <: IndexedMonomial
    N = densetype(M)
    return divides(convert(N, a), convert(N, b))
end

struct DensePolynomial{Order <: MonomialOrder, C}
    coeffs::Vector{C}
end

monomialorder(::Type{DensePolynomial{Order, C}}) where {Order, C} = Order()
basering(::Type{DensePolynomial{Order, C}}) where {Order, C} = C

monomialtype(P::Type{<:DensePolynomial}) = IndexedMonomial{typeof(monomialorder(P)), Int}

DensePolynomial(order::MonomialOrder, coeffs::Vector) = DensePolynomial{typeof(order), eltype(coeffs)}(coeffs)

function to_dense(f)
    P = typeof(f)
    ix = 1
    coeffs = basering(P)[]
    for t in terms(f)
        while ix < monomial(t).ix
            push!(coeffs, zero(basering(P)))
            ix += 1
        end
        push!(coeffs, coefficient(t))
        ix += 1
    end
    return DensePolynomial(monomialorder(f), coeffs)
end

densepolynomialtype(::Type{P}) where P <: Polynomial = DensePolynomial{typeof(monomialorder(P)), basering(P)}

function convert(P::Type{<:PolynomialBy{Order, C}}, p::DensePolynomial{Order, C}) where {Order, C}
    M = monomialtype(P)
    terms = map(enumerate(p.coeffs)) do x
        ix, c = x
        Term(M(ByIndex(), ix), c)
    end
    filter!(!iszero, terms)
    P(terms)
end

function op_ordered_terms!(op, p::DensePolynomial, d, terms)
    for t in terms
        t′ = d * t
        ix = monomial(t′).ix
        while ix > length(p.coeffs)
            push!(p.coeffs, zero(eltype(p.coeffs)))
        end
        p.coeffs[ix] = op(p.coeffs[ix], coefficient(t′))
    end
end

_leading_index(p::DensePolynomial) = findlast(!iszero, p.coeffs)
leading_coefficient(p::DensePolynomial{Order}; order::Order) where Order = p.coeffs[_leading_index(p)]
leading_monomial(p::DensePolynomial{Order}; order::Order) where Order = monomialtype(typeof(p))(ByIndex(), _leading_index(p))
tail(p::DensePolynomial{Order}; order::Order) where Order = typeof(p)(p.coeffs[1:_leading_index(p)-1])
function leading_term(p::DensePolynomial{Order}; order::Order) where Order
    ix = _leading_index(p)
    m = monomialtype(typeof(p))(ByIndex(), ix)
    c = p.coeffs[ix]
    Term(m, c)
end

function terms(p::DensePolynomial{Order}; order::Order) where Order
    return (
        Term((monomialtype(typeof(p)))(ByIndex(), ix), c)
        for (ix, c) in enumerate(p.coeffs)
        if !iszero(c)
    )
end

struct TailTerms2{Reverse, P}
    p::P
end
function iterate(t::TailTerms2{true}, state=_leading_index(t.p)-1)
    M = monomialtype(typeof(t.p))
    T = Term{M, basering(typeof(t.p))}
    while state >= 1
        if !iszero(t.p.coeffs[state])
            return T(M(ByIndex(), state), t.p.coeffs[state]), state - 1
        end
        state -= 1
    end
    return nothing
end
function iterate(t::TailTerms2{false}, state=1)
    M = monomialtype(typeof(t.p))
    T = Term{M, basering(typeof(t.p))}
    while state <= _leading_index(t.p) - 1
        if !iszero(t.p.coeffs[state])
            return T(M(ByIndex(), state), t.p.coeffs[state]), state + 1
        end
        state += 1
    end
    return nothing
end
tailterms(p::DensePolynomial, ::Val{reverse}) where reverse = TailTerms2{reverse, typeof(p)}(p)

zero(P::Type{<:DensePolynomial}) = P(basering(P)[])
zero(p::DensePolynomial) = typeof(p)(basering(typeof(p))[])
iszero(p::DensePolynomial) = iszero(p.coeffs)

function +(a::P, b::P) where P <: DensePolynomial
    longest, shortest = length(a.coeffs) > length(b.coeffs) ?
                        (a, b) : (b, a)
    coeffs = copy(longest.coeffs)
    coeffs[1:length(shortest.coeffs)] .+= shortest.coeffs

    P(coeffs)
end

function -(a::P, b::P) where P <: DensePolynomial
    if length(a.coeffs) > length(b.coeffs)
        coeffs = copy(a.coeffs)
        coeffs[1:length(b.coeffs)] .-= b.coeffs
    else
        coeffs = -b.coeffs
        coeffs[1:length(a.coeffs)] .+= a.coeffs
    end

    P(coeffs)
end

//(p::DensePolynomial, c::Number) = typeof(p)(p.coeffs .// c)

function getindex(p::DensePolynomial{Order}, m::IndexedMonomial{Order}) where Order <: MonomialOrder
    if m.ix <= length(p.coeffs)
        return p.coeffs[m.ix]
    else
        return zero(basering(typeof(p)))
    end
end


end
