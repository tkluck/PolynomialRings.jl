import ..MonomialOrderings: rulesymbol
import ..MonomialIterators: monomialiter, IndexedMonomial, ByIndex, degrevlex_index

"""
    DensePolynomial{M, C} where M <: AbstractMonomial where C

This type represents a polynomial as a vector of coefficients, ordered by
increasing monomial order. (see `PolynomialRings.MonomialOrderings`).
"""
struct DensePolynomial{M <: AbstractMonomial, C}
    coeffs :: Vector{C}
    DensePolynomial{M, C}(coeffs::Vector{C}) where {M <: AbstractMonomial, C} = new(coeffs)
end

const DensePolynomialOver{C,Order} = DensePolynomial{<:AbstractMonomial{Order}, C}
const DensePolynomialBy{Order,C}   = DensePolynomialOver{C,Order}
const DensePolynomialIn{M}         = DensePolynomial{M}

isstrictlysparse(P::Type{<:DensePolynomial}) = false
issparse(P::Type{<:DensePolynomial}) = false

monomials(f::DensePolynomial) = monomialiter(monomialtype(f), length(f.coeffs))
# TODO: rename because of naming clash with the Expansions. version
coefficients(f::DensePolynomial) = f.coeffs

# -----------------------------------------------------------------------------
#
# Methods for collection-of-terms
#
# -----------------------------------------------------------------------------
function Base.empty!(p::DensePolynomial)
    empty!(p.coeffs)
    p
end

function Base.push!(p::DensePolynomialBy{Order}, t::TermBy{Order}) where Order <: MonomialOrder
    rulesymbol(Order) == :degrevlex || error("Not implemented")
    # XXX FIXME TODO XXX
    m = monomial(t)
    ix = m isa TupleMonomial ? degrevlex_index(m.e) : m.ix
    @assert ix > length(p.coeffs)
    _ensurecoeffs!(p.coeffs, ix)
    p.coeffs[ix] += coefficient(t)

    @assertvalid p
end

Base.sizehint!(p::DensePolynomial, n) = sizehint!(p.coeffs, n)
Base.copy!(dst::DensePolynomial, src::DensePolynomial) = copy!(dst.coeffs, src.coeffs)

hash(p::DensePolynomial, h::UInt) = hash(hash(p.coeffs, h), hash(monomialtype(p)))

_leading_term_ix(p::DensePolynomialBy{Order}, order::Order) where Order <: MonomialOrder = findlast(!iszero, p.coeffs)
function _monomialbyindex(p::DensePolynomial, ix)
    M = monomialtype(p)
    IxM = IndexedMonomial{typeof(monomialorder(M)), typeof(ix)}
    return convert(M, IxM(ByIndex(), ix))
end

function _ensurecoeffs!(coeffs, n)
    if (m = length(coeffs)) < n
        resize!(coeffs, n)
        for i in m + 1 : n
            coeffs[i] = zero(eltype(coeffs))
        end
    end
    coeffs
end

function tail(p::DensePolynomialBy{Order}, order::Order) where Order <: MonomialOrder
    ix = findlast(!iszero, p.coeffs)
    return typeof(p)(p.coeffs[1:ix-1])
end

# -----------------------------------------------------------------------------
#
# zero, one, etc
#
# -----------------------------------------------------------------------------
zero(::Type{P}) where P <: DensePolynomial = @assertvalid P(basering(P)[])
one(::Type{P})  where P <: DensePolynomial = @assertvalid P([one(basering(P))])
iszero(a::P)    where P <: DensePolynomial = iszero(a.coeffs)

function ==(a::P, b::P)  where P <: DensePolynomial
    N = min(length(a.coeffs), length(b.coeffs))
    all(i -> a.coeffs[i] == b.coeffs[i], 1:N) &&
    all(i -> iszero(a.coeffs[i]), N + 1 : length(a)) &&
    all(i -> iszero(b.coeffs[i]), N + 1 : length(b))
end

#function Base.iterate(it::NZTerms{P}, state=(monomialiter(monomialtype(P)), 1)) where P <: DensePolynomial
#    m_it, ix = state
#    while true
#        ix <= length(coefficients(it.p)) || return nothing
#        if (c = coefficients(it.p)[ix]) |> !iszero
#            return (Term(m_it[ix], c), (m_it, ix + 1))
#        end
#        ix += 1
#    end
#    return nothing
#end

function Base.get(p::DensePolynomialIn{M}, m::M, default) where M <: AbstractMonomial
    rulesymbol(monomialorder(M)) == :degrevlex || error("Not implemented")
    ix = m isa TupleMonomial ? degrevlex_index(m.e) : m.ix
    if ix <= length(coefficients(p))
        c = coefficients(p)[ix]
        return iszero(c) ? default : c
    end
    return default
end

+(a::P)         where P <: DensePolynomial = @assertvalid P(copy(a.coeffs))
-(a::P)         where P <: DensePolynomial = @assertvalid P(map(-, a.coeffs))

function map_coefficients(f, a::DensePolynomial)
    @assertvalid typeof(a)(map(f, coefficients(a)))
end

function convert(P::Type{<:DensePolynomialOver{C,O}}, p::DensePolynomialOver{D,O}) where {C,D,O <: MonomialOrder}
    return P(convert.(C, p.coeffs))
end
