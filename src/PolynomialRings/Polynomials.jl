module Polynomials

import Base: OneTo
import Base: first, last, copy, hash, convert
import Base: zero, one, +, -, *, ==, div, iszero, ^, gcd, exp
import SparseArrays: SparseVector, HigherOrderFns, issparse

import InPlace: @inplace, inplace!, inclusiveinplace!
import Transducers: Transducer, Eduction

import ..AbstractMonomials: AbstractMonomial
import ..MonomialOrderings: MonomialOrder, NamedMonomialOrder, NumberedMonomialOrder
import ..MonomialOrderings: monomialorderkey
#import ..Monomials.IndexedMonomials: IndexedMonomial
import ..NamingSchemes: Named, Numbered, NamingScheme, InfiniteScheme, nestednamingscheme, isvalid
import ..Terms: Term, monomial, coefficient
import ..Util: @assertvalid, _debug_isvalid, isdisjoint
import PolynomialRings: generators, max_variable_index, basering, monomialtype
import PolynomialRings: leading_coefficient, leading_monomial
import PolynomialRings: leading_term, termtype, monomialorder, nzterms, exptype, namingscheme, expansion
import PolynomialRings: polynomialtype
import PolynomialRings: tail
import PolynomialRings: variablesymbols, allvariablesymbols, fullboundnames

# -----------------------------------------------------------------------------
#
# Type shorthands I
#
# -----------------------------------------------------------------------------

const NamedMonomial           = AbstractMonomial{<:NamedMonomialOrder}
const NumberedMonomial        = AbstractMonomial{<:NumberedMonomialOrder}
const MonomialBy{Order}       = AbstractMonomial{Order}
const TermOver{C,Order}       = Term{<:AbstractMonomial{Order}, C}
const TermBy{Order,C}        = TermOver{C,Order}
const TermIn{M}              = Term{M}

include("SparsePolynomials.jl")
#include("DensePolynomials.jl")
abstract type DensePolynomial{M, C} end
abstract type DensePolynomialBy{M, C} end
abstract type DensePolynomialOver{M, C} end

const Polynomial{M, C} = Union{SparsePolynomial{M, C}, DensePolynomial{M, C}}

function polynomialtype(M::Type{<:AbstractMonomial}, C::Type; sparse=true)
    if !isdisjoint(namingscheme(M), nestednamingscheme(C)) || !isdisjoint(namingscheme(M), fullboundnames(C))
        error("Duplicate veriable names while creating polynomialring in $M over $C")
    end
    if C <: AbstractMonomial
        C = polynomialtype(C, Int)
    elseif C <: Term
        C = polynomialtype(C)
    end
    if !isconcretetype(C)
        error("Cannot create a polynomial ring over $C as it is not concrete")
    end
    if !sparse
        M = IndexedMonomial{typeof(monomialorder(M)), Int}
    end
    return sparse ? SparsePolynomial{M, C} : DensePolynomial{M, C}
end

function polynomialtype(P::Type{<:Polynomial}; sparse=true)
    polynomialtype(monomialtype(P), basering(P), sparse=sparse)
end


# -----------------------------------------------------------------------------
#
# Monomial constructor from exponents
#
# -----------------------------------------------------------------------------
exp(P::Type{<:Polynomial}, exps) = convert(P, exp(termtype(P), exps))

# -----------------------------------------------------------------------------
#
# Type shorthands II
#
# -----------------------------------------------------------------------------

const PolynomialOver{C,Order} = Polynomial{<:AbstractMonomial{Order}, C}
const NamedTerm{C}            = TermOver{C,<:NamedMonomialOrder}
const NumberedTerm{C}         = TermOver{C,<:NumberedMonomialOrder}
const NamedPolynomial{C}      = PolynomialOver{C,<:NamedMonomialOrder}
const NumberedPolynomial{C}   = PolynomialOver{C,<:NumberedMonomialOrder}
const PolynomialBy{Order,C}   = PolynomialOver{C,Order}
const PolynomialIn{M}         = Polynomial{M}

# -----------------------------------------------------------------------------
#
# Type information
#
# -----------------------------------------------------------------------------
termtype(::Type{<:Polynomial{M,C}}) where {M,C}  = Term{M,C}
exptype(::Type{P}, scheme::NamingScheme...) where P<:Polynomial = exptype(termtype(P), scheme...)
namingscheme(::Type{P}) where P<:Polynomial = namingscheme(termtype(P))
monomialorder(::Type{P}) where P<:Polynomial = monomialorder(termtype(P))
basering(::Type{P}) where P <: Polynomial = basering(termtype(P))
monomialtype(::Type{P}) where P <: Polynomial = monomialtype(termtype(P))
allvariablesymbols(::Type{P}) where P <: Polynomial = union(allvariablesymbols(basering(P)), variablesymbols(P))

issparse(f::Polynomial) = issparse(typeof(f))
isstrictlysparse(f::Polynomial) = isstrictlysparse(typeof(f))

max_variable_index(scheme::InfiniteScheme, f::Polynomial) = iszero(f) ? 0 : maximum(max_variable_index(scheme, t) for t in nzterms(f, monomialorder(f)))

# -----------------------------------------------------------------------------
#
# Iterating over summands
#
# -----------------------------------------------------------------------------
struct Expansion{P <: Polynomial}
    p :: P
end
Base.iterate(ex::Expansion, state...) = iterate(zip(monomials(ex.p), coefficients(ex.p)), state...)
Base.eltype(ex::Expansion) = Tuple{monomialtype(ex.p), basering(ex.p)}
Base.length(ex::Expansion) = length(coefficients(ex.p))
expansion(p::PolynomialBy{Order}, order::Order) where Order<:MonomialOrder = Expansion(p)

struct NZTerms{P <: Polynomial}
    p :: P
end
Base.eltype(it::NZTerms) = termtype(it.p)
Base.length(it::NZTerms) = nztermscount(it.p)
function Base.iterate(it::NZTerms, state=1)
    while true
        state <= length(coefficients(it.p)) || return nothing
        c = coefficients(it.p)[state]
        m = _monomialbyindex(it.p, state)
        (isstrictlysparse(it.p) || !iszero(c)) && return (Term(m, c), state + 1)
        state += 1
    end
    return nothing
end
nzterms(p::PolynomialBy{Order}, order::Order) where Order <: MonomialOrder = NZTerms(p)
nzterms(p::Polynomial; order::MonomialOrder=monomialorder(p)) = nzterms(p, order)

nztermscount(p::Polynomial) = isstrictlysparse(p) ? length(coefficients(p)) : count(!iszero, coefficients(p))

nztailterms(p::PolynomialBy{Order}; order::Order=monomialorder(p)) where Order <: MonomialOrder = (
    Term(_monomialbyindex(p, ix), coefficients(p)[ix])
    for ix in reverse(1:_leading_term_ix(p, order) - 1) if
    isstrictlysparse(p) || !iszero(coefficients(p)[ix])
)
nzrevterms(p::PolynomialBy{Order}; order::Order=monomialorder(p)) where Order <: MonomialOrder = (
    Term(_monomialbyindex(p, ix), coefficients(p)[ix])
    for ix in reverse(1:_leading_term_ix(p, order)) if
    isstrictlysparse(p) || !iszero(coefficients(p)[ix])
)

function leading_term(p::Polynomial; order::MonomialOrder=monomialorder(p))
    ix = _leading_term_ix(p, order)
    Term(_monomialbyindex(p, ix), coefficients(p)[ix])
end
leading_monomial(p::Polynomial; order::MonomialOrder=monomialorder(p)) = _monomialbyindex(p, _leading_term_ix(p, order))
leading_coefficient(p::Polynomial; order::MonomialOrder=monomialorder(p)) = coefficients(p)[_leading_term_ix(p, order)]

monomialorderkey(order, a::Polynomial) = iszero(a) ? nothing : leading_monomial(a, order=order)

tail(p::Polynomial, order::MonomialOrder) = p - leading_term(p; order=order)
tail(p::Polynomial; order::MonomialOrder=monomialorder(p)) = tail(p, order)
# -----------------------------------------------------------------------------
#
# Methods for collection-of-terms
#
# -----------------------------------------------------------------------------
Base.append!(dst::Polynomial, src) = for t in src; push!(dst, t); end
Base.copy!(dst::Polynomial, src) = (append!(empty!(dst), src); dst)
Base.copy!(x::Polynomial, ed::Eduction) = copy!(Transducer(ed), x, ed.coll)


generators(::Type{P}) where P <: Polynomial = map(P, generators(termtype(P)))

"""
    coeff = get(p::PolynomialIn{M}, m::M, default) where M <: AbstractMonomial

The coefficient of `p` at `m`, or `default` if this coefficient is zero.

Typical use will have `default=zero(basering(p))`, (in which case `p[m]` is
equivalent), but there is sometimes a distinct advantage to `default=nothing`.
For example, when `basering(p) == BigInt`, the result `zero(BigInt)` needs
an allocation, and that's wasteful if the caller only wants to do `iszero(...)`.
In this situation, `isnothing(get(p, m, nothing))` is much faster.
"""
function Base.get(p::PolynomialIn{M}, m::M, default) where M <: AbstractMonomial
    if (range = searchsorted(monomials(p), m)) |> !isempty
        ix = first(range)
        if ix <= length(coefficients(p))
            c = coefficients(p)[ix]
            return (isstrictlysparse(p) || !iszero(c)) ? c : default
        end
    end
    return default
end

Base.getindex(p::PolynomialIn{M}, m::M) where M <: AbstractMonomial = get(p, m, zero(basering(p)))

# match the behaviour for Number
# some code treats numbers as collection-like
for Number in [Polynomial, Term, AbstractMonomial]
    @eval begin
        Base.size(x::$Number) = ()
        Base.size(x::$Number, d::Integer) = d < 1 ? throw(BoundsError()) : 1
        Base.axes(x::$Number) = ()
        Base.axes(x::$Number, d::Integer) = d < 1 ? throw(BoundsError()) : OneTo(1)
        Base.eltype(::Type{T}) where {T<:$Number} = T
        Base.ndims(x::$Number) = 0
        Base.ndims(::Type{<:$Number}) = 0
        Base.length(x::$Number) = 1
        Base.firstindex(x::$Number) = 1
        Base.lastindex(x::$Number) = 1
        Base.IteratorSize(::Type{<:$Number}) = HasShape{0}()
        Base.keys(::$Number) = OneTo(1)

        Base.getindex(x::$Number) = x
        function Base.getindex(x::$Number, i::Integer)
            Base.@_inline_meta
            @boundscheck i == 1 || throw(BoundsError())
            x
        end
        function Base.getindex(x::$Number, I::Integer...)
            Base.@_inline_meta
            @boundscheck all(i == 1 for i in I) || throw(BoundsError())
            x
        end
        Base.first(x::$Number) = x
        Base.last(x::$Number) = x
        Base.copy(x::$Number) = x # some code treats numbers as collection-like

        # more of the same "we're secretly a 0-dimensional container,
        # except that these are not defined for Base.Number (but arguably
        # they should be).
        Base.values(x::$Number) = (x,)
        Base.pairs(x::$Number) = ((1, x),)
        Base.getindex(x::$Number, i::CartesianIndex{0}) = x
        Base.keytype(x::$Number) = Int
        Base.valtype(x::$Number) = typeof(x)
        Base.keytype(::Type{<:$Number}) = Int
        Base.valtype(T::Type{<:$Number}) = T
    end
end

# -----------------------------------------------------------------------------
#
# To/from dense representation
#
# -----------------------------------------------------------------------------
function todense(f::Polynomial)
    P = polynomialtype(typeof(f), sparse=false)
    P(f)
end

function tosparse(f::Polynomial)
    P = polynomialtype(typeof(f), sparse=true)
    P(f)
end

# -----------------------------------------------------------------------------
#
# Improve performance for sparse arrays of Polynomials
#
# -----------------------------------------------------------------------------
HigherOrderFns._iszero(f::Polynomial) = iszero(f)

function _debug_isvalid(f::SparsePolynomial)
    length(f.monomials) == length(f.coeffs) &&
    all(!iszero, f.coeffs) &&
    issorted(f.monomials)
end

function _debug_isvalid(f::DensePolynomial)
    true
end

end
