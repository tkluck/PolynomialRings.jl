module Polynomials

import Base: first, last, copy, hash, convert
import Base: zero, one, +, -, *, ==, div, iszero, diff, ^, gcd
import Base: OneTo
import SparseArrays: SparseVector, HigherOrderFns, issparse

import InPlace: @inplace, inplace!, inclusiveinplace!
import Transducers: Transducer, Eduction

import ..MonomialOrderings: MonomialOrder
import ..Monomials: AbstractMonomial, TupleMonomial, VectorMonomial
import ..IndexedMonomials: IndexedMonomial
import ..NamingSchemes: Named, Numbered, NamingScheme, fullnamingscheme, isdisjoint, isvalid
import ..Terms: Term, monomial, coefficient
import ..Util: @assertvalid, _debug_isvalid
import PolynomialRings: generators, to_dense_monomials, max_variable_index, basering, monomialtype
import PolynomialRings: leading_coefficient, leading_monomial
import PolynomialRings: leading_term, termtype, monomialorder, nzterms, exptype, namingscheme, expansion
import PolynomialRings: tail
import PolynomialRings: variablesymbols, allvariablesymbols, fullboundnames
import PolynomialRings: polynomialtype

# -----------------------------------------------------------------------------
#
# Type shorthands I
#
# -----------------------------------------------------------------------------

const NamedOrder              = MonomialOrder{Rule,<:Named}    where Rule
const NumberedOrder           = MonomialOrder{Rule,<:Numbered} where Rule
const NamedMonomial           = AbstractMonomial{<:NamedOrder}
const NumberedMonomial        = AbstractMonomial{<:NumberedOrder}
const MonomialBy{Order}       = AbstractMonomial{Order}
const TermOver{C,Order}       = Term{<:AbstractMonomial{Order}, C}
const TermBy{Order,C}        = TermOver{C,Order}
const TermIn{M}              = Term{M}

include("SparsePolynomials.jl")
include("DensePolynomials.jl")

const Polynomial{M, C} = Union{SparsePolynomial{M, C}, DensePolynomial{M, C}}

function polynomialtype(M::Type{<:AbstractMonomial}, C::Type; sparse=true)
    if !isdisjoint(namingscheme(M), fullnamingscheme(C)) || !isdisjoint(namingscheme(M), fullboundnames(C))
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
# Type shorthands II
#
# -----------------------------------------------------------------------------

const PolynomialOver{C,Order} = Polynomial{<:AbstractMonomial{Order}, C}
const NamedTerm{C}            = TermOver{C,<:NamedOrder}
const NumberedTerm{C}         = TermOver{C,<:NumberedOrder}
const NamedPolynomial{C}      = PolynomialOver{C,<:NamedOrder}
const NumberedPolynomial{C}   = PolynomialOver{C,<:NumberedOrder}
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

tail(p::Polynomial, order::MonomialOrder) = p - leading_term(p; order=order)
tail(p::Polynomial; order::MonomialOrder=monomialorder(p)) = tail(p, order)
# -----------------------------------------------------------------------------
#
# Methods for collection-of-terms
#
# -----------------------------------------------------------------------------
Base.append!(dst::Polynomial, src) = for t in src; push!(dst, t); end
Base.copy!(dst::Polynomial, src) = append!(empty!(dst), src)
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

function Base.Order.lt(order::MonomialOrder, a::P, b::P) where P <: Polynomial
    iszero(b) && return false
    iszero(a) && return true
    Base.Order.lt(order, leading_monomial(a, order=order), leading_monomial(b, order=order))
end

# -----------------------------------------------------------------------------
#
# Constructor function
#
# -----------------------------------------------------------------------------
"""
    polynomial_ring(symbols::Symbol...; basering=Rational{BigInt}, exptype=Int16, monomialorder=:degrevlex)

Create a type for the polynomial ring over `basering` in variables with names
specified by `symbols`, and return the type and a tuple of these variables.

The `exptype` parameter defines the integer type for the exponents.

The `monomialorder` defines an order for the monomials for e.g. Gröbner basis computations;
it also defines the internal sort order. Built-in values are `:degrevlex`,
`:deglex` and `:lex`. This function will accept any symbol, though, and you can
define your own monomial order by implementing

    Base.Order.lt(::MonomialOrder{:myorder}, a::M, b::M) where M <: AbstractMonomial

See `PolynomialRings.MonomialOrderings` for examples.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R,(x,y,z) = polynomial_ring(:x, :y, :z);

julia> x*y + z
x*y + z
```
"""
function polynomial_ring(symbols::Symbol...; basering::Type=Rational{BigInt}, exptype::Type=Int16, monomialorder::Symbol=:degrevlex, sparse=true)
    length(symbols) > 0 || throw(ArgumentError("Need at least one variable name"))
    allunique(symbols) || throw(ArgumentError("Duplicated symbols when extending $basering by $(Named{symbols}())"))
    scheme = Named{symbols}()
    P = polynomial_ring(scheme, basering=basering, exptype=exptype, monomialorder=monomialorder, sparse=sparse)
    return P, generators(P)
end

function numbered_polynomial_ring(symbol::Symbol; basering::Type=Rational{BigInt}, exptype::Type=Int16, monomialorder::Symbol=:degrevlex, sparse=sparse)
    scheme =  Numbered{symbol, Inf}()
    P = polynomial_ring(scheme, basering=basering, exptype=exptype, monomialorder=monomialorder, sparse=sparse)
    return P
end

function numbered_polynomial_ring(symbol::Symbol, n::Integer; basering::Type=Rational{BigInt}, exptype::Type=Int16, monomialorder::Symbol=:degrevlex, sparse=true)
    scheme =  Numbered{symbol, n}()
    P = polynomial_ring(scheme, basering=basering, exptype=exptype, monomialorder=monomialorder, sparse=sparse)
    return P, generators(P)
end

function polynomial_ring(scheme::NamingScheme; basering::Type=Rational{BigInt}, exptype::Type=Int16, monomialorder::Symbol=:degrevlex, sparse=true)
    if !isdisjoint(scheme, fullnamingscheme(basering)) || !isdisjoint(scheme, fullboundnames(basering)) || !isvalid(scheme)
        throw(ArgumentError("Duplicated symbols when extending $basering by $scheme"))
    end
    order = MonomialOrder{monomialorder, typeof(scheme)}()
    M = monomialtype(order, exptype)
    return polynomialtype(M, basering, sparse=sparse)
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
