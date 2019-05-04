module Polynomials

import Base: first, last, copy, hash, pairs
import SparseArrays: SparseVector, HigherOrderFns, issparse

import ..MonomialOrderings: MonomialOrder
import ..Monomials: AbstractMonomial, TupleMonomial, VectorMonomial
import ..NamingSchemes: Named, Numbered, NamingScheme, fullnamingscheme, isdisjoint, isvalid
import ..Terms: Term, monomial, coefficient
import PolynomialRings: generators, to_dense_monomials, max_variable_index, basering, monomialtype
import PolynomialRings: leading_coefficient, leading_monomial
import PolynomialRings: leading_term, termtype, monomialorder, nzterms, exptype, namingscheme
import PolynomialRings: tail
import PolynomialRings: variablesymbols, allvariablesymbols, fullboundnames
import PolynomialRings: polynomialtype

# -----------------------------------------------------------------------------
#
# Polynomial
#
# -----------------------------------------------------------------------------

"""
    Polynomial{M, C} where M <: AbstractMonomial where C

This type represents a polynomial as a vector of monomials
and a vector of coefficients. All methods guarantee and assume
that the vector is sorted by increasing monomial order (see
`PolynomialRings.MonomialOrderings`).
"""
struct Polynomial{M <: AbstractMonomial, C, MonomVector}
    monomials::MonomVector
    coeffs::Vector{C}
end

Polynomial(monomials, coeffs::Vector) = Polynomial{eltype(monomials), eltype(coeffs), typeof(monomials)}(monomials, coeffs)

polynomialtype(M::Type{<:AbstractMonomial}, C::Type) = Polynomial{M, C, Vector{M}}

# -----------------------------------------------------------------------------
#
# Type shorthands
#
# -----------------------------------------------------------------------------

const NamedOrder              = MonomialOrder{Rule,<:Named}    where Rule
const NumberedOrder           = MonomialOrder{Rule,<:Numbered} where Rule
const NamedMonomial           = AbstractMonomial{<:NamedOrder}
const NumberedMonomial        = AbstractMonomial{<:NumberedOrder}
const TermOver{C,Order}       = Term{<:AbstractMonomial{Order}, C}
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

isstrictlysparse(P::Type{<:Polynomial}) = monomialstype(P) <: Vector
isstrictlysparse(f::Polynomial) = isstrictlysparse(typeof(f))
issparse(P::Type{<:Polynomial}) = monomialstype(P) <: Vector
issparse(f::Polynomial) = issparse(typeof(f))


pairs(p::PolynomialBy{Order}, order::Order) where Order<:MonomialOrder = zip(p.monomials, p.coeffs)
pairs(p::Polynomial; order::MonomialOrder=monomialorder(p)) = pairs(p, order)

nztermscount(p::Polynomial) = isstrictlysparse(p) ? length(p.coeffs) : count(!iszero, p.coeffs)

nzterms(p::PolynomialBy{Order}, order::Order) where Order <: MonomialOrder = (
    Term(m, c)
    for (m, c) in pairs(p, order) if
    isstrictlysparse(p) || !iszero(c)
)
nzterms(p::Polynomial; order::MonomialOrder=monomialorder(p)) = nzterms(p, order)

nztailterms(p::PolynomialBy{Order}; order::Order=monomialorder(p)) where Order <: MonomialOrder = (
    Term(p.monomials[ix], p.coeffs[ix])
    for ix in reverse(1:_leading_term_ix(p, order) - 1) if
    isstrictlysparse(p) || !iszero(p.coeffs[ix])
)
nzrevterms(p::PolynomialBy{Order}; order::Order=monomialorder(p)) where Order <: MonomialOrder = (
    Term(p.monomials[ix], p.coeffs[ix])
    for ix in reverse(1:_leading_term_ix(p, order)) if
    isstrictlysparse(p) || !iszero(p.coeffs[ix])
)

termtype(::Type{Polynomial{M,C,MV}}) where {M,C,MV}  = Term{M,C}
monomialstype(::Type{Polynomial{M,C,MV}}) where {M,C,MV} = MV
exptype(::Type{P}, scheme::NamingScheme...) where P<:Polynomial = exptype(termtype(P), scheme...)
namingscheme(::Type{P}) where P<:Polynomial = namingscheme(termtype(P))
monomialorder(::Type{P}) where P<:Polynomial = monomialorder(termtype(P))
basering(::Type{P}) where P <: Polynomial = basering(termtype(P))
monomialtype(::Type{P}) where P <: Polynomial = monomialtype(termtype(P))
allvariablesymbols(::Type{P}) where P <: Polynomial = union(allvariablesymbols(basering(P)), variablesymbols(P))

hash(p::Polynomial, h::UInt) = hash(p.monomials, hash(p.coeffs, h))

generators(::Type{P}) where P <: Polynomial = map(P, generators(termtype(P)))

function to_dense_monomials(n, p::Polynomial)
    coeffs = map(deepcopy, p.coeffs)
    monomials = to_dense_monomials.(n, p.monomials)
    return Polynomial(monomials, coeffs)
end

# FIXME: allow for infinite-length p.monomials
max_variable_index(p::Polynomial) = iszero(p) ? 0 : maximum(max_variable_index(m) for m in p.monomials)

_leading_term_ix(p::Polynomial, order::MonomialOrder) = argmax(order, p.monomials)
_leading_term_ix(p::PolynomialBy{Order}, order::Order) where Order <: MonomialOrder = isstrictlysparse(p) ? length(p.coeffs) : findlast(!iszero, p.coeffs)
function leading_term(p::Polynomial; order::MonomialOrder=monomialorder(p))
    ix = _leading_term_ix(p, order)
    Term(p.monomials[ix], p.coeffs[ix])
end
leading_monomial(p::Polynomial; order::MonomialOrder=monomialorder(p)) = p.monomials[_leading_term_ix(p, order)]
leading_coefficient(p::Polynomial; order::MonomialOrder=monomialorder(p)) = p.coeffs[_leading_term_ix(p, order)]

function tail(p::PolynomialBy{Order}, order::Order) where Order <: MonomialOrder
    ix = _leading_term_ix(p, order)
    typeof(p)(p.monomials[1:ix-1], p.coeffs[1:ix-1])
end
tail(p::Polynomial, order::MonomialOrder) = p - leading_term(p; order=order)
tail(p::Polynomial; order::MonomialOrder=monomialorder(p)) = tail(p, order)

function Base.getindex(p::PolynomialIn{M}, m::M) where M <: AbstractMonomial
    if (range = searchsorted(p.monomials, m)) |> !isempty
        ix = first(range)
        if ix <= length(p.coeffs)
            return p.coeffs[ix]
        end
    end
    return zero(basering(p))
end

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
function polynomial_ring(symbols::Symbol...; basering::Type=Rational{BigInt}, exptype::Type=Int16, monomialorder::Symbol=:degrevlex)
    length(symbols) > 0 || throw(ArgumentError("Need at least one variable name"))
    allunique(symbols) || throw(ArgumentError("Duplicated symbols when extending $basering by $(Named{symbols}())"))
    scheme = Named{symbols}()
    P = polynomial_ring(scheme, basering=basering, exptype=exptype, monomialorder=monomialorder)
    return P, generators(P)
end

function numbered_polynomial_ring(symbol::Symbol; basering::Type=Rational{BigInt}, exptype::Type=Int16, monomialorder::Symbol=:degrevlex)
    scheme =  Numbered{symbol, Inf}()
    P = polynomial_ring(scheme, basering=basering, exptype=exptype, monomialorder=monomialorder)
    return P
end

function numbered_polynomial_ring(symbol::Symbol, n::Integer; basering::Type=Rational{BigInt}, exptype::Type=Int16, monomialorder::Symbol=:degrevlex)
    scheme =  Numbered{symbol, n}()
    P = polynomial_ring(scheme, basering=basering, exptype=exptype, monomialorder=monomialorder)
    return P, generators(P)
end

function polynomial_ring(scheme::NamingScheme; basering::Type=Rational{BigInt}, exptype::Type=Int16, monomialorder::Symbol=:degrevlex)
    if !isdisjoint(scheme, fullnamingscheme(basering)) || !isdisjoint(scheme, fullboundnames(basering)) || !isvalid(scheme)
        throw(ArgumentError("Duplicated symbols when extending $basering by $scheme"))
    end
    order = MonomialOrder{monomialorder, typeof(scheme)}()
    M = monomialtype(order, exptype)
    return polynomialtype(M, basering)
end

# -----------------------------------------------------------------------------
#
# Improve performance for sparse arrays of Polynomials
#
# -----------------------------------------------------------------------------
HigherOrderFns._iszero(f::Polynomial) = iszero(f)

end
