module Polynomials

import Base: first, last, copy, hash
import SparseArrays: SparseVector

import ..MonomialOrderings: MonomialOrder
import ..MonomialOrderings: MonomialOrder
import ..Monomials: AbstractMonomial, TupleMonomial, VectorMonomial
import ..Terms: Term, monomial, coefficient
import ..Util: lazymap
import ..NamingSchemes: Named, Numbered, NamingScheme, fullnamingscheme, isdisjoint, isvalid
import PolynomialRings: generators, to_dense_monomials, max_variable_index, basering, monomialtype
import PolynomialRings: leading_coefficient, leading_monomial
import PolynomialRings: leading_term, termtype, monomialorder, terms, exptype, namingscheme
import PolynomialRings: tail
import PolynomialRings: variablesymbols, allvariablesymbols, fullboundnames

# -----------------------------------------------------------------------------
#
# Polynomial
#
# -----------------------------------------------------------------------------

"""
    Polynomial{T} where T <: Term

This type represents a polynomial as a vector of terms. All methods guarantee and assume
that the vector is sorted by increasing monomial order (see
`PolynomialRings.MonomialOrderings`).
"""
struct Polynomial{M,C}
    terms::Vector{Term{M,C}}
    Polynomial{M,C}(terms::Vector{Term{M,C}}) where {M,C} = new(terms)
end

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

nterms(p::Polynomial) = length(p.terms)

terms(p::PolynomialBy{Order}, order::Order) where Order<:MonomialOrder = p.terms
terms(p::Polynomial, order::MonomialOrder)                  = sort(p.terms, order=order)
terms(p::Polynomial; order::MonomialOrder=monomialorder(p)) = terms(p, order)

termtype(::Type{Polynomial{M,C}}) where {M,C}  = Term{M,C}
exptype(::Type{P}) where P<:Polynomial = exptype(termtype(P))
namingscheme(::Type{P}) where P<:Polynomial = namingscheme(termtype(P))
monomialorder(::Type{P}) where P<:Polynomial = monomialorder(termtype(P))
basering(::Type{P}) where P <: Polynomial = basering(termtype(P))
monomialtype(::Type{P}) where P <: Polynomial = monomialtype(termtype(P))
allvariablesymbols(::Type{P}) where P <: Polynomial = union(allvariablesymbols(basering(P)), variablesymbols(P))

hash(p::Polynomial, h::UInt) = hash(p.terms, h)

generators(::Type{P}) where P <: Polynomial = lazymap(
    g->P([g]), generators(termtype(P))
)

function to_dense_monomials(n, p::Polynomial)
    A = [ to_dense_monomials(n, t) for t in terms(p, order=monomialorder(p)) ]
    T = eltype(A)
    M = monomialtype(T)
    C = basering(T)
    return Polynomial{M,C}(A)
end

max_variable_index(p::Polynomial) = iszero(p) ? 0 : maximum(max_variable_index(t) for t in terms(p))


leading_term(p::Polynomial; order::MonomialOrder=monomialorder(p)) = last(terms(p, order=order))
leading_monomial(p::Polynomial; order::MonomialOrder=monomialorder(p)) = monomial(leading_term(p, order=order))
leading_coefficient(p::Polynomial; order::MonomialOrder=monomialorder(p)) = coefficient(leading_term(p, order=order))

tail(p::PolynomialBy{Order}, order::Order) where Order <: MonomialOrder = typeof(p)(p.terms[1:end-1])
tail(p::Polynomial, order::MonomialOrder) = p - leading_term(p; order=order)
tail(p::Polynomial; order::MonomialOrder=monomialorder(p)) = tail(p, order)

_monomial(m::AbstractMonomial) = m
_monomial(m) = monomial(m)
function Base.getindex(p::PolynomialIn{M}, m::M) where M <: AbstractMonomial
    if (range = searchsorted(p.terms, m, by=_monomial)) |> !isempty
        ix = first(range)
        return coefficient(p.terms[ix])
    else
        return zero(basering(p))
    end
end

# match the behaviour for Number
first(p::Polynomial) = p
last(p::Polynomial) = p
copy(p::Polynomial) = p

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
    return Polynomial{M, basering}
end

end
