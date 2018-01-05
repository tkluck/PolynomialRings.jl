module Polynomials

import PolynomialRings.Monomials: AbstractMonomial, TupleMonomial, VectorMonomial
import PolynomialRings.MonomialOrderings: MonomialOrder
import PolynomialRings.VariableNames: Named, Numbered
import PolynomialRings.Terms: Term, monomial, coefficient

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import PolynomialRings: generators, to_dense_monomials, max_variable_index, basering, monomialtype
import PolynomialRings: leading_term, termtype, monomialorder, terms, exptype, namestype
import PolynomialRings: leading_coefficient, leading_monomial
import PolynomialRings: variablesymbols, allvariablesymbols
import Base: copy, hash
import Base.Order: lt
import PolynomialRings.MonomialOrderings: MonomialOrder

# -----------------------------------------------------------------------------
#
# Polynomial
#
# -----------------------------------------------------------------------------

"""
    Polynomial{A, Order} where A <: AbstractVector{T} where T <: Term where Order <: Val

This type represents a polynomial as a vector of terms. All methods guarantee and assume
that the vector is sorted by increasing monomial order, according to `Order` (see
`PolynomialRings.MonomialOrderings`).
"""
struct Polynomial{A, Order}
    terms::A
    Polynomial{A, Order}(terms::A) where A <: AbstractVector{T} where T <: Term where Order = new(terms)
end

# -----------------------------------------------------------------------------
#
# Type shorthands
#
# -----------------------------------------------------------------------------

const NamedMonomial                 = AbstractMonomial{<:Named}
const NumberedMonomial              = AbstractMonomial{<:Numbered}
const PolynomialOver{C,Names,Order} = Polynomial{<:AbstractVector{<:Term{<:AbstractMonomial{Names}, C}},Order}
const NamedPolynomial{C,Order}      = PolynomialOver{C,<:Named,Order}
const NumberedPolynomial{C,Order}   = PolynomialOver{C,<:Numbered,Order}
const PolynomialBy{Names,Order,C}   = PolynomialOver{C,Names,Order}

# -----------------------------------------------------------------------------
#
# Type information
#
# -----------------------------------------------------------------------------

terms(p::Polynomial) = p.terms

termtype(::Type{Polynomial{A, Order}}) where {A,Order} = eltype(A)
exptype(::Type{P}) where P<:Polynomial = exptype(termtype(P))
namestype(::Type{P}) where P<:Polynomial = namestype(termtype(P))
monomialorder(::Type{Polynomial{A, Order}}) where {A,Order} = MonomialOrder{Order}()
monomialordersymbol(::Type{Polynomial{A, Order}}) where {A,Order} = Order
monomialordersymbol(::Polynomial{A, Order}) where {A,Order} = Order
basering(::Type{P}) where P <: Polynomial = basering(termtype(P))
monomialtype(::Type{P}) where P <: Polynomial = monomialtype(termtype(P))
allvariablesymbols(::Type{P}) where P <: Polynomial = union(allvariablesymbols(basering(P)), variablesymbols(P))

hash(p::Polynomial, h::UInt) = hash(p.terms, h)

import PolynomialRings.Util: lazymap
generators(::Type{P}) where P <: Polynomial = lazymap(
    g->P([g]), generators(termtype(P))
)

function to_dense_monomials(n, p::Polynomial)
    A = [ to_dense_monomials(n, t) for t in terms(p) ]
    return Polynomial{typeof(A), monomialordersymbol(p)}(A)
end

max_variable_index(p::Polynomial) = iszero(p) ? 0 : maximum(max_variable_index(t) for t in terms(p))

leading_term(::MonomialOrder{Order}, p::PolynomialBy{Names,Order}) where {Names,Order} = last(terms(p))
leading_term(o::MonomialOrder, p::Polynomial) = maximum(o, terms(p))
leading_term(p::Polynomial) = leading_term(monomialorder(p), p)

leading_monomial(o::MonomialOrder, p::Polynomial) = monomial(leading_term(o, p))
leading_monomial(p::Polynomial) = monomial(leading_term(p))

leading_coefficient(o::MonomialOrder, p::Polynomial) = coefficient(leading_term(o, p))
leading_coefficient(p::Polynomial) = coefficient(leading_term(p))

copy(p::Polynomial) = typeof(p)(copy(p.terms))

lt(o::MonomialOrder, a::P, b::P) where P <: Polynomial = lt(o, leading_monomial(o, a), leading_monomial(o, b))

# -----------------------------------------------------------------------------
#
# Constructor function
#
# -----------------------------------------------------------------------------
"""
    polynomial_ring(symbols::Symbol...; basering=Rational{BigInt}, exptype=UInt16, monomialorder=:degrevlex)

Create a type for the polynomial ring over `basering` in variables with names
specified by `symbols`, and return the type and a tuple of these variables.

The `exptype` parameter defines the integer type for the exponents.

The `monomialorder` defines an order for the monomials for e.g. Gröbner basis computations;
it also defines the internal sort order. Built-in values are `:degrevlex`
and `:deglex`. This function will accept any symbol, though, and you can
define your own monomial order by implementing

    Base.Order.lt(::MonomialOrder{:myorder}, a::M, b::M) where M <: AbstractMonomial

See `PolynomialRings.MonomialOrderings` for examples.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R,(x,y,z) = polynomial_ring(:x, :y, :z);

julia> x*y + z
z + x*y
```
"""
function polynomial_ring(symbols::Symbol...; basering::Type=Rational{BigInt}, exptype::Type=UInt16, monomialorder::Symbol=:degrevlex)
    length(symbols)>0 || throw(ArgumentError("Need at least one variable name"))
    if any(s in allvariablesymbols(basering) for s in symbols) || !allunique(symbols)
        throw(ArgumentError("Duplicated symbols when extending $basering by $(Named{symbols})"))
    end

    P = Polynomial{Vector{Term{TupleMonomial{length(symbols),exptype, Named{symbols}}, basering}}, monomialorder}
    return P, generators(P)
end

function numbered_polynomial_ring(symbol::Symbol; basering::Type=Rational{BigInt}, exptype::Type=UInt16, monomialorder::Symbol=:degrevlex)
    if symbol in allvariablesymbols(basering)
        throw(ArgumentError("Duplicated symbols when extending $basering by $(Numbered{symbol})"))
    end

    P = Polynomial{Vector{Term{VectorMonomial{SparseVector{exptype,Int}, exptype, Numbered{symbol}}, basering}}, monomialorder}
    return P
end



end
