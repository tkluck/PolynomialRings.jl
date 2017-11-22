module Polynomials

import PolynomialRings.Monomials: TupleMonomial
import PolynomialRings.MonomialOrderings: MonomialOrder
import PolynomialRings.VariableNames: Named, Numbered
import PolynomialRings.Terms: Term

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import PolynomialRings: generators, to_dense_monomials, max_variable_index, basering, monomialtype
import PolynomialRings: leading_term, termtype, monomialorder, terms, exptype, namestype
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

max_variable_index(p::Polynomial) = maximum(max_variable_index(t) for t in terms(p))

leading_term(p::Polynomial) = last(terms(p))

copy(p::Polynomial) = typeof(p)(copy(p.terms))

lt(o::MonomialOrder, a::P,b::P) where P <: Polynomial = lt(o, monomial(leading_term(a)), monomial(leading_term(b)))

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

The `monomialorder` defines an order for the monomials for e.g. Groebner basis computations;
it also defines the internal sort order. Built-in values are `:degrevlex`
and `:deglex`. This function will accept any symbol, though, and you can
define your own monomial order by implementing

    Base.Order.lt(::MonomialOrder{:myorder}, a::M, b::M) where M <: AbstractMonomial

See `PolynomialRings.MonomialOrderings` for examples.

# Examples
```jldoctest
julia> R,(x,y,z) = polynomial_ring(:x, :y, :z)
julia> x*y + z
1 z + 1 x y
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



end
