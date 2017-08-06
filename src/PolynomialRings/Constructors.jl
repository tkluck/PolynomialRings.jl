module Constructors

import PolynomialRings: generators, base_extend
import PolynomialRings.Polynomials: Polynomial
import PolynomialRings.NamedPolynomials: NamedPolynomial, names, polynomialtype
import PolynomialRings.Terms: Term, basering
import PolynomialRings.Monomials: TupleMonomial, VectorMonomial
import PolynomialRings.Util: lazymap

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: convert

# -----------------------------------------------------------------------------
#
# Constructing polynomial_rings
#
# -----------------------------------------------------------------------------
"""
    polynomial_ring(basering::Type, symbols::Symbol...)

Create a type for the polynomial ring over `basering` in variables with names
specified by `symbols`, and return the type and a tuple of these variables.

# Examples
```jldoctest
julia> R,(x,y,z) = polynomial_ring(Int, :x, :y, :z)
julia> x*y + z
1 z + 1 x y
```
"""
function polynomial_ring(basering::Type, symbols::Symbol...)
    length(symbols)>0 || throw(ArgumentError("Need at least one variable name"))

    P = Polynomial{Vector{Term{TupleMonomial{length(symbols),Int16}, basering}}, :degrevlex}
    gens = generators(P)
    NP = NamedPolynomial{P, symbols}

    return NP, map(g->NP(g), gens)
end

function convert(::Type{NP}, x::Symbol) where NP<:NamedPolynomial
    T = names(NP)
    for (i,s) in enumerate(T)
        if s == x
            return NP(generators(polynomialtype(NP))[i])
        end
    end
    throw(ArgumentError("Variable $x does not appear in $NP"))
end

"""
    formal_coefficients(R, name::Symbol)

Return a `Channel` with formal coefficients for the polynomial ring `R`.

Formal coefficients means that these are generators for a polynomial ring
`C` with an unbounded number of variables, and this polynomial ring is used
(through base extension) as the coefficients for `R`.

In other words, the channel yields `c_i⊗ 1` for generators `c_i ∈ C` and `1 ∈ R`.

# Examples
```jldoctest
julia> R,(x,) = polynomial_ring(Int, :x);
julia> coeffs = formal_coefficients(R, :c);
julia> c() = take!(coeffs);
julia> [c()*x^2 + c()*x + c() , c()*x^2 + c()*x + c()]
2-element Array{(Polynomial over (Polynomial over Int64 in c0) in x),1}:
 1 c3 + 1 c2 x + 1 c1 x^2
 1 c6 + 1 c5 x + 1 c4 x^2
```
"""
function formal_coefficients(::Type{NP}, name::Symbol) where NP <: NamedPolynomial
    _C = Polynomial{Vector{Term{VectorMonomial{SparseVector{Int16,Int}}, Int}}, :degrevlex}
    CC = NamedPolynomial{_C, name}

    PP = base_extend(NP, CC)
    C = basering(PP)
    P = polynomialtype(C)

    return lazymap(g->PP(C(g)), generators(P))
end


end
