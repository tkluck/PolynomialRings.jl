module NamedPolynomials

import PolynomialRings.Polynomials: Polynomial
import PolynomialRings.Constructors: free_generators

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: promote_rule, convert
import Base: +,*,-,==,zero,one
import PolynomialRings: iszero


"""
    NamedPolynomial{P<:Polynomial, Names}

A type representing variable names + a storage format.
"""
struct NamedPolynomial{P<:Polynomial, Names}
    p::P
end

polynomialtype(::Type{NamedPolynomial{P,Names}}) where P <: Polynomial where Names = P


# -----------------------------------------------------------------------------
#
# Promoting scalars to polynomials
#
# -----------------------------------------------------------------------------

promote_rule(::Type{NP}, ::Type{C}) where NP <: NamedPolynomial{P, Names} where P <: Polynomial where {C,Names} = NamedPolynomial{promote_type(P, C), Names}

convert(::Type{NP}, a::C) where NP <: NamedPolynomial{P, Names} where P <: Polynomial where {C,Names} = NP(convert(promote_type(P,C), a))

# -----------------------------------------------------------------------------
#
# Pass-through operations
#
# -----------------------------------------------------------------------------
+(a::NP,b::NP) where NP <: NamedPolynomial = NP(a.p+b.p)
-(a::NP,b::NP) where NP <: NamedPolynomial = NP(a.p-b.p)
*(a::NP,b::NP) where NP <: NamedPolynomial = NP(a.p*b.p)

==(a::NP,b::NP) where NP <: NamedPolynomial = a.p==b.p
iszero(a::NamedPolynomial) = iszero(a.p)
zero(::Type{NP}) where NP <: NamedPolynomial = NP(zero(polynomialtype(NP)))
one(::Type{NP})  where NP <: NamedPolynomial = NP( one(polynomialtype(NP)))

# -----------------------------------------------------------------------------
#
# Constructing polynomial_rings
#
# -----------------------------------------------------------------------------
function polynomial_ring(basering::Type, symbols::Symbol...)
    Names = Tuple{symbols...}
    gens = free_generators(length(symbols))
    NP = NamedPolynomial{eltype(gens), Names}

    return NP, map(g->NP(g), gens)
end


end
