module Ideals

using Nulls
using PolynomialRings.Polynomials: Polynomial
using PolynomialRings.Groebner: groebner_transformation

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: promote_rule, convert
import Base: zero, one, in, rem, issubset, inv
import Base: +,-,*,/,//,==,!=
import Base: show
import PolynomialRings: generators, expansion
import PolynomialRings: allvariablesymbols, fraction_field
import PolynomialRings.Expansions: _expansion

# -----------------------------------------------------------------------------
#
# Constructors
#
# -----------------------------------------------------------------------------

mutable struct Ideal{P<:Polynomial}
    generators::AbstractVector{P}
    _grb::Union{Null, AbstractVector}
    _trns::Union{Null, AbstractMatrix}
end
Ideal(generators::AbstractVector{<:Polynomial}) = Ideal(generators, null, null)
Ideal(generators::Polynomial...) = Ideal(collect(generators), null, null)

ring(I::Ideal{P}) where P<:Polynomial = P

# -----------------------------------------------------------------------------
#
# On-demand computed helper data
#
# -----------------------------------------------------------------------------

generators(I::Ideal) = I.generators
function _grb(I::Ideal)
    if isnull(I._grb)
        I._grb, I._trns = groebner_transformation(I.generators)
    end
    I._grb
end
function _trns(I::Ideal)
    if isnull(I._grb)
        I._grb, I._trns = groebner_transformation(I.generators)
    end
    I._trns
end

# -----------------------------------------------------------------------------
#
# Operations
#
# -----------------------------------------------------------------------------
rem(f, I::Ideal) = rem(ring(I)(f), _grb(I))
in(f, I::Ideal) = iszero(rem(f, I))

issubset(I::Ideal{P}, J::Ideal{P}) where P<:Polynomial = all(g in J for g in generators(I))
==(I::Ideal{P}, J::Ideal{P}) where P<:Polynomial = I⊆J && J⊆I

# -----------------------------------------------------------------------------
#
# Conversions
#
# -----------------------------------------------------------------------------
function convert(::Type{Ideal{P1}}, I::Ideal{P2}) where {P1<:Polynomial, P2<:Polynomial}
    return Ideal(map(P1, generators(I)))
end

# -----------------------------------------------------------------------------
#
# Display
#
# -----------------------------------------------------------------------------
show(io::IO, I::Ideal) = show(io, tuple(I.generators...))


end
