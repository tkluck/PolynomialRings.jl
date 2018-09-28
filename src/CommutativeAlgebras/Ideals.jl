module Ideals

using PolynomialRings.Polynomials: Polynomial
using PolynomialRings: gröbner_basis, gröbner_transformation

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: promote_rule, convert
import Base: zero, one, in, div, rem, divrem, rem, issubset, inv
import Base: +,-,*,^,/,//,==,!=, hash
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
    _grb::Union{Nothing, AbstractVector}
    _trns::Union{Nothing, AbstractMatrix}
end
Ideal(generators::AbstractVector{<:Polynomial}) = Ideal(generators, nothing, nothing)
Ideal(generators::Polynomial...) = Ideal(collect(generators), nothing, nothing)

ring(I::Ideal{P}) where P<:Polynomial = P

# -----------------------------------------------------------------------------
#
# On-demand computed helper data
#
# -----------------------------------------------------------------------------

generators(I::Ideal) = I.generators
function _grb(I::Ideal)
    if I._grb === nothing
        I._grb = gröbner_basis(I.generators)
    end
    I._grb
end
function _grb_trns(I::Ideal)
    if I._trns === nothing
        I._grb, I._trns = gröbner_transformation(I.generators)
    end
    I._grb, I._trns
end

# -----------------------------------------------------------------------------
#
# Operations
#
# -----------------------------------------------------------------------------
function divrem(f, I::Ideal)
    G, T = _grb_trns(I)
    d, r = divrem(f, G)
    d*T, r
end

div(f, I::Ideal) = divrem(f, I)[1]
rem(f, I::Ideal) = rem(ring(I)(f), _grb(I))
in(f, I::Ideal) = iszero(rem(f, I))

issubset(I::Ideal{P}, J::Ideal{P}) where P<:Polynomial = all(g in J for g in generators(I))
==(I::Ideal{P}, J::Ideal{P}) where P<:Polynomial = I⊆J && J⊆I

+(I::Ideal{P}, J::Ideal{P}) where P<:Polynomial = Ideal([generators(I);generators(J)])
*(I::Ideal{P}, J::Ideal{P}) where P<:Polynomial = Ideal([
    i*j for i in generators(I) for j in generators(J)
])
^(I::Ideal, n::Integer) = Base.power_by_squaring(I,n)

hash(I::Ideal, h::UInt) = hash(I.generators, h)

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
