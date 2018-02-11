module QuotientRings

using Nulls

using PolynomialRings
using PolynomialRings.Polynomials: Polynomial, exptype, leading_term
using PolynomialRings.Terms: Term, monomial, coefficient
using PolynomialRings.Ideals: Ideal, _grb
using PolynomialRings: construct_monomial, variablesymbols

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: promote_rule, convert
import Base: zero, one, rem, copy
import Base: show
import Base: +,-,*,/,//,==,!=
import PolynomialRings: allvariablesymbols
import PolynomialRings.Ideals: ring

# -----------------------------------------------------------------------------
#
# Constructors
#
# -----------------------------------------------------------------------------
struct QuotientRing{P<:Polynomial, ID}
    f::P
    QuotientRing{P,ID}(f::P) where {P,ID} = new(rem(f, _ideal(QuotientRing{P,ID})))
end
ring(::Type{Q}) where Q<:QuotientRing{P} where P = P

function _ideal end
function /(::Type{P}, I::Ideal{P}) where P<:Polynomial
    ID = hash(I)
    R = QuotientRing{P, ID}
    @eval _ideal(::Type{$R}) = $I

    return R
end

/(::Type{P}, I::Ideal) where P<:Polynomial = P / Ideal{P}(I)


# -----------------------------------------------------------------------------
#
# Operations for QuotientRings (mostly pass-through)
#
# -----------------------------------------------------------------------------

zero(::Type{Q}) where Q<:QuotientRing{P} where P<:Polynomial = Q(zero(P))
one(::Type{Q})  where Q<:QuotientRing{P} where P<:Polynomial = Q(one(P))
zero(a::QuotientRing) = zero(typeof(a))
one(a::QuotientRing)  = one(typeof(a))
copy(a::QuotientRing) = a

+(a::QuotientRing) = a
-(a::Q) where Q<:QuotientRing = Q(-a.f)
+(a::Q, b::Q)  where Q<:QuotientRing = Q(a.f+b.f)
-(a::Q, b::Q)  where Q<:QuotientRing = Q(a.f-b.f)
*(a::Q, b::Q)  where Q<:QuotientRing = Q(a.f*b.f)
==(a::Q, b::Q) where Q<:QuotientRing = a.f == b.f
!=(a::Q, b::Q) where Q<:QuotientRing = a.f != b.f
allvariablesymbols(::Type{Q}) where Q<:QuotientRing = allvariablesymbols(ring(Q))

# -----------------------------------------------------------------------------
#
# Conversion and promotion
#
# -----------------------------------------------------------------------------
function promote_rule(::Type{Q}, ::Type{C}) where Q<:QuotientRing{P} where {P<:Polynomial,C}
    rule_for_P = typejoin( promote_rule(P,C), promote_rule(C,P) )
    if rule_for_P === P
        return Q
    else
        return Union{}
    end
end

function convert(::Type{Q}, c::C) where Q<:QuotientRing{P} where {P<:Polynomial,C}
    Q(convert(P, c))
end

convert(::Type{Q}, q::Q) where Q<:QuotientRing{P} where {P<:Polynomial} = q

# -----------------------------------------------------------------------------
#
# Operations through promotion
#
# -----------------------------------------------------------------------------
+(a::QuotientRing, b) = +(promote(a,b)...)
+(a, b::QuotientRing) = +(promote(a,b)...)
-(a::QuotientRing, b) = -(promote(a,b)...)
-(a, b::QuotientRing) = -(promote(a,b)...)
*(a::QuotientRing, b) = *(promote(a,b)...)
*(a, b::QuotientRing) = *(promote(a,b)...)
//(a::QuotientRing, b) = //(promote(a,b)...)
//(a, b::QuotientRing) = //(promote(a,b)...)
==(a::QuotientRing, b) = ==(promote(a,b)...)
==(a, b::QuotientRing) = ==(promote(a,b)...)
!=(a::QuotientRing, b) = !=(promote(a,b)...)
!=(a, b::QuotientRing) = !=(promote(a,b)...)

# -----------------------------------------------------------------------------
#
# Information operations
#
# -----------------------------------------------------------------------------
function monomial_basis(::Type{Q}) where Q<:QuotientRing
    P = ring(Q)
    MAX = typemax(exptype(P))

    leading_monomials = [monomial(leading_term(f)).e for f in _grb(_ideal(Q))]

    # lattice computation: find the monomials that are not divisible
    # by any of the leading terms
    nvars = nfields(eltype(leading_monomials))
    rectangular_bounds = fill(MAX, nvars)
    for m in leading_monomials
        if count(!iszero, m) == 1
            i = findfirst(m)
            rectangular_bounds[i] = min( m[i], rectangular_bounds[i] )
        end
    end

    if !all(b->b<MAX, rectangular_bounds)
        throw("$Q is not a number field; it is infinite dimensional")
    end

    divisible = BitArray(rectangular_bounds...)
    for m in leading_monomials
        block = [(m[i]+1):b for (i,b) in enumerate(rectangular_bounds)]
        setindex!(divisible, true, block...)
    end

    return [tuple([i-1 for i in ind2sub(divisible,i)]...) for i in eachindex(divisible) if !divisible[i]]
end

function representation_matrix(::Type{Q}, x::Symbol) where Q<:QuotientRing
    P = ring(Q)
    xs = variablesymbols(P)

    basis_exponents = monomial_basis(Q)
    basis = map(e->Q(construct_monomial(P,e)), basis_exponents)

    left_action = Q(P(x)) .* basis
    columns = map(v->coefficient.(v.f,basis_exponents,xs...), left_action)
    hcat(columns...)
end

function representation_matrix(::Type{Q}, f) where Q<:QuotientRing
    P = ring(Q)
    xs = variablesymbols(P)
    matrices = representation_matrix.(Q,xs)
    reduce(+, zero(matrices[1]),
        coeff*prod(matrices.^exp)
        for (exp,coeff) in expansion(f, xs...)
    )
end

# -----------------------------------------------------------------------------
#
# Friendly display
#
# -----------------------------------------------------------------------------

function show(io::IO, x::QuotientRing)
    print(io, x.f)
end

end
