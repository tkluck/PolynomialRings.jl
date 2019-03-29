module QuotientRings

using PolynomialRings
import Base: +,-,*,/,//,^,==,!=
import Base: promote_rule, convert
import Base: show
import Base: zero, one, rem, copy

import ..Ideals: Ideal, _grb
import ..Ideals: ring
import ..NamingSchemes: boundnames, fullboundnames, namingscheme, fullnamingscheme
import ..NamedPolynomials: minring
import ..Polynomials: Polynomial, exptype, leading_term, basering, PolynomialOver
import ..Polynomials: termtype, monomialtype
import ..Terms: Term, monomial, coefficient
import PolynomialRings: allvariablesymbols
import PolynomialRings: construct_monomial, variablesymbols

# -----------------------------------------------------------------------------
#
# Constructors
#
# -----------------------------------------------------------------------------
struct QuotientRing{P<:Polynomial, ID}
    f::P
    QuotientRing{P,ID}(f::P) where {P,ID} = new(rem(f, _ideal(QuotientRing{P,ID})))
end
ring(::Type{<:QuotientRing{P}}) where P = P

const _ideals = Dict()
_ideal(R) = _ideals[R]
function /(::Type{P}, I::Ideal{P}) where P<:Polynomial
    ID = hash(I)
    R = QuotientRing{P, ID}

    if !haskey(_ideals, R)
        _ideals[R] = I
    end

    return R
end

/(::Type{P}, I) where P<:Polynomial = P / Ideal{P}(map(P, I))


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
-(a::Q)                       where Q<:QuotientRing = Q(-a.f)
+(a::Q, b::Q)                 where Q<:QuotientRing = Q(a.f+b.f)
-(a::Q, b::Q)                 where Q<:QuotientRing = Q(a.f-b.f)
*(a::Q, b::Q)                 where Q<:QuotientRing = Q(a.f*b.f)
^(a::Q, n::Integer)           where Q<:QuotientRing = Base.power_by_squaring(a, n)
==(a::Q, b::Q)                where Q<:QuotientRing = a.f == b.f
!=(a::Q, b::Q)                where Q<:QuotientRing = a.f != b.f
allvariablesymbols(::Type{Q}) where Q<:QuotientRing = allvariablesymbols(ring(Q))
# boundnames and fullboundnames return the same result: need to assume all
# variables may appear in _ideal(Q).
boundnames(::Type{Q})         where Q<:QuotientRing = fullnamingscheme(ring(Q))
fullboundnames(::Type{Q})     where Q<:QuotientRing = fullnamingscheme(ring(Q))

# -----------------------------------------------------------------------------
#
# Conversion and promotion
#
# -----------------------------------------------------------------------------
@generated function promote_rule(::Type{Q}, ::Type{C}) where Q<:QuotientRing{P} where {P<:Polynomial,C<:Number}
    P′ = promote_rule(P, C)
    if P′ !== Union{} && P′ <: Polynomial
        I = Ideal(map(P′, _ideal(Q)))
        res = P′/I
    else
        res = Union{}
    end
    :( $res )
end

@generated function promote_rule(::Type{Q1}, ::Type{Q2}) where {Q1 <: QuotientRing, Q2 <: QuotientRing}
    P = promote_type(ring(Q1), ring(Q2))
    I = Ideal(map(P, _ideal(Q1))) + Ideal(map(P, _ideal(Q2)))
    res = P/I
    :( $res )
end

function convert(::Type{Q}, c::C) where Q<:QuotientRing{P} where {P<:Polynomial,C}
    Q(convert(P, c))
end

@generated function convert(::Type{Q1}, c::Q2) where {Q1 <: QuotientRing{P1, ID1}, Q2 <: QuotientRing{P2, ID2}} where {P1 <: Polynomial, P2 <: Polynomial, ID1, ID2}
    P1 = ring(Q1)
    I2_image = Ideal(P1.(_ideal(Q2)))
    I2_image ⊆ _ideal(Q1) || error("Cannot convert $Q2 to $Q1; the conversion is not compatible with the quotients.")
    quote
        Q1(convert($P1, c.f))
    end
end


convert(::Type{Q}, q::Q) where Q <: QuotientRing{P, ID} where {P <: Polynomial, ID} = q

# -----------------------------------------------------------------------------
#
# Contructor-style conversions
#
# -----------------------------------------------------------------------------
(::Type{QuotientRing{P, ID}})(a) where {P, ID} = convert(QuotientRing{P, ID}, a)

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
==(a::QuotientRing, b) = ==(promote(a,b)...)
==(a, b::QuotientRing) = ==(promote(a,b)...)

+(a::QuotientRing,  b::QuotientRing) = +(promote(a,b)...)
-(a::QuotientRing,  b::QuotientRing) = -(promote(a,b)...)
*(a::QuotientRing,  b::QuotientRing) = *(promote(a,b)...)
==(a::QuotientRing, b::QuotientRing) = ==(promote(a,b)...)

/(a::QuotientRing, b::Number)  = typeof(a)(a.f /  b)
//(a::QuotientRing, b::Number) = typeof(a)(a.f // b)

# FIXME: the case I = (1)
minring(a::QuotientRing) = (r = minring(a.f)) <: Polynomial ? typeof(a) : r

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
    nvars = fieldcount(eltype(leading_monomials))
    rectangular_bounds = fill(MAX, nvars)
    for m in leading_monomials
        if count(!iszero, m) == 1
            i = findfirst(!iszero, m)
            rectangular_bounds[i] = min( m[i], rectangular_bounds[i] )
        end
    end

    if !all(b->b<MAX, rectangular_bounds)
        throw("$Q is infinite dimensional and does not have a finite monomial basis")
    end

    divisible = BitArray(undef, rectangular_bounds...)
    divisible .= false
    for m in leading_monomials
        block = [(m[i]+1):b for (i,b) in enumerate(rectangular_bounds)]
        divisible[block...] .= true
    end

    return map(i->i.-1, map(Tuple, findall(!, divisible)))
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

convert(::Type{P}, a::QuotientRing) where P <: Polynomial = P(convert(basering(P), a))
# resolve ambiguity
function convert(::Type{P}, a::Q) where P <: PolynomialOver{Q} where Q <: QuotientRing
    if iszero(a)
        return zero(P)
    else
        T = termtype(P)
        M = monomialtype(P)
        return P([T(one(M),deepcopy(a))])
    end
end
end
