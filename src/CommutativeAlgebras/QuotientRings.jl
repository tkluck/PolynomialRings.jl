module QuotientRings

using PolynomialRings
import Base: +,-,*,/,//,^,==,!=
import Base: promote_rule, convert
import Base: show
import Base: zero, one, rem, copy

import ..Constants: Constant, One, MinusOne, Zero
import ..Ideals: Ideal, _grb
import ..Ideals: ring
import ..NamingSchemes: boundnames, fullboundnames, namingscheme, fullnamingscheme
import ..Polynomials: Polynomial, exptype, leading_term
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
@generated _ideal(R) = :( _ideals[R] )
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
function promote_rule(::Type{Q}, ::Type{C}) where Q<:QuotientRing{P} where {P<:Polynomial,C<:Number}
    P′ = promote_rule(P, C)
    if P′ !== Union{}
        I = Ideal(map(P′, _ideal(Q)))
        return P′/I
    end
    return Union{}
end

function convert(::Type{Q}, c::C) where Q<:QuotientRing{P} where {P<:Polynomial,C}
    Q(convert(P, c))
end

@generated function convert(::Type{Q1}, c::Q2) where {Q1 <: QuotientRing{P1}, Q2 <: QuotientRing} where P1 <: Polynomial
    P1 = ring(Q1)
    I2_image = Ideal(P1.(_ideal(Q2)))
    I2_image ⊆ _ideal(Q1) || error("Cannot convert $Q2 to $Q1; the conversion is not compatible with the quotients.")
    quote
        Q1(convert($P1, c.f))
    end
end


convert(::Type{Q}, q::Q) where Q <: QuotientRing = q

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

# -----------------------------------------------------------------------------
#
# Resolve method ambiguity
#
# -----------------------------------------------------------------------------
for N = [QuotientRing]
    @eval begin
        promote_rule(::Type{T}, ::Type{C}) where {T<:$N, C <: Constant} = T

        convert(::Type{T}, ::One)      where T<:$N = one(T)
        convert(::Type{T}, ::Zero)     where T<:$N = zero(T)
        convert(::Type{T}, ::MinusOne) where T<:$N = -one(T)

        # fix method ambiguities
        *(x::$N, ::One) = deepcopy(x)
        *(::One, x::$N) = deepcopy(x)
        *(x::$N, ::MinusOne) = -x
        *(::MinusOne, x::$N) = -x

        +(x::$N, ::Zero) = deepcopy(x)
        -(x::$N, ::Zero) = deepcopy(x)
        *(x::$N, ::Zero) = zero(x)
        +(::Zero, x::$N) = deepcopy(x)
        -(::Zero, x::$N) = -x
        *(::Zero, x::$N) = zero(x)
    end
end

end
