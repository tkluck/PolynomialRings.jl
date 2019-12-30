module Operators

import Base: zero, one, +, -, *, ==, div, iszero, diff, ^, gcd

import InPlace: @inplace, inplace!, inclusiveinplace!

import ..Constants: Zero
import ..MonomialOrderings: MonomialOrder, @withmonomialorder
import ..Monomials: AbstractMonomial
import ..Polynomials: Polynomial, termtype, nztermscount, monomialorder, monomialtype, monomials, coefficients, map_coefficients
import ..Polynomials: leading_term, nzrevterms, nztailterms, nzterms
import ..Polynomials: PolynomialBy, TermBy, MonomialBy, isstrictlysparse, TermOver
import ..Terms: Term, monomial, coefficient
import ..Util: @assertvalid
import PolynomialRings: basering, exptype, base_extend, base_restrict
import PolynomialRings: lcm_multipliers, expansion
import PolynomialRings: leading_monomial, leading_coefficient
import PolynomialRings: maybe_div

# -----------------------------------------------------------------------------
#
# zero, one, etc
#
# -----------------------------------------------------------------------------
zero(::P)       where P <: Polynomial = zero(P)
one(::P)        where P <: Polynomial = one(P)

# -----------------------------------------------------------------------------
#
# addition, subtraction
#
# -----------------------------------------------------------------------------
+(a::PolynomialBy{Order}, b::PolynomialBy{Order}) where Order = a .+ b
-(a::PolynomialBy{Order}, b::PolynomialBy{Order}) where Order = a .- b


# -----------------------------------------------------------------------------
#
# multiplication
#
# -----------------------------------------------------------------------------
function *(a::PolynomialBy{Order}, b::PolynomialBy{Order}) where Order
    P = promote_type(typeof(a), typeof(b))
    # FIXME(tkluck): promote_type currently only guarantees that
    #     namingscheme(P) == namingscheme(Order)
    # See NamedPolynomials.jl
    @assert monomialorder(P) == Order()

    res = zero(P)
    for t_a in nzterms(a), t_b in nzterms(b)
        res += t_a * t_b
    end
    return @assertvalid res
end

# -----------------------------------------------------------------------------
#
# long division
#
# -----------------------------------------------------------------------------
abstract type RedType end
struct Lead <: RedType end
struct Full <: RedType end
struct Tail <: RedType end

terms_to_reduce(::Lead, f; order) = (leading_term(f, order=order),)
terms_to_reduce(::Full, f; order) = nzrevterms(f, order=order)
terms_to_reduce(::Tail, f; order) = nztailterms(f, order=order)

function one_step_div!(f::PolynomialBy{Order}, g::PolynomialBy{Order}; order::Order, redtype::RedType) where Order <: MonomialOrder
    @withmonomialorder order
    if iszero(f)
        return nothing
    end
    if iszero(g)
        throw(DivideError())
    end
    lt_g = leading_term(g)
    for t in terms_to_reduce(redtype, f, order=order)
        factor = maybe_div(t, lt_g)
        if factor !== nothing
            @. f -= factor * g
            return factor
        end
    end
    return nothing
end

function one_step_xdiv!(f::PolynomialBy{Order}, g::PolynomialBy{Order}; order::Order, redtype::RedType) where Order <: MonomialOrder
    @withmonomialorder order
    if iszero(f)
        return nothing
    end
    if iszero(g)
        throw(DivideError())
    end
    lt_g = leading_monomial(g)
    m2 = leading_coefficient(g)
    for t in terms_to_reduce(redtype, f, order=order)
        factor = maybe_div(monomial(t), lt_g)
        if factor !== nothing
            m1 = coefficient(t)
            k1, k2 = lcm_multipliers(m1, m2)
            @. f = k1 * f - k2 * (factor * g)
            return k1, k2 * factor
        end
    end
    return nothing
end

# -----------------------------------------------------------------------------
#
# gcds and content
#
# -----------------------------------------------------------------------------
gcd(f::Polynomial, g::Integer) = gcd(g, reduce(gcd, coefficients(f), init=zero(basering(f))))
gcd(g::Integer, f::Polynomial) = gcd(g, reduce(gcd, coefficients(f), init=zero(basering(f))))

div(f::Polynomial, g::Integer) = map_coefficients(c -> c÷g, f)

content(f::Polynomial) = gcd(f, 0)

common_denominator(a) = denominator(a)
common_denominator(a, b) = lcm(denominator(a), denominator(b))
common_denominator(a, b...) = lcm(denominator(a), denominator.(b)...)
common_denominator(f::Polynomial) = iszero(f) ? 1 : mapreduce(common_denominator, lcm, coefficients(f))

function integral_fraction(f::Polynomial)
    N = common_denominator(f)
    return base_restrict(N * f), N
end


# -----------------------------------------------------------------------------
#
# Use Term/Monomial/Coefficient as a scalar
#
# -----------------------------------------------------------------------------
for Coeff in [Any, Polynomial, Number]
    @eval begin
        function *(a::C, b::P) where P <: Polynomial{M,C} where {M <: AbstractMonomial, C <: $Coeff}
            iszero(a) && return zero(P)
            map_coefficients(b_i -> a * b_i, b)
        end
        function *(a::P, b::C) where P <: Polynomial{M,C} where {M <: AbstractMonomial, C <: $Coeff}
            iszero(b) && return zero(P)
            map_coefficients(a_i -> a_i * b, a)
        end
    end
end

# -----------------------------------------------------------------------------
#
# Multiplying Terms in-place
#
# -----------------------------------------------------------------------------
function inplace!(::typeof(*), a::T, b::MonomialBy{Order}, c::T) where T <: TermBy{Order} where Order <: MonomialOrder
    if coefficient(a) === coefficient(c)
        # in-place means that we do not need to deepcopy the coefficient
        a = Term(b * monomial(c), coefficient(c))
    else
        a = b * c
    end
    a
end

function inplace!(::typeof(*), a::T, b::C, c::T) where T <: TermOver{C} where C
    if coefficient(a) === coefficient(c)
        coef = coefficient(a)
        @inplace coef *= b
        a = Term(monomial(c), coef)
    else
        a = b * c
    end
    a
end

end
