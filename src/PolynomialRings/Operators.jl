module Operators

import PolynomialRings.Monomials: AbstractMonomial
import PolynomialRings.Terms: Term, exponent, coefficient
import PolynomialRings.Polynomials: Polynomial, termtype, terms

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: zero, one, +, -

# -----------------------------------------------------------------------------
#
# zero, one, etc
#
# -----------------------------------------------------------------------------
zero(::Type{P}) where P <: Polynomial = P([])
one(::Type{P})  where P <: Polynomial = P([one(termtype(P))])

# -----------------------------------------------------------------------------
#
# addition, subtraction
#
# -----------------------------------------------------------------------------
function +(a::Polynomial{A1,Order}, b::Polynomial{A2,Order}) where A1<:AbstractVector{Term{M,C1}} where A2<:AbstractVector{Term{M,C2}} where M <: AbstractMonomial where {C1, C2, Order}

    T = Term{M, promote_type(C1,C2)}
    res = Vector{T}(length(a.terms) + length(b.terms))
    n = 0

    state_a = start(terms(a))
    state_b = start(terms(b))
    while !done(terms(a), state_a) && !done(terms(b), state_b)
        (term_a, next_state_a) = next(terms(a), state_a)
        (term_b, next_state_b) = next(terms(b), state_b)
        exponent_a, coefficient_a = exponent(term_a), coefficient(term_a)
        exponent_b, coefficient_b = exponent(term_b), coefficient(term_b)

        if isless(exponent_a, exponent_b, Order)
            @inbounds res[n+=1] = term_a
            state_a = next_state_a
        elseif isless(exponent_b, exponent_a, Order)
            @inbounds res[n+=1] = term_b
            state_b = next_state_b
        else
            coeff = coefficient_a + coefficient_b
            if coeff != 0
                @inbounds res[n+=1] = Term(exponent_a, coeff)
            end
            state_b = next_state_b
            state_a = next_state_a
        end
    end

    for t in Iterators.rest(terms(a), state_a)
        @inbounds res[n+=1] = t
    end
    for t in Iterators.rest(terms(b), state_b)
        @inbounds res[n+=1] = t
    end

    resize!(res, n)
    return Polynomial(res)
end

function -(a::Polynomial{A1,Order}, b::Polynomial{A2,Order}) where A1<:AbstractVector{Term{M,C1}} where A2<:AbstractVector{Term{M,C2}} where M <: AbstractMonomial where {C1, C2, Order}

    T = Term{M, promote_type(C1,C2)}
    res = Vector{T}(length(a.terms) + length(b.terms))
    n = 0

    state_a = start(terms(a))
    state_b = start(terms(b))
    while !done(terms(a), state_a) && !done(terms(b), state_b)
        (term_a, next_state_a) = next(terms(a), state_a)
        (term_b, next_state_b) = next(terms(b), state_b)
        exponent_a, coefficient_a = exponent(term_a), coefficient(term_a)
        exponent_b, coefficient_b = exponent(term_b), coefficient(term_b)

        if isless(exponent_a, exponent_b, Order)
            @inbounds res[n+=1] = term_a
            state_a = next_state_a
        elseif isless(exponent_b, exponent_a, Order)
            @inbounds res[n+=1] = -term_b
            state_b = next_state_b
        else
            coeff = coefficient_a - coefficient_b
            if coeff != 0
                @inbounds res[n+=1] = Term(exponent_a, coeff)
            end
            state_b = next_state_b
            state_a = next_state_a
        end
    end

    for t in Iterators.rest(terms(a), state_a)
        @inbounds res[n+=1] = t
    end
    for t in Iterators.rest(terms(b), state_b)
        @inbounds res[n+=1] = -t
    end

    resize!(res, n)
    return Polynomial(res)
end


end
