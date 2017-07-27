module Operators

import PolynomialRings: leading_term
import PolynomialRings.Monomials: AbstractMonomial
import PolynomialRings.Terms: Term, monomial, coefficient
import PolynomialRings.Polynomials: Polynomial, termtype, terms, monomialorder

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: zero, one, +, -, *, ==, divrem, iszero, diff
import PolynomialRings: maybe_div

# -----------------------------------------------------------------------------
#
# zero, one, etc
#
# -----------------------------------------------------------------------------
@generated function zero(::Type{P}) where P <: Polynomial
    i = P(termtype(P)[])
    quote $i end
end
@generated function one(::Type{P})  where P <: Polynomial
    i = P([one(termtype(P))])
    quote $i end
end
zero(::P)       where P <: Polynomial = zero(P)
one(::P)        where P <: Polynomial = one(P)

iszero(a::P)        where P <: Polynomial = length(terms(a)) == 0
==(a::P,b::P)       where P <: Polynomial = a.terms == b.terms
+(a::P)             where P <: Polynomial = a
-(a::P)             where P <: Polynomial = P([-t for t in terms(a)])

# -----------------------------------------------------------------------------
#
# addition, subtraction
#
# -----------------------------------------------------------------------------
function +(a::Polynomial{A1,Order}, b::Polynomial{A2,Order}) where A1<:AbstractVector{Term{M,C1}} where A2<:AbstractVector{Term{M,C2}} where M <: AbstractMonomial where {C1, C2, Order}

    assert(issorted(terms(a), lt=(a,b)->isless(monomial(a),monomial(b),Val{Order})))
    assert(issorted(terms(b), lt=(a,b)->isless(monomial(a),monomial(b),Val{Order})))

    T = Term{M, promote_type(C1,C2)}
    P = Polynomial{Vector{T},Order}
    res = Vector{T}(length(a.terms) + length(b.terms))
    n = 0

    state_a = start(terms(a))
    state_b = start(terms(b))
    while !done(terms(a), state_a) && !done(terms(b), state_b)
        (term_a, next_state_a) = next(terms(a), state_a)
        (term_b, next_state_b) = next(terms(b), state_b)
        exponent_a, coefficient_a = monomial(term_a), coefficient(term_a)
        exponent_b, coefficient_b = monomial(term_b), coefficient(term_b)

        if isless(exponent_a, exponent_b, Val{Order})
            @inbounds res[n+=1] = term_a
            state_a = next_state_a
        elseif isless(exponent_b, exponent_a, Val{Order})
            @inbounds res[n+=1] = term_b
            state_b = next_state_b
        else
            coeff = coefficient_a + coefficient_b
            if !iszero(coeff)
                @inbounds res[n+=1] = T(exponent_a, coeff)
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
    assert(issorted(res, lt=(a,b)->isless(monomial(a),monomial(b),Val{Order})))
    return P(res)
end

function -(a::Polynomial{A1,Order}, b::Polynomial{A2,Order}) where A1<:AbstractVector{Term{M,C1}} where A2<:AbstractVector{Term{M,C2}} where M <: AbstractMonomial where {C1, C2, Order}

    assert(issorted(terms(a), lt=(a,b)->isless(monomial(a),monomial(b),Val{Order})))
    assert(issorted(terms(b), lt=(a,b)->isless(monomial(a),monomial(b),Val{Order})))

    T = Term{M, promote_type(C1,C2)}
    P = Polynomial{Vector{T},Order}
    res = Vector{T}(length(a.terms) + length(b.terms))
    n = 0

    state_a = start(terms(a))
    state_b = start(terms(b))
    while !done(terms(a), state_a) && !done(terms(b), state_b)
        (term_a, next_state_a) = next(terms(a), state_a)
        (term_b, next_state_b) = next(terms(b), state_b)
        exponent_a, coefficient_a = monomial(term_a), coefficient(term_a)
        exponent_b, coefficient_b = monomial(term_b), coefficient(term_b)

        if isless(exponent_a, exponent_b, Val{Order})
            @inbounds res[n+=1] = term_a
            state_a = next_state_a
        elseif isless(exponent_b, exponent_a, Val{Order})
            @inbounds res[n+=1] = -term_b
            state_b = next_state_b
        else
            coeff = coefficient_a - coefficient_b
            if !iszero(coeff)
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
    assert(issorted(res, lt=(a,b)->isless(monomial(a),monomial(b),Val{Order})))
    return P(res)
end

# -----------------------------------------------------------------------------
#
# multiplication
#
# -----------------------------------------------------------------------------
import PolynomialRings.Util: BoundedHeap
import DataStructures: enqueue!, dequeue!, peek

function *(a::Polynomial{A1,Order}, b::Polynomial{A2,Order}) where A1<:AbstractVector{Term{M,C1}} where A2<:AbstractVector{Term{M,C2}} where M <: AbstractMonomial where {C1, C2, Order}

    assert(issorted(terms(a), lt=(a,b)->isless(monomial(a),monomial(b),Val{Order})))
    assert(issorted(terms(b), lt=(a,b)->isless(monomial(a),monomial(b),Val{Order})))

    T = Term{M, promote_type(C1,C2)}
    PP = Polynomial{Vector{T}, Order}

    if iszero(a) || iszero(b)
        return zero(PP)
    end

    summands = Vector{T}(length(terms(a)) * length(terms(b)))
    k = 0

    row_indices= zeros(Int, length(terms(a)))
    col_indices= zeros(Int, length(terms(b)))

    # using a bounded queue not to drop items when it gets too big, but to allocate it
    # once to its maximal theoretical size and never reallocate.
    lt = Base.Order.Lt( (a,b) -> isless(monomial(a[3]),monomial(b[3]),Val{Order}) )
    minimal_corners = BoundedHeap{Tuple{Int, Int, T}, lt}(min(length(terms(a)), length(terms(b))))
    @inbounds t = terms(a)[1] * terms(b)[1]
    enqueue!(minimal_corners, (1,1,t))
    @inbounds while length(minimal_corners)>0
        row, col, t = peek(minimal_corners)
        dequeue!(minimal_corners)
        summands[k+=1] = t
        row_indices[row] = col
        col_indices[col] = row
        if row < length(terms(a)) && row_indices[row+1] == col - 1
            @inbounds t = terms(a)[row+1] * terms(b)[col]
            enqueue!(minimal_corners, (row+1,col, t))
        end
        if col < length(terms(b)) && col_indices[col+1] == row - 1
            @inbounds t = terms(a)[row] * terms(b)[col+1]
            enqueue!(minimal_corners, (row,col+1, t))
        end
    end

    assert(k == length(summands))
    assert(issorted(summands, lt=(a,b)->isless(monomial(a),monomial(b),Val{Order})))

    if length(summands) > 0
        last_exp = monomial(summands[1])
        n = 1
        for j in 2:length(summands)
            exponent, coef = monomial(summands[j]), coefficient(summands[j])
            if exponent == last_exp
                cur_coef = coefficient(summands[n])
                @inbounds summands[n] = Term(exponent, cur_coef + coef)
            else
                @inbounds summands[n+=1] = summands[j]
                last_exp = exponent
            end
        end
        resize!(summands, n)
        filter!(t -> !iszero(t), summands)
    end
    return PP(summands)
end

# -----------------------------------------------------------------------------
#
# long division
#
# -----------------------------------------------------------------------------
function divrem(f::Polynomial{A1,Order}, g::Polynomial{A2,Order}) where A1<:AbstractVector{Term{M,C1}} where A2<:AbstractVector{Term{M,C2}} where M <: AbstractMonomial where {C1, C2, Order}
    if iszero(f)
        return zero(g), f
    end
    if iszero(g)
        throw(DivideError())
    end
    lt_g = leading_term(g)
    for t in terms(f)
        factor = maybe_div(t, lt_g)
        if !isnull(factor)
            return typeof(f)([factor]), f - factor*g
        end
    end
    return zero(g), f
end

function leaddivrem(f::Polynomial{A1,Order}, g::Polynomial{A2,Order}) where A1<:AbstractVector{Term{M,C1}} where A2<:AbstractVector{Term{M,C2}} where M <: AbstractMonomial where {C1, C2, Order}
    if iszero(f)
        return zero(g), f
    end
    if iszero(g)
        throw(DivideError())
    end
    lt_f = leading_term(f)
    lt_g = leading_term(g)
    factor = maybe_div(lt_f, lt_g)
    if !isnull(factor)
        return typeof(f)([factor]), f - factor*g
    end
    return zero(g), f
end

# -----------------------------------------------------------------------------
#
# differentation
#
# -----------------------------------------------------------------------------
function diff(f::Polynomial, i::Integer)
    new_terms = filter(t->!iszero(t), map(t->diff(t,i), terms(f)))
    sort!(new_terms, lt=(a,b)->isless(monomial(a),monomial(b),Val{monomialorder(f)}))
    return typeof(f)(new_terms)
end

# -----------------------------------------------------------------------------
#
# Use Term as a polynomial
#
# -----------------------------------------------------------------------------
function *(a::T, b::P) where P<:Polynomial{V} where V<:AbstractVector{T} where T<:Term
    P([ T(monomial(a) * monomial(t), coefficient(a) * coefficient(t)) for t in terms(b) ])
end
function *(a::P, b::T) where P<:Polynomial{V} where V<:AbstractVector{T} where T<:Term
    P([ T(monomial(t) * monomial(b), coefficient(t) * coefficient(b)) for t in terms(a) ])
end


end
