module Operators

import PolynomialRings: leading_term, basering, exptype, base_extend, base_restrict
import PolynomialRings.Monomials: AbstractMonomial
import PolynomialRings.MonomialOrderings: MonomialOrder
import PolynomialRings.Terms: Term, monomial, coefficient
import PolynomialRings.Polynomials: Polynomial, termtype, terms, monomialorder
import PolynomialRings.Polynomials: PolynomialBy

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: zero, one, +, -, *, ==, div, iszero, diff, ^, gcd
import PolynomialRings: maybe_div

# -----------------------------------------------------------------------------
#
# zero, one, etc
#
# -----------------------------------------------------------------------------
zero(::Type{P}) where P<:Polynomial = P(termtype(P)[])
one(::Type{P})  where P<:Polynomial = P([one(termtype(P))])
zero(::P)       where P <: Polynomial = zero(P)
one(::P)        where P <: Polynomial = one(P)

iszero(a::P)        where P <: Polynomial = length(terms(a)) == 0
==(a::P,b::P)       where P <: Polynomial = a.terms == b.terms
+(a::P)             where P <: Polynomial = a
-(a::P)             where P <: Polynomial = P([-t for t in terms(a)])

# -----------------------------------------------------------------------------
#
# utility for operators
#
# -----------------------------------------------------------------------------
function _collect_summands!(summands::AbstractVector{T}) where T <: Term{M,C} where {M,C}
    if !isempty(summands)
        last_exp = monomial(summands[1])
        n = 1
        for j in 2:length(summands)
            exponent, coef = monomial(summands[j]), coefficient(summands[j])
            if exponent == last_exp
                cur_coef = coefficient(summands[n])
                @inbounds summands[n] = T(exponent, cur_coef + coef)
            else
                @inbounds summands[n+=1] = summands[j]
                last_exp = exponent
            end
        end
        resize!(summands, n)
        filter!(!iszero, summands)
    end
end

if VERSION < v"0.7-"
    const mpz_t = Ref{BigInt}
    add!(x::BigInt, a::BigInt, b::BigInt) = (ccall((:__gmpz_add, :libgmp), Void, (mpz_t, mpz_t, mpz_t), x, a, b); x)
    add!(x::BigInt, b::BigInt) = add!(x, x, b)
else
    using Base.GMP.MPZ: add!
end

function _collect_summands!(summands::AbstractVector{T}) where T <: Term{M, BigInt} where M
    if !isempty(summands)
        last_exp = monomial(summands[1])
        n = 1
        @inbounds for j in 2:length(summands)
            exponent, coef = monomial(summands[j]), coefficient(summands[j])
            if exponent == last_exp
                cur_coef = coefficient(summands[n])
                add!(cur_coef, coef)
            else
                summands[n+=1] = T(exponent, copy(coef))
                last_exp = exponent
            end
        end
        resize!(summands, n)
        filter!(!iszero, summands)
    end
end

# -----------------------------------------------------------------------------
#
# addition, subtraction
#
# -----------------------------------------------------------------------------
function +(a::Polynomial{A1,Order}, b::Polynomial{A2,Order}) where A1<:AbstractVector{Term{M,C1}} where A2<:AbstractVector{Term{M,C2}} where M <: AbstractMonomial where {C1, C2, Order}


    C = promote_type(C1,C2)
    T = Term{M, C}
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

        if Base.Order.lt(MonomialOrder{Order}(), exponent_a, exponent_b)
            @inbounds res[n+=1] = T(exponent_a, coefficient_a)
            state_a = next_state_a
        elseif Base.Order.lt(MonomialOrder{Order}(), exponent_b, exponent_a)
            @inbounds res[n+=1] = T(exponent_b, coefficient_b)
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
        @inbounds res[n+=1] = base_extend(t, C)
    end
    for t in Iterators.rest(terms(b), state_b)
        @inbounds res[n+=1] = base_extend(t, C)
    end

    resize!(res, n)
    return P(res)
end

function -(a::Polynomial{A1,Order}, b::Polynomial{A2,Order}) where A1<:AbstractVector{Term{M,C1}} where A2<:AbstractVector{Term{M,C2}} where M <: AbstractMonomial where {C1, C2, Order}


    C = promote_type(C1,C2)
    T = Term{M, C}
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

        if Base.Order.lt(MonomialOrder{Order}(), exponent_a, exponent_b)
            @inbounds res[n+=1] = T(exponent_a, coefficient_a)
            state_a = next_state_a
        elseif Base.Order.lt(MonomialOrder{Order}(), exponent_b, exponent_a)
            @inbounds res[n+=1] = -T(exponent_b, coefficient_b)
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
        @inbounds res[n+=1] = base_extend(t, C)
    end
    for t in Iterators.rest(terms(b), state_b)
        @inbounds res[n+=1] = -base_extend(t, C)
    end

    resize!(res, n)
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


    C = promote_type(C1, C2)
    T = Term{M, C}
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
    order = Base.Order.Lt((a,b)->Base.Order.lt(MonomialOrder{Order}(), a[3], b[3]))
    minimal_corners = BoundedHeap(Tuple{Int,Int,T}, min(length(terms(a)), length(terms(b))), order)
    @inbounds t = terms(a)[1] * terms(b)[1]
    enqueue!(minimal_corners, (1,1,t))
    @inbounds while length(minimal_corners)>0
        row, col, t = peek(minimal_corners)
        dequeue!(minimal_corners)
        summands[k+=1] = base_extend(t, C)
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

    _collect_summands!(summands)

    return PP(summands)
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

function one_step_divrem(::Full, o::MonomialOrder, f::PolynomialBy{Names,Order}, g::PolynomialBy{Names,Order}) where {Names, Order}
    if iszero(f)
        return zero(g), f
    end
    if iszero(g)
        throw(DivideError())
    end
    lt_g = leading_term(o, g)
    for t in @view terms(f)[end:-1:1]
        factor = maybe_div(t, lt_g)
        if !isnull(factor)
            return typeof(f)([factor]), f - factor*g
        end
    end
    return zero(g), f
end

function one_step_divrem(::Lead, o::MonomialOrder, f::PolynomialBy{Names,Order}, g::PolynomialBy{Names,Order}) where {Names, Order}
    if iszero(f)
        return zero(g), f
    end
    if iszero(g)
        throw(DivideError())
    end
    lt_f = leading_term(o, f)
    lt_g = leading_term(o, g)
    factor = maybe_div(lt_f, lt_g)
    if !isnull(factor)
        return typeof(f)([factor]), f - factor*g
    end
    return zero(g), f
end

function one_step_divrem(::Tail, o::MonomialOrder, f::PolynomialBy{Names,Order}, g::PolynomialBy{Names,Order}) where {Names, Order}
    if iszero(f)
        return zero(g), f
    end
    if iszero(g)
        throw(DivideError())
    end
    lt_g = leading_term(o, g)
    # FIXME: when o != monomialorder(f), this is not correct!
    for t in @view terms(f)[end-1:-1:1]
        factor = maybe_div(t, lt_g)
        if !isnull(factor)
            return typeof(f)([factor]), f - factor*g
        end
    end
    return zero(g), f
end


function one_step_rem(::Full, o::MonomialOrder, f::PolynomialBy{Names,Order}, g::PolynomialBy{Names,Order}) where {Names, Order}
    if iszero(f)
        return f
    end
    if iszero(g)
        throw(DivideError())
    end
    lt_g = leading_term(o, g)
    for t in @view terms(f)[end:-1:1]
        factor = maybe_div(t, lt_g)
        if !isnull(factor)
            return f - factor*g
        end
    end
    return f
end

function one_step_rem(::Lead, o::MonomialOrder, f::PolynomialBy{Names,Order}, g::PolynomialBy{Names,Order}) where {Names, Order}
    if iszero(f)
        return f
    end
    if iszero(g)
        throw(DivideError())
    end
    lt_f = leading_term(o, f)
    lt_g = leading_term(o, g)
    factor = maybe_div(lt_f, lt_g)
    if !isnull(factor)
        return f - factor*g
    end
    return f
end

function one_step_rem(::Tail, o::MonomialOrder, f::PolynomialBy{Names,Order}, g::PolynomialBy{Names,Order}) where {Names, Order}
    if iszero(f)
        return f
    end
    if iszero(g)
        throw(DivideError())
    end
    lt_g = leading_term(o, g)
    # FIXME: when o != monomialorder(f), this is not correct!
    for t in @view terms(f)[end-1:-1:1]
        factor = maybe_div(t, lt_g)
        if !isnull(factor)
            return f - factor*g
        end
    end
    return f
end

function one_step_div(redtype::RedType, o::MonomialOrder, f::PolynomialBy{Names,Order}, g::PolynomialBy{Names,Order}) where {Names, Order}
    one_step_divrem(redtype, o, f, g)[1]
end

# -----------------------------------------------------------------------------
#
# exponentiation
#
# -----------------------------------------------------------------------------
function multinomial(n,k...)
    @assert sum(k) == n

    i = 1
    for k_i in k
        i *= binomial(n,k_i)
        n -= k_i
    end
    i
end

function ^(f::Polynomial, n::Integer)
    if n == 0
        return one(f)
    end
    if n == 1
        return f
    end

    T = termtype(f)
    C = basering(f)
    E = exptype(f)
    I = typeof(n)

    N = length(terms(f))

    # need BigInts to do the multinom computation, but we'll cast
    # back to I = typeof(n) when we use it as an exponent
    bign = BigInt(n)
    i = zeros(BigInt, N)
    i[N] = bign

    summands = Vector{T}(Int( multinomial(bign+N-1, N-1, bign) ))
    s = 0

    while true
        c = try
            C(multinomial(bign, i...))
        catch
            # FIXME: what's the Julian way of doing a typeassert e::IneactError
            # and bubble up all other exceptions?
            throw(OverflowError("Coefficient overflow while doing exponentiation; suggested fix is replacing `f^n` by `base_extend(f, BigInt)^n`"))
        end
        new_coeff = c * prod(coefficient(f.terms[k])^I(i[k]) for k=1:N)
        new_monom = prod(monomial(f.terms[k])^E(i[k]) for k=1:N)
        summands[s+=1] = T(new_monom, new_coeff)
        carry = 1
        for j = N-1:-1:1
            i[j] += carry
            i[N] -= carry
            if i[N] < 0
                carry = 1
                i[N] += i[j]
                i[j] = 0
            else
                carry = 0
            end
        end
        if carry != 0
            break
        end
    end

    sort!(summands, order=monomialorder(f))

    _collect_summands!(summands)

    return typeof(f)(summands)

end

# -----------------------------------------------------------------------------
#
# differentation
#
# -----------------------------------------------------------------------------
function diff(f::Polynomial, i::Integer)
    iszero(f) && return zero(f)
    new_terms = filter(!iszero, map(t->diff(t,i), terms(f)))
    sort!(new_terms, order=monomialorder(f))
    return typeof(f)(new_terms)
end

# -----------------------------------------------------------------------------
#
# gcds and content
#
# -----------------------------------------------------------------------------
gcd(f::Polynomial, g::Integer) = gcd(g, reduce(gcd, 0, (coefficient(t) for t in terms(f))))
gcd(g::Integer, f::Polynomial) = gcd(g, reduce(gcd, 0, (coefficient(t) for t in terms(f))))

function div(f::Polynomial, g::Integer)
    T = termtype(f)
    P = typeof(f)
    new_terms = [T(monomial(t),div(coefficient(t),g)) for t in terms(f)]
    filter!(!iszero, new_terms)
    return P(new_terms)
end

content(f::Polynomial) = gcd(f, 0)

common_denominator(a) = denominator(a)
common_denominator(a, b) = lcm(denominator(a), denominator(b))
common_denominator(a, b...) = lcm(denominator(a), denominator.(b)...)
common_denominator(f::Polynomial) = iszero(f) ? 1 : lcm([common_denominator(coefficient(t)) for t in terms(f)]...)

function integral_fraction(f::Polynomial)
    D = common_denominator(f)

    return base_restrict(D*f), D
end

"""
    p = map_coefficients(f, q)

Apply a function `f` to all coefficients of `q`, and return the result.
"""
function map_coefficients(f, a::Polynomial)
    T = termtype(a)
    new_terms = map(t->T(monomial(t), f(coefficient(t))), terms(a))
    # work around type inference issue
    new_terms = collect(T, new_terms)
    filter!(!iszero, new_terms)
    return typeof(a)(new_terms)
end

# -----------------------------------------------------------------------------
#
# Use Term/Monomial as a polynomial
#
# -----------------------------------------------------------------------------
function *(a::T, b::P) where P<:Polynomial{V} where V<:AbstractVector{T} where T<:Term
    P(map(t->a*t, terms(b)))
end
function *(a::P, b::T) where P<:Polynomial{V} where V<:AbstractVector{T} where T<:Term
    P(map(t->t*b, terms(a)))
end
function *(a::M, b::P) where P<:Polynomial{<:AbstractVector{<:Term{M}}} where M<:AbstractMonomial
    P(map(t->t*a, terms(b)))
end
function *(a::P, b::M) where P<:Polynomial{<:AbstractVector{<:Term{M}}} where M<:AbstractMonomial
    P(map(t->t*b, terms(a)))
end


end
