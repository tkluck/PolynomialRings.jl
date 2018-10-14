module Operators

import Base: zero, one, +, -, *, ==, div, iszero, diff, ^, gcd

import DataStructures: enqueue!, dequeue!
import InPlace: @inplace

import ..Constants: Zero
import ..MonomialOrderings: MonomialOrder
import ..Monomials: AbstractMonomial
import ..Polynomials: Polynomial, termtype, terms, monomialorder, monomialtype
import ..Polynomials: PolynomialBy
import ..Terms: Term, monomial, coefficient
import ..Util: BoundedHeap
import ..Util: ParallelIter
import PolynomialRings: basering, exptype, base_extend, base_restrict
import PolynomialRings: lcm_multipliers
import PolynomialRings: leading_monomial, leading_coefficient, leading_term
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
+(a::P)             where P <: Polynomial = deepcopy(a)
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


function _collect_summands!(summands::AbstractVector{T}) where T <: Term{M, BigInt} where M
    if !isempty(summands)
        last_exp = monomial(summands[1])
        n = 1
        @inbounds for j in 2:length(summands)
            exponent, coef = monomial(summands[j]), coefficient(summands[j])
            if exponent == last_exp
                cur_coef = coefficient(summands[n])
                @inplace cur_coef += coef
            else
                summands[n+=1] = summands[j]
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
function _map(op, a::PolynomialBy{Order}, b::PolynomialBy{Order}) where Order
    P = promote_type(typeof(a), typeof(b))
    T = termtype(P)
    ≺(a,b) = Base.Order.lt(Order(), a, b)

    res = Vector{T}(undef, length(a.terms) + length(b.terms))
    n = 0

    for (m, cleft, cright) in ParallelIter(
            monomial, coefficient, ≺,
            Zero(), Zero(),
            terms(a), terms(b),
        )
        coeff = op(cleft, cright)
        if !iszero(coeff)
            @inbounds res[n+=1] = T(m, coeff)
        end
    end
    resize!(res, n)
    return P(res)
end

+(a::PolynomialBy{Order}, b::PolynomialBy{Order}) where Order = _map(+, a, b)
-(a::PolynomialBy{Order}, b::PolynomialBy{Order}) where Order = _map(-, a, b)

# -----------------------------------------------------------------------------
#
# multiplication
#
# -----------------------------------------------------------------------------

"""
    f = g * h

Return the product of two polynomials.

The implementation is as follows.

A naive implementation would have three steps: first, generate all the summands
as the cartesian product of the terms of `g` and the terms of `h`. Second, sort
the list by monomial order. Third, walk over the sorted list and sum the
coefficients of any terms with equal monomial.

A major improvement can be had if we avoid the sorting, and instead walk
over the cartesian product in the right order.

To understand this, let the following diagram represent the summands
in the cartesian product, with monomial order of the factors increasing
top to bottom and left to right:

    . . . . . . . . . . .
    . . . . . . . . . . .
    . . . . . . . . . . .
    . . . . . . . . . . .

When a certain number of terms have been evaluated and added to the
output (marked by `*` below), the situation may be as follows:

    * * * * * * * ? . . .
    * * * ? . . . . . . .
    ? . . . . . . . . . .
    . . . . . . . . . . .

The key insight is that _the only possibility for the next minimal
terms are the ones marked by `?`_. This is because of the multiplicative
property of monomial orders (``m ≺ n ⇒ km ≺ kn``).

We call these possible minimal terms the 'minimal corners'. In the
implementation below, a `Heap` data structure keeps track of them.

This allows us to avoid separate sorting and summing passes. In turn,
this allows keeping running totals of the coefficients and do all these
operations in-place for mutable types (e.g. BigInt).
"""
function *(a::PolynomialBy{Order}, b::PolynomialBy{Order}) where Order
    ≺(a, b) = Base.Order.lt(Order(), a, b)
    P = promote_type(typeof(a), typeof(b))
    C = basering(P)
    T = termtype(P)
    M = monomialtype(P)

    if iszero(a) || iszero(b)
        return zero(P)
    end

    t_a = terms(a)
    t_b = terms(b)
    l_a = length(t_a)
    l_b = length(t_b)

    summands = Vector{T}(undef, l_a * l_b)
    k = 0

    done_until_col_at_row = zeros(Int, l_a)
    done_until_row_at_col = zeros(Int, l_b)

    # We use a *bounded* queue not because we want to drop items when it
    # gets to big, but because we want to allocate it once to its maximal
    # theoretical size, and then never reallocate.
    order = Base.Order.Lt((a,b) -> a[3] ≺ b[3])
    Key = Tuple{Int, Int, M}
    minimal_corners = BoundedHeap(Key, min(l_a, l_b), order)

    # initialize with the minimal term at (row, col) = (1, 1)
    @inbounds m = monomial(t_a[1]) * monomial(t_b[1])
    enqueue!(minimal_corners, (1, 1, m))

    temp = zero(C)
    cur_monom = nothing
    cur_coeff = nothing

    @inbounds while !isempty(minimal_corners)
        row, col, m = dequeue!(minimal_corners)

        # compute the product of the product at (row, col)
        if m == cur_monom
            @inplace temp = coefficient(t_a[row]) * coefficient(t_b[col])
            @inplace cur_coeff += temp
        else
            if cur_monom !== nothing && !iszero(cur_coeff)
                summands[k+=1] = T(cur_monom, cur_coeff)
            end
            cur_coeff = coefficient(t_a[row]) * coefficient(t_b[col])
            cur_monom = m
        end

        # mark as done
        done_until_col_at_row[row] = col
        done_until_row_at_col[col] = row

        # decide whether we just added new minimal corners
        if row < l_a && done_until_col_at_row[row+1] == col - 1
            r, c = row + 1, col
            m = monomial(t_a[r]) * monomial(t_b[c])
            enqueue!(minimal_corners, (r, c, m))
        end
        if col < l_b && done_until_row_at_col[col+1] == row - 1
            r, c = row, col + 1
            m = monomial(t_a[r]) * monomial(t_b[c])
            enqueue!(minimal_corners, (r, c, m))
        end
    end
    summands[k+=1] = T(cur_monom, cur_coeff)
    resize!(summands, k)
    return P(summands)
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

terms_to_reduce(::Lead, f) = terms(f)[end:end]
terms_to_reduce(::Full, f) = @view terms(f)[end:-1:1]
terms_to_reduce(::Tail, f) = @view terms(f)[end-1:-1:1]

function one_step_div!(redtype::RedType, o::MonomialOrder, f::PolynomialBy{Order}, g::PolynomialBy{Order}) where Order
    if iszero(f)
        return nothing
    end
    if iszero(g)
        throw(DivideError())
    end
    lt_g = leading_term(o, g)
    for t in terms_to_reduce(redtype, f)
        factor = maybe_div(t, lt_g)
        if factor !== nothing
            @. f -= factor * g
            return factor
        end
    end
    return nothing
end

function one_step_xdiv!(redtype::RedType, o::MonomialOrder, f::PolynomialBy{Order}, g::PolynomialBy{Order}) where Order
    if iszero(f)
        return nothing
    end
    if iszero(g)
        throw(DivideError())
    end
    lt_g = leading_monomial(o, g)
    m2 = leading_coefficient(o, g)
    for t in terms_to_reduce(redtype, f)
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
    if n == 1 || iszero(f)
        return deepcopy(f)
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

    summands = Vector{T}(undef, Int( multinomial(bign+N-1, N-1, bign) ))
    s = 0

    while true
        c = try
            C(multinomial(bign, i...))
        catch
            # FIXME: what's the Julian way of doing a typeassert e::InexactError
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
# differentiation
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
gcd(f::Polynomial, g::Integer) = gcd(g, reduce(gcd, (coefficient(t) for t in terms(f)),init=0))
gcd(g::Integer, f::Polynomial) = gcd(g, reduce(gcd, (coefficient(t) for t in terms(f)),init=0))

div(f::Polynomial, g::Integer) = map_coefficients(c -> c÷g, f)

content(f::Polynomial) = gcd(f, 0)

common_denominator(a) = denominator(a)
common_denominator(a, b) = lcm(denominator(a), denominator(b))
common_denominator(a, b...) = lcm(denominator(a), denominator.(b)...)
common_denominator(f::Polynomial) = iszero(f) ? 1 : lcm(map(common_denominator∘coefficient, terms(f))...)

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
    op(c) = (res = f(c); res === c ? deepcopy(res) : res)
    new_terms = map(t->T(monomial(t), op(coefficient(t))), terms(a))
    # work around type inference issue
    new_terms = collect(T, new_terms)
    filter!(!iszero, new_terms)
    return typeof(a)(new_terms)
end

# -----------------------------------------------------------------------------
#
# Use Term/Monomial/Coefficient as a scalar
#
# -----------------------------------------------------------------------------
function *(a::T, b::P) where P<:Polynomial{M,C} where T<:Term{M,C} where {M,C}
    iszero(a) && return zero(P)
    P(map(t->a*t, terms(b)))
end
function *(a::P, b::T) where P<:Polynomial{M,C} where T<:Term{M,C} where {M,C}
    iszero(b) && return zero(P)
    P(map(t->t*b, terms(a)))
end
function *(a::M, b::P) where P<:Polynomial{M} where M<:AbstractMonomial
    P(map(t->t*a, terms(b)))
end
function *(a::P, b::M) where P<:Polynomial{M} where M<:AbstractMonomial
    P(map(t->t*b, terms(a)))
end


end
