module Operators

import Base: zero, one, +, -, *, ==, div, iszero, diff, ^, gcd

import DataStructures: enqueue!, dequeue!
import InPlace: @inplace, inclusiveinplace!

import ..Constants: Zero
import ..MonomialOrderings: MonomialOrder, @withmonomialorder
import ..Monomials: AbstractMonomial
import ..Polynomials: Polynomial, termtype, nztermscount, monomialorder, monomialtype
import ..Polynomials: monomialstype
import ..Polynomials: leading_term, nzrevterms, nztailterms, nzterms
import ..Polynomials: PolynomialBy, isstrictlysparse
import ..Terms: Term, monomial, coefficient
import ..Util: BoundedHeap
import ..Util: ParallelIter
import PolynomialRings: basering, exptype, base_extend, base_restrict
import PolynomialRings: lcm_multipliers
import PolynomialRings: leading_monomial, leading_coefficient
import PolynomialRings: maybe_div

function _ensurecoeffs!(coeffs, n)
    if (m = length(coeffs)) < n
        resize!(coeffs, n)
        for i in m + 1 : n
            coeffs[i] = zero(eltype(coeffs))
        end
    end
    coeffs
end

# -----------------------------------------------------------------------------
#
# zero, one, etc
#
# -----------------------------------------------------------------------------
zero(::Type{P}) where P<:Polynomial = P(monomialstype(P)(), basering(P)[])
one(::Type{P})  where P<:Polynomial = P([one(monomialtype(P))], [one(basering(P))])
zero(::P)       where P <: Polynomial = zero(P)
one(::P)        where P <: Polynomial = one(P)

iszero(a::P)        where P <: Polynomial = iszero(a.coeffs)
# FIXME: allow for structural zeros
==(a::P, b::P)      where P <: Polynomial = a.monomials == b.monomials && a.coeffs == b.coeffs
+(a::P)             where P <: Polynomial = P(copy(a.monomials), copy(a.coeffs))
-(a::P)             where P <: Polynomial = P(copy(a.monomials), map(-, a.coeffs))

# -----------------------------------------------------------------------------
#
# utility for operators
#
# -----------------------------------------------------------------------------
function _filterzeros!(p::Polynomial)
    tgtix = 0
    for srcix in eachindex(p.coeffs)
        if !iszero(p.coeffs[srcix])
            tgtix += 1
            p.monomials[tgtix] = p.monomials[srcix]
            p.coeffs[tgtix] = p.coeffs[srcix]
        end
    end
    resize!(p.monomials, tgtix)
    resize!(p.coeffs, tgtix)
    p
end

function _collectsummands!(p::Polynomial)
    if length(p.coeffs) > 1
        I = sortperm(p.monomials, order=monomialorder(p))
        p.monomials[:] = p.monomials[I]
        p.coeffs[:] = p.coeffs[I]
        tgtix = 1
        for srcix in 2:length(p.coeffs)
            if p.monomials[tgtix] == p.monomials[srcix]
                @inplace p.coeffs[tgtix] += p.coeffs[srcix]
            else
                tgtix += 1
                p.monomials[tgtix] = p.monomials[srcix]
                p.coeffs[tgtix] = p.coeffs[srcix]
            end
        end
        resize!(p.monomials, tgtix)
        resize!(p.coeffs, tgtix)
    end
    _filterzeros!(p)
end

# -----------------------------------------------------------------------------
#
# addition, subtraction
#
# -----------------------------------------------------------------------------
function _map(op, a::PolynomialBy{Order}, b::PolynomialBy{Order}) where Order
    P = promote_type(typeof(a), typeof(b))
    # FIXME(tkluck): promote_type currently only guarantees that
    #     namingscheme(P) == namingscheme(Order)
    # See NamedPolynomials.jl
    @assert monomialorder(P) == Order()
    M = monomialtype(P)
    C = basering(P)
    ≺(a,b) = Base.Order.lt(Order(), a, b)

    if a.monomials === b.monomials
        if length(a.coeffs) < length(b.coeffs)
            coeffs = op.(Zero(), b.coeffs)
            initial = 1:length(a.coeffs)
            coeffs[initial] .= op.(view(a.coeffs, initial), view(b.coeffs, initial))
            return _filterzeros!(P(copy(b.monomials), coeffs))
        else
            coeffs = op.(a.coeffs, Zero())
            initial = 1:length(b.coeffs)
            coeffs[initial] .= op.(view(a.coeffs, initial), view(b.coeffs, initial))
            return _filterzeros!(P(copy(b.monomials), coeffs))
        end
    end

    monomials = Vector{M}(undef, length(a.monomials) + length(b.monomials))
    coeffs    = Vector{C}(undef, length(a.coeffs)    + length(b.coeffs))
    n = 0

    for (m, coeff) in ParallelIter(
            first, last, ≺,
            Zero(), Zero(), op,
            pairs(a, Order()), pairs(b, Order()),
        )
        if !iszero(coeff)
            n += 1
            @inbounds monomials[n] = m
            @inbounds coeffs[n] = coeff
        end
    end
    resize!(monomials, n)
    resize!(coeffs, n)
    return P(monomials, coeffs)
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
    # FIXME(tkluck): promote_type currently only guarantees that
    #     namingscheme(P) == namingscheme(Order)
    # See NamedPolynomials.jl
    @assert monomialorder(P) == Order()
    C = basering(P)
    T = termtype(P)
    M = monomialtype(P)

    if iszero(a) || iszero(b)
        return zero(P)
    end

    l_a = length(a.coeffs)
    l_b = length(b.coeffs)

    monomials = Vector{M}(undef, l_a * l_b)
    coeffs = Vector{C}(undef, l_a * l_b)
    k = 0

    done_until_col_at_row = zeros(Int, l_a)
    done_until_row_at_col = zeros(Int, l_b)

    # We use a *bounded* queue not because we want to drop items when it
    # gets too big, but because we want to allocate it once to its maximal
    # theoretical size, and then never reallocate.
    order = Base.Order.Lt((a, b) -> a[3] ≺ b[3])
    Key = Tuple{Int, Int, M}
    minimal_corners = BoundedHeap(Key, min(l_a, l_b), order)

    # initialize with the minimal term at (row, col) = (1, 1)
    @inbounds m = a.monomials[1] * b.monomials[1]
    enqueue!(minimal_corners, (1, 1, m))

    temp = zero(C)

    @inbounds while !isempty(minimal_corners)
        row, col, m = dequeue!(minimal_corners)

        # compute the product of the terms at (row, col)
        if k > 0 && m == monomials[k]
            @inplace temp = a.coeffs[row] * b.coeffs[col]
            @inplace coeffs[k] += temp
        else
            k += 1
            monomials[k] = m
            coeffs[k] = a.coeffs[row] * b.coeffs[col]
        end

        # mark as done
        done_until_col_at_row[row] = col
        done_until_row_at_col[col] = row

        # decide whether we just added new minimal corners
        if row < l_a && done_until_col_at_row[row+1] == col - 1
            r, c = row + 1, col
            m = a.monomials[r] * b.monomials[c]
            enqueue!(minimal_corners, (r, c, m))
        end
        if col < l_b && done_until_row_at_col[col+1] == row - 1
            r, c = row, col + 1
            m = a.monomials[r] * b.monomials[c]
            enqueue!(minimal_corners, (r, c, m))
        end
    end
    resize!(monomials, k)
    resize!(coeffs, k)
    return _filterzeros!(P(monomials, coeffs))
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

    P = typeof(f)
    M = monomialtype(f)
    C = basering(f)
    E = exptype(f)
    I = typeof(n)

    N = length(f.coeffs)

    # need BigInts to do the multinom computation, but we'll cast
    # back to I = typeof(n) when we use it as an exponent
    bign = BigInt(n)
    i = zeros(BigInt, N)
    i[N] = bign

    nterms = Int(multinomial(bign + N - 1, N - 1, bign))
    monomials = Vector{M}(undef, nterms)
    coeffs = Vector{C}(undef, nterms)
    s = 0

    while true
        c = try
            C(multinomial(bign, i...))
        catch
            # FIXME: what's the Julian way of doing a typeassert e::InexactError
            # and bubble up all other exceptions?
            throw(OverflowError("Coefficient overflow while doing exponentiation; suggested fix is replacing `f^n` by `base_extend(f, BigInt)^n`"))
        end
        s += 1
        monomials[s] =     prod(f.monomials[k] ^ E(i[k]) for k = 1:N)
        coeffs[s]    = c * prod(f.coeffs[k]    ^ I(i[k]) for k = 1:N)

        carry = 1
        for j = N - 1 : -1 : 1
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

    _collectsummands!(P(monomials, coeffs))
end

# -----------------------------------------------------------------------------
#
# differentiation
#
# -----------------------------------------------------------------------------
function diff(f::Polynomial, i::Integer)
    iszero(f) && return zero(f)
    new_terms = filter(!iszero, map(t->diff(t,i), nzterms(f)))
    sort!(new_terms, order=monomialorder(f))
    monomials = [monomial(t) for t in new_terms]
    coeffs = [coefficient(t) for t in new_terms]
    return typeof(f)(monomials, coeffs)
end

# -----------------------------------------------------------------------------
#
# gcds and content
#
# -----------------------------------------------------------------------------
gcd(f::Polynomial, g::Integer) = gcd(g, reduce(gcd, f.coeffs, init=zero(basering(f))))
gcd(g::Integer, f::Polynomial) = gcd(g, reduce(gcd, f.coeffs, init=zero(basering(f))))

div(f::Polynomial, g::Integer) = map_coefficients(c -> c÷g, f)

content(f::Polynomial) = gcd(f, 0)

common_denominator(a) = denominator(a)
common_denominator(a, b) = lcm(denominator(a), denominator(b))
common_denominator(a, b...) = lcm(denominator(a), denominator.(b)...)
common_denominator(f::Polynomial) = iszero(f) ? 1 : mapreduce(common_denominator, lcm, f.coeffs)

function integral_fraction(f::Polynomial)
    D = common_denominator(f)

    return base_restrict(D*f), D
end

"""
    p = map_coefficients(f, q)

Apply a function `f` to all coefficients of `q`, and return the result.
"""
function map_coefficients(f, a::Polynomial)
    _filterzeros!(Polynomial(copy(a.monomials), map(f, a.coeffs)))
end

# -----------------------------------------------------------------------------
#
# Use Term/Monomial/Coefficient as a scalar
#
# -----------------------------------------------------------------------------
function *(a::M, b::P) where P<:Polynomial{M} where M<:AbstractMonomial
    P(a .* b.monomials, copy(b.coeffs))
end
function *(a::P, b::M) where P<:Polynomial{M} where M<:AbstractMonomial
    P(a.monomials .* b, copy(a.coeffs))
end
for Coeff in [Any, Number]
    @eval begin
        function *(a::T, b::P) where P<:Polynomial{M,C,MV} where T<:Term{M,C} where {M <: AbstractMonomial, C <: $Coeff, MV}
            iszero(a) && return zero(P)
            P(monomial(a) .* b.monomials, coefficient(a) .* b.coeffs)
        end
        function *(a::P, b::T) where P<:Polynomial{M,C,MV} where T<:Term{M,C} where {M <: AbstractMonomial, C <: $Coeff, MV}
            iszero(b) && return zero(P)
            P(a.monomials .* monomial(b), a.coeffs .* coefficient(b))
        end
        function *(a::C, b::P) where P<:Polynomial{M,C,MV} where {M <: AbstractMonomial, C <: $Coeff, MV}
            iszero(a) && return zero(P)
            P(copy(b.monomials), a .* b.coeffs)
        end
        function *(a::P, b::C) where P<:Polynomial{M,C,MV} where {M <: AbstractMonomial, C <: $Coeff, MV}
            iszero(b) && return zero(P)
            P(copy(a.monomials), a.coeffs .* b)
        end
    end
end
# -----------------------------------------------------------------------------
#
# Adding terms/monomials/scalars
#
# -----------------------------------------------------------------------------
function inclusiveinplace!(::typeof(+), a::P, b::T) where
            P <: Polynomial{M, C} where
            T <: Term{M, C} where
            {M <: AbstractMonomial, C}
    ix = searchsorted(a.monomials, monomial(b))
    if length(ix) == 1
        i = first(ix)
        _ensurecoeffs!(a.coeffs, i)
        @inplace a.coeffs[i] += coefficient(b)
        if isstrictlysparse(a) && iszero(a.coeffs[i])
            deleteat!(a.monomials, i)
            deleteat!(a.coeffs, i)
        end
    elseif isempty(ix)
        i = first(ix)
        insert!(a.monomials, i, monomial(b))
        insert!(a.coeffs, i, coefficient(b))
    else
        @error "Invalid polynomial" a dump(a)
        error("Invalid polynomial")
    end
    a
end

function inclusiveinplace!(::typeof(+), a::P, b::M) where
            P <: Polynomial{M, C} where
            {M <: AbstractMonomial, C}
    ix = searchsorted(a.monomials, b)
    if length(ix) == 1
        i = first(ix)
        _ensurecoeffs!(a.coeffs, i)
        @inplace a.coeffs[i] += one(basering(a))
        if isstrictlysparse(a) && iszero(a.coeffs[i])
            deleteat!(a.monomials, i)
            deleteat!(a.coeffs, i)
        end
    elseif isempty(ix)
        i = first(ix)
        insert!(a.monomials, i, b)
        insert!(a.coeffs, i, one(basering(a)))
    else
        @error "Invalid polynomial" a dump(a)
        error("Invalid polynomial")
    end
    a
end

function inclusiveinplace!(::typeof(+), a::P, b::C) where
            P <: Polynomial{M, C} where
            {M <: AbstractMonomial, C}
    ix = searchsorted(a.monomials, one(monomialtype(a)))
    if length(ix) == 1
        i = first(ix)
        _ensurecoeffs!(a.coeffs, i)
        @inplace a.coeffs[i] += b
        if isstrictlysparse(a) && iszero(a.coeffs[i])
            deleteat!(a.monomials, i)
            deleteat!(a.coeffs, i)
        end
    elseif isempty(ix)
        i = first(ix)
        insert!(a.monomials, i, one(monomialtype(a)))
        insert!(a.coeffs, i, b)
    else
        @error "Invalid polynomial" a dump(a)
        error("Invalid polynomial")
    end
    a
end








end
