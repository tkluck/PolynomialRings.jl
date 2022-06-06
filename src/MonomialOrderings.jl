"""
    module MonomialOrderings

Offer support for monomial orderings.
"""
module MonomialOrderings

import Base.Order: Ordering
import Base: findmin, findmax, argmin, argmax
import Base: min, max, minimum, maximum
import Base: promote_rule

import ..NamingSchemes: NamingScheme, Named, Numbered
import PolynomialRings: leading_monomial, leading_coefficient, leading_term, tail, deg
import PolynomialRings: monomialorder, namingscheme

"""
    abstract type MonomialOrder{Names} <: Base.Order.Ordering end

Represents a total order between monomials.
"""
abstract type MonomialOrder{Names <: NamingScheme} <: Ordering end

"""
    abstract type AtomicMonomialOrder{Names} <: MonomialOrder{Names} end

Represents a monomial order that can be chained to form lexicographical orders.
"""
abstract type AtomicMonomialOrder{Names} <: MonomialOrder{Names} end

namingscheme(::O)       where O <: MonomialOrder{Names} where Names = Names.instance
namingscheme(::Type{O}) where O <: MonomialOrder{Names} where Names = Names.instance

monomialorder(o::MonomialOrder) = o

NamedMonomialOrder{Names}        = MonomialOrder{Named{Names}}
NumberedMonomialOrder{Name, Max} = MonomialOrder{Numbered{Name, Max}}

# -----------------------------------------------------------------------------
#
# Information functions
#
# -----------------------------------------------------------------------------
degreecompatible(::MonomialOrder) = false

monomialorderkey(order, a) = iszero(a) ? nothing : a # TODO: rename! because typeof(monomialorderkey()) != monomialorderkeytype
monomialorderkeytype(T) = keytype(T)
monomialordereltype(T) = eltype(T)
function monomialorderkeypair end

# -----------------------------------------------------------------------------
#
# Utility functions related to orderings (min/max/argmin/etc)
#
# -----------------------------------------------------------------------------
min(m::MonomialOrder, x, y) = Base.Order.lt(m, x, y) ? x : y
max(m::MonomialOrder, x, y) = Base.Order.lt(m, x, y) ? y : x
min(m::MonomialOrder, a, b, c, xs...) = (op(x,y) = min(m,x,y); Base.afoldl(op, op(op(a,b),c), xs...))
max(m::MonomialOrder, a, b, c, xs...) = (op(x,y) = max(m,x,y); Base.afoldl(op, op(op(a,b),c), xs...))
function findmin(order::MonomialOrder, iter)
    p = pairs(iter)
    y = iterate(p)
    if y === nothing
        throw(ArgumentError("collection must be non-empty"))
    end
    (mi, m), s = y
    i = mi
    while true
        y = iterate(p, s)
        y === nothing && break
        m != m && break
        (i, ai), s = y
        if ai != ai || Base.Order.lt(order, ai, m)
            m = ai
            mi = i
        end
    end
    return (m, mi)
end
function findmax(order::MonomialOrder, iter)
    p = pairs(iter)
    y = iterate(p)
    if y === nothing
        throw(ArgumentError("collection must be non-empty"))
    end
    (mi, m), s = y
    i = mi
    while true
        y = iterate(p, s)
        y === nothing && break
        m != m && break
        (i, ai), s = y
        if ai != ai || Base.Order.lt(order, m, ai)
            m = ai
            mi = i
        end
    end
    return (m, mi)
end

# resolve ambiguity since Julia 1.8
findmin(order::MonomialOrder, a::AbstractArray) = invoke(findmin, Tuple{MonomialOrder, Any}, order, a)
findmax(order::MonomialOrder, a::AbstractArray) = invoke(findmax, Tuple{MonomialOrder, Any}, order, a)

argmin(m::MonomialOrder, iter) = findmin(m, iter)[2]
argmax(m::MonomialOrder, iter) = findmax(m, iter)[2]

function _minimum(order, iter)
    y = iterate(iter)
    isnothing(y) && throw(ArgumentError("collection must be non-empty"))
    (v, state) = y
    while true
        y = iterate(iter, state)
        isnothing(y) && break
        (vv, state) = y
        Base.Order.lt(order, vv, v) && (v = vv)
    end
    return v
end

function _maximum(order, iter)
    y = iterate(iter)
    isnothing(y) && throw(ArgumentError("collection must be non-empty"))
    (v, state) = y
    while true
        y = iterate(iter, state)
        isnothing(y) && break
        (vv, state) = y
        Base.Order.lt(order, v, vv) && (v = vv)
    end
    return v
end

minimum(order::MonomialOrder, iter) = _minimum(order, iter)
minimum(order::MonomialOrder, iter::AbstractArray) = _minimum(order, iter)
maximum(order::MonomialOrder, iter) = _maximum(order, iter)
maximum(order::MonomialOrder, iter::AbstractArray) = _maximum(order, iter)

macro withmonomialorder(order)
    esc(quote
        ≺(a, b) =  Base.Order.lt($order, a, b)
        ⪯(a, b) = !Base.Order.lt($order, b, a)
        ≻(a, b) =  Base.Order.lt($order, b, a)
        ⪰(a, b) = !Base.Order.lt($order, a, b)
        leading_monomial(f) = $leading_monomial(f, order=$order)
        leading_term(f) = $leading_term(f, order=$order)
        leading_coefficient(f) = $leading_coefficient(f, order=$order)
        lm(f) = $leading_monomial(f, order=$order)
        lt(f) = $leading_term(f, order=$order)
        lc(f) = $leading_coefficient(f, order=$order)
        tail(f) = $tail(f, order=$order)
        deg(f) = $deg(f, $namingscheme($order))
    end)
end

end
