"""
    module PolynomialRings.StandardMonomialOrderings

This module contains the implementation of `Base.Order.lt` for the
:degrevlex, the :deglex and the :lex orders. This is not part of
the `MonomialOrderings` module in order to break a dependency cycle
with the `AbstractMonomials` module.
"""
module StandardMonomialOrderings

import Base: promote_rule
import Base.Order: Ordering

import ..AbstractMonomials: AbstractMonomial, exponentsnz, revexponentsnz
import ..MonomialOrderings: AtomicMonomialOrder, MonomialOrder, degreecompatible
import ..MonomialOrderings: monomialorderkey, monomialorderkeypair
import ..NamingSchemes: namingscheme, Named, NamingScheme
import ..Polynomials: Polynomial
import ..Terms: Term
import PolynomialRings: deg, leading_monomial


"""
    struct MonomialOrdering{Rule, Names} <: AtomicMonomialOrder{Names} end

For implementing your own monomial order, do the following:

1. Choose a symbol to represent it, say `:myorder`
2. `Base.Order.lt(::MonomialOrdering{:myorder}, a, b) = ...`

A few useful functions are [`exponents`](@ref) and [`exponentsnz`](@ref). See
[`PolynomialRings.AbstractMonomials`](@ref) and
[`PolynomialRings.MonomialOrderings`](@ref) for details.

You can then create a ring that uses it by calling

    R,vars = polynomial_ring(vars...; monomialorder=:myorder)

There is no performance cost for using your own monomial order compared to a
built-in one.
"""
struct MonomialOrdering{Rule, Names} <: AtomicMonomialOrder{Names} end

rulesymbol(::O)       where O <: MonomialOrdering{Rule, Names} where {Rule, Names} = Rule
rulesymbol(::Type{O}) where O <: MonomialOrdering{Rule, Names} where {Rule, Names} = Rule

# -----------------------------------------------------------------------------
#
# Promotions for different variable name sets
#
# -----------------------------------------------------------------------------
function promote_rule(::Type{M1}, ::Type{M2}) where {M1 <: MonomialOrdering, M2 <: MonomialOrdering}
    scheme = promote_type(typeof(namingscheme(M1)), typeof(namingscheme(M2)))
    if scheme <: NamingScheme
        return MonomialOrdering{:degrevlex, scheme}
    else
        return Union{}
    end
end

# -----------------------------------------------------------------------------
#
# deg(rev)lex orders
#
# -----------------------------------------------------------------------------

degreecompatible(::MonomialOrdering{:degrevlex}) = true

function Base.Order.lt(order::MonomialOrdering{:degrevlex}, a, b)
    iszero(b) && return false
    iszero(a) && return true
    a = monomialorderkey(order, a)
    b = monomialorderkey(order, b)
    scheme = namingscheme(order)
    if deg(a, scheme) == deg(b, scheme)
        for (_, (d, e)) in revexponentsnz(scheme, a, b)
            if d != e
                return d > e
            end
        end
        return false
    else
        return deg(a, scheme) < deg(b, scheme)
    end
end

degreecompatible(::MonomialOrdering{:deglex}) = true

function Base.Order.lt(order::MonomialOrdering{:deglex}, a, b)
    iszero(b) && return false
    iszero(a) && return true
    a = monomialorderkey(order, a)
    b = monomialorderkey(order, b)
    scheme = namingscheme(order)
    if deg(a, scheme) == deg(b, scheme)
        for (_, (d, e)) in exponentsnz(scheme, a, b)
            if d != e
                return d < e
            end
        end
        return false
    else
        return deg(a, scheme) < deg(b, scheme)
    end
end

# TODO(?): deprecate in favour of LexCombinationOrder
function Base.Order.lt(order::MonomialOrdering{:lex}, a, b)
    iszero(b) && return false
    iszero(a) && return true
    a = monomialorderkey(order, a)
    b = monomialorderkey(order, b)
    scheme = namingscheme(order)
    for (_, (d, e)) in exponentsnz(scheme, a, b)
        if d != e
            return d < e
        end
    end
    return false
end

# This method is mostly for supporting leading monomials of elements of a free
# f.g. module which is a tuple (index, monomial). That's in use in Gröbner,
# and maybe this implementation detail should move there.
function Base.Order.lt(m::MonomialOrder, a::T, b::T) where T <: Tuple
    error("Can we remove this?")
    for i = 1:fieldcount(T)
        if fieldtype(T,i) <: AbstractMonomial
            if Base.Order.lt(m, a[i], b[i])
                return true
            elseif Base.Order.lt(m, b[i], a[i])
                return false
            end
        else
            if isless(a[i], b[i])
                return true
            elseif isless(b[i], a[i])
                return false
            end
        end
    end
    return false
end

# -----------------------------------------------------------------------------
#
# KeyOrder and LexCombinationOrder
#
# -----------------------------------------------------------------------------

struct KeyOrder{Order} <: AtomicMonomialOrder{Nothing}
    order :: Order
end

KeyOrder() = KeyOrder{typeof(Base.Order.Reverse)}(Base.Order.Reverse)

monomialorderkeypair(order, a::Pair) = a

maxnonzero(::typeof(Base.Order.Forward), a) = findlast(!iszero, a)
maxnonzero(::typeof(Base.Order.Reverse), a) = findfirst(!iszero, a)

function monomialorderkeypair(order, a)
    if (ix = maxnonzero(order, a)) |> !isnothing
        return ix => a[ix]
    else
        return ix => nothing
    end
end

function Base.Order.lt(order::KeyOrder, a, b)
    ixa, _ = monomialorderkeypair(order.order, a)
    ixb, _ = monomialorderkeypair(order.order, b)

    isnothing(ixb) && return false
    isnothing(ixa) && return true

    return Base.Order.lt(order.order, ixa, ixb)
end

const UniformTuple{T, N} = NTuple{N, T}

struct LexCombinationOrder{Orders <: UniformTuple{AtomicMonomialOrder}, Names} <: MonomialOrder{Names}
    orders :: Orders
    names  :: Names
end

atoms(order::AtomicMonomialOrder) = (order,)
atoms(order::LexCombinationOrder) = order.orders

flattentuple() = ()
flattentuple(a, as...) = tuple(a..., flattentuple(as...)...)

Base.first(order::LexCombinationOrder) = order.orders[1]
Base.tail(order::LexCombinationOrder) = LexCombinationOrder(Base.tail(order.orders)...)

function LexCombinationOrder(order::AtomicMonomialOrder)
    return LexCombinationOrder((order,), namingscheme(order))
end

function LexCombinationOrder(orders::MonomialOrder...) where Orders
    orders = flattentuple(map(atoms, orders)...)
    names = promote_type(filter(!isnothing, map(namingscheme, orders))...)
    LexCombinationOrder(orders, names)
end

Base.Order.lt(order::LexCombinationOrder{<:Tuple{}}, a, b) = false

function Base.Order.lt(order::LexCombinationOrder{<:Tuple{KeyOrder, Vararg}}, a, b)
    o, os = first(order), Base.tail(order)

    ixa, aval = monomialorderkeypair(o.order, a)
    ixb, bval = monomialorderkeypair(o.order, b)

    isnothing(ixb) && return false
    isnothing(ixa) && return true

    Base.Order.lt(o.order, ixa, ixb) && return true
    Base.Order.lt(o.order, ixb, ixa) && return false

    return Base.Order.lt(os, aval, bval)
end

innerval(x) = x
innerval(x::Pair) = x.second

function Base.Order.lt(order::LexCombinationOrder{<:Tuple}, a, b)
    o, os = first(order), Base.tail(order)
    if Base.Order.lt(o, innerval(a), innerval(b))
        return true
    elseif Base.Order.lt(o, innerval(b), innerval(a))
        return false
    else
        return Base.Order.lt(os, a, b)
    end
end

# -----------------------------------------------------------------------------
#
# Constructor macros
#
# -----------------------------------------------------------------------------

function syms_from_comparison(expr, macroname)
    if expr isa Symbol
        return tuple(expr)
    elseif expr.head == :call && expr.args[1] == :>
        syms = expr.args[2:3]
        return tuple(syms...)
    elseif expr.head == :comparison
        syms = expr.args[1:2:end]
        comparisons = expr.args[2:2:end]
        all(isequal(:>), comparisons) || error("Use $macroname as follows: $macroname(x > y > z)")
        return tuple(syms...)
    else
        error("Use $macroname as follows: $macroname(x > y > z)")
    end
end

macro degrevlex(expr)
    syms = syms_from_comparison(expr, "@degrevlex")
    return MonomialOrdering{:degrevlex, Named{syms}}()
end

macro deglex(expr)
    syms = syms_from_comparison(expr, "@deglex")
    return MonomialOrdering{:deglex, Named{syms}}()
end

function _wrap_lonely_syms(sym::Symbol)
    return :( MonomialOrdering{:degrevlex, Named{($(QuoteNode(sym)),)}}() )
end

function _wrap_lonely_syms(expr::Expr)
    if expr.head == :macrocall && expr.args[1] == Symbol("@keyorder")
        return KeyOrder()
    end
    return expr
end

_wrap_lonely_syms(expr) = expr

macro lex(expr)
    syms = syms_from_comparison(expr, "@lex")
    syms = map(_wrap_lonely_syms, syms)

    return :( LexCombinationOrder($(syms...)) )
end


end # module
