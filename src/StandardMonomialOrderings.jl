"""
    module PolynomialRings.StandardMonomialOrderings

This module contains the implementation of `Base.Order.lt` for the
:degrevlex, the :deglex and the :lex orders. This is not part of
the `MonomialOrderings` module in order to break a dependency cycle
with the `AbstractMonomials` module.
"""
module StandardMonomialOrderings

import ..AbstractMonomials: AbstractMonomial, exponentsnz, revexponentsnz
import ..MonomialOrderings: MonomialOrder
import ..NamingSchemes: namingscheme
import PolynomialRings: deg, leading_monomial

function Base.Order.lt(order::MonomialOrder{:degrevlex}, a, b)
    iszero(b) && return false
    iszero(a) && return true
    a = leading_monomial(a, order=order)
    b = leading_monomial(b, order=order)
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

function Base.Order.lt(order::MonomialOrder{:deglex}, a, b)
    iszero(b) && return false
    iszero(a) && return true
    a = leading_monomial(a, order=order)
    b = leading_monomial(b, order=order)
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

function Base.Order.lt(order::MonomialOrder{:lex}, a, b)
    iszero(b) && return false
    iszero(a) && return true
    a = leading_monomial(a, order=order)
    b = leading_monomial(b, order=order)
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


end # module
