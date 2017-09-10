module Modules

import PolynomialRings.Polynomials: Polynomial
import PolynomialRings.Operators: leaddivrem
import PolynomialRings.NamedPolynomials: NamedPolynomial

AbstractModuleElement{P<:Polynomial} = Union{P, AbstractArray{P}}
AbstractNamedModuleElement{NP<:NamedPolynomial} = Union{NP, AbstractArray{NP}}
modulebasering(::Type{A}) where A <: AbstractModuleElement{P} where P<:Polynomial = P

_P = Union{Polynomial,NamedPolynomial}

import PolynomialRings: leading_term, iszero, base_extend
import Base: divrem

function leading_term(x::AbstractArray{P}) where P<:Polynomial
    i = findfirst(x)
    if i>0
        return (i, x[i])
    else
        return nothing
    end
end

iszero(x::AbstractArray{P}) where P<:_P = (i = findfirst(x); i>0 ? iszero(x[i]) : true)

base_extend(x::AbstractArray{P}, ::Type{C}) where P<:_P where C = map(p->base_extend(p,C), x)
base_extend(x::AbstractArray{P})            where P<:_P         = map(base_extend, x)

function divrem(a::AbstractArray{P}, b::AbstractArray{P}) where P<:Polynomial
    i = findfirst(b)
    if i>0
        (q,r) = divrem(a[i], b[i])
        return q, a - q*b
    else
        return zero(P), a
    end
end

function leaddivrem(a::AbstractArray{P}, b::AbstractArray{P}) where P<:Polynomial
    i = findfirst(b)
    if i>0
        (q,r) = leaddivrem(a[i], b[i])
        return q, a - q*b
    else
        return zero(P), a
    end
end


end
