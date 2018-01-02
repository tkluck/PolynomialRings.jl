module Modules

import PolynomialRings.Polynomials: Polynomial, monomialorder
import PolynomialRings.MonomialOrderings: MonomialOrder
import PolynomialRings.Operators: RedType, leaddiv, leadrem, leaddivrem

AbstractModuleElement{P<:Polynomial} = Union{P, AbstractArray{P}}
modulebasering(::Type{A}) where A <: AbstractModuleElement{P} where P<:Polynomial = P
modulebasering(::A)       where A <: AbstractModuleElement{P} where P<:Polynomial = modulebasering(A)

import PolynomialRings: leading_term, iszero, base_extend
import Base: div, rem, divrem

function leading_term(x::AbstractArray{P}) where P<:Polynomial
    i = findfirst(x)
    if i>0
        return (i, x[i])
    else
        return nothing
    end
end

iszero(x::AbstractArray{P}) where P<:Polynomial = (i = findfirst(x); i>0 ? iszero(x[i]) : true)

base_extend(x::AbstractArray{P}, ::Type{C}) where P<:Polynomial where C = map(p->base_extend(p,C), x)
base_extend(x::AbstractArray{P})            where P<:Polynomial         = map(base_extend, x)

function divrem(redtype::RedType, o::MonomialOrder, a::A, b::A) where A<:AbstractArray{<:Polynomial}
    i = findfirst(b)
    if i>0
        (q,r) = divrem(redtype, o, a[i], b[i])
        if iszero(q)
            # make sure to maintain object identity for a
            return q, a
        else
            return q, a - q*b
        end
    else
        return zero(P), a
    end
end

div(redtype::RedType, o::MonomialOrder, a::A, b::A) where A<:AbstractArray{<:Polynomial} = divrem(redtype, o, a, b)[1]
rem(redtype::RedType, o::MonomialOrder, a::A, b::A) where A<:AbstractArray{<:Polynomial} = divrem(redtype, o, a, b)[2]

leaddivrem(f::A,g::AbstractVector{A}) where A<:AbstractArray{P} where P<:Polynomial = divrem(Lead(), monomialorder(P), f, g)
divrem(f::A,g::AbstractVector{A})     where A<:AbstractArray{P} where P<:Polynomial = divrem(Full(), monomialorder(P), f, g)
leadrem(f::A,g::AbstractVector{A})    where A<:AbstractArray{P} where P<:Polynomial = rem(Lead(), monomialorder(P), f, g)
rem(f::A,g::AbstractVector{A})        where A<:AbstractArray{P} where P<:Polynomial = rem(Full(), monomialorder(P), f, g)
leaddiv(f::A,g::AbstractVector{A})    where A<:AbstractArray{P} where P<:Polynomial = div(Lead(), monomialorder(P), f, g)
div(f::A,g::AbstractVector{A})        where A<:AbstractArray{P} where P<:Polynomial = div(Full(), monomialorder(P), f, g)

end
