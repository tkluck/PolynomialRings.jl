module Modules

import PolynomialRings.Polynomials: Polynomial
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

function divrem(redtype::RedType,a::A, b::A) where A<:AbstractArray{<:Polynomial}
    i = findfirst(b)
    if i>0
        (q,r) = divrem(redtype,a[i], b[i])
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

div(redtype::RedType, a::A, b::A) where A<:AbstractArray{<:Polynomial} = divrem(redtype, a, b)[1]
rem(redtype::RedType, a::A, b::A) where A<:AbstractArray{<:Polynomial} = divrem(redtype, a, b)[2]

leaddivrem(f::A,g::AbstractVector{A}) where A<:AbstractArray{Polynomial} = divrem(Lead(), f, g)
divrem(f::A,g::AbstractVector{A})     where A<:AbstractArray{Polynomial} = divrem(Full(), f, g)
leadrem(f::A,g::AbstractVector{A})    where A<:AbstractArray{Polynomial} = rem(Lead(), f, g)
rem(f::A,g::AbstractVector{A})        where A<:AbstractArray{Polynomial} = rem(Full(), f, g)
leaddiv(f::A,g::AbstractVector{A})    where A<:AbstractArray{Polynomial} = div(Lead(), f, g)
div(f::A,g::AbstractVector{A})        where A<:AbstractArray{Polynomial} = div(Full(), f, g)

end
