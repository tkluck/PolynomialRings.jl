module Reductions

import PolynomialRings.Polynomials: Polynomial, monomialorder
import PolynomialRings.Modules: AbstractModuleElement, modulebasering

# imports for overloading
import Base: div, rem, divrem
import PolynomialRings.Operators: RedType, Lead, Full, leaddiv, leadrem, leaddivrem

"""
    f_red = rem(f, G)

Return the multivariate reduction of a polynomial `f` by a vector of
polynomials `G`. By definition, this means that no leading term of a polynomial
in `G` divides any monomial in `f`, and `f_red + factors * G == f` for some
factors.

If you need to obtain the vector of factors, use `divrem` instead.

# Examples
In one variable, this is just the normal Euclidean algorithm:
```jldoctest
julia> R,(x,y) = polynomial_ring(:x, :y, basering=Complex{Int});
julia> rem(x^1 + 1, [x-im])
0
julia> rem(x^2 + y^2 + 1, [x, y])
1
```
"""
function rem(redtype::RedType, f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    if typeof(redtype) <: Full
        f_red = rem(Lead(),f,G)
    elseif typeof(redtype) <: Lead
        f_red = f
    else
    @assert false "unreachable: didn't expect $redtype"
    end
    i = 1
    while i<=length(G)
        g = G[i]
        if iszero(g)
            i += 1
            continue
        end
        q, f_red = divrem(redtype, f_red, g)
        if !iszero(q)
            i = 1
        else
            i += 1
        end
        if iszero(f_red)
            return f_red
        end
    end
    return f_red
end

"""
    factors, f_red = divrem(f, G)

Return the multivariate reduction of a polynomial `f` by a vector of
polynomials `G`, together with  row vector of factors. By definition, this
means that no leading term of a polynomial in `G` divides any monomial in
`f`, and `f_red + factors * G == f`.

# Examples
In one variable, this is just the normal Euclidean algorithm:
```jldoctest
julia> R,(x,y) = polynomial_ring(:x, :y, basering=Complex{Int});
julia> divrem(x^1 + 1, [x-im])
(0, [x+im]')
julia> divrem(x^2 + y^2 + 1, [x, y])
(1, [x,y]')
```
"""
function divrem(redtype::RedType, f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    if typeof(redtype) <: Full
        factors, f_red = divrem(Lead(),f,G)
    elseif typeof(redtype) <: Lead
        factors = transpose(spzeros(modulebasering(M), length(G)))
        f_red = f
    else
        @assert false "unreachable: didn't expect $redtype"
    end
    i = 1
    while i<=length(G)
        g = G[i]
        if iszero(g)
            i += 1
            continue
        end
        q, f_red = divrem(redtype, f_red, g)
        if !iszero(q)
            factors[1, i] += q
            i = 1
        else
            i += 1
        end
        if iszero(f_red)
            return factors, f_red
        end
    end
    return factors, f_red
end

function div(redtype::RedType, f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    divrem(redtype, f, G)[1]
end

leaddivrem(f::M,g::AbstractVector{M}) where M<:Polynomial = divrem(Lead(), f, g)
divrem(f::M,g::AbstractVector{M})     where M<:Polynomial = divrem(Full(), f, g)
leadrem(f::M,g::AbstractVector{M})    where M<:Polynomial = rem(Lead(), f, g)
rem(f::M,g::AbstractVector{M})        where M<:Polynomial = rem(Full(), f, g)
leaddiv(f::M,g::AbstractVector{M})    where M<:Polynomial = div(Lead(), f, g)
div(f::M,g::AbstractVector{M})        where M<:Polynomial = div(Full(), f, g)

leaddivrem(f::M,g::AbstractVector{M}) where M<:AbstractArray{<:Polynomial} = divrem(Lead(), f, g)
divrem(f::M,g::AbstractVector{M})     where M<:AbstractArray{<:Polynomial} = divrem(Full(), f, g)
leadrem(f::M,g::AbstractVector{M})    where M<:AbstractArray{<:Polynomial} = rem(Lead(), f, g)
rem(f::M,g::AbstractVector{M})        where M<:AbstractArray{<:Polynomial} = rem(Full(), f, g)
leaddiv(f::M,g::AbstractVector{M})    where M<:AbstractArray{<:Polynomial} = div(Lead(), f, g)
div(f::M,g::AbstractVector{M})        where M<:AbstractArray{<:Polynomial} = div(Full(), f, g)

end
