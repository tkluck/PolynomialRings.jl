module Reductions

import PolynomialRings.Polynomials: Polynomial, monomialorder
import PolynomialRings.Modules: AbstractModuleElement, modulebasering

# imports for overloading
import Base: div, rem, divrem
import PolynomialRings.Operators: leaddiv, leadrem, leaddivrem

function leadrem(f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    f_red = f
    i = 1
    while i<=length(G)
        g = G[i]
        iszero(g) && continue
        q, f_red = leaddivrem(f_red, g)
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

function leaddivrem(f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    factors = transpose(spzeros(modulebasering(M), length(G)))
    f_red = f
    i = 1
    while i<=length(G)
        g = G[i]
        iszero(g) && continue
        q, f_red = leaddivrem(f_red, g)
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

leaddiv(f::M, G::AbstractVector{M}) where M <: AbstractModuleElement = leaddivrem(f, G)[1]

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
rem(f::P, G::AbstractVector{P}) where P <: Polynomial = _rem(f,G)
rem(f::M, G::AbstractVector{M}) where M <: AbstractArray{<:Polynomial} = _rem(f,G)
function _rem(f, G)
    f_red = leadrem(f,G)

    i=1
    while i<=length(G)
        g = G[i]
        iszero(g) && continue
        q, f_red = divrem(f_red, g)
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
divrem(f::P, G::AbstractVector{P}) where P <: Polynomial = _divrem(f,G)
divrem(f::M, G::AbstractVector{M}) where M <: AbstractArray{<:Polynomial} = _divrem(f,G)
function _divrem(f, G)
    factors, f_red = leaddivrem(f,G)

    i=1
    while i<=length(G)
        g = G[i]
        iszero(g) && continue
        q, f_red = divrem(f_red, g)
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

div(f::P, G::AbstractVector{P}) where P <: Polynomial = _divrem(f,G)[1]
div(f::M, G::AbstractVector{M}) where M <: AbstractArray{<:Polynomial} = _divrem(f,G)[1]

end
