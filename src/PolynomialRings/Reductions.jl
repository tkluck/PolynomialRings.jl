module Reductions

import SparseArrays: spzeros

import PolynomialRings.MonomialOrderings: MonomialOrder
import PolynomialRings.Polynomials: Polynomial, monomialorder
import PolynomialRings.Modules: AbstractModuleElement, modulebasering
import PolynomialRings.Polynomials: PolynomialBy

# imports for overloading
import Base: div, rem, divrem
import PolynomialRings.Operators: RedType, Lead, Full, Tail
import PolynomialRings.Operators: one_step_div, one_step_rem, one_step_divrem

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
julia> using PolynomialRings

julia> R,(x,y) = polynomial_ring(:x, :y, basering=Complex{Int});

julia> rem(x^2 + 1, [x-im])
0

julia> rem(x^2 + y^2 + 1, [x, y])
1 + 0im
```
"""
function rem(redtype::RedType, o::MonomialOrder, f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    if typeof(redtype) <: Full
        f_red = rem(Lead(),o,f,G)
    elseif typeof(redtype) <: Lead || typeof(redtype) <: Tail
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
        reduced = one_step_rem(redtype, o, f_red, g)
        if reduced !== f_red
            i = 1
        else
            i += 1
        end
        f_red = reduced
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
julia> using PolynomialRings

julia> R,(x,y) = polynomial_ring(:x, :y, basering=Complex{Int});

julia> divrem(x^2 + 1, [x-im])
(Complex{Int64}[x,y][x + 0 + 1im], 0)

julia> divrem(x^2 + y^2 + 1, [x, y])
(Complex{Int64}[x,y][x y], 1 + 0im)

```
"""
function divrem(redtype::RedType, o::MonomialOrder, f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    if typeof(redtype) <: Full
        factors, f_red = divrem(Lead(),o,f,G)
    elseif typeof(redtype) <: Lead || typeof(redtype) <: Tail
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
        q, f_red = one_step_divrem(redtype, o, f_red, g)
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

function div(redtype::RedType, o::MonomialOrder, f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    divrem(redtype, o, f, G)[1]
end

_unpack(a) = a[1]
_unpack(a::Tuple) = a[1][1], a[2]
leaddivrem(f::PolynomialBy{Order}, g::PolynomialBy{Order}) where Order = divrem(Lead(), Order(), f, [g]) |> _unpack
divrem(f::PolynomialBy{Order}, g::PolynomialBy{Order})     where Order = divrem(Full(), Order(), f, [g]) |> _unpack
leadrem(f::PolynomialBy{Order}, g::PolynomialBy{Order})    where Order = rem(Lead(), Order(), f, [g])
rem(f::PolynomialBy{Order}, g::PolynomialBy{Order})        where Order = rem(Full(), Order(), f, [g])
leaddiv(f::PolynomialBy{Order}, g::PolynomialBy{Order})    where Order = div(Lead(), Order(), f, [g]) |> _unpack
div(f::PolynomialBy{Order}, g::PolynomialBy{Order})        where Order = div(Full(), Order(), f, [g]) |> _unpack

divrem(redtype::RedType, o::MonomialOrder, f::P, g::P) where P<:Polynomial = divrem(redtype, o, f, [g]) |> _unpack
rem(redtype::RedType, o::MonomialOrder, f::P, g::P)    where P<:Polynomial = rem(redtype, o, f, [g])
div(redtype::RedType, o::MonomialOrder, f::P, g::P)    where P<:Polynomial = div(redtype, o, f, [g]) |> _unpack

leaddivrem(o::MonomialOrder, f, g) = divrem(Lead(), o, f, g)
divrem(o::MonomialOrder, f, g) = divrem(Full(), o, f, g)
leadrem(o::MonomialOrder, f, g) = rem(Lead(), o, f, g)
rem(o::MonomialOrder, f, g) = rem(Full(), o, f, g)
leaddiv(o::MonomialOrder, f, g) = div(Lead(), o, f, g)
div(o::MonomialOrder, f, g) = div(Full(), o, f, g)

leaddivrem(f::M,g::AbstractVector{M}) where M<:Polynomial = divrem(Lead(), monomialorder(M), f, g)
divrem(f::M,g::AbstractVector{M})     where M<:Polynomial = divrem(Full(), monomialorder(M), f, g)
leadrem(f::M,g::AbstractVector{M})    where M<:Polynomial = rem(Lead(), monomialorder(M), f, g)
rem(f::M,g::AbstractVector{M})        where M<:Polynomial = rem(Full(), monomialorder(M), f, g)
leaddiv(f::M,g::AbstractVector{M})    where M<:Polynomial = div(Lead(), monomialorder(M), f, g)
div(f::M,g::AbstractVector{M})        where M<:Polynomial = div(Full(), monomialorder(M), f, g)


end
