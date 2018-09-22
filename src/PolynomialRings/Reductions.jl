module Reductions

import SparseArrays: spzeros

import PolynomialRings.MonomialOrderings: MonomialOrder
import PolynomialRings.Polynomials: Polynomial, monomialorder
import PolynomialRings.Modules: AbstractModuleElement, modulebasering
import PolynomialRings.Polynomials: PolynomialBy
import PolynomialRings.Operators: one_step_div!, one_step_xdiv!
import PolynomialRings.Operators: RedType, Lead, Full, Tail

# imports for overloading
import Base: div, rem, divrem
import PolynomialRings: div!, rem!, xdiv!, xrem!, xdiv, xrem, xdivrem

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
function rem end

function rem!(redtype::RedType, o::MonomialOrder, f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    if typeof(redtype) <: Full
        any_reductions = rem!(Lead(), o, f, G)
    elseif typeof(redtype) <: Lead || typeof(redtype) <: Tail
        any_reductions = false
    else
        @assert false "unreachable: didn't expect $redtype"
    end
    i = 1
    while i<=length(G) && !iszero(f)
        g = G[i]
        if iszero(g)
            i += 1
            continue
        end
        result = one_step_div!(redtype, o, f, g)
        if result === nothing
            i += 1
        else
            any_reductions = true
            i = 1
        end
    end
    return any_reductions
end

function xrem!(redtype::RedType, o::MonomialOrder, f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    if typeof(redtype) <: Full
        any_reductions = xrem!(Lead(), o, f, G)
    elseif typeof(redtype) <: Lead || typeof(redtype) <: Tail
        any_reductions = false
    else
        @assert false "unreachable: didn't expect $redtype"
    end
    i = 1
    while i<=length(G) && !iszero(f)
        g = G[i]
        if iszero(g)
            i += 1
            continue
        end
        result = one_step_xdiv!(redtype, o, f, g)
        if result === nothing
            i += 1
        else
            any_reductions = true
            i = 1
        end
    end
    return any_reductions
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
function divrem end

function div!(redtype::RedType, o::MonomialOrder, f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    if typeof(redtype) <: Full
        factors = div!(Lead(), o, f, G)
    elseif typeof(redtype) <: Lead || typeof(redtype) <: Tail
        factors = transpose(spzeros(modulebasering(M), length(G)))
    else
        @assert false "unreachable: didn't expect $redtype"
    end
    i = 1
    while i<=length(G) && !iszero(f)
        g = G[i]
        if iszero(g)
            i += 1
            continue
        end
        factor = one_step_div!(redtype, o, f, g)
        if factor === nothing
            i += 1
        else
            factors[1, i] += factor
            i = 1
        end
    end
    return factors
end

function xdiv!(redtype::RedType, o::MonomialOrder, f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    if typeof(redtype) <: Full
        m, factors = xdiv!(Lead(), o, f, G)
    elseif typeof(redtype) <: Lead || typeof(redtype) <: Tail
        m = one(basering(f))
        factors = transpose(spzeros(modulebasering(M), length(G)))
    else
        @assert false "unreachable: didn't expect $redtype"
    end
    i = 1
    while i<=length(G) && !iszero(f)
        g = G[i]
        if iszero(g)
            i += 1
            continue
        end
        restult = one_step_xdiv!(redtype, o, f, g)
        if result === nothing
            i += 1
        else
            k, factor = result
            m *= k # TODO: in-place for BigInt
            factors[1, i] += factor
            i = 1
        end
    end
    return m, factors
end

function div(redtype::RedType, o::MonomialOrder, f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    f′ = deepcopy(f)
    return div!(redtype, o, f′, G)
end

function rem(redtype::RedType, o::MonomialOrder, f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    f′ = deepcopy(f)
    any_reductions = rem!(redtype, o, f′, G)
    return any_reductions ? f′ : f
end

function divrem(redtype::RedType, o::MonomialOrder, f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    f′ = deepcopy(f)
    factors = div!(redtype, o, f′, G)
    return factors, iszero(factors) ? f : f′
end

function xdiv(redtype::RedType, o::MonomialOrder, f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    f′ = deepcopy(f)
    return xdiv!(redtype, o, f′, G)
end

function xrem(redtype::RedType, o::MonomialOrder, f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    f′ = deepcopy(f)
    any_reductions = xrem!(redtype, o, f′, G)
    return any_reductions ? f′ : f
end

function xdivrem(redtype::RedType, o::MonomialOrder, f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    f′ = deepcopy(f)
    m, factors = xdiv!(redtype, o, f′, G)
    return m, factors, iszero(factors) ? f : f′
end

# _unpack for div's result
_unpack(a) = a[1]
# _unpack for divrem's result
_unpack(a::Tuple{A,B}) where {A,B} = a[1][1], a[2]
# _unpack for xdivrem's result
_unpack(a::Tuple{A,B,C}) where {A,B,C} = a[1], a[2][1], a[3]
leaddivrem(f::PolynomialBy{Order}, g::PolynomialBy{Order}) where Order = divrem(Lead(), Order(), f, [g]) |> _unpack
divrem(f::PolynomialBy{Order}, g::PolynomialBy{Order})     where Order = divrem(Full(), Order(), f, [g]) |> _unpack
leadrem(f::PolynomialBy{Order}, g::PolynomialBy{Order})    where Order = rem(Lead(), Order(), f, [g])
rem(f::PolynomialBy{Order}, g::PolynomialBy{Order})        where Order = rem(Full(), Order(), f, [g])
leaddiv(f::PolynomialBy{Order}, g::PolynomialBy{Order})    where Order = div(Lead(), Order(), f, [g]) |> _unpack
div(f::PolynomialBy{Order}, g::PolynomialBy{Order})        where Order = div(Full(), Order(), f, [g]) |> _unpack

div!(f::PolynomialBy{Order}, g::PolynomialBy{Order})        where Order = div!(Full(), Order(), f, [g]) |> _unpack
rem!(f::PolynomialBy{Order}, g::PolynomialBy{Order})        where Order = rem!(Full(), Order(), f, [g]) |> _unpack
xdiv!(f::PolynomialBy{Order}, g::PolynomialBy{Order})        where Order = xdiv!(Full(), Order(), f, [g]) |> _unpack
xrem!(f::PolynomialBy{Order}, g::PolynomialBy{Order})        where Order = xrem!(Full(), Order(), f, [g]) |> _unpack
xdiv(f::PolynomialBy{Order}, g::PolynomialBy{Order})        where Order = xdiv(Full(), Order(), f, [g]) |> _unpack
xrem(f::PolynomialBy{Order}, g::PolynomialBy{Order})        where Order = xrem(Full(), Order(), f, [g]) |> _unpack
xdivrem(f::PolynomialBy{Order}, g::PolynomialBy{Order})        where Order = xdivrem(Full(), Order(), f, [g]) |> _unpack

divrem(redtype::RedType, o::MonomialOrder, f::P, g::P) where P<:Polynomial = divrem(redtype, o, f, [g]) |> _unpack
rem(redtype::RedType, o::MonomialOrder, f::P, g::P)    where P<:Polynomial = rem(redtype, o, f, [g])
div(redtype::RedType, o::MonomialOrder, f::P, g::P)    where P<:Polynomial = div(redtype, o, f, [g]) |> _unpack
xdiv(redtype::RedType, o::MonomialOrder, f::P, g::P)    where P<:Polynomial = xdiv(redtype, o, f, [g]) |> _unpack
xrem(redtype::RedType, o::MonomialOrder, f::P, g::P)    where P<:Polynomial = xrem(redtype, o, f, [g]) |> _unpack
xdivrem(redtype::RedType, o::MonomialOrder, f::P, g::P)    where P<:Polynomial = xdivrem(redtype, o, f, [g]) |> _unpack

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
div!(f::M,g::AbstractVector{M})       where M<:Polynomial = div!(Full(), monomialorder(M), f, g)
rem!(f::M,g::AbstractVector{M})       where M<:Polynomial = rem!(Full(), monomialorder(M), f, g)
xdiv!(f::M,g::AbstractVector{M})      where M<:Polynomial = xdiv!(Full(), monomialorder(M), f, g)
xrem!(f::M,g::AbstractVector{M})      where M<:Polynomial = xrem!(Full(), monomialorder(M), f, g)
xdiv(f::M,g::AbstractVector{M})       where M<:Polynomial = xdiv(Full(), monomialorder(M), f, g)
xrem(f::M,g::AbstractVector{M})       where M<:Polynomial = xrem(Full(), monomialorder(M), f, g)
xdivrem(f::M,g::AbstractVector{M})    where M<:Polynomial = xdivrem(Full(), monomialorder(M), f, g)


end
