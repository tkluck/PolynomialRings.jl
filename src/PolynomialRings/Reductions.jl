module Reductions

import Base: div, rem, divrem
import SparseArrays: spzeros

import ..Expansions: deg, atomicorder
import ..Modules: AbstractModuleElement, modulebasering
import ..MonomialOrderings: MonomialOrder
import ..Operators: RedType, Lead, Full, Tail
import ..Operators: one_step_div!, one_step_xdiv!, content
import ..Polynomials: Polynomial, monomialorder, leading_monomial
import ..Polynomials: PolynomialBy
import ..Util: @showprogress, unalias
import PolynomialRings: basering
import PolynomialRings: div!, rem!, xdiv!, xrem!, xdiv, xrem, xdivrem
import PolynomialRings: gröbner_basis, syzygies
import PolynomialRings: leaddiv, leaddivrem, leadrem

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

"""
    any_reductions = rem!(f, G)

Compute the multivariate reduction of a polynomial `f` by a vector of
polynomials `G`, in-place. By definition, this means that after applying
`rem!` no, leading term of a polynomial in `G` divides any monomial in `f`, and
`f + factors * G` is equal to the original value of `f` for some row
vector `factors`.

The return value `any_reductions` is `true` if and only if `factors` is nonzero.
Note that `factors` itself is not actually computed and not returned. If you
need to obtain it, use `div!`.

If you want to allow clearing denominators, e.g. reduce ```2x^2``` by ```3x```
even though your base ring is ℤ, use `xrem!` instead.

# Examples
In one variable, this is just the normal Euclidean algorithm:
```jldoctest
julia> using PolynomialRings

julia> R,(x,y) = polynomial_ring(:x, :y, basering=Complex{Int});

julia> f = x^2 + 1
x^2 + 1 + 0im

julia> rem!(f, [x-im])
true

julia> f
0

julia> g = x^2 + y^2 + 1
x^2 + y^2 + 1 + 0im

julia> rem!(g, [x, y])
true

julia> g
1 + 0im
```
"""
function rem!(f::M, G::AbstractVector; order::MonomialOrder=monomialorder(f), redtype::RedType=Full()) where M <: AbstractModuleElement
    if typeof(redtype) <: Full
        any_reductions = rem!(f, G, order=order, redtype=Lead())
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
        result = one_step_div!(f, g, order=order, redtype=redtype)
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
    any_reductions = xrem!(f, G)

Compute the multivariate reduction of a polynomial `f` by a vector of
polynomials `G`, in-place. By definition, this means that after applying
`rem!` no, leading term of a polynomial in `G` divides any monomial in `f`, and
`f + factors * G` is equal to `m` times the original value of `f` for some
scalar `m` and for some row vector `factors`.

The return value `any_reductions` is `true` if and only if `factors` is nonzero.
Note that `factors` itself is not actually computed and not returned. If you
need to obtain it, use `xdiv!`. The same holds for `m`.

The difference between `xdiv!` and `div` is that the former allows clearing
denominators, e.g. reduce ```2x^2``` by ```3x``` even when the base ring is ℤ.

# Examples
In one variable, this is just the normal Euclidean algorithm:
```jldoctest
julia> using PolynomialRings

julia> R,(x,y) = polynomial_ring(:x, :y, basering=Complex{Int});

julia> f = x^2 + 1
x^2 + 1 + 0im

julia> xrem!(f, [x-im])
true

julia> f
0

julia> g = x^2 + y^2 + 1
x^2 + y^2 + 1 + 0im

julia> xrem!(g, [x, y])
true

julia> g
1 + 0im
```
"""
function xrem!(f::M, G::AbstractVector; order::MonomialOrder=monomialorder(f), redtype::RedType=Full()) where M <: AbstractModuleElement
    if typeof(redtype) <: Full
        any_reductions = xrem!(f, G, order=order, redtype=Lead())
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
        result = one_step_xdiv!(f, g, order=order, redtype=redtype)
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

"""
    factors = div!(f, G)

Compute the multivariate reduction of a polynomial `f` by a vector of
polynomials `G`, in-place. By definition, this means that after applying
`rem!` no, leading term of a polynomial in `G` divides any monomial in `f`, and
`f + factors * G` is equal to the original value of `f`.

The return value is `nothing` if no reduction has taken place. This situation
could also be represented by the zero vector, but we choose `nothing` for
efficiency.

If you want to allow clearing denominators, e.g. reduce ```2x^2``` by ```3x```
even though your base ring is ℤ, use `xdiv!` instead.

# Examples
In one variable, this is just the normal Euclidean algorithm:
```jldoctest
julia> using PolynomialRings

julia> R,(x,y) = polynomial_ring(:x, :y, basering=Complex{Int});

julia> f = x^2 + 1 + 0im
x^2 + 1 + 0im

julia> collect(div!(f, [x-im]))
1×1 Array{Complex{Int64}[x,y],2}:
 x + 0 + 1im

julia> f
0

julia> g = x^2 + y^2 + 1
x^2 + y^2 + 1 + 0im

julia> collect(div!(g, [x, y]))
1×2 Array{Complex{Int64}[x,y],2}:
 x  y

julia> g
1 + 0im
```
"""
function div!(f::M, G::AbstractVector; order::MonomialOrder=monomialorder(f), redtype::RedType=Full()) where M <: AbstractModuleElement
    if typeof(redtype) <: Full
        factors = div!(f, G, order=order, redtype=Lead())
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
        factor = one_step_div!(f, g, order=order, redtype=redtype)
        if factor === nothing
            i += 1
        else
            factors[1, i] += factor
            i = 1
        end
    end
    return factors
end

"""
    m, factors = xdiv!(f, G)

Compute the multivariate reduction of a polynomial `f` by a vector of
polynomials `G`, in-place. By definition, this means that after applying
`rem!` no, leading term of a polynomial in `G` divides any monomial in `f`, and
`f + factors * G` is equal to `m` times the original value of `f`.

The difference between `xdiv!` and `div` is that the former allows clearing
denominators, e.g. reduce ```2x^2``` by ```3x``` even when the base ring is ℤ.

# Examples
In one variable, this is just the normal Euclidean algorithm:
```jldoctest
julia> using PolynomialRings

julia> R,(x,y) = polynomial_ring(:x, :y, basering=Complex{Int});

julia> f = x^2 + y^2 + 1
x^2 + y^2 + 1 + 0im

julia> xdiv!(f, [x-im])
(1 + 0im, Complex{Int64}[x,y][x + 0 + 1im])

julia> f
y^2

julia> g = x^2 + y^2 + 1
x^2 + y^2 + 1 + 0im

julia> xdiv!(g, [x, y])
(1 + 0im, Complex{Int64}[x,y][x y])

julia> g
1 + 0im
```
"""
function xdiv!(f::M, G::AbstractVector; order::MonomialOrder=monomialorder(f), redtype::RedType=Full()) where M <: AbstractModuleElement
    if typeof(redtype) <: Full
        m, factors = xdiv!(f, G, order=order, redtype=Lead())
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
        result = one_step_xdiv!(f, g, order=order, redtype=redtype)
        if result === nothing
            i += 1
        else
            k, factor = result
            m *= k # TODO: in-place for BigInt
            factors[1, :] *= k
            factors[1, i] += factor
            i = 1
        end
    end
    return m, factors
end

function div(f::M, G::AbstractVector; kwds...) where M <: AbstractModuleElement
    M′ = promote_type(M, eltype(G))
    f′ = unalias(M′, f)
    return div!(f′, G; kwds...)
end

function rem(f::M, G::AbstractVector; kwds...) where M <: AbstractModuleElement
    M′ = promote_type(M, eltype(G))
    f′ = unalias(M′, f)
    any_reductions = rem!(f′, G; kwds...)
    return any_reductions ? f′ : f
end

function divrem(f::M, G::AbstractVector; kwds...) where M <: AbstractModuleElement
    M′ = promote_type(M, eltype(G))
    f′ = unalias(M′, f)
    factors = div!(f′, G; kwds...)
    return factors, iszero(factors) ? f : f′
end

function xdiv(f::M, G::AbstractVector; kwds...) where M <: AbstractModuleElement
    M′ = promote_type(M, eltype(G))
    f′ = unalias(M′, f)
    return xdiv!(f′, G; kwds...)
end

"""
    f_red = xrem(f, G)

Return the multivariate reduction of a polynomial `f` by a vector of
polynomials `G`. By definition, this means that no leading term of a polynomial
in `G` divides any monomial in `f`, and `f_red + factors * G == m * f` for some
factors and for some integer `m`.

If you need to obtain the vector of factors, use `xdivrem` instead.

# Examples
In one variable, this is just the normal Euclidean algorithm:
```jldoctest
julia> using PolynomialRings

julia> R,(x,y) = polynomial_ring(:x, :y, basering=Complex{Int});

julia> xrem(x^2 + 1, [x-im])
0

julia> xrem(x^2 + y^2 + 1, [x, y])
1 + 0im
```
"""
function xrem(f::M, G::AbstractVector; kwds...) where M <: AbstractModuleElement
    M′ = promote_type(M, eltype(G))
    f′ = unalias(M′, f)
    any_reductions = xrem!(f′, G; kwds...)
    return any_reductions ? f′ : f
end

function xdivrem(f::M, G::AbstractVector; kwds...) where M <: AbstractModuleElement
    M′ = promote_type(M, eltype(G))
    f′ = unalias(M′, f)
    m, factors = xdiv!(f′, G; kwds...)
    return m, factors, iszero(factors) ? f : f′
end

# _unpack for div's result
_unpack(a::AbstractArray) = a[1]
# _unpack for divrem's result
_unpack(a::Tuple{<:AbstractArray,<:Any}) = a[1][1], a[2]
# _unpack for xdivrem's result
_unpack(a::Tuple{<:Any,<:AbstractArray,<:Any}) = a[1], a[2][1], a[3]
# _unpack for xdiv!'s result
_unpack(a::Tuple{<:Any,<:AbstractArray}) = a[1], a[2][1]
# _unpack for rem's result
_unpack(a) = a

# ergonomic versions:
#     div(f, g) for div(f, [g])
#     leaddiv for div(; redtype=Lead())
#     div(f, g) for div(f, g, order=monomialorder(f)) if f and g have the same order
# etc
for fn in [:divrem, :div, :rem]
    for x in ["", "x"]
        for inplace in ["", "!"]
            for (redtype, prefix) in [(Lead(), "lead"), (Tail(), "tail")]
                fnname = Symbol(x, prefix, fn, inplace)
                target = Symbol(x, fn, inplace)
                @eval function $fnname(f::PolynomialBy{Order}, g::PolynomialBy{Order}; order=monomialorder(f)) where Order
                    $target(f, [g], order=order, redtype=$redtype) |> _unpack
                end
            end
            fnname = Symbol(x, fn, inplace)
            target = Symbol(x, fn, inplace)
            @eval function $fnname(f::PolynomialBy{Order}, g::PolynomialBy{Order}; order=monomialorder(f), redtype=Full()) where Order
                $target(f, [g], order=order, redtype=redtype) |> _unpack
            end
        end
    end
end

interreduce(G::AbstractVector{<:AbstractModuleElement}; kwds...) = interreduce!(deepcopy(G); kwds...)

function interreduce!(G::AbstractVector{<:AbstractModuleElement}; kwds...)
    order = get(kwds, :order, monomialorder(modulebasering(eltype(G))))

    lm(f) = leading_monomial(f, order=order)
    S = unique(map(lm, G))
    @showprogress "Interreducing" for ix in 1:length(G)
        xrem!(G[ix], G[[1 : ix - 1; ix + 1 : end]]; kwds...)
        if !iszero(G[ix]) && basering(modulebasering(eltype(G))) <: Integer
            G[ix] ÷= content(G[ix])
        end
    end

    filter!(!iszero, G)
    T = unique(map(lm, G))

    G
end

function mingenerators(I::AbstractVector{<:AbstractModuleElement})
    G = gröbner_basis(I, alg=:gwv)
    syz = syzygies(G)

    superfluous_cols = Int[]
    for row in axes(syz, 1)
        for col in axes(syz, 2)
            if deg(syz[row, col], atomicorder(monomialorder(eltype(I)))) == 0
                c = syz[row, col].coeffs[1]
                for r in [1:row-1; row+1:size(syz, 1)]
                    syz[r, :] -= (syz[r, col] // c ) * syz[row, :]
                end
                push!(superfluous_cols, col)
            end
        end
    end

    for col in sort!(superfluous_cols, rev=true)
        deleteat!(G, col)
    end

    return G
end

end
