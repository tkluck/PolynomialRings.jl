module GröbnerF4GB


import PolynomialRings

import DataStructures: SortedDict, DefaultDict
import IterTools: chain

import ..Backends.Gröbner: F4GB
import ..MonomialOrderings: MonomialOrder, @withmonomialorder
import ..Polynomials: Polynomial, terms
import ..Terms: monomial
import PolynomialRings: gröbner_basis
import PolynomialRings: maybe_div, termtype, lcm_multipliers

"""
    gröbner_basis = f4gb(monomialorder, polynomials)

An implementation of the F4GB algorithm as popularized by
> Rusydi Makarim, Marc Stevens, "M4GB: An efficient Groebner-basis algorithm", ISSAC 2017
"""
function f4gb(order::MonomialOrder, F::AbstractVector{<:Polynomial})
    @withmonomialorder order

    L, M = [], Dict()
    P = []
    for f in F
        f = mulfullreduce!(L, M, one(termtype(f)), f, order=order)
        if !iszero(f)
            updatereduce!(L, M, P, f, order=order)
        end
    end
    while !isempty(P)
        (fₗₘ, gₗₘ) = select!(P)
        f = M[fₗₘ]; g = M[gₗₘ]

        c_f, c_g = lcm_multipliers(lt(f), lt(g))
        h₁ = mulfullreduce!(L, M, c_f, tail(f), order=order)
        h₂ = mulfullreduce!(L, M, c_g, tail(g), order=order)
        if (h = h₁ - h₂) |> !iszero
            updatereduce!(L, M, P, h, order=order)
        end
    end

    return [M[fₗₘ] for fₗₘ in L]
end

select!(P) = popfirst!(P)

function updatereduce!(L, M, P, f; order)
    @withmonomialorder order

    H = [f // lc(f)]

    while true
        U = setdiff(
            Set(monomial(t) for x in chain(values(M), H) for t in terms(tail(x))),
            map(lm, H)
        )
        filter!(u -> divides(lm(f), u), U)
        isempty(U) && break
        u = maximum(order, U)
        h = mulfullreduce!(L, M, maybe_div(u, lm(f)) * inv(lc(f)), tail(f), order=order)
        push!(H, u + h)
    end

    sort!(H, order=order)
    while !isempty(H)
        h = popfirst!(H)
        for g in H
            c = g[lm(h)]
            @. g -= c * h
        end
        for g in values(M)
            c = g[lm(h)]
            @. g -= c * h
        end
        M[lm(h)] = h
    end
    update!(L, P, lm(f))
end

function update!(L, P, fₗₘ)
    push!(L, fₗₘ)
    for l in L
        if lcm(l, fₗₘ) != l*fₗₘ
            push!(P, (l, fₗₘ))
        end
    end
end

function mulfullreduce!(L, M, t, f; order)
    @withmonomialorder order

    h = zero(f)
    for s in terms(f, order=order)
        r = t * s
        g = getreductor!(M, L, r; order=order)
        if g != nothing
            d = maybe_div(r, lt(g))
            h .-= d .* tail(g)
        else
            h .+= r
        end
    end

    return h
end

function getreductor!(M, L, r; order)
    @withmonomialorder order

    if monomial(r) in keys(M)
        return M[monomial(r)]
    else
        fₗₘ = reducesel(L, monomial(r))
        fₗₘ == nothing && return nothing
        f = M[fₗₘ]
        h = mulfullreduce!(L, M, maybe_div(r, lt(f)), tail(f), order=order)
        res = r + h
        M[lm(res)] = res
        return res
    end
end

function reducesel(L, m)
    for l in L
        divides(l, m) && return l
    end
    return nothing
end

divides(f, g) = maybe_div(g, f) != nothing

function gröbner_basis(::F4GB, o::MonomialOrder, G::AbstractArray{<:Polynomial}; kwds...)
    isempty(G) && return copy(G)
    return f4gb(o, G, kwds...)
end

end
