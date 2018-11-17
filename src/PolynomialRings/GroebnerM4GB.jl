module GröbnerF4GB


import PolynomialRings
import Base.Iterators: flatten

import DataStructures: PriorityQueue, enqueue!, dequeue!
import IterTools: chain
import ProgressMeter: Progress, finish!, next!

import ..Backends.Gröbner: M4GB
import ..MonomialOrderings: MonomialOrder, @withmonomialorder
import ..Polynomials: Polynomial, terms
import ..Terms: monomial
import PolynomialRings: gröbner_basis, monomialtype
import PolynomialRings: maybe_div, termtype, lcm_multipliers

"""
    gröbner_basis = m4gb(monomialorder, polynomials)

An implementation of the M4GB algorithm as popularized by
> Rusydi Makarim, Marc Stevens, "M4GB: An efficient Groebner-basis algorithm", ISSAC 2017
"""
function m4gb(order::MonomialOrder, F::AbstractVector{<:Polynomial})
    @withmonomialorder order

    R = eltype(F); LM = monomialtype(R)
    L, M = Set{LM}(), Dict{LM, R}()
    P = PriorityQueue{Tuple{LM, LM}, LM}(order)

    for f in F
        f = mulfullreduce!(L, M, one(termtype(f)), f, order=order)
        if !iszero(f)
            updatereduce!(L, M, P, f, order=order)
        end
    end
    progress = Progress(length(P), "Computing Gröbner basis: ")
    loops = 0
    while !isempty(P)
        (fₗₘ, gₗₘ) = select!(P)
        f = M[fₗₘ]; g = M[gₗₘ]

        progress.n = length(P) + loops
        next!(progress; showvalues = [(Symbol("|L|"), length(L)), (Symbol("|P|"), length(P)), (:loops, loops)])

        c_f, c_g = lcm_multipliers(lt(f), lt(g))
        h₁ = mulfullreduce!(L, M, c_f, tail(f), order=order)
        h₂ = mulfullreduce!(L, M, c_g, tail(g), order=order)
        if (h = h₁ - h₂) |> !iszero
            updatereduce!(L, M, P, h, order=order)
        end
        loops += 1
    end
    finish!(progress)

    return [M[fₗₘ] for fₗₘ in L]
end

select!(P) = dequeue!(P)

function updatereduce!(L, M, P, f; order)
    @withmonomialorder order

    H = [f // lc(f)]
    lm_H = Set(lm(h) for h in H)

    while true
        U = [monomial(t) for x in flatten((values(M), H)) for t in x.terms[1:end-1]]
        filter!(u -> u ∉ lm_H && divides(lm(f), u), U)
        isempty(U) && break

        u = maximum(order, U)
        h = mulfullreduce!(L, M, maybe_div(u, lm(f)) * inv(lc(f)), tail(f), order=order)
        push!(H, u + h)
        push!(lm_H, u)
    end

    sort!(H, order=order)
    while !isempty(H)
        h = popfirst!(H)
        for g in H
            if (c = g[lm(h)]) |> !iszero
                @. g -= c * h
            end
        end
        for g in values(M)
            if (c = g[lm(h)]) |> !iszero
                @. g -= c * h
            end
        end
        M[lm(h)] = h
    end
    update!(L, P, lm(f))
end

function update!(L, P, fₗₘ)
    C = similar(P)
    for gₗₘ in L
        enqueue!(C, (fₗₘ, gₗₘ), lcm(fₗₘ, gₗₘ))
    end
    D = []
    while !isempty(C)
        (fₗₘ, gₗₘ) = select!(C)
        u = lcm(fₗₘ, gₗₘ)
        if u == fₗₘ * gₗₘ || !any(flatten((keys(C), D))) do pair
            divides(lcm(pair[1], pair[2]), u)
        end
            push!(D, (fₗₘ, gₗₘ))
        end
    end
    P_new = filter(pair -> !isone(gcd(pair[1], pair[2])), D)
    for ((p1, p2), lcm_p) in P
        if !divides(fₗₘ, lcm_p) ||
            lcm(p1, fₗₘ) == lcm_p ||
            lcm(p2, fₗₘ) == lcm_p
            push!(P_new, (p1, p2))
        end
    end
    empty!(P)
    for (p1, p2) in P_new
        enqueue!(P, minmax(p1, p2), lcm(p1, p2))
    end
    filter!(l -> !divides(fₗₘ, l), L)
    push!(L, fₗₘ)
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
            #h .+= r
            push!(h.terms, r)
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

function gröbner_basis(::M4GB, o::MonomialOrder, G::AbstractArray{<:Polynomial}; kwds...)
    isempty(G) && return copy(G)
    return m4gb(o, G, kwds...)
end

end
