module GröbnerM4GB


import PolynomialRings
import Base.Iterators: flatten

import DataStructures: DefaultDict, SortedSet
import DataStructures: PriorityQueue, enqueue!, dequeue_pair!, SortedSet
import ProgressMeter: Progress, finish!, next!, @showprogress

import ..Backends.Gröbner: M4GB
import ..Modules: AbstractModuleElement, modulebasering, Signature, leading_row
import ..MonomialOrderings: MonomialOrder, @withmonomialorder
import ..Monomials: AbstractMonomial
import ..Operators: integral_fraction
import ..Polynomials: Polynomial, terms
import ..Terms: monomial
import PolynomialRings: gröbner_basis, monomialtype, base_extend
import PolynomialRings: maybe_div, termtype, lcm_multipliers

"""
    gröbner_basis = m4gb(monomialorder, polynomials)

An implementation of the M4GB algorithm as popularized by
> Rusydi Makarim, Marc Stevens, "M4GB: An efficient Groebner-basis algorithm", ISSAC 2017
"""
function m4gb(order::MonomialOrder, F::AbstractVector{<:AbstractModuleElement})
    @withmonomialorder order

    R = eltype(F)
    A = modulebasering(R)
    LM = monomialtype(eltype(F))
    L, M = SortedSet{LM}(order), Dict{LM, R}()
    MM = DefaultDict{LM, SortedSet{R}}(() -> SortedSet{R}(order))
    P = PriorityQueue{Tuple{LM, LM}, LM}(order)

    @showprogress "Gröbner: preparing inputs: " for f in map(R, F)
        f = mulfullreduce!(L, M, one(termtype(A)), f, order=order)
        if !iszero(f)
            updatereduce!(L, M, MM, P, f, order=order)
        end
    end
    progress = Progress(length(P), "Computing Gröbner basis: ")
    loops = 0
    while !isempty(P)
        ((fₗₘ, gₗₘ), _) = select!(P)
        f = M[fₗₘ]; g = M[gₗₘ]

        c_f, c_g = lcm_multipliers(lt(f), lt(g))
        h₁ = mulfullreduce!(L, M, c_f, tail(f), order=order)
        h₂ = mulfullreduce!(L, M, c_g, tail(g), order=order)
        if (h = h₁ - h₂) |> !iszero
            updatereduce!(L, M, MM, P, h, order=order)
        end

        loops += 1
        progress.n = length(P) + loops
        next!(progress; showvalues = [(Symbol("|L|"), length(L)), (Symbol("|P|"), length(P)), (Symbol("|M|"), length(M)), (:loops, loops)])

    end
    finish!(progress)

    return [M[fₗₘ] for fₗₘ in L]
end

select!(P) = dequeue_pair!(P)

tailterms_divisible_by(p::Polynomial, m::AbstractMonomial, reverse::Val{true}) = (
    t
    for t in @view(p.terms[end-1:-1:1]) if
    divides(m, monomial(t))
)

function tailterms_divisible_by(p::AbstractVector{<:Polynomial}, m::Signature, reverse::Val{true})
    l = leading_row(p)
    row = m.i
    if m.i == l
        return (
            Signature(m.i, t)
            for t in @view(p[m.i].terms[end-1:-1:1]) if
            divides(m.m, monomial(t))
        )
    elseif m.i > l
        return (
            Signature(m.i, t)
            for t in @view(p[m.i].terms[end:-1:1]) if
            divides(m.m, monomial(t))
        )
    else
        return ()
    end
end

function update_with(M, H, lm_H, fₗₘ; order)
    @withmonomialorder order

    max = nothing
    for h in flatten((values(M), H))
        for t in tailterms_divisible_by(h, fₗₘ, Val(true))
            if max !== nothing && monomial(t) ⪯ max
                break
            end
            if monomial(t) ∉ lm_H
                max = monomial(t)
                break
            end
        end
    end
    return max
end

function updatereduce!(L, M, MM, P, f; order)
    @withmonomialorder order

    H = [f // lc(f)]
    lm_H = Set(lm(h) for h in H)

    while (u = update_with(M, H, lm_H, lm(f), order=order)) != nothing
        h = mulfullreduce!(L, M, maybe_div(u, lm(f)) * inv(lc(f)), tail(f), order=order)
        res = if u isa Signature
            x = h[u.i]
            push!(x.terms, u.m)
            @assert issorted(x.terms, order=order)
            h[u.i] = x
            h
        else
            u + h
        end
        push!(H, res)
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
        for g in MM[lm(h)]
            if (c = g[lm(h)]) |> !iszero
                @. g -= c * h
                for t in terms(h, order=order)
                    push!(MM[monomial(t)], g)
                end
            end
        end
        M[lm(h)] = h
        for t in terms(h, order=order)
            push!(MM[monomial(t)], h)
        end
    end
    update!(L, P, lm(f); order=order)
end

mutuallyprime(a, b) = lcm(a, b) == a * b
mutuallyprime(a::Signature, b::Signature) = a.i == b.i ? mutuallyprime(a.m, b.m) : nothing

function update!(L, P, fₗₘ; order)
    @withmonomialorder order

    C = similar(P)
    for gₗₘ in L
        if (u = lcm(fₗₘ, gₗₘ)) |> !isnothing
            enqueue!(C, (fₗₘ, gₗₘ), u)
        end
    end
    D = similar(C)
    while !isempty(C)
        ((fₗₘ, gₗₘ), u) = select!(C)
        if mutuallyprime(fₗₘ, gₗₘ) || !any(flatten((keys(C), keys(D)))) do pair
            divides(lcm(pair[1], pair[2]), u)
        end
            enqueue!(D, (fₗₘ, gₗₘ), u)
        end
    end
    P_new = filter!(D) do pair
        (p1, p2), _ = pair
        !mutuallyprime(p1, p2)
    end
    for ((p1, p2), lcm_p) in pairs(P)
        if !divides(fₗₘ, lcm_p) ||
            lcm(p1, fₗₘ) == lcm_p ||
            lcm(p2, fₗₘ) == lcm_p
            enqueue!(P_new, (p1, p2), lcm_p)
        end
    end
    empty!(P)
    for ((p1, p2), lcm_p) in pairs(P_new)
        p = p1 ≺ p2 ? (p1, p2) : (p2, p1)
        enqueue!(P, p, lcm_p)
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
            if r isa Signature
                x = h[r.i]
                push!(x.terms, r.m)
                h[r.i] = x
            else
                push!(h.terms, r)
            end
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
        res = if r isa Signature
            x = h[r.i]
            push!(x.terms, r.m)
            @assert issorted(x.terms, order=order)
            h[r.i] = x
            h
        else
            r + h
        end
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

function gröbner_basis(::M4GB, o::MonomialOrder, G::AbstractArray{<:AbstractModuleElement}; kwds...)
    isempty(G) && return copy(G)
    return m4gb(o, G, kwds...)
end

end
