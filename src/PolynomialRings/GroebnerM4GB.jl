module GröbnerM4GB


import PolynomialRings
import Base.Iterators: flatten
import Base.Order: ReverseOrdering

import DataStructures: PriorityQueue, enqueue!, dequeue_pair!, SortedSet, SortedDict
import ProgressMeter: Progress, finish!, next!
import TimerOutputs: TimerOutput, @timeit

import ..Backends.Gröbner: M4GB
import ..Constants: One
import ..MonomialOrderings: MonomialOrder, @withmonomialorder
import ..Monomials: any_divisor
import ..Polynomials: Polynomial
import ..Terms: monomial, coefficient, Term
import ..DensePolynomials: to_dense, op_ordered_terms!, tailterms
import ..DensePolynomials: densepolynomialtype, MonomialSet
import PolynomialRings: gröbner_basis, monomialtype, basering
import PolynomialRings: maybe_div, termtype, lcm_multipliers, divides

const to = TimerOutput()

"""
    gröbner_basis = m4gb(monomialorder, polynomials)

An implementation of the M4GB algorithm as popularized by
> Rusydi Makarim, Marc Stevens, "M4GB: An efficient Groebner-basis algorithm", ISSAC 2017
"""
function m4gb(order::MonomialOrder, F::AbstractVector{<:Polynomial})
    @withmonomialorder order

    R = eltype(F); LM = monomialtype(R)
    RDense = densepolynomialtype(R)
    L, M = SortedSet{LM}(order), Dict{LM, RDense}()
    P = PriorityQueue{Tuple{LM, LM}, LM}(order)

    for f in F
        f = mulfullreduce!(L, M, one(termtype(f)), to_dense(f), order)
        if !iszero(f)
            updatereduce!(L, M, P, f, order)
        end
    end
    progress = Progress(length(P), "Computing Gröbner basis: ")
    loops = 0
    while !isempty(P)
        ((fₗₘ, gₗₘ),_) = select!(P)
        f = M[fₗₘ]; g = M[gₗₘ]

        c_f, c_g = lcm_multipliers(lt(f), lt(g))
        h₁ = mulfullreduce!(L, M, c_f, tail(f), order)
        h₂ = mulfullreduce!(L, M, c_g, tail(g), order)
        if (h = h₁ - h₂) |> !iszero
            updatereduce!(L, M, P, h, order)
        end

        loops += 1
        progress.n = length(P) + loops
        next!(progress; showvalues = [(Symbol("|L|"), length(L)), (Symbol("|P|"), length(P)), (Symbol("|M|"), length(M)), (:loops, loops)])

    end
    finish!(progress)

    return [convert(R, M[fₗₘ]) for fₗₘ in L]
end

select!(P) = dequeue_pair!(P)

function update_with(M, H, lm_H, fₗₘ, order)
    @withmonomialorder order

    max = nothing
    for h in flatten((values(M), H))
        for t in tailterms(h, Val(true))
            if max !== nothing && monomial(t) ⪯ max
                break
            end
            if monomial(t) ∉ lm_H && divides(fₗₘ, monomial(t))
                max = monomial(t)
                break
            end
        end
    end
    return max
end

function updatereduce!(L, M, P, f, order)
    @withmonomialorder order

    H = [f // lc(f)]
    lm_H = MonomialSet()
    push!(lm_H, lm(f))

    while (u = update_with(M, H, lm_H, lm(f), order)) != nothing
        h = mulfullreduce!(L, M, maybe_div(u, lm(f)) * inv(lc(f)), tail(f), order)
        push!(H, u + h)
        push!(lm_H, u)
    end

    sort!(H, order=order)
    while !isempty(H)
        h = popfirst!(H)
        for g in H
            if (c = g[lm(h)]) |> !iszero
                #@. g -= c * h
                g.coeffs[1:length(h.coeffs)] .-= c .* h.coeffs
            end
        end
        for g in values(M)
            if (c = g[lm(h)]) |> !iszero
                #@. g -= c * h
                g.coeffs[1:length(h.coeffs)] .-= c .* h.coeffs
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
    D = similar(C)
    while !isempty(C)
        ((fₗₘ, gₗₘ), u) = select!(C)
        if u == fₗₘ * gₗₘ || !any(flatten((pairs(C), pairs(D)))) do pair
            (_, lcm_p) = pair
            divides(lcm_p, u)
        end
            enqueue!(D, (fₗₘ, gₗₘ), u)
        end
    end
    P_new = filter!(D) do pair
        (p1, p2), lcm_p = pair
        p1 * p2 != lcm_p
    end
    for ((p1, p2), lcm_p) in P
        if !divides(fₗₘ, lcm_p) ||
            lcm(p1, fₗₘ) == lcm_p ||
            lcm(p2, fₗₘ) == lcm_p
            enqueue!(P_new, (p1, p2), lcm_p)
        end
    end
    empty!(P)
    for ((p1, p2), lcm_p) in P_new
        enqueue!(P, minmax(p1, p2), lcm_p)
    end
    filter!(l -> !divides(fₗₘ, l), L)
    push!(L, fₗₘ)
end


function mulfullreduce!(L, M, t, f, order)
    @withmonomialorder order

    h = zero(f)
    for s in terms(f)
        r = t * s
        g = getreductor!(M, L, r, order)
        if g != nothing
            d = maybe_div(r, lt(g))
            # h .-= d .* tail(g)
            op_ordered_terms!(-, h, d, tailterms(g, Val(false)))
        else
            # h .+= r
            op_ordered_terms!(+, h, One(), (r,))
        end
    end

    return h

end

function getreductor!(M, L, r, order)
    @withmonomialorder order

    res = nothing
    if monomial(r) in keys(M)
        res = M[monomial(r)]
    else
        fₗₘ = reducesel(L, monomial(r), order)
        fₗₘ == nothing && return nothing
        f = M[fₗₘ]
        h = mulfullreduce!(L, M, maybe_div(r, lt(f)), tail(f), order)
        # res = r + h
        op_ordered_terms!(+, h, One(), (r,))
        M[lm(h)] = h
        res = h
    end
    return res
end

function reducesel(L, m, order)
    for l in L
        divides(l, m) && return l
    end
    return nothing
end

function gröbner_basis(::M4GB, o::MonomialOrder, G::AbstractArray{<:Polynomial}; kwds...)
    isempty(G) && return copy(G)
    res =  m4gb(o, G, kwds...)
    @show to
    return res
end

end
