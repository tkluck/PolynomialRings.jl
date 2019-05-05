module GröbnerM4GB


import PolynomialRings

import DataStructures: OrderedDict, SortedDict
import DataStructures: PriorityQueue, enqueue!, dequeue_pair!
import InPlace: @inplace

import ..Backends.Gröbner: M4GB
import ..IndexedMonomials: ByIndex
import ..Modules: AbstractModuleElement, modulebasering, Signature, leading_row
import ..MonomialIterators: monomialiter
import ..MonomialOrderings: MonomialOrder, @withmonomialorder
import ..Monomials: AbstractMonomial, total_degree, lcm_degree
import ..Operators: integral_fraction
import ..Polynomials: Polynomial, nzterms, nztailterms, nzrevterms
import ..Terms: monomial, coefficient, Term
import ..Util: @showprogress, interval, last_, chain
import PolynomialRings: gröbner_basis, monomialtype, base_extend
import PolynomialRings: maybe_div, divides, termtype, lcm_multipliers, mutuallyprime

mutable struct LType{R, LM}
    multiples  :: Vector{LM}
    superseded :: Bool
end

mutable struct MType{R, LM}
    f             :: Union{Nothing, R}
    multiple_of   :: LM
    reduced_until :: LM
end

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

    L = OrderedDict{LM, LType{R, LM}}()
    M = SortedDict{LM, Union{Nothing, MType{R, LM}}}(order)
    P = PriorityQueue{Tuple{LM, LM}, LM}(order)

    ensure_multiples_materialized!(M, L, maximum(order, map(lm, F)), order)

    @showprogress "Gröbner: preparing inputs: " L M P for f in sort(F, order=order, rev=true)
        f = mulfullreduce!(L, M, one(termtype(A)), f, order)
        if !iszero(f)
            lazyupdatereduce!(L, M, P, f, order)
        end
    end
    @showprogress "Computing Gröbner basis: " L M P while !isempty(P)
        ((fₗₘ, gₗₘ), lcm_p) = select!(P)
        f = M[fₗₘ].f; g = M[gₗₘ].f

        ensure_multiples_materialized!(M, L, lcm_p, order)

        c_f, c_g = lcm_multipliers(lt(f), lt(g))
        h₁ = mulfullreduce!(L, M, c_f, tail(f), order)
        h₂ = mulfullreduce!(L, M, c_g, tail(g), order)
        if (h = h₁ - h₂) |> !iszero
            lazyupdatereduce!(L, M, P, h, order)
        end
    end

    return [M[fₗₘ].f for (fₗₘ, l) in pairs(L) if !l.superseded]
end

select!(P) = dequeue_pair!(P)

function lazyupdatereduce!(L, M, P, f, order)
    @withmonomialorder order

    M[lm(f)] = MType(f // lc(f), lm(f), lm(f))
    update!(L, M, P, lm(f), order)
end

function update!(L, M, P, fₗₘ, order)
    @withmonomialorder order

    C = similar(P)
    for (gₗₘ, _) in pairs(L)
        if (u = lcm(fₗₘ, gₗₘ)) |> !isnothing
            enqueue!(C, (fₗₘ, gₗₘ), u)
        end
    end
    D = similar(C)
    while !isempty(C)
        ((fₗₘ, gₗₘ), u) = select!(C)
        if mutuallyprime(fₗₘ, gₗₘ) || !any(chain(pairs(C), pairs(D))) do pair
            (_, lcm_p) = pair
            divides(lcm_p, u)
        end
            enqueue!(D, (fₗₘ, gₗₘ), u)
        end
    end
    filter!(D) do pair
        (p1_, p2_), _ = pair
        !mutuallyprime(p1_, p2_)
    end
    filter!(P) do pair
        (p1, p2), lcm_p = pair

        !divides(fₗₘ, lcm_p) ||
        lcm(p1, fₗₘ) == lcm_p ||
        lcm(p2, fₗₘ) == lcm_p
    end
    for ((p1, p2), lcm_p) in pairs(D)
        p = p1 ≺ p2 ? (p1, p2) : (p2, p1)
        enqueue!(P, p, lcm_p)
    end
    for (gₗₘ, l) in pairs(L)
        if divides(fₗₘ, gₗₘ)
            l.superseded = true
            for m in l.multiples
                M[m].multiple_of = fₗₘ
            end
        end
    end
    multiples = materialize_multiples!(M, fₗₘ, order=order)
    L[fₗₘ] = valtype(L)(multiples, false)
end

function mulfullreduce!(L, M, t, f, order)
    @withmonomialorder order

    h = zero(f)
    for s in nzterms(f, order=order)
        r = t * s
        g = getreductor!(M, L, monomial(r), order)
        if g != nothing
            d = coefficient(r) // lc(g)
            h .-= d .* tail(g)
        else
            @inplace h += r
        end
    end

    return h
end

Something(::Type{Union{Nothing, T}}) where T = T

function materialize_multiples!(M, fₗₘ, materialize_until=nothing; order)
    @withmonomialorder order

    materialize_until = something(materialize_until, max(order, fₗₘ, last(M)[1]))

    multiples = typeof(fₗₘ)[]
    for m in monomialiter(keytype(M))
        n = m * fₗₘ
        n ≻ materialize_until && break
        if isnothing(M[n])
            M[n] = Something(valtype(M))(nothing, fₗₘ, fₗₘ)
            push!(multiples, n)
        elseif M[n].multiple_of == fₗₘ
            push!(multiples, n)
        end
    end
    return multiples
end

function ensure_multiples_materialized!(M, L, materialize_until, order)
    @withmonomialorder order

    if !isempty(M)
        cur, _ = last(M)
        materialize_until ⪯ cur && return
        materialize_until = typeof(materialize_until)(ByIndex(), materialize_until.ix + cur.ix)
    end

    for m in monomialiter(keytype(M))
        m ≻ materialize_until && break
        if m ∉ keys(M)
            M[m] = nothing
        end
    end

    for (fₗₘ, l) in pairs(L)
        l.superseded && continue
        l.multiples = materialize_multiples!(M, fₗₘ, materialize_until, order=order)
    end
end

function getreductor!(M, L, gₗₘ, order)
    @withmonomialorder order

    m = M[gₗₘ]
    isnothing(m) && return nothing

    if isnothing(m.f)
        fₗₘ = m.multiple_of
        f = M[fₗₘ].f
        m.f = mulfullreduce!(L, M, maybe_div(gₗₘ, lm(f)), tail(f), order)
        @inplace m.f += gₗₘ * inv(lc(f))
        m.reduced_until = last_(L)
    end

    g₀ = m.f
    for (fₗₘ, l) in interval(L, m.reduced_until, lo=:exclusive)
        l.superseded && continue
        fₗₘ ≺ gₗₘ || continue
        for m in l.multiples
            if (c = g₀[m]) |> !iszero
                m == gₗₘ && break
                h = getreductor!(M, L, m, order)
                d = c // lc(h)
                @. g₀ -= d * h
            end
        end
    end
    m.reduced_until = last_(L)

    return m.f
end

function gröbner_basis(::M4GB, o::MonomialOrder, G::AbstractArray{<:AbstractModuleElement}; kwds...)
    G = base_extend.(G)
    isempty(G) && return copy(G)
    return m4gb(o, G, kwds...)
end

end
