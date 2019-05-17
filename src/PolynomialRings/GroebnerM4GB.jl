module GröbnerM4GB


import PolynomialRings

import DataStructures: OrderedDict, SortedDict, DefaultDict
import DataStructures: PriorityQueue, enqueue!, dequeue_pair!
import InPlace: @inplace

import ..Backends.Gröbner: M4GB, GWV
import ..Constants: One, Zero
import ..IndexedMonomials: ByIndex, IndexedMonomial
import ..Modules: AbstractModuleElement, modulebasering, Signature, leading_row
import ..MonomialIterators: monomialiter
import ..MonomialOrderings: MonomialOrder, @withmonomialorder
import ..Monomials: AbstractMonomial, total_degree, lcm_degree, num_variables
import ..NamingSchemes: namingscheme
import ..Operators: integral_fraction
import ..Polynomials: Polynomial, nzterms, nztailterms, nzrevterms, leading_monomial
import ..Terms: monomial, coefficient, Term
import ..Util: @showprogress, interval, last_, chain, nzpairs
import PolynomialRings: gröbner_basis, monomialtype, base_extend
import PolynomialRings: maybe_div, divides, termtype, lcm_multipliers, mutuallyprime

const lr = leading_row

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
    LM = monomialtype(R)
    Ix = keytype(R)
    MDict = SortedDict{LM, Union{Nothing, MType{R, LM}}, typeof(order)}

    L = OrderedDict{LM, LType{R, LM}}()
    M = DefaultDict{Ix, MDict}(() -> MDict(order))
    P = PriorityQueue{Tuple{LM, LM}, LM}(order)

    F = copy(F)
    sort!(F, order=order, rev=true)
    filter!(!iszero, F)

    for f in F
        ensure_reducers_materialized!(M, L, One(), f, order)
    end
    @showprogress "Gröbner: preparing inputs: " L M P for f in F
        f = mulfullreduce!(L, M, one(termtype(A)), f, order)
        if !iszero(f)
            lazyupdatereduce!(L, M, P, f, order)
        end
    end
    @showprogress "Computing Gröbner basis: " L M P while !isempty(P)
        ((fₗₘ, gₗₘ), lcm_p) = select!(P)
        f = M[lr(fₗₘ)][fₗₘ].f
        g = M[lr(gₗₘ)][gₗₘ].f
        c_f, c_g = lcm_multipliers(lt(f), lt(g))

        if R <: Polynomial
            # For modules, calling this once every loop is not good
            # enough. That's why we only call it here for polynomials,
            # while for modules, we call it inside getreductor!.
            # (Technically, this depends on whether the monomial order
            # is isomorphic to ω or e.g. ω + ω. TODO: find a more
            # concise way of representing this difference.)
            ensure_reducers_materialized!(M, L, monomial(c_f), f, order)
            ensure_reducers_materialized!(M, L, monomial(c_g), g, order)
        end

        h₁ = mulfullreduce!(L, M, c_f, tail(f), order)
        h₂ = mulfullreduce!(L, M, c_g, tail(g), order)
        if (h = h₁ - h₂) |> !iszero
            lazyupdatereduce!(L, M, P, h, order)
        end
    end

    return [M[lr(fₗₘ)][fₗₘ].f for (fₗₘ, l) in pairs(L) if !l.superseded]
end

select!(P) = dequeue_pair!(P)

function lazyupdatereduce!(L, M, P, f, order)
    @withmonomialorder order

    M[lr(f)][lm(f)] = MType(f // lc(f), lm(f), lm(f))
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
                M[lr(m)][m].multiple_of = fₗₘ
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

function materialize_multiples!(M, fₗₘ; order)
    @withmonomialorder order

    MonomialType = fₗₘ isa Signature ?
                   typeof(fₗₘ.m) :
                   typeof(fₗₘ)

    Mᵣ = M[lr(fₗₘ)]
    isempty(Mᵣ) && return

    materialize_until = max(order, fₗₘ, last(Mᵣ)[1])

    multiples = typeof(fₗₘ)[]
    for m in monomialiter(MonomialType)
        n = m * fₗₘ
        n ≻ materialize_until && break
        if isnothing(Mᵣ[n])
            Mᵣ[n] = Something(valtype(Mᵣ))(nothing, fₗₘ, fₗₘ)
            push!(multiples, n)
        elseif Mᵣ[n].multiple_of == fₗₘ
            push!(multiples, n)
        end
    end
    return multiples
end

_linearly_dependent_monomials(m::AbstractMonomial) = monomialiter(typeof(m))
_linearly_dependent_monomials(s::Signature) = (
    Signature(s.i, m)
    for m in monomialiter(typeof(s.m))
)

_enumerate_lms_of_rows(order, f::Polynomial) = (leading_monomial(f, order=order),)
_enumerate_lms_of_rows(order, f::AbstractArray{<:Polynomial}) = (
    Signature(i, leading_monomial(f_i, order=order))
    for (i, f_i) in nzpairs(f)
)
_enumerate_lms_of_rows(order, f::Signature) = (f,)
_enumerate_lms_of_rows(order, f::AbstractMonomial) = (f,)

function ensure_reducers_materialized!(M, L, factor, f, order)
    @withmonomialorder order

    dirty = Set{keytype(M)}()

    for gₗₘ in _enumerate_lms_of_rows(order, f)
        materialize_until = factor * gₗₘ
        Mᵣ = M[lr(gₗₘ)]

        if !isempty(Mᵣ)
            cur, _ = last(Mᵣ)
            materialize_until ⪯ cur && continue
            if materialize_until isa IndexedMonomial
                # use Fibonacci growth for online resizing of the
                # materialized leading monomials.
                materialize_until = typeof(materialize_until)(ByIndex(), materialize_until.ix + cur.ix)
            end
        end

        for m in _linearly_dependent_monomials(materialize_until)
            m ≻ materialize_until && break
            if m ∉ keys(Mᵣ)
                Mᵣ[m] = nothing
                push!(dirty, lr(gₗₘ))
            end
        end
    end

    if !isempty(dirty)
        for (fₗₘ, l) in pairs(L)
            l.superseded && continue
            lr(fₗₘ) ∈ dirty || continue
            l.multiples = materialize_multiples!(M, fₗₘ, order=order)
        end
    end
end

function getreductor!(M, L, gₗₘ, order)
    @withmonomialorder order

    if gₗₘ isa Signature
        # For modules, calling this once every loop is not good
        # enough.
        ensure_reducers_materialized!(M, L, One(), gₗₘ, order)
    end

    m = M[lr(gₗₘ)][gₗₘ]
    isnothing(m) && return nothing

    if isnothing(m.f)
        fₗₘ = m.multiple_of
        f = M[lr(fₗₘ)][fₗₘ].f
        m.f = mulfullreduce!(L, M, maybe_div(gₗₘ, lm(f)), tail(f), order)
        @inplace m.f += gₗₘ * inv(lc(f))
        m.reduced_until = last_(L)
    end

    g₀ = m.f
    for (fₗₘ, l) in interval(L, m.reduced_until, lo=:exclusive)
        l.superseded && continue
        fₗₘ ≺ gₗₘ || continue
        for m in l.multiples
            if (c = get(g₀, m, Zero())) |> !iszero
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
    num_variables(namingscheme(o)) < Inf || return gröbner_basis(GWV(), o, G)
    G = base_extend.(G)
    isempty(G) && return copy(G)
    return m4gb(o, G, kwds...)
end

end
