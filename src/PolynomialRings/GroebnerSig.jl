module GröbnerSig


import PolynomialRings
import LinearAlgebra: Transpose
import SparseArrays: SparseVector

import DataStructures: DefaultDict
import DataStructures: PriorityQueue, enqueue!, dequeue!
import IterTools: chain

import ..AbstractMonomials: deg, any_divisor
import ..Backends.Gröbner: Backend, F5C, Arri
import ..Modules: AbstractModuleElement, modulebasering
import ..MonomialOrderings: MonomialOrder, degreecompatible, @withmonomialorder
import ..Operators: Lead, Full, integral_fraction, content
import ..Polynomials: Polynomial, monomialorder, monomialtype
import ..Terms: monomial, coefficient
import PolynomialRings: gröbner_basis
import PolynomialRings: leading_term, leading_monomial, lcm_multipliers, lcm_degree, fraction_field, basering, base_extend, base_restrict
import PolynomialRings: leadrem, xrem!
import PolynomialRings: maybe_div, termtype, monomialtype, exptype, leading_row, leading_coefficient

reduction_rem(::Arri, m, G; order) = semi_complete_reduction_rem(m, G, order=order)

function semi_complete_reduction_rem(m, G; order)
    @withmonomialorder order

    σ,p = m
    p = deepcopy(p)
    i = 1
    while !iszero(p) && i <= length(G)
        τ, q = G[i]
        if !iszero(q)
            t = maybe_div(leading_monomial(p), leading_monomial(q))
            if t !== nothing
                if t * τ ≺ σ
                    c_p = leading_coefficient(p)
                    c_q = leading_coefficient(q)
                    m_p, m_q = lcm_multipliers(c_p, c_q)
                    @. p = m_p * p - m_q*(t*q)
                    i = 1
                    continue
                end
            end
        end
        i += 1
    end
    if basering(p) <: Integer
        p = p ÷ content(p)
    end
    return (σ, p)
end

function s_poly_lm(p, q; order)
    @withmonomialorder order
    (m_p, m_q) = lcm_multipliers(leading_term(p), leading_term(q))
    S_pq = m_p * p - m_q * q
    return iszero(S_pq) ? nothing : leading_monomial(S_pq)
end

function is_prunable(::Arri, x, G, P, S; order)
    @withmonomialorder order
    (σ, p, q) = x

    isnothing(s_poly_lm(p, q; order=order)) && return true
    # (AR) there exist (τ F i+1 , g) ∈ G and t ∈ M such that tτ = σ and lm (tg) <
    # lm (S p,q ), or there exist (τ F i+1 , f, g) ∈ S ∪ P and t ∈ M such that tτ = σ
    # and lm (tS f,g ) < lm (S p,q ).
    any(G) do y
        τ, g = y
        t = maybe_div(σ, τ)
        t !== nothing && t * leading_monomial(g) ≺ s_poly_lm(p, q, order=order)
    end || any(values(P)) do SS
        any(SS) do pair
            (τ, f, g),_ = pair
            t = maybe_div(σ, τ)
            t !== nothing && t * s_poly_lm(o, f, g) ≺ s_poly_lm(p, q, order=order)
        end
    end || any(S) do pair
        (τ, f, g),_ = pair
        t = maybe_div(σ, τ)
        t !== nothing && t * s_poly_lm(o, f, g) ≺ s_poly_lm(o, p, q)
    end
end

is_sig_redundant(G, i::Integer; order) = is_sig_redundant(G[i], G[[1:i-1; i+1:end]], order=order)

function is_sig_redundant(f, G; order)
    @withmonomialorder order
    (σ, f) = f
    σ.first != 1 && return false
    length(G) == 0 && return false
    iszero(f) && return false
    lm_f = leading_monomial(f)
    return any(G) do g
        (τ, g) = g
        !iszero(g) && maybe_div(σ, τ) !== nothing && maybe_div(lm_f, leading_monomial(g)) !== nothing
    end
end

"""
    gröbner_basis = gröbner_basis_sig_incremental(algorithm, monomialorder, polynomials)

An implementation of the generic signature-based algorithm as popularized by
> Eder, Christian, and John Edward Perry. "Signature-based algorithms to compute
> Gröbner bases." Proceedings of the 36th international symposium on Symbolic and
> algebraic computation. ACM, 2011.
The `alg` parameter decides whether this reduces to F5C, G²W, or Arri.
For now, only Arri has been implemented.

This incremental algorithm assumes that `polynomials[2:end]` is already a Gröbner
basis, and we've just added `polynomials[1]`. This convention is opposite from
Eder/Perry but it fits with our definition of signature as the _first_ nonzero
leading monomial in a vector.
"""
function gröbner_basis_sig_incremental(alg::Backend, polynomials::AbstractVector{PP}; order::MonomialOrder) where PP <: Polynomial
    @assert degreecompatible(order)
    @withmonomialorder order

    R = PP
    M = monomialtype(PP)
    Degree = exptype(PP)
    Rm = Transpose{R, SparseVector{R,Int}}
    Signature = monomialtype(polynomials)

    signature(m) = m[1]
    # --------------------------------------------------------------------------
    # Declare the variables where we'll accumulate the result
    # --------------------------------------------------------------------------
    G = Tuple{Signature, R}[]
    PQ = PriorityQueue{Tuple{Signature, R, R}, Signature}
    P = DefaultDict{Degree, PQ}(PQ(order))
    Syz = Set{Signature}()

    let n = length(polynomials)
        for (i,p) in enumerate(polynomials)
            s = Signature(i, one(M))
            push!(G, (s, p))
        end
    end
    let new_p = polynomials[1]
        for p in polynomials[2:end]
            m_a, m_b = lcm_multipliers(leading_monomial(new_p), leading_monomial(p))
            s = Signature(1, m_a)
            enqueue!(P[deg(m_a)], (s, new_p, p), s)
        end
    end
    for (i,p) in enumerate(polynomials)
        i == 1 && continue
        push!(Syz, Signature(i, leading_monomial(p)))
    end

    loops = 0
    considered = 0
    divisors_considered = 0
    divisor_considerations = 0
    progress_logged = false

    while !isempty(P)
        # prune P w.r.t. Syz

        current_degree = minimum(keys(P))
        S = P[current_degree]
        delete!(P, current_degree)

        while !isempty(S)
            loops += 1
            if loops % 100 == 0
                l = length(G)
                k = length(P)
                h = length(Syz)
                @info("$alg: After $loops loops: $l elements in basis; $considered pairs considered; |P|=$k, |Syz|=$h")
                progress_logged = true
            end
            # prune S w.r.t. Syz
            #for x in keys(S)
            #    if is_prunable(alg, x, G, P, S, order=order)
            #        delete!(S, x)
            #    end
            #end

            (σ, p, q) = dequeue!(S)

            is_prunable(alg, (σ, p, q), G, P, S, order=order) && continue

            considered += 1

            (m_p, m_q) = lcm_multipliers(leading_term(p), leading_term(q))
            S_pq = m_p * p - m_q * q
            (σ, r) = reduction_rem(alg, (σ, S_pq), G, order=order)

            if iszero(r)
                filter!(S) do k_v
                    k,v = k_v
                    (τ, _, _) = k
                    divisible = maybe_div(τ, σ) !== nothing
                    !divisible
                end
                for SS in values(P)
                    filter!(SS) do k_v
                        k,v = k_v
                        (τ, _, _) = k
                        divisible = maybe_div(τ, σ) !== nothing
                        !divisible
                    end
                end
                push!(Syz, σ)
            elseif !is_sig_redundant((σ, r), G, order=order)
                for (i,(τ,g)) in enumerate(G)
                    iszero(g) && continue
                    τ.first == 1 || continue
                    is_sig_redundant(G, i, order=order) && continue
                    m_r, m_g = lcm_multipliers(leading_monomial(r), leading_monomial(g))
                    if m_r * σ != m_g * τ
                        if m_r * σ ⪰ m_g * τ
                            (μ, p, q) = (m_r * σ, r, g)
                        else
                            (μ, p, q) = (m_g * τ, g, r)
                        end
                        if !any(Syz) do τ
                            divisible = maybe_div(μ, τ) !== nothing
                            divisible
                        end
                            if deg(μ) == current_degree
                                S[μ,p,q] = μ
                            else
                                P[deg(μ)][μ,p,q] = μ
                            end
                        end
                    end
                end
            end
            push!(G, (σ, r))
        end

        considered += 1
    end

    for i in length(G):-1:1
        if is_sig_redundant(G, i, order=order)
            deleteat!(G, i)
        end
    end

    result = getindex.(G, 2)
    filter!(!iszero, result)
    progress_logged && @info("Done. Returning a Gröbner basis of length $(length(result))")

    return result
end

function interreduce!(H; order)
    for i in 1:length(H)
        xrem!(H[i], H[[1:i-1; i+1:end]], order=order)
        if basering(eltype(H)) <: Integer
            H[i] ÷= content(H[i])
        end
    end
    filter!(!iszero, H)
end

function gröbner_basis(alg::Arri, o::MonomialOrder, G::AbstractArray{<:Polynomial}; kwds...)
    # we go from last to first instead of from first to last, since in our convention,
    # the signature is the _first_ nonzero leading monomial in a vector, not the _last_.
    P = eltype(G)
    R = base_restrict(P)
    if basering(P) <: Rational
        G = map(g->integral_fraction(g)[1], G)
    end
    H = R[]
    ix = findlast(!iszero, G)
    if !isnothing(ix)
        pushfirst!(H, G[ix])
        for g in G[ix-1:-1:1]
            iszero(g) && continue
            pushfirst!(H, g)
            H = gröbner_basis_sig_incremental(alg, H; order=o, kwds...)
            interreduce!(H, order=o)
        end
    end
    H = map(h->base_extend(h, P), H)

    return H
end

end
