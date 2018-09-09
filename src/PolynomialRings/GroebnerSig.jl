module GröbnerSig

using DataStructures: DefaultDict
using DataStructures: PriorityQueue, enqueue!, dequeue!
using IterTools: chain

import PolynomialRings
import PolynomialRings: gröbner_basis
import PolynomialRings.Backends.Gröbner: Backend, F5C, Arri

import PolynomialRings: leading_term, leading_monomial, lcm_multipliers, lcm_degree, fraction_field, basering, base_extend
import PolynomialRings: maybe_div, termtype, monomialtype, exptype, leading_row, leading_coefficient
import PolynomialRings.MonomialOrderings: MonomialOrder, degreecompatible
import PolynomialRings.Monomials: total_degree, any_divisor
import PolynomialRings.Polynomials: Polynomial, monomialorder, monomialtype
import PolynomialRings.Terms: monomial, coefficient
import PolynomialRings.Modules: AbstractModuleElement, modulebasering
import PolynomialRings.Operators: Lead, Full
import PolynomialRings: leadrem
using LinearAlgebra: Transpose
using SparseArrays: SparseVector

reduction_rem(::Arri, o, m, G) = semi_complete_reduction_rem(o, m, G)

function semi_complete_reduction_rem(o, m, G)
    σ,p = m
    i = 1
    while !iszero(p) && i <= length(G)
        τ, q = G[i]
        if !iszero(q)
            t = maybe_div(leading_monomial(o,p), leading_monomial(o,q))
            if t !== nothing
                if Base.Order.lt(o, t * τ, σ)
                    a = leading_coefficient(o,p) // leading_coefficient(o,q)
                    p = p - a*(t*q)
                    i = 1
                    continue
                end
            end
        end
        i += 1
    end
    return (σ, p)
end

function s_poly_lm(o, p, q)
    (m_p, m_q) = lcm_multipliers(leading_monomial(o,p), leading_monomial(o,q))
    (c_p, c_q) = leading_coefficient.(o, (p,q))
    S_pq = m_p * p - c_p//c_q * m_q * q
    leading_monomial(o, S_pq)
end

function is_prunable(::Arri, o, x, G, P, S)
    (σ, p, q) = x
    # (AR) there exist (τ F i+1 , g) ∈ G and t ∈ M such that tτ = σ and lm (tg) <
    # lm (S p,q ), or there exist (τ F i+1 , f, g) ∈ S ∪ P and t ∈ M such that tτ = σ
    # and lm (tS f,g ) < lm (S p,q ).
    any(G) do y
        τ, g = y
        t = maybe_div(σ, τ)
        t !== nothing && Base.Order.lt(o, t * leading_monomial(g), s_poly_lm(o, p, q))
    end || any(values(P)) do SS
        any(SS) do pair
            (τ, f, g),_ = pair
            t = maybe_div(σ, τ)
            t !== nothing && Base.Order.lt(o, t * s_poly_lm(o, f, g), s_poly_lm(o, p, q))
        end
    end || any(S) do pair
        (τ, f, g),_ = pair
        t = maybe_div(σ, τ)
        t !== nothing && Base.Order.lt(o, t * s_poly_lm(o, f, g), s_poly_lm(o, p, q))
    end
end

is_sig_redundant(o, G, i::Integer) = is_sig_redundant(o, G[i], G[[1:i-1; i+1:end]])

function is_sig_redundant(o, f, G)
    (σ, f) = f
    σ.i != 1 && return false
    length(G) == 0 && return false
    iszero(f) && return false
    lm_f = leading_monomial(o, f)
    return any(G) do g
        (τ, g) = g
        !iszero(g) && maybe_div(σ, τ) !== nothing && maybe_div(lm_f, leading_monomial(o,g)) !== nothing
    end
end

"""
    gröbner_basis = gröbner_basis_sig_incremental(algorithm, monomialorder, polynomials)

An implementation of the generic signature-based algorithm as popularized by
> Eder, Christian, and John Edward Perry. "Signature-based algorithms to compute
> Gröbner bases." Proceedings of the 36th international symposium on Symbolic and
> algebraic computation. ACM, 2011.
The `alg` parameter decides whether this reduces to F5C, G²W, or Arri.
For now, only F5C has been implemented.

This incremental algorithm assumes that `polynomials[2:end]` is already a Gröbner
basis, and we've just added `polynomials[1]`. This convention is opposite from
Eder/Perry but it fits with our definition of signature as the _first_ nonzero
leading monomial in a vector.
"""
function gröbner_basis_sig_incremental(alg::Backend, o::MonomialOrder, polynomials::AbstractVector{PP}) where PP <: Polynomial
    @assert degreecompatible(o)

    R = base_extend(PP)
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
    P = DefaultDict{Degree, PQ}(PQ(o))
    Syz = Set{Signature}()

    let n = length(polynomials)
        for (i,p) in enumerate(polynomials)
            s = Signature(i, one(M))
            push!(G, (s, p))
        end
    end
    let new_p = polynomials[1]
        for p in polynomials[2:end]
            m_a, m_b = lcm_multipliers(leading_monomial(o,new_p), leading_monomial(o,p))
            s = Signature(1, m_a)
            enqueue!(P[total_degree(m_a)], (s, new_p, p), s)
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
            #    if is_prunable(alg, o, x, G, P, S)
            #        delete!(S, x)
            #    end
            #end

            (σ, p, q) = dequeue!(S)

            is_prunable(alg, o, (σ, p, q), G, P, S) && continue

            considered += 1

            (m_p, m_q) = lcm_multipliers(leading_monomial(o,p), leading_monomial(o,q))
            (c_p, c_q) = leading_coefficient.(o,(p,q))
            S_pq = m_p * p - c_p//c_q * m_q * q
            (σ, r) = reduction_rem(alg, o, (σ, S_pq), G)

            if iszero(r)
                filter!(S) do k,v
                    (τ, _, _) = k
                    divisible = maybe_div(τ, σ) !== nothing
                    !divisible
                end
                for SS in values(P)
                    filter!(SS) do k,v
                        (τ, _, _) = k
                        divisible = maybe_div(τ, σ) !== nothing
                        !divisible
                    end
                end
                push!(Syz, σ)
            elseif !is_sig_redundant(o, (σ, r), G)
                for (i,(τ,g)) in enumerate(G)
                    iszero(g) && continue
                    τ.i == 1 || continue
                    is_sig_redundant(o, G, i) && continue
                    m_r, m_g = lcm_multipliers(leading_monomial(o,r), leading_monomial(o,g))
                    if m_r * σ != m_g * τ
                        if !Base.Order.lt(o, m_r * σ, m_g * τ)
                            (μ, p, q) = (m_r * σ, r, g)
                        else
                            (μ, p, q) = (m_g * τ, g, r)
                        end
                        if !any(Syz) do τ
                            divisible = maybe_div(μ, τ) !== nothing
                            divisible
                        end
                            if total_degree(μ) == current_degree
                                S[μ,p,q] = μ
                            else
                                P[total_degree(μ)][μ,p,q] = μ
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
        if is_sig_redundant(o, G, i)
            deleteat!(G, i)
        end
    end

    result = getindex.(G, 2)
    filter!(!iszero, result)
    progress_logged && @info("Done. Returning a Gröbner basis of length $(length(result))")

    return result
end

function interreduce!(o, H)
    @info("Interreducing $(length(H)) polynomials")
    for i in 1:length(H)
        @info("$i/$(length(H))")
        H[i] = leadrem(o, H[i], H[[1:i-1; i+1:end]])
    end
    filter!(!iszero, H)
    @info("After interreduction, $(length(H)) polynomials left")
end

function gröbner_basis(alg::Arri, o::MonomialOrder, G::AbstractArray{<:Polynomial}; kwds...)
    # we go from last to first instead of from first to last, since in our convention,
    # the signature is the _first_ nonzero leading monomial in a vector, not the _last_.
    H = G[end:end]
    for g in G[end-1:-1:1]
        unshift!(H, g)
        H = gröbner_basis_sig_incremental(alg, o, H, kwds...)
        interreduce!(o, H)
    end

    return H
end

end
