module GröbnerSig

using Nulls
using DataStructures: DefaultDict
using DataStructures: PriorityQueue, enqueue!, dequeue!
using Iterators: chain

import PolynomialRings
import PolynomialRings: gröbner_basis
import PolynomialRings.Backends.Gröbner: Backend, F5C

import PolynomialRings: leading_term, leading_monomial, lcm_multipliers, lcm_degree, fraction_field, basering, base_extend
import PolynomialRings: maybe_div, termtype, monomialtype, leading_row, leading_coefficient
import PolynomialRings.MonomialOrderings: MonomialOrder, degreecompatible
import PolynomialRings.Monomials: total_degree, any_divisor
import PolynomialRings.Polynomials: Polynomial, monomialorder, monomialtype
import PolynomialRings.Terms: monomial, coefficient
import PolynomialRings.Modules: AbstractModuleElement, modulebasering
import PolynomialRings.Operators: Lead, Full

function semi_complete_reduction_rem(o, m, G)
    σ,p = m
    i = 1
    while !iszero(p) && i <= length(G)
        τ, q = G[i]
        if !iszero(q)
            t = maybe_div(leading_monomial(o,p), leading_monomial(o,q))
            if !isnull(t)
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

is_sig_redundant(o, G, i::Integer) = is_sig_redundant(o, G[i], G[[1:i-1; i+1:end]])

function is_sig_redundant(o, f, G)
    (σ, f) = f
    σ.i != 1 && return false
    length(G) == 0 && return false
    iszero(f) && return false
    lm_f = leading_monomial(o, f)
    return any(G) do g
        (τ, g) = g
        iszero(g) && return false
        return !isnull(maybe_div(σ, τ)) && !isnull(maybe_div(lm_f, leading_monomial(o,g)))
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
    Rm = RowVector{R, SparseVector{R,Int}}
    M = monomialtype(PP)
    Signature = monomialtype(polynomials)

    signature(m) = m[1]
    # --------------------------------------------------------------------------
    # Declare the variables where we'll accumulate the result
    # --------------------------------------------------------------------------
    G = Tuple{Signature, R}[]
    PQ = PriorityQueue{Tuple{Signature, R, R}, Signature}
    P = DefaultDict{Int, PQ}(PQ(o))
    Syz = [] # DefaultDict{Int, Set{monomialtype(R)}}(Set{monomialtype(R)})

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

    loops = 0
    considered = 0
    divisors_considered = 0
    divisor_considerations = 0
    progress_logged = false

    while length(P) > 0
        loops += 1
        if loops % 100 == 0
            l = length(G)
            k = length(P)
            h = length(Syz)
            info("$alg: After $loops loops: $l elements in basis; $considered pairs considered; |P|=$k, |Syz|=$h")
            progress_logged = true
        end

        current_degree = minimum(keys(P))
        S = P[current_degree]
        delete!(P, current_degree)

        while length(S) > 0
            (σ, p, q) = dequeue!(S)

            (m_p, m_q) = lcm_multipliers(leading_monomial(o,p), leading_monomial(o,q))
            (c_p, c_q) = leading_coefficient.((p,q))
            S_pq = m_p * p - c_p//c_q * m_q * q
            (σ, r) = semi_complete_reduction_rem(o, (σ, S_pq), G)

            if !iszero(r) && !is_sig_redundant(o, (σ, r), G)
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
                        if total_degree(μ) == current_degree
                            (μ,p,q) ∉ keys(S) && enqueue!(S, (μ, p, q), μ)
                        else
                            (μ,p,q) ∉ keys(P[total_degree(μ)]) && enqueue!(P[total_degree(μ)], (μ, p, q), μ)
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
    progress_logged && info("Done. Returning a Gröbner basis of length $(length(result))")

    return result
end

function interreduce!(o, H)
    for i in 1:length(H)
        H[i] = rem(o, H[i], H[[1:i-1; i+1:end]])
    end
    filter!(!iszero, H)
end

function gröbner_basis(alg::F5C, o::MonomialOrder, G::AbstractArray{<:Polynomial}; kwds...)
    length(G) == 0 && return copy(G)

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
