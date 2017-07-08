module Groebner

import PolynomialRings: leading_term, lcm_multipliers
import PolynomialRings.Polynomials: Polynomial
import PolynomialRings.NamedPolynomials: NamedPolynomial
import PolynomialRings.Modules: AbstractModuleElement, modulebasering

function red(f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    factors = transpose(spzeros(modulebasering(M), length(G)))
    frst = true
    more_loops = false
    f_red = f
    i = 1
    while i<=length(G)
        frst = false
        more_loops = false
        g = G[i]
        q, f_red = divrem(f_red, g)
        if !iszero(q)
            factors[1, i] += q
            i = 1
        else
            i += 1
        end
        if iszero(f_red)
            return f_red, factors
        end
    end

    return f_red, factors
end

function groebner_basis(polynomials::AbstractVector{M}) where M <: AbstractModuleElement

    P = modulebasering(M)
    nonzero_indices = find(p->!iszero(p), polynomials)
    result = polynomials[nonzero_indices]
    transformation =Vector{P}[ P[ i==nonzero_indices[j] ? 1 : 0 for i in eachindex(polynomials)] for j in eachindex(result)]
    if length(result)>=1 # work around compiler bug for empty iterator
        pairs_to_consider = [
            (i,j) for i in eachindex(result) for j in eachindex(result) if i < j
        ]
    else
        pairs_to_consider = Tuple{Int,Int}[]
    end

    while length(pairs_to_consider) > 0
        (i,j) = pop!(pairs_to_consider)
        a = result[i]
        b = result[j]

        lt_a = leading_term(a)
        lt_b = leading_term(b)

        m_a, m_b = lcm_multipliers(lt_a, lt_b)

        S = m_a * a - m_b * b

        # potential speedup: wikipedia says that in all but the 'last steps'
        # (whichever those may be), we can get away with a version of red
        # that only does lead division
        (S_red, factors) = red(S, result)

        factors[1, i] -= m_a
        factors[1, j] += m_b

        if !iszero(S_red)
            new_j = length(result)+1
            append!(pairs_to_consider, [(new_i, new_j) for new_i in eachindex(result)])
            push!(result, S_red)

            nonzero_factors = find(factors)
            tr = [ -sum(factors[x] * transformation[x][y] for x in nonzero_factors) for y in eachindex(polynomials) ]
            push!(transformation, tr)
        end
    end

    #sorted = sortperm(result, by=p->leading_term(p), rev=true)
    #result = result[sorted]
    #transformation = transformation[sorted]

    flat_tr = sparse([ transformation[x][y] for x=eachindex(result), y=eachindex(polynomials) ])

    return result, flat_tr

end

function syzygies{M <: AbstractModuleElement}(polynomials::AbstractVector{M})
    pairs_to_consider = [
        (i,j) for i in eachindex(polynomials) for j in eachindex(polynomials) if i < j
    ]

    result = Vector{RowVector{modulebasering(M)}}()

    for (i,j) in pairs_to_consider
        a = polynomials[i]
        b = polynomials[j]
        lt_a = leading_term(a)
        lt_b = leading_term(b)

        maybe_multipliers = _maybe_lcm_multipliers(lt_a, lt_b)
        if !isnull(maybe_multipliers)
            m_a, m_b = get(maybe_multipliers)
            S = m_a * a - m_b * b

            (S_red, syzygy) = red(S, polynomials)
            if !iszero(S_red)
                throw(ArgumentError("syzygies(...) expects a Groebner basis, so S_red = $( S_red ) should be zero"))
            end
            syzygy[1,i] -= m_a
            syzygy[1,j] += m_b

            (syz_red, _) = red(syzygy, result)
            if !iszero(syz_red)
                push!(result, syz_red)
            end
        end
    end

    flat_result = [ result[x][1,y] for x=eachindex(result), y=eachindex(polynomials) ]

    return flat_result
end

groebner_basis(G::AbstractVector{NP}) where NP<:NamedPolynomial = ((res, tr) = groebner_basis(map(g->g.p,G)); (map(NP, res), map(NP, tr)))

end