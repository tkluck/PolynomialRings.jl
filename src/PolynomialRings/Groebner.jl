module Gröbner

import LinearAlgebra: Transpose
import SparseArrays: SparseVector


import ..Modules: AbstractModuleElement, modulebasering, leading_row
import ..Polynomials: monomialorder
import PolynomialRings: leading_term, lcm_multipliers
import PolynomialRings: syzygies


"""
    syz = syzygies(G)

Return all relations between the elements of G.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> I = [x^5, x^2 + y, x*y + y^2];

julia> G, tr = gröbner_transformation(I);

julia> K = syzygies(G) * tr; # the kernel of the map R^3 -> I induced by these generators

julia> iszero(K * I)
true
```
"""
function syzygies(polynomials::AbstractVector{M}) where M <: AbstractModuleElement
    o = monomialorder(eltype(polynomials))
    pairs_to_consider = [
        (i,j) for i in eachindex(polynomials) for j in eachindex(polynomials)
        if i < j && leading_row(polynomials[i]) == leading_row(polynomials[j])
    ]

    result = Vector{Transpose{modulebasering(M),SparseVector{modulebasering(M),Int}}}()

    for (i,j) in pairs_to_consider
        a = polynomials[i]
        b = polynomials[j]
        lt_a = leading_term(o, a)
        lt_b = leading_term(o, b)

        m_a, m_b = lcm_multipliers(lt_a, lt_b)
        S = m_a * a - m_b * b

        (syzygy, S_red) = divrem(o, S, polynomials)
        if !iszero(S_red)
            throw(ArgumentError("syzygies(...) expects a Gröbner basis, so S_red = $( S_red ) should be zero"))
        end
        syzygy[1,i] -= m_a
        syzygy[1,j] += m_b

        syz_red = rem(o, syzygy, result)
        if !iszero(syz_red)
            push!(result, syz_red)
        end
    end

    flat_result = [ result[x][1,y] for x=eachindex(result), y=eachindex(polynomials) ]

    return flat_result
end

end
