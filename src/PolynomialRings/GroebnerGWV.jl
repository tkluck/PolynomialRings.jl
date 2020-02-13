module GröbnerGWV


import PolynomialRings
import LinearAlgebra: Transpose
import SparseArrays: SparseVector, sparsevec, sparse

import DataStructures: SortedDict, DefaultDict

import ..AbstractMonomials: any_divisor
import ..Backends.Gröbner: GWV
import ..Constants: Zero
import ..NamingSchemes: namingscheme
import ..Modules: AbstractModuleElement, modulebasering, leading_row
import ..Modules: withtransformations, separatetransformation
import ..MonomialOrderings: MonomialOrder, @withmonomialorder
import ..Operators: Lead, Full, content, integral_fraction
import ..Polynomials: Polynomial, monomialorder, monomialtype, PolynomialBy
import ..Reductions: interreduce!, one_step_xdiv!
import ..StandardMonomialOrderings: LexCombinationOrder, KeyOrder
import ..Terms: monomial, coefficient
import ..Util: @showprogress
import PolynomialRings: gröbner_basis, gröbner_transformation, xrem!
import PolynomialRings: leading_term, leading_monomial, lcm_multipliers, lcm_degree, fraction_field, basering, base_extend, base_restrict
import PolynomialRings: maybe_div, divides, termtype, monomialtype, leading_row, leading_coefficient

const lr = leading_row
maybe_lr(v) = iszero(v) ? nothing : lr(v)
maybe_lm(v, order) = iszero(v) ? nothing : leading_monomial(v, order=order)

reduceop!(v1, m1, m2, t, v2) = @. v1 = m1*v1 - m2*(t*v2)


function regular_topreduce_rem(m, G; order)
    @withmonomialorder order
    u1,v1 = m
    v1 = deepcopy(v1)
    lr1 = maybe_lr(v1)
    lm1 = maybe_lm(v1, order)
    i = 1
    supertopreducible = false
    while i <= length(G[lr1])
        u2, lm2, v2 = G[lr1][i]
        if isnothing(lm2)
            if maybe_div(u1, u2) !== nothing
                supertopreducible = true
            end
        elseif !isnothing(lm1)
            t = maybe_div(lm1, lm2)
            if t !== nothing
                c1 = leading_coefficient(v1)
                c2 = leading_coefficient(v2)
                if t * u2 ≺ u1
                    # new_u1 = u1 - c*(t*u2)
                    #@. v1 = m1*v1 - m2*(t*v2)
                    one_step_xdiv!(v1, v2, order=order, redtype=Lead())
                    lm1 = maybe_lm(v1, order)
                    lr1 = maybe_lr(v1)
                    supertopreducible = false
                    i = 1
                    continue
                elseif t * u2 == u1 && c1 == c2
                    supertopreducible = true
                end
            end
        end
        i += 1
    end

    if basering(modulebasering(v1)) <: Integer
        v1 = v1 ÷ content(v1)
    end

    return (m[1],v1), supertopreducible ? :supertopreducible : :notsupertopreducible
end

"""
    gröbner_basis = gwv(monomialorder, polynomials)

An implementation of the GWV algorithm as popularized by
> Shuhong Gao, Frank Volny, and Mingsheng Wang. "A new algorithm for computing
> Groebner bases." IACR Cryptology ePrint Archive 2010 (2010): 641.
"""
function gwv(order::MonomialOrder, polynomials::AbstractVector{M}, ::Val{with_transformation}) where M <: AbstractModuleElement where with_transformation
    @withmonomialorder order

    if with_transformation
        polynomials = withtransformations(polynomials)
    else
        polynomials = map(polynomials) do f
            f, n = integral_fraction(f)
            f
        end
    end
    filter!(!iszero, polynomials)

    # experimentally, it seems much better to sort in
    # decreasing monomial order
    sort!(polynomials, order=order, rev=true)

    P = modulebasering(M)
    R = base_restrict(P)
    S = eltype(polynomials)
    Signature = monomialtype(R[])
    LM = monomialtype(S)
    Ix = keytype(S)
    MM = Tuple{Signature, S}
    SigOrder = LexCombinationOrder(KeyOrder(), order)

    signature(m) = m[1]
    # --------------------------------------------------------------------------
    # Declare the variables where we'll accumulate the result
    # --------------------------------------------------------------------------
    G = DefaultDict{Union{Ix, Nothing}, Vector{Tuple{Signature, Union{LM, Nothing}, S}} }(Vector{Tuple{Signature, Union{LM, Nothing}, S}})
    G_by_sig = DefaultDict{Any, Vector{Tuple{Signature, Union{LM, Nothing}, S}} }(Vector{Tuple{Signature, Union{LM, Nothing}, S}})
    H = DefaultDict{Int, Set{monomialtype(R)}}(Set{monomialtype(R)})
    JP = SortedDict{Signature, MM}(SigOrder)

    n = length(polynomials)
    @showprogress "Gröbner: preparing inputs" for (i,p) in enumerate(polynomials)
        T = leading_monomial( sparsevec(Dict(i=>one(R)), n) )
        m = (T, p)
        if T ∈ keys(JP)
            oldu,oldp = JP[T]
            if p ≺ oldp
                JP[T] = m
            end
        else
            JP[T] = m
        end
    end

    # step 3
    @showprogress "Computing Gröbner basis: " G H JP while !isempty(JP)
        # step 1.
        sig, m = first(JP)
        delete!(JP, sig)
        (T, v1) = m

        # step 2: criterion from thm 2.3(c)
        # there is a pair (u_2, v_2) ∈ G so that lm(u_2) divides
        # lm(T) and t lm(v_2) ≺ lm(v_1) where t = lm(T)/lm(u_2)
        lm1 = leading_monomial(v1)
        if any(G_by_sig[lr(T)]) do m2
            u2,lm2,v2 = m2
            if (t = maybe_div(T, u2)) |> !isnothing
                if t * lm2 ≺ lm1
                    return true
                end
            end
            return false
        end
            continue
        end

        (_,v), status = regular_topreduce_rem(m, G, order=order)
        lmv = maybe_lm(v, order)

        if (lmv = maybe_lm(v, order)) |> isnothing
            newh = T
            push!(H[newh.first], newh.second)
            filter!(JP) do key_value
                sig, jp = key_value
                T2, v2 = jp
                !divides(newh, T2)
            end
        else
            if status == :supertopreducible
                # pass
            elseif status == :notsupertopreducible
                # i) Add the leading terms of the principle syzygies, vT j − v j T for
                # 1 ≤ j ≤ |U |, to H,
                if M <: Polynomial # this syzygy does not exist in the case of modules.
                    for (Tj, lmj, vj) in G[lr(v)]
                        # syzygy = v*Tj - vj*T
                        lhs = lmv*Tj
                        rhs = lmj*T
                        if lhs != rhs
                            newh = max(order, lhs, rhs)
                            push!(H[newh.first], newh.second)
                        end
                    end
                end
                # ii) Form new J-pairs of (T, v) and (T j , v j ), 1 ≤ j ≤ |U |,
                # iii) Insert into JP all such J-pairs whose signatures are not re-
                # ducible by H (storing only one J-pair for each distinct signature
                # T , the one with v-part minimal), and
                for (Tj, lmj, vj) in G[lr(v)]
                    t1_t2 = lcm_multipliers(lmv, lmj)
                    t1_t2 === nothing && continue
                    t1, t2 = t1_t2
                    c = leading_coefficient(v)
                    cj = leading_coefficient(vj)
                    lhs = t1*T
                    rhs = t2*Tj
                    if !(c == cj && lhs == rhs)
                        if lhs ≺ rhs
                            Jsig = rhs
                            Jpair = (t2*Tj, t2*vj)
                        else
                            Jsig = lhs
                            Jpair = (t1*T, t1*v)
                        end
                        if !any_divisor(Jsig.second, namingscheme(order)) do d
                            d in H[Jsig.first]
                        end
                            # (storing only one J-pair for each distinct signature
                            # T , the one with v-part minimal)
                            if Jsig in keys(JP)
                                oldu,oldv = JP[Jsig]
                                newv = Jpair[2]
                                if newv ≺ oldv
                                    JP[Jsig] = Jpair
                                end
                            else
                                JP[Jsig] = Jpair
                            end
                        end
                    end
                end
                # iv) Append T to U and v to V .
                push!(G[lr(v)], (T,maybe_lm(v, order),v))
                push!(G_by_sig[lr(T)], (T,maybe_lm(v, order),v))
            else
                @assert false "Didn't expect $status"
            end
        end
    end

    # --------------------------------------------------------------------------
    # Interreduce the result
    # --------------------------------------------------------------------------
    result = [f for G_i in values(G) for (_,_,f) in G_i]
    interreduce!(result, order=order)
    # --------------------------------------------------------------------------
    # Return the result
    # --------------------------------------------------------------------------
    if with_transformation
        result, transformation = separatetransformation(result)
        result = map(p->base_extend(p, basering(P)), result)
        return result, transformation
    else
        result = map(p->base_extend(p, basering(P)), result)
        return result
    end
end

function gröbner_basis(::GWV, o::MonomialOrder, G::AbstractVector{<:AbstractModuleElement}; kwds...)
    # GWV chokes on empty arrays mainly because it tries to modify the input
    # array a few times (restrict to integers, possibly add the transformation)
    # so lets short-circuit that case.
    isempty(G) && return copy(G)
    return gwv(o, G, Val(false); kwds...)
end

function gröbner_transformation(::GWV, o::MonomialOrder, G::AbstractVector{<:AbstractModuleElement}; kwds...)
    # GWV chokes on empty arrays mainly because it tries to modify the input
    # array a few times (restrict to integers, possibly add the transformation)
    # so lets short-circuit that case.
    P = modulebasering(eltype(G))
    if isempty(G)
        return copy(G), sparse(Matrix{P}(undef, 0, 0))
    end
    return gwv(o, G, Val(true); kwds...)
end

end
