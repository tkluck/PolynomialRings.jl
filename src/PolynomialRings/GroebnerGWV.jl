module GröbnerGWV


import PolynomialRings
import LinearAlgebra: Transpose
import SparseArrays: SparseVector, sparsevec, sparse

import DataStructures: SortedDict, DefaultDict
import ProgressMeter: Progress, finish!, next!, @showprogress

import ..Backends.Gröbner: GWV
import ..Modules: AbstractModuleElement, modulebasering
import ..Modules: withtransformations, separatetransformation
import ..MonomialOrderings: MonomialOrder, @withmonomialorder
import ..Monomials: total_degree, any_divisor
import ..Operators: Lead, Full, content, integral_fraction
import ..Polynomials: Polynomial, monomialorder, monomialtype, PolynomialBy
import ..Terms: monomial, coefficient
import PolynomialRings: gröbner_basis, gröbner_transformation, xrem!
import PolynomialRings: leading_term, leading_monomial, lcm_multipliers, lcm_degree, fraction_field, basering, base_extend, base_restrict
import PolynomialRings: maybe_div, termtype, monomialtype, leading_row, leading_coefficient

function regular_topreduce_rem(m, G; order)
    @withmonomialorder order
    u1,v1 = m
    v1 = deepcopy(v1)
    i = 1
    supertopreducible = false
    while i <= length(G)
        u2, v2 = G[i]
        if iszero(v2)
            if maybe_div(u1, u2) !== nothing
                supertopreducible = true
            end
        elseif !iszero(v1)
            t = maybe_div(leading_monomial(v1), leading_monomial(v2))
            if t !== nothing
                c1 = leading_coefficient(v1)
                c2 = leading_coefficient(v2)
                m1, m2 = lcm_multipliers(c1, c2)
                if t * u2 ≺ u1
                    # new_u1 = u1 - c*(t*u2)
                    @. v1 = m1*v1 - m2*(t*v2)
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
function gwv(order::MonomialOrder, polynomials::AbstractVector{M}; with_transformation=false) where M <: AbstractModuleElement
    @withmonomialorder order

    if with_transformation
        polynomials = withtransformations(polynomials)
    else
        polynomials = map(polynomials) do f
            f, n = integral_fraction(f)
            f
        end
    end

    # experimentally, it seems much better to sort in
    # decreasing monomial order
    polynomials = sort(polynomials, order=order, rev=true)

    P = modulebasering(M)
    R = base_restrict(P)
    S = eltype(polynomials)
    Signature = monomialtype(R[])
    MM = Tuple{Signature, S}

    signature(m) = m[1]
    # --------------------------------------------------------------------------
    # Declare the variables where we'll accumulate the result
    # --------------------------------------------------------------------------
    G = Tuple{Signature, S}[]
    H = DefaultDict{Int, Set{monomialtype(R)}}(Set{monomialtype(R)})
    JP = SortedDict{Signature, MM}(order)

    n = length(polynomials)
    for (i,p) in enumerate(polynomials)
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

    progress = Progress(length(JP), "Computing Gröbner basis: ")
    loops = 0
    # step 3
    while !isempty(JP)
        loops += 1
        progress.n = length(JP) + loops
        next!(progress; showvalues = [(Symbol("|G|"), length(G)), (Symbol("|JP|"), length(JP)), (:loops, loops)])

        # step 1.
        sig, m = first(JP)
        delete!(JP, sig)
        (T, v1) = m

        # step 2: criterion from thm 2.3(c)
        # there is a pair (u_2, v_2) ∈ G so that lm(u_2) divides
        # lm(T) and t lm(v_2) ≺ lm(v_1) where t = lm(T)/lm(u_2)
        if any(G) do m2
            u2,v2 = m2
            t = maybe_div(T, u2)
            if t !== nothing
                if t * leading_monomial(v2) ≺ leading_monomial(v1)
                    return true
                end
            end
            return false
        end
            continue
        end

        (_,v), status = regular_topreduce_rem(m, G, order=order)

        if iszero(v)
            newh = T
            push!(H[newh.i], newh.m)
            filter!(JP) do key_value
                sig, jp = key_value
                T2, v2 = jp
                divisible = maybe_div(T2, newh) !== nothing
                !divisible
            end
        else
            if status == :supertopreducible
                # pass
            elseif status == :notsupertopreducible
                # i) Add the leading terms of the principle syzygies, vT j − v j T for
                # 1 ≤ j ≤ |U |, to H,
                if M <: Polynomial # this syzygy does not exist in the case of modules.
                    for (Tj, vj) in G
                        # syzygy = v*Tj - vj*T
                        lhs = leading_monomial(v)*Tj
                        rhs = leading_monomial(vj)*T
                        if lhs != rhs
                            newh = max(order, lhs, rhs)
                            push!(H[newh.i], newh.m)
                        end
                    end
                end
                # ii) Form new J-pairs of (T, v) and (T j , v j ), 1 ≤ j ≤ |U |,
                # iii) Insert into JP all such J-pairs whose signatures are not re-
                # ducible by H (storing only one J-pair for each distinct signature
                # T , the one with v-part minimal), and
                for (Tj, vj) in G
                    t1_t2 = lcm_multipliers(leading_monomial(v), leading_monomial(vj))
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
                        if !any_divisor(Jsig.m) do d
                            d in H[Jsig.i]
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
                push!(G, (T,v))
            else
                @assert false "Didn't expect $status"
            end
        end
    end

    # --------------------------------------------------------------------------
    # Interreduce the result
    # --------------------------------------------------------------------------
    result = getindex.(G, 2)
    k = length(result)
    @showprogress "Interreducing result" for i in 1:k
        xrem!(result[i], result[[1:i-1; i+1:k]], order=order)
        if basering(modulebasering(eltype(result))) <: Integer
            result[i] ÷= content(result[i])
        end
    end
    # what we filter out is probably a Gröbner basis for the syzygies, and
    # maybe the caller wants to have it?
    filter!(!iszero, result)
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

function gröbner_basis(::GWV, o::MonomialOrder, G::AbstractArray{<:AbstractModuleElement}; kwds...)
    # GWV chokes on empty arrays mainly because it tries to modify the input
    # array a few times (restrict to integers, possibly add the transformation)
    # so lets short-circuit that case.
    isempty(G) && return copy(G)
    return gwv(o, G, with_transformation=false, kwds...)
end

function gröbner_transformation(::GWV, o::MonomialOrder, G::AbstractArray{<:AbstractModuleElement}; kwds...)
    # GWV chokes on empty arrays mainly because it tries to modify the input
    # array a few times (restrict to integers, possibly add the transformation)
    # so lets short-circuit that case.
    P = modulebasering(eltype(G))
    if isempty(G)
        return copy(G), sparse(Matrix{P}(undef, 0, 0))
    end
    return gwv(o, G, with_transformation=true, kwds...)
end

end
