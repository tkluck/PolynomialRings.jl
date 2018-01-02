module GröbnerGWV

using Nulls
using DataStructures: SortedDict, DefaultDict
using Iterators: chain

import PolynomialRings
import PolynomialRings: gröbner_basis

import PolynomialRings: leading_term, lcm_multipliers, lcm_degree, fraction_field, basering, base_extend
import PolynomialRings: maybe_div
import PolynomialRings.MonomialOrderings: MonomialOrder
import PolynomialRings.Monomials: total_degree, any_divisor
import PolynomialRings.Polynomials: Polynomial, monomialorder, monomialtype
import PolynomialRings.Terms: monomial, coefficient
import PolynomialRings.Modules: AbstractModuleElement, modulebasering
import PolynomialRings.Operators: Lead, Full

# a few functions to be able to write the same algorithm for
# computations in a free f.g. module and in a polynomial ring.
# In this context, a 'monomial' is either a monomial (polynomial ring)
# or a tuple of (index, monomial) (free f.g. module).
_leading_row(p::Polynomial) = 1
_leading_row(a::AbstractArray) = findfirst(a)
_leading_term(o::MonomialOrder, p::Polynomial) = leading_term(o, p)
_leading_term(o::MonomialOrder, a::AbstractArray) = leading_term(o, a[_leading_row(a)])
_leading_monomial(o::MonomialOrder, p::Polynomial) = monomial(leading_term(o, p))
_leading_monomial(o::MonomialOrder, a::AbstractArray) = (i = findfirst(a); i == 0 ? null : (i, _leading_monomial(o, a[i])))
_leading_coefficient(o::MonomialOrder, p::Polynomial) = coefficient(leading_term(o, p))
_leading_coefficient(o::MonomialOrder, a::AbstractArray) = (i = findfirst(a); (i, _leading_coefficient(o, a[i])))
_lcm_degree(a, b) = lcm_degree(a, b)
_lcm_degree(a::Tuple, b::Tuple) = lcm_degree(a[2], b[2])
_maybe_div(a, b) = maybe_div(a,b)
_maybe_div(a::Tuple, b::Tuple) = (a[1] == b[1]) ? _maybe_div(a[2], b[2]) : null

function regular_topreduce_rem(o, m, G)
    u1,v1 = m
    i = 1
    supertopreducible = false
    while i <= length(G)
        u2, v2 = G[i]
        if iszero(v2)
            if !iszero(u1) && !iszero(u2) && !isnull(_maybe_div(_leading_monomial(o,u1), _leading_monomial(o,u2)))
                supertopreducible = true
            end
        elseif !iszero(v1)
            t = _maybe_div(_leading_monomial(o,v1), _leading_monomial(o,v2))
            if !isnull(t)
                lr1 = _leading_row(u1)
                lr2 = _leading_row(u2)
                lm1 = monomial(_leading_term(o,u1))
                lm2 = monomial(_leading_term(o,u2))
                if lr2 > lr1 || (lr1 == lr2 && Base.Order.lt(o, t * lm2, lm1))
                    c = _leading_coefficient(o,v1) // _leading_coefficient(o,v2)
                    new_u1 = u1 - c*(t*u2)
                    if _leading_monomial(o,new_u1) != _leading_monomial(o,u1)
                        supertopreducible = true
                    else
                        u1, v1 = (new_u1, v1 - c*(t*v2))
                        supertopreducible = false
                        i = 1
                        continue
                    end
                end
            end
        end
        i += 1
    end

    return (u1,v1), supertopreducible ? :supertopreducible : :notsupertopreducible
end

function gwv(o::MonomialOrder, polynomials::AbstractVector{P}) where P <: Polynomial
    R = base_extend(P)
    Rm = RowVector{R, SparseVector{R,Int}}
    M = Tuple{Rm, R}
    Sig = Tuple{Int, monomialtype(R)}
    RmLM = Tuple{Int, monomialtype(R)}

    signature(m) = _leading_monomial(o,m[1])
    siglt(a,b) = (a[1] > b[1] || (a[1] == b[1] && Base.Order.lt(o, a[2], b[2])))
    # --------------------------------------------------------------------------
    # Declare the variables where we'll accumulate the result
    # --------------------------------------------------------------------------
    G = Tuple{Rm, R}[]
    H = DefaultDict{Int, Set{monomialtype(R)}}(Set{monomialtype(R)})
    JP = SortedDict{Sig, M}(Base.Order.Lt(siglt))
    #JP = PriorityQueue{M, Sig}(Base.Order.Lt(siglt))

    n = length(polynomials)
    for (i,p) in enumerate(polynomials)
        T = sparsevec(Dict(i=>one(R)), n)'
        m = (T, p)
        JP[signature(m)] = m
    end

    loops = 0
    considered = 0
    divisors_considered = 0
    divisor_considerations = 0
    progress_logged = false
    # step 3
    while length(JP) > 0
        loops += 1
        if loops % 100 == 0
            l = length(G)
            k = length(JP)
            h = sum(length, values(H))
            info("GWV: After $loops loops: $l elements in basis; $considered J-pairs considered; |JP|=$k, |H|=$h; $divisor_considerations considerations of divisors ($(divisors_considered/divisor_considerations) divisors on average).")
            progress_logged = true
        end

        # step 1.
        sig, m = first(JP)
        delete!(JP, sig)
        (T, v1) = m

        # step 2: criterion from thm 2.3(c)
        # there is a pair (u_2, v_2) ∈ G so that lm(u_2) divides
        # lm(T) and t lm(v_2) ≺ lm(v_1) where t = lm(T)/lm(u_2)
        if any(G) do m2
            u2,v2 = m2
            t = _maybe_div(_leading_monomial(o,T), _leading_monomial(o,u2))
            if !isnull(t)
                if Base.Order.lt(o, t * _leading_monomial(o,v2), _leading_monomial(o,v1))
                    return true
                end
            end
            return false
        end
            continue
        end

        (_,v), status = regular_topreduce_rem(o, m, G)

        if iszero(v)
            newh = _leading_monomial(o,T)
            push!(H[newh[1]], newh[2])
            filter!(JP) do sig, jp
                T2, v2 = jp
                divisible = !isnull(_maybe_div(_leading_monomial(o,T2), newh))
                !divisible
            end
        else
            if status == :supertopreducible
                # pass
            elseif status == :notsupertopreducible
                # i) Add the leading terms of the principle syzygies, vT j − v j T for
                # 1 ≤ j ≤ |U |, to H,
                for (Tj, vj) in G
                    syzygy = v*Tj - vj*T
                    if !iszero(syzygy)
                        newh = _leading_monomial(o,syzygy)
                        push!(H[newh[1]], newh[2])
                    end
                end
                # ii) Form new J-pairs of (T, v) and (T j , v j ), 1 ≤ j ≤ |U |,
                # iii) Insert into JP all such J-pairs whose signatures are not re-
                # ducible by H (storing only one J-pair for each distinct signature
                # T , the one with v-part minimal), and
                for (Tj, vj) in G
                    lm1 = _leading_monomial(o,v)
                    lm2 = _leading_monomial(o,vj)
                    t1, t2 = lcm_multipliers(lm1, lm2)
                    c = coefficient(_leading_term(o,v)) // coefficient(_leading_term(o,vj))
                    lr1 = _leading_row(T)
                    lr2 = _leading_row(Tj)
                    lt1 = _leading_term(o,T)
                    lt2 = _leading_term(o,Tj)
                    if lr1 > lr2 || ((lr1 == lr2) && Base.Order.lt(o, t1*monomial(lt1), t2*monomial(lt2)))
                        Jsig = (lr2, t2*monomial(lt2))
                        Jpair = (t2*Tj, t2*vj)
                    else
                        Jsig = (lr1, t1*monomial(lt1))
                        Jpair = (t1*T, t1*v)
                    end
                    red = t1*T - c*(t2*Tj)
                    if !iszero(red) && _leading_monomial(o,red) == Jsig
                        divisor_considerations += 1
                        if !any_divisor(Jsig[2]) do d
                            divisors_considered += 1
                            d in H[Jsig[1]]
                        end
                            if Jsig in keys(JP)
                                oldu,oldv = JP[Jsig]
                                newv = Jpair[2]
                                if Base.Order.lt(o, _leading_monomial(o,newv), _leading_monomial(o,oldv))
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

        considered += 1
    end

    # --------------------------------------------------------------------------
    # Interreduce the result
    # --------------------------------------------------------------------------
    result = getindex.(G, 2)
    k = length(result)
    progress_logged && info("Done; interreducing the $k result polynomials")
    for i in 1:k
        result[i] = rem(o, result[i], result[[1:i-1; i+1:k]])
    end
    filter!(!iszero, result)
    progress_logged && info("Done. Returning a Gröbner basis of length $(length(result))")
    # --------------------------------------------------------------------------
    # Return the result
    # --------------------------------------------------------------------------
    return result
end

struct GWV <: PolynomialRings.Backends.Gröbner.Backend end

gröbner_basis(::GWV, o::MonomialOrder, G::AbstractArray{<:Polynomial}; kwds...) = gwv(o, G, kwds...)

end
