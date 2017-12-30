module Groebner

using Nulls
using DataStructures: PriorityQueue, enqueue!, dequeue!

import PolynomialRings: leading_term, lcm_multipliers, lcm_degree, fraction_field, basering, base_extend
import PolynomialRings: maybe_div
import PolynomialRings.Monomials: total_degree
import PolynomialRings.Polynomials: Polynomial, monomialorder, terms
import PolynomialRings.Terms: monomial
import PolynomialRings.Modules: AbstractModuleElement, modulebasering
import PolynomialRings.Operators: Lead, Full

# a few functions to be able to write the same algorithm for
# computations in a free f.g. module and in a polynomial ring.
# In this context, a 'monomial' is either a monomial (polynomial ring)
# or a tuple of (index, monomial) (free f.g. module).
_leading_row(p::Polynomial) = 1
_leading_row(a::AbstractArray) = findfirst(a)
_leading_term(p::Polynomial) = leading_term(p)
_leading_term(a::AbstractArray) = leading_term(a[_leading_row(a)])
_leading_monomial(p::Polynomial) = monomial(leading_term(p))
_leading_monomial(a::AbstractArray) = (i = findfirst(a); (i, _leading_monomial(a[i])))
_lcm_degree(a, b) = lcm_degree(a, b)
_lcm_degree(a::Tuple, b::Tuple) = lcm_degree(a[2], b[2])
_lcm_multipliers(a, b) = lcm_multipliers(a, b)
_lcm_multipliers(a::Tuple, b::Tuple) = lcm_multipliers(a[2], b[2])

function buchberger(polynomials::AbstractVector{M}, ::Val{with_transformation}) where M <: AbstractModuleElement where with_transformation
    P = base_extend(modulebasering(M))

    # --------------------------------------------------------------------------
    # Declare the variables where we'll accumulate the result
    # --------------------------------------------------------------------------
    result = base_extend.(polynomials)
    if with_transformation
        n = length(polynomials)
        transformation = [ sparsevec(Dict(i=>one(P)), n) for i in 1:n ]
    end
    # --------------------------------------------------------------------------
    # Declare a few helper functions to facilitate manipulating the result array
    # and the transformation that yields it. This involves some bookkeeping
    # mainly because, during the algorithm, it may turn out that some entries
    # reduce to zero. We remove them, but that changes the indices of the
    # other polynomials. For this reason, we give every polynomial
    # a 'stable' index that does not change over the lifetime of this function.
    # --------------------------------------------------------------------------
    stable_ix_to_ix = collect(1:length(result))

    # NOTE: these views make using stable indices easy on the eye, but they
    # may also lead to out-of-bounds memory access as I don't think the values
    # in the index array are bounds checked after creating the view. So be sure
    # to call `isremoved` before indexing into these!
    stable_result = view(result, stable_ix_to_ix)
    if with_transformation
        stable_transformation = view(transformation, stable_ix_to_ix)
    end
    function add_result_element(f, factors...)
        if iszero(f)
            push!(stable_ix_to_ix, 0)
        else
            push!(result, f)
            push!(stable_ix_to_ix, length(result))
            if with_transformation
                tr = sum( m_i * stable_transformation[i] for (i,m_i) in factors )
                push!(transformation, tr)
            end
        end
        stable_ix = length(stable_ix_to_ix)
        return stable_ix
    end
    function remove_result_element(stable_ix)
        ix = stable_ix_to_ix[stable_ix]
        deleteat!(result, ix)
        map!(i -> i>ix ? i-1 : i, stable_ix_to_ix, stable_ix_to_ix)
        stable_ix_to_ix[stable_ix] = 0
        if with_transformation
            deleteat!(transformation, ix)
        end
    end
    isremoved(stable_ix) = stable_ix_to_ix[stable_ix] == 0
    all_stable_indices() = find(!iszero, stable_ix_to_ix)
    all_other_stable_indices(stable_ix) = filter(i->i!=stable_ix, all_stable_indices())

    function reduce_result_element(reducetype, stable_ix, other_stable_indices)
        isremoved(stable_ix) && return :zero
        other_stable_indices = filter(!isremoved, other_stable_indices)
        unreduced = stable_result[stable_ix]
        if with_transformation
            q, reduced = divrem(reducetype, unreduced, @view stable_result[other_stable_indices])
        else
            reduced    =    rem(reducetype, unreduced, @view stable_result[other_stable_indices])
        end
        if iszero(reduced)
            remove_result_element(stable_ix)
            update_priorities(stable_ix)
            return :zero
        # NOTE: we're using the fact that (div)rem(...) will return the _identical_
        # object in case no reduction takes place.
        elseif reduced !== unreduced
            # @assert reduced != unreduced
            stable_result[stable_ix] = reduced
            if with_transformation
                nonzero_ixs = find(q)
                for j in nonzero_ixs
                    stable_transformation[stable_ix] -= q[j] * stable_transformation[other_stable_indices[j]]
                end
            end
            update_priorities(stable_ix)
            return :nonzero
        else
            return :unchanged
        end
    end
    full_reduce_result_element(stable_ix) = full_reduce_result_element(stable_ix, all_other_stable_indices(stable_ix))
    function full_reduce_result_element(stable_ix, other_stable_indices_hint)
        res = reduce_result_element(Lead(), stable_ix, other_stable_indices_hint)
        if res == :zero || res == :unchanged
            return res
        elseif res == :nonzero
            res2 = reduce_result_element(Full(), stable_ix, all_other_stable_indices(stable_ix))
            if res2 == :zero
                return :zero
            else
                for other_ix in all_other_stable_indices(stable_ix)
                    full_reduce_result_element(other_ix, stable_ix:stable_ix)
                end
                # the recursion above may have removed us by now
                if isremoved(stable_ix)
                    return :zero
                else
                    return :nonzero
                end
            end
        else
            @assert false "unreachable: didn't expect $res"
        end
    end

    # --------------------------------------------------------------------------
    # Declare a few functions for maintaining a priority queue for all the pairs
    # of (stable) indices for which we still need to consider the S polynomial.
    # --------------------------------------------------------------------------
    pairs_to_consider = PriorityQueue{Tuple{Int,Int},Int}()
    _pair(i,j) = (min(i,j), max(i,j))
    function pair_priority(i,j)
        a = stable_result[i]
        b = stable_result[j]
        lm_a = _leading_monomial(a)
        lm_b = _leading_monomial(b)
        _lcm_degree(lm_a, lm_b)
    end
    function update_priorities(k)
        for ((i,j),prio) in pairs_to_consider
            if !isremoved(i) && !isremoved(j) && (i == k || j == k)
                pairs_to_consider[i,j] = pair_priority(i,j)
            end
        end
    end
    function add_pair(i,j)
        isremoved(i) && return
        isremoved(j) && return
        i == j && return
        a = stable_result[i]
        b = stable_result[j]
        if _leading_row(a) == _leading_row(b)
            pairs_to_consider[i,j] = pair_priority(i,j)
        end
    end
    function pop_pair()
        while true
            if length(pairs_to_consider)>0
                (i,j) = dequeue!(pairs_to_consider)
                if !isremoved(i) && !isremoved(j)
                    return i,j
                end
            else
                return null
            end
        end
    end

    # --------------------------------------------------------------------------
    # Now, we start the real work:
    #  1. reduce the input polynomials among themselves.
    #  2. add all pairs of polynomials to the queue.
    #  3. consume the queue:
    #     3a. discard this pair if it satisfies Gebauer/Möller's criterion
    #     3b. add the S - polynomial to the set
    #     3c. reduce it w.r.t. the rest
    #     3d. if it remains nonzero, add every new pair to the queue.
    # --------------------------------------------------------------------------

    # step 1.
    for stable_ix in all_stable_indices()
        full_reduce_result_element(stable_ix)
    end

    # step 2.
    for j in all_stable_indices()
        for i in 1:(j-1)
            add_pair(i,j)
        end
    end

    loops = 0
    reductions_to_zero = 0
    saved = 0
    # step 3
    while true
        loops += 1
        if loops % 1000 == 0
            l = length(result)
            k = length(pairs_to_consider)
            info("Groebner: After about $loops loops: $l elements in basis; $saved reductions saved; $reductions_to_zero reductions to zero; $k pairs left to consider.")
        end

        p = pop_pair()
        isnull(p) && break
        (i,j) = p

        a = stable_result[i]
        b = stable_result[j]

        lt_a = _leading_term(a)
        lt_b = _leading_term(b)

        m_a, m_b = lcm_multipliers(lt_a, lt_b)

        # step 3a
        leading_lcm = m_a*lt_a
        if total_degree(leading_lcm) == total_degree(lt_a) + total_degree(lt_b)
            saved += 1
            continue
        end
        if any(all_stable_indices()) do l
           l != i && l != j &&
           _leading_row(stable_result[l]) == _leading_row(a) &&
           !(_pair(i,l) in keys(pairs_to_consider)) &&
           !(_pair(j,l) in keys(pairs_to_consider)) &&
           !isnull(maybe_div(leading_lcm, _leading_term(stable_result[l])))
        end
            saved += 1
            continue
        end

        # step 3b
        S = m_a * a - m_b * b
        stable_ix = add_result_element(S, i=>m_a, j=>-m_b)
        # step 3c
        if full_reduce_result_element(stable_ix) != :zero
            # step 3d
            for other_ix in all_other_stable_indices(stable_ix)
                add_pair(other_ix, stable_ix)
            end
        else
            reductions_to_zero += 1
        end
    end

    # --------------------------------------------------------------------------
    # Return the result
    # --------------------------------------------------------------------------
    if with_transformation
        # prepare result: `transformation` was an array of sparse arrays to be able
        # to efficiently push to it, but for the end user, a (sparse) matrix is more
        # convenient.
        flat_tr = spzeros(P, length(result), length(polynomials))
        for (i,x) in enumerate(transformation)
            flat_tr[i,:] = x
        end
        return result, flat_tr
    else
        return result
    end
end

function syzygies(polynomials::AbstractVector{M}) where M <: AbstractModuleElement
    pairs_to_consider = [
        (i,j) for i in eachindex(polynomials) for j in eachindex(polynomials)
        if i < j && _leading_row(polynomials[i]) == _leading_row(polynomials[j])
    ]

    result = Vector{RowVector{modulebasering(M),SparseVector{modulebasering(M),Int}}}()

    for (i,j) in pairs_to_consider
        a = polynomials[i]
        b = polynomials[j]
        lt_a = _leading_term(a)
        lt_b = _leading_term(b)

        m_a, m_b = lcm_multipliers(lt_a, lt_b)
        S = m_a * a - m_b * b

        (syzygy, S_red) = divrem(S, polynomials)
        if !iszero(S_red)
            throw(ArgumentError("syzygies(...) expects a Groebner basis, so S_red = $( S_red ) should be zero"))
        end
        syzygy[1,i] -= m_a
        syzygy[1,j] += m_b

        syz_red = rem(syzygy, result)
        if !iszero(syz_red)
            push!(result, syz_red)
        end
    end

    flat_result = [ result[x][1,y] for x=eachindex(result), y=eachindex(polynomials) ]

    return flat_result
end

import PolynomialRings.Backends
import PolynomialRings.Backends.Groebner: Buchberger
"""
    basis, transformation = groebner_transformation(polynomials)

Return a groebner basis for the ideal generated by `polynomials`, together with a
`transformation` that proves that each element in `basis` is in that ideal (i.e.
`basis == transformation * polynomials`).
"""
groebner_transformation(G; kwds...) = groebner_transformation(Backends.Groebner.default, G, kwds...)
"""
    basis = groebner_basis(polynomials)

Return a groebner basis for the ideal generated by `polynomials`.
"""
groebner_basis(G; kwds...) = groebner_basis(Backends.Groebner.default, G, kwds...)

groebner_transformation(::Buchberger, G; kwds...) = buchberger(G, Val{true}(), kwds...)
groebner_basis(::Buchberger, G; kwds...) = buchberger(G, Val{false}(), kwds...)

# FIXME: why doesn't this suppress info(...) output?
logging(DevNull, current_module(), kind=:info)

end
