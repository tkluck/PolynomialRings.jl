module Gröbner

using DataStructures: PriorityQueue, enqueue!, dequeue!

import PolynomialRings: gröbner_basis, gröbner_transformation, syzygies
import PolynomialRings.Backends.Gröbner: Buchberger

import PolynomialRings: leading_term, leading_monomial, lcm_multipliers, lcm_degree, fraction_field, basering, base_extend
import PolynomialRings: maybe_div
import PolynomialRings.Monomials: total_degree
import PolynomialRings.MonomialOrderings: MonomialOrder
import PolynomialRings.Polynomials: Polynomial, monomialorder, terms
import PolynomialRings.Terms: monomial
import PolynomialRings.Modules: AbstractModuleElement, modulebasering, leading_row
import PolynomialRings.Operators: Lead, Full, Tail
if VERSION >= v"0.7-"
    using LinearAlgebra: Transpose
    using SparseArrays: spzeros, sparsevec, SparseVector
else
    Transpose = RowVector
    findall(f, A) = find(f, A)
end

"""
    gröbner_basis = buchberger(monomialorder, polynomials, Val{false}())
    gröbner_basis, transformation = buchberger(monomialorder, polynomials, Val{true}())

An implementation of the Buchberger algorithm with a few standard optimizations.
This is based on the description in
> Cox, David, John Little, and Donal O'shea. Ideals, varieties, and algorithms.
> Vol. 3. New York: Springer, 1992.
They describe a "Criterion" (capitalized) which seems to be known in the
literature as Gebauer/Möller's optimization, which is how I've described it
below.

In addition to that, with every addition of a nonzero polynomial \$f\$ to the
result set, we check for every other polynomial \$g\$ whether it now reduces to
zero w.r.t. the new set. If so, we discard it; if not, we perform a tail
reduction on \$g\$, hoping that this reduces its number of monomials, speeding up
future reductions.

We avoid reducing \$g\$'s lead monomial if \$g\$ doesn't reduce to zero, as I'm
not convinced that maintains the correctness of the algorithm.
"""
function buchberger(o::MonomialOrder, polynomials::AbstractVector{M}, ::Val{with_transformation}) where M <: AbstractModuleElement where with_transformation
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
    all_stable_indices() = findall(!iszero, stable_ix_to_ix)
    all_other_stable_indices(stable_ix) = filter(i->i!=stable_ix, all_stable_indices())

    function reduce_result_element(reducetype, stable_ix, other_stable_indices, is_new)
        isremoved(stable_ix) && return :zero
        other_stable_indices = filter(!isremoved, other_stable_indices)
        unreduced = stable_result[stable_ix]
        if with_transformation
            q, reduced = divrem(reducetype, o, unreduced, @view stable_result[other_stable_indices])
        else
            reduced    =    rem(reducetype, o, unreduced, @view stable_result[other_stable_indices])
        end
        if iszero(reduced)
            remove_result_element(stable_ix)
            update_priorities(stable_ix)
            return :zero
        # NOTE: we're using the fact that (div)rem(...) will return the _identical_
        # object in case no reduction takes place.
        elseif reduced === unreduced
            return :unchanged
        else
            # @assert reduced != unreduced
            # if the leading term has changed but we didn't fully reduce to
            # zero, we cannot guarantee the correctness of this algorithm if we've
            # already computed S-pairs with this element. In that case, we
            # discard the result of the full reduction and only do a tail
            # reduction instead.
            if !is_new && leading_term(o, reduced) != leading_term(o, unreduced)
                if with_transformation
                    q, reduced = divrem(Tail(), o, unreduced, @view stable_result[other_stable_indices])
                else
                    reduced    =    rem(Tail(), o, unreduced, @view stable_result[other_stable_indices])
                end
                if reduced === unreduced
                    return :unchanged
                end
            end
            stable_result[stable_ix] = reduced
            if with_transformation
                # can't use findall(): q is a row vector, but we want
                # integer indexes to be able to match them to other_stable_indices
                nonzero_ixs = filter(i->!iszero(q[i]), 1:length(q))
                for j in nonzero_ixs
                    stable_transformation[stable_ix] -= q[j] * stable_transformation[other_stable_indices[j]]
                end
            end
            update_priorities(stable_ix)
            return :nonzero
        end
    end
    full_reduce_result_element(stable_ix) = full_reduce_result_element(stable_ix, all_other_stable_indices(stable_ix))
    function full_reduce_result_element(stable_ix, other_stable_indices_hint, is_new=true)
        res = reduce_result_element(Lead(), stable_ix, other_stable_indices_hint, is_new)
        if res == :zero || res == :unchanged
            return res
        elseif res == :nonzero
            res2 = reduce_result_element(Full(), stable_ix, all_other_stable_indices(stable_ix), is_new)
            if res2 == :zero
                return :zero
            else
                for other_ix in all_other_stable_indices(stable_ix)
                    full_reduce_result_element(other_ix, stable_ix:stable_ix, false)
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
        lm_a = leading_monomial(o, a)
        lm_b = leading_monomial(o, b)
        lcm_degree(lm_a, lm_b)
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
        if leading_row(a) == leading_row(b)
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
                return nothing
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
    considered = 0
    # step 3
    while true
        loops += 1
        if loops % 100 == 0
            l = length(result)
            k = length(pairs_to_consider)
            info("Gröbner: After about $loops loops: $l elements in basis; $considered S-polynomials considered; at most $k pairs left to consider.")
        end

        p = pop_pair()
        p === nothing && break
        (i,j) = p

        a = stable_result[i]
        b = stable_result[j]

        lt_a = leading_term(o, a)
        lt_b = leading_term(o, b)

        m_a, m_b = lcm_multipliers(lt_a, lt_b)

        # step 3a
        leading_lcm = m_a*lt_a
        if total_degree(leading_lcm) == total_degree(lt_a) + total_degree(lt_b)
            continue
        end
        if any(all_stable_indices()) do l
           l != i && l != j &&
           leading_row(stable_result[l]) == leading_row(a) &&
           !(_pair(i,l) in keys(pairs_to_consider)) &&
           !(_pair(j,l) in keys(pairs_to_consider)) &&
           maybe_div(leading_lcm, leading_term(o, stable_result[l])) !== nothing
        end
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
        end
        considered += 1
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


gröbner_transformation(::Buchberger, o::MonomialOrder, G; kwds...) = buchberger(o, G, Val{true}(), kwds...)
gröbner_basis(::Buchberger, o::MonomialOrder, G; kwds...) = buchberger(o, G, Val{false}(), kwds...)

end
