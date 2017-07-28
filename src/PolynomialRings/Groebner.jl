module Groebner

import PolynomialRings: leading_term, lcm_multipliers, deg, lcm_degree
import PolynomialRings.Polynomials: Polynomial
import PolynomialRings.Terms: monomial
import PolynomialRings.NamedPolynomials: NamedPolynomial
import PolynomialRings.Modules: AbstractModuleElement, AbstractNamedModuleElement, modulebasering
import PolynomialRings.Operators: leaddivrem

import PolynomialRings.Util: ReadWriteLock, read_lock!, write_lock!, read_unlock!, write_unlock!
"""
    f_red, factors = red(f, G)

Return the multivariate reduction of a polynomial `f` by a vector of
polynomials `G`, together with  row vector of factors. By definition, this
means that no leading term of a polynomial in `G` divides any monomial in
`f`, and `f_red + factors * G == f`.

# Examples
In one variable, this is just the normal Euclidean algorithm:
```jldoctest
julia> R,(x,y) = polynomial_ring(Complex{Int}, :x, :y);
julia> red(x^1 + 1, [x-im])
(0, [x+im]')
julia> red(x^2 + y^2 + 1, [x, y])
(1, [x,y]')
```
"""
function leadred(f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    factors = transpose(spzeros(modulebasering(M), length(G)))
    frst = true
    more_loops = false
    f_red = f
    i = 1
    while i<=length(G)
        frst = false
        more_loops = false
        g = G[i]
        q, f_red = leaddivrem(f_red, g)
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

function red(f::M, G::AbstractVector{M}) where M <: AbstractModuleElement
    f_red, factors = leadred(f,G)

    frst = true
    more_loops = false
    i=1
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

_leading_row(p::Polynomial) = 1
_leading_row(a::AbstractArray) = findfirst(a)
_leading_term(p::Polynomial) = leading_term(p)
_leading_term(a::AbstractArray) = leading_term(a[_leading_row(a)])
using DataStructures
"""
    basis, transformation = groebner_basis(polynomials)

Return a groebner basis for the ideal generated by `polynomials`, together with a
`transformation` that proves that each element in `basis` is in that ideal (i.e.
`basis == transformation * polynomials`).
"""
function groebner_basis(polynomials::AbstractVector{M}, ::Type{Val{with_transformation}}; max_degree=Inf) where M <: AbstractModuleElement where with_transformation

    P = modulebasering(M)
    nonzero_indices = find(p->!iszero(p), polynomials)
    result = polynomials[nonzero_indices]

    if with_transformation
        transformation =Vector{P}[ P[ i==nonzero_indices[j] ? 1 : 0 for i in eachindex(polynomials)] for j in eachindex(result)]
    end

    pairs_to_consider = PriorityQueue(Tuple{Int,Int}, Int)
    for j in eachindex(result)
        for i in 1:(j-1)
            a = result[i]
            b = result[j]
            if _leading_row(a) == _leading_row(b)
                lt_a = _leading_term(a)
                lt_b = _leading_term(b)
                degree = lcm_degree(lt_a, lt_b)

                if degree < deg(lt_a) + deg(lt_b)
                    if degree <= max_degree
                        enqueue!(pairs_to_consider, (i,j), degree)
                    end
                end
            end
        end
    end


    result_lock = ReadWriteLock{Threads.Mutex}()

    Threads.@threads for thread=1:Threads.nthreads() # run code on all threads
        while true
            write_lock!(result_lock)
            if length(pairs_to_consider) == 0
                write_unlock!(result_lock)
                break
            end
            (i,j) = dequeue!(pairs_to_consider)
            write_unlock!(result_lock)

            read_lock!(result_lock)
            a = result[i]
            b = result[j]
            read_unlock!(result_lock)

            lt_a = _leading_term(a)
            lt_b = _leading_term(b)

            m_a, m_b = lcm_multipliers(lt_a, lt_b)

            if monomial(m_a) == monomial(lt_b)
                continue
            end

            S = m_a * a - m_b * b

            # potential speedup: wikipedia says that in all but the 'last steps'
            # (whichever those may be), we can get away with a version of red
            # that only does lead division
            read_lock!(result_lock)
            snapshot = result[1:end]
            read_unlock!(result_lock)
            (S_red, factors) = red(S, snapshot)

            if !iszero(S_red)
                write_lock!(result_lock)

                # we'd now like to add our new-found basis element to result, but
                # another thread may have added new elements since we created our
                # snapshot. So we do the following:
                # 1.  check whether f_red can be reduced further with the newly
                #     added elements
                # 2a. if not, add it.
                # 2b. if so, we'll have to also see whether the further reduced
                #     f_red can be further reduced.
                # In the 2b. case, we release the lock, take a new snapshot and
                # basically restart the computation. It is hoped that this is
                # either relatively rare, or is a brief computation.

                second_snapshot = result[length(snapshot)+1:end]

                (S_red, remaining_factors) = red(S_red, second_snapshot)
                while !iszero(remaining_factors)
                    # case 2b: new snapshot and new computation
                    snapshot = result[1:end]

                    write_unlock!(result_lock)
                    (S_red, new_factors) = red(S_red, snapshot)
                    factors = new_factors + [factors remaining_factors]
                    write_lock!(result_lock)

                    second_snapshot = result[length(snapshot)+1:end]
                    (S_red, remaining_factors) = red(S_red, second_snapshot)
                end
                # case 2a
                factors = [factors remaining_factors]

                if !iszero(S_red)
                    new_j = length(result)+1
                    new_lr = _leading_row(S_red)
                    new_lt = _leading_term(S_red)
                    for new_i in eachindex(result)
                        new_a = result[new_i]
                        if _leading_row(new_a) == new_lr
                            new_lt_a = _leading_term(new_a)
                            degree = lcm_degree(new_lt_a, new_lt)

                            if degree < deg(new_lt_a) + deg(new_lt)
                                if degree <= max_degree
                                    enqueue!(pairs_to_consider, (new_i,new_j), degree)
                                end
                            end
                        end
                    end

                    push!(result, S_red)

                    if with_transformation
                        factors[1, i] -= m_a
                        factors[1, j] += m_b
                        nonzero_factors = find(factors)
                        tr = [ -sum(factors[x] * transformation[x][y] for x in nonzero_factors) for y in eachindex(polynomials) ]
                        push!(transformation, tr)
                    end
                end
                write_unlock!(result_lock)
            end
        end
    end

    #sorted = sortperm(result, by=p->leading_term(p), rev=true)
    #result = result[sorted]
    #transformation = transformation[sorted]

    if with_transformation
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
        (i,j) for i in eachindex(polynomials) for j in eachindex(polynomials) if i < j
    ]

    result = Vector{RowVector{modulebasering(M),SparseVector{modulebasering(M),Int}}}()

    for (i,j) in pairs_to_consider
        a = polynomials[i]
        b = polynomials[j]
        lt_a = leading_term(a)
        lt_b = leading_term(b)

        m_a, m_b = lcm_multipliers(lt_a, lt_b)
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
        push!(result, syzygy)
    end

    flat_result = [ result[x][1,y] for x=eachindex(result), y=eachindex(polynomials) ]

    return flat_result
end

# note the double use of transpose; that's a workaround for some type-inference bug that I don't
# quite understand. Without the workaround, map(NP, factors) results in a SparseVector{Any} which
# is a recipe for disaster because there is no zero(Any).
red(f::NP, G::AbstractVector{NP}) where NP<:NamedPolynomial = ((f_red,factors) = red(f.p, map(g->g.p,G)); (NP(f_red), map(NP,factors')'))

_unpack(p) = broadcast(g->g.p, p)
_pack(::Type{NP}, a) where NP <: NamedPolynomial = broadcast(NP, a)

function groebner_basis(G::AbstractVector{M}, ::Type{Val{true}}; kwds...) where M<:AbstractNamedModuleElement{NP} where NP<:NamedPolynomial
    res, tr = groebner_basis(map(_unpack,G), Val{true}; kwds...)
    map(g->_pack(NP,g), res), map(g->_pack(NP,g), tr)
end

function groebner_basis(G::AbstractVector{M}, ::Type{Val{false}}; kwds...) where M<:AbstractNamedModuleElement{NP} where NP<:NamedPolynomial
    res = groebner_basis(map(_unpack,G), Val{false}; kwds...)
    map(g->_pack(NP,g), res)
end

groebner_basis(G; kwds...) = groebner_basis(G, Val{true}, kwds...)

function syzygies(G::AbstractVector{M}) where M<:AbstractNamedModuleElement{NP} where NP<:NamedPolynomial
    res = syzygies(map(_unpack,G))
    map(g->_pack(NP,g), res)
end

end
