module Arrays

import PolynomialRings.Monomials: AbstractMonomial, expstype
import PolynomialRings.Terms: Term
import PolynomialRings.Polynomials: Polynomial
import IterTools: groupby
import PolynomialRings.Expansions: _expansion_expr, _expansion_types
import PolynomialRings: base_restrict
if VERSION >= v"0.7-"
    import SparseArrays: issparse, spzeros
    import LinearAlgebra: Transpose
else
    Transpose = RowVector
end

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: *, transpose, diff
import PolynomialRings: monomialorder
import PolynomialRings: to_dense_monomials, max_variable_index, monomialorder
import PolynomialRings.Operators: common_denominator, integral_fraction
import PolynomialRings.Expansions: expansion, coefficients, coefficient, deg
import PolynomialRings.Expansions: constant_coefficient, linear_coefficients, expansion_terms
if VERSION < v"0.7-"
    import Base: det
else
    import LinearAlgebra: det
end

max_variable_index(a::AbstractArray{<:Polynomial}) = isempty(a) ? 0 : maximum(max_variable_index(a_i) for a_i in a)

function to_dense_monomials(a::AbstractArray{P}) where P <: Polynomial
    n = max_variable_index(a)
    to_dense_monomials.(n, a)
end

monomialorder(::Type{<:AbstractArray{P}}) where P <: Polynomial = monomialorder(P)

# -----------------------------------------------------------------------------
#
# Helpers for wrapping 'expansion' like things
#
# -----------------------------------------------------------------------------
_softnext(iter, state) = done(iter, state) ? (nothing, state) : next(iter, state)

_joint_iteration(iters, groupby, value) = Channel() do ch
    states = start.(iters)
    while !all(done.(iters, states))
        items_and_states = _softnext.(iters, states)
        items            = getindex.(items_and_states, 1)
        next_states      = getindex.(items_and_states, 2)

        cur_key = minimum(groupby, filter(i->i!==nothing, items))
        cur_indices = map(i->i!==nothing && groupby(i)==cur_key, items)
        cur_values = value.(items[cur_indices])

        push!(ch, (cur_key, cur_indices, cur_values))

        states[cur_indices] = next_states[cur_indices]
    end
end

function expansion(a::AbstractArray{P}, args...) where P <: Polynomial
    MonomialType, CoeffType =_expansion_types(P, args...)
    zero_element = issparse(a) ? spzeros(CoeffType, size(a)...) : zeros(CoeffType, size(a))
    return Channel(ctype=Tuple{expstype(MonomialType),typeof(zero_element)}) do ch
        nonzero_indices = LinearIndices(a)[findall(!iszero,a)]
        # needs collect even though I was hoping to do this lazily. A channel
        # can't deal with holding onto the state for a few iterations
        for (monomial, indices, coefficients) in _joint_iteration(map(a_i->collect(expansion(a_i, args...)), collect(a[nonzero_indices])), i->i[1], i->i[2])
            el = copy(zero_element)
            el[nonzero_indices[indices]] = coefficients
            push!(ch, (monomial,el))
        end
    end
end

function coefficients(a::AbstractArray{P}, args...) where P <: Polynomial
    return [c for (p,c) in expansion(a, args...)]
end

function (p::Array{P})(; kwargs...) where P <: Polynomial
    return map(p_i -> p_i(;kwargs...), p)
end

function coefficient(a::AbstractArray{P}, args...) where P <: Polynomial
    return map(a_i->coefficient(a_i, args...), a)
end

function constant_coefficient(a::AbstractArray{P}, args...) where P <: Polynomial
    return map(a_i->constant_coefficient(a_i, args...), a)
end

function linear_coefficients(a::AbstractArray{P}, args...) where P <: Polynomial
    MonomialType, CoeffType =_expansion_types(P, args...)
    zero_element = issparse(a) ? spzeros(CoeffType, size(a)...) : zeros(CoeffType, size(a))

    nonzero_indices = LinearIndices(a)[findall(!iszero,a)]
    items = _joint_iteration(map(a_i->linear_coefficients(a_i, args...), collect(a[nonzero_indices])), i->1, identity)
    return map(items) do item
        (_,indices,coefficients) = item
        el = copy(zero_element)
        el[nonzero_indices[indices]] = coefficients
        el
    end
end

function expansion_terms(a::AbstractArray{P}, symbols...) where P <: Polynomial
    MonomialType, CoeffType =_expansion_types(P, symbols...)
    vars = map(P, symbols)
    return [
        prod(v^k for (v,k) in zip(vars,w))*P.(c)
        for (w,c) in expansion(a, symbols...)
    ]
end

function deg(a::AbstractArray{P}, args...) where P <: Polynomial
    iszero(a) && return -1
    return maximum(a_i->deg(a_i, args...), a[findall(!iszero,a)])
end

"""
    flat_coefficients(a, symbol, [symbol...])

Return the *polynomial* coefficients of the *matrix* coefficients of `a`, when
those matrix coefficients are regarded as polynomials in the given variables.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> collect(flat_coefficients([x^3 + y^2; y^5], :y))
3-element Array{ℤ[x],1}:
 x^3
 1
 1

julia> collect(flat_coefficients([x^3 + y^2, y^5], :x, :y))
3-element Array{BigInt,1}:
 1
 1
 1
```
# See also
`@coefficients`, `@expansion`, `expansion`, `@coefficient` and `coefficient`
"""
function flat_coefficients(a::AbstractArray{P}, args...) where P <: Polynomial
    return vcat([coefficients(a_i, args...) for a_i in a]...)
end

"""
    @flat_coefficients(a, var, [var...])

Return the *polynomial* coefficients of the *matrix* coefficients of `a`, when
those matrix coefficients are regarded as polynomials in the given variables.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> collect(flat_coefficients([x^3 + y^2; y^5], :y))
3-element Array{ℤ[x],1}:
 x^3
 1
 1

julia> collect(flat_coefficients([x^3 + y^2, y^5], :x, :y))
3-element Array{BigInt,1}:
 1
 1
 1
```
# See also
`flat_coefficients`, `@expansion`, `expansion`, `@coefficient` and `coefficient`
"""
macro flat_coefficients(a, symbols...)
    expansion_expr = _expansion_expr(symbols)
    quote
        flat_coefficients($(esc(a)), $expansion_expr)
    end
end

common_denominator(a::AbstractArray{P}) where P <: Polynomial = mapreduce(common_denominator, lcm, a)

function integral_fraction(a::AbstractArray{P}) where P <: Polynomial
    D = common_denominator(a)

    return base_restrict.(D*a), D
end

function det(m::M) where M <: AbstractMatrix{P} where P <: Polynomial
    n,k = size(m)
    n == k || throw(ArgumentError("Cannot compute determinant of an $n x $k matrix"))

    if n == 1
        return m[1,1]
    end

    return (
        sum(
            m[i,1] * det([ m[1:(i-1),2:n] ; m[(i+1):n,2:n] ])
            for i=1:2:n
        )
        -
        sum(
            m[i,1] * det([ m[1:(i-1),2:n] ; m[(i+1):n,2:n] ])
            for i=2:2:n
        )
    )
end

_PT = Union{Polynomial,Term,AbstractMonomial}
*(A::_PT, B::AbstractArray) = broadcast(*, Ref(A), B)
*(A::AbstractArray, B::_PT) = broadcast(*, A, Ref(B))
*(A::_PT, B::Transpose) = Transpose(broadcast(*, Ref(A), transpose(B)))
*(A::Transpose, B::_PT) = Transpose(broadcast(*, transpose(A), Ref(B)))

transpose(a::_PT) = a

diff(a::A, s::Symbol) where A <: AbstractArray{P} where P <: Polynomial = broadcast(a_i->diff(a_i, s), a)

end
