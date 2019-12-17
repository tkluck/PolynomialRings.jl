module Arrays

import Base: *, transpose, diff, div
import LinearAlgebra: Transpose
import LinearAlgebra: det
import SparseArrays: issparse, spzeros, SparseVector, SparseMatrixCSC, AbstractSparseArray
import SparseArrays: nonzeros

import IterTools: groupby

import ..Expansions: _expansion_expr, expansiontypes
import ..Expansions: constant_coefficient, linear_coefficients, expansion_terms
import ..Expansions: expansion, coefficients, coefficient, deg
import ..Expansions: substitutedtype
import ..Monomials: AbstractMonomial, expstype
import ..Operators: common_denominator, integral_fraction, map_coefficients
import ..Polynomials: Polynomial, PolynomialOver
import ..Terms: Term
import PolynomialRings: base_restrict
import PolynomialRings: monomialorder
import PolynomialRings: to_dense_monomials, max_variable_index, monomialorder

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
function _joint_iteration(f, iters, groupby, value)
    it = iterate.(iters)
    active = it .!= nothing
    while any(active)
        activeix = findall(active)
        activeit = it[activeix]
        items = getindex.(activeit, 1)

        cur_key = minimum(groupby, items)
        cur_ix = findall(isequal(cur_key)∘groupby, items)
        cur_indices = activeix[cur_ix]
        cur_values = value.(items[cur_ix])

        f(cur_key, cur_indices, cur_values)

        for ix in cur_indices
            x = iterate(iters[ix], it[ix][2])
            # for some reason, type inference doesn't see that `it` may contain `nothing`,
            # so we cannot assign it. This works around that.
            if x === nothing
                active[ix] = false
            else
                it[ix] = x
            end
        end
        activeix = findall(active)
    end
end

function expansion(a::AbstractArray{P}, args...) where P <: Polynomial
    MonomialType, CoeffType = expansiontypes(P, args...)
    zero_element = issparse(a) ? spzeros(CoeffType, size(a)...) : zeros(CoeffType, size(a))
    res = Tuple{MonomialType, typeof(zero_element)}[]
    nonzero_indices = LinearIndices(a)[findall(!iszero,a)]
    _joint_iteration(map(a_i->collect(expansion(a_i, args...)), collect(a[nonzero_indices])), i->i[1], i->i[2]) do monomial, indices, coefficients
        el = copy(zero_element)
        el[nonzero_indices[indices]] = coefficients
        push!(res, (monomial,el))
    end
    return res
end

function coefficients(a::AbstractArray{P}, args...) where P <: Polynomial
    return [c for (p,c) in expansion(a, args...)]
end

if VERSION > v"1.3-"
    function (p::AbstractArray{P})(; kwargs...) where P <: Polynomial
        ElType = substitutedtype(eltype(p); kwargs...)
        res = similar(p, ElType)
        for ix in eachindex(p)
            res[ix] = p[ix](;kwargs...)
        end
        res
    end
else
    function (p::Vector{P})(; kwargs...) where P <: Polynomial
        ElType = substitutedtype(eltype(p); kwargs...)
        res = similar(p, ElType)
        for ix in eachindex(p)
            res[ix] = p[ix](;kwargs...)
        end
        res
    end
    function (p::Matrix{P})(; kwargs...) where P <: Polynomial
        ElType = substitutedtype(eltype(p); kwargs...)
        res = similar(p, ElType)
        for ix in eachindex(p)
            res[ix] = p[ix](;kwargs...)
        end
        res
    end
end

function coefficient(a::AbstractArray{P}, args...) where P <: Polynomial
    return map(a_i->coefficient(a_i, args...), a)
end

function constant_coefficient(a::AbstractArray{P}, args...) where P <: Polynomial
    return map(a_i->constant_coefficient(a_i, args...), a)
end

function linear_coefficients(a::AbstractArray{P}, args...) where P <: Polynomial
    MonomialType, CoeffType = expansiontypes(P, args...)
    zero_element = issparse(a) ? spzeros(CoeffType, size(a)...) : zeros(CoeffType, size(a))

    nonzero_indices = LinearIndices(a)[findall(!iszero,a)]
    res = typeof(zero_element)[]
    _joint_iteration(map(a_i->linear_coefficients(a_i, args...), collect(a[nonzero_indices])), i->1, identity) do _,indices,coefficients
        el = copy(zero_element)
        el[nonzero_indices[indices]] = coefficients
        push!(res, el)
    end
    return res
end

function expansion_terms(a::AbstractArray{P}, symbols...) where P <: Polynomial
    return [
        P.(m * c)
        for (m, c) in expansion(a, symbols...)
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

common_denominator(a::AbstractArray{P}) where P <: Polynomial = mapreduce(common_denominator, lcm, a, init=common_denominator(zero(P)))

common_denominator(a::AbstractSparseArray{P}) where P <: Polynomial = mapreduce(common_denominator, lcm, nonzeros(a), init=common_denominator(zero(P)))

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
*(A::_PT, B::AbstractArray) = broadcast(*, A, B)
*(A::AbstractArray, B::_PT) = broadcast(*, A, B)
*(A::_PT, B::Transpose) = Transpose(broadcast(*, A, transpose(B)))
*(A::Transpose, B::_PT) = Transpose(broadcast(*, transpose(A), B))
div(a::A, s::Integer) where A <: AbstractArray{P} where P<:PolynomialOver{<:Integer} = map(a_i->map_coefficients(c->div(c,s), a_i), a)
transpose(a::_PT) = a

diff(a::A, s::Symbol) where A <: AbstractArray{P} where P <: Polynomial = broadcast(a_i->diff(a_i, s), a)

end
