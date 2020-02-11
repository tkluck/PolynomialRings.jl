module Arrays

import Base: *, transpose, diff, div
import LinearAlgebra: Transpose
import LinearAlgebra: det
import SparseArrays: SparseVector, SparseMatrixCSC, AbstractSparseArray
import SparseArrays: nonzeros

import ..AbstractMonomials: AbstractMonomial
import ..Expansions: order_from_expr
import ..Expansions: expandcoefficients, deg
import ..Expansions: substitutedtype
import ..NamingSchemes: remove_variables, Variable
import ..Operators: common_denominator, integral_fraction
import ..Polynomials: Polynomial, PolynomialOver, map_coefficients
import ..StandardMonomialOrderings: KeyOrder, LexCombinationOrder
import ..Terms: Term
import ..Util: nzpairs
import PolynomialRings: base_restrict
import PolynomialRings: monomialorder

remove_variables(::Type{Array{P, N}}, scheme) where {P, N} = Array{remove_variables(P, scheme), N}
remove_variables(::Type{SparseVector{P, I}}, scheme) where {P, I} = SparseVector{remove_variables(P, scheme), I}
remove_variables(::Type{SparseMatrixCSC{P, I}}, scheme) where {P, I} = SparseMatrixCSC{remove_variables(P, scheme), I}

function (p::AbstractArray{P})(; kwargs...) where P <: Polynomial
    ElType = substitutedtype(eltype(p); kwargs...)
    res = similar(p, ElType)
    for ix in eachindex(p)
        res[ix] = p[ix](;kwargs...)
    end
    res
end


function deg(a::AbstractArray{P}, args...) where P <: Polynomial
    iszero(a) && return -1
    return maximum(((i, ai),) -> deg(a_i, args...), nzpairs(a))
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
`@expandcoefficients`, `@expansion`, `expansion`, `@coefficient` and `coefficient`
"""
function flat_coefficients(a::AbstractArray{P}, spec...) where P <: Polynomial
    order = monomialorder(spec...)
    return expandcoefficients(a, LexCombinationOrder(KeyOrder(), order))
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
    expansion_expr = order_from_expr(symbols)
    quote
        flat_coefficients($(esc(a)), $expansion_expr)
    end
end

common_denominator(a::AbstractArray{P}) where P <: Polynomial = mapreduce(common_denominator, lcm, a, init=common_denominator(zero(P)))

common_denominator(a::AbstractSparseArray{P}) where P <: Polynomial = mapreduce(common_denominator, lcm, nonzeros(a), init=common_denominator(zero(P)))

function integral_fraction(a::AbstractArray{P}) where P <: Polynomial
    D = common_denominator(a)

    return base_restrict.(D .* a), D
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

diff(a::AbstractArray{<:Polynomial}, s::Union{Variable, Symbol}) = broadcast(a_i->diff(a_i, s), a)

end
