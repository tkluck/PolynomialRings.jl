module Arrays

import PolynomialRings: to_dense_monomials, max_variable_index, to_dense_monomials
import PolynomialRings.Terms: Term
import PolynomialRings.Polynomials: Polynomial
import PolynomialRings.NamedPolynomials: NamedPolynomial
import PolynomialRings.Expansions: expansion, coefficients
import Iterators: groupby

_P = Union{Polynomial, NamedPolynomial}


# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: *, det, transpose, diff


function to_dense_monomials(a::AbstractArray{NP}) where NP <: NamedPolynomial
    n = maximum(max_variable_index(a_i) for a_i in a)
    [ to_dense_monomials(n, a_i) for a_i in a]
end

function expansion(a::AbstractArray{NP}, args...) where NP <: NamedPolynomial
    array_of_expansions = [ (w,p,i) for (i, a_i) in enumerate(a) for (w,p) in expansion(a_i, args...)]
    sort!(array_of_expansions, by=x->x[1])

    res = []
    for group in groupby(x -> x[1], array_of_expansions)
        r = zeros(typeof(group[1][2]), size(a))
        for (w,p,i) in group
            r[i] = p
        end
        push!(res, (group[1][1], r))
    end

    return res
end

function coefficients(a::AbstractArray{NP}, args...) where NP <: NamedPolynomial
    return [c for (p,c) in expansion(a, args...)]
end

"""
    flat_coefficients(a, symbol, [symbol...])

Return the *polynomial* coefficients of the *matrix* coefficients of `a`, when
those matrix coefficients are regarded as polynomials in the given variables.

# Examples
```jldoctest
julia> R = @ring ℤ[x,y];
julia> collect(flat_coefficients([x^3 + y^2; y^5], :y))
[1 x^3, 1, 1]
julia> collect(flat_coefficients([x^3 + y^2, y^5], :x, :y))
[1, 1, 1]
```
# See also
`@coefficients`, `@expansion`, `expansion`, `@coefficient` and `coefficient`
"""
function flat_coefficients(a::AbstractArray{NP}, args...) where NP <: NamedPolynomial
    return vcat([coefficients(a_i, args...) for a_i in a]...)
end

"""
    @flat_coefficients(a, var, [var...])

Return the *polynomial* coefficients of the *matrix* coefficients of `a`, when
those matrix coefficients are regarded as polynomials in the given variables.

# Examples
```jldoctest
julia> R = @ring ℤ[x,y];
julia> collect(flat_coefficients([x^3 + y^2; y^5], :y))
[1 x^3, 1, 1]
julia> collect(flat_coefficients([x^3 + y^2, y^5], :x, :y))
[1, 1, 1]
```
# See also
`flat_coefficients`, `@expansion`, `expansion`, `@coefficient` and `coefficient`
"""
macro flat_coefficients(a, symbols...)
    quote
        flat_coefficients($(esc(a)), $symbols...)
    end
end

function det(m::M) where M <: AbstractMatrix{P} where P <: _P
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

_PT = Union{Polynomial,Term,NamedPolynomial}
*(A::_PT, B::AbstractArray) = broadcast(*, A, B)
*(A::AbstractArray, B::_PT) = broadcast(*, A, B)
*(A::_PT, B::RowVector) = RowVector(broadcast(*, A, transpose(B)))
*(A::RowVector, B::_PT) = RowVector(broadcast(*, transpose(A), B))

transpose(a::_PT) = a

diff(a::A, s::Symbol) where A <: AbstractArray{P} where P <: _P = broadcast(a_i->diff(a_i, s), a)

end
