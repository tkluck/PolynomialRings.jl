module Arrays

import PolynomialRings: to_dense_monomials, max_variable_index, to_dense_monomials
import PolynomialRings.Polynomials: Polynomial
import PolynomialRings.NamedPolynomials: NamedPolynomial

_P = Union{Polynomial, NamedPolynomial}


# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: *, det


function to_dense_monomials(a::AbstractArray{NP}) where NP <: NamedPolynomial
    n = maximum(max_variable_index(a_i) for a_i in a)
    [ to_dense_monomials(n, a_i) for a_i in a]
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

*(A::_P, B::AbstractArray) = broadcast(*, A, B)
*(A::AbstractArray, B::_P) = broadcast(*, A, B)

end
