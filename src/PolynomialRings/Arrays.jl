module Arrays

import PolynomialRings: to_dense_monomials, max_variable_index, to_dense_monomials
import PolynomialRings.NamedPolynomials: NamedPolynomial

function to_dense_monomials(a::AbstractArray{NP}) where NP <: NamedPolynomial
    n = maximum(max_variable_index(a_i) for a_i in a)
    [ to_dense_monomials(n, a_i) for a_i in a]
end

end
