generators(x) = throw(AssertionError("Not implemented"))
⊗(x) = throw(AssertionError("Not implemented"))
to_dense_monomials(n,x) = throw(AssertionError("Not implemented"))
max_variable_index(x) = throw(AssertionError("Not implemented"))
base_extend(::Type{A}, ::Type{B}) where {A,B} = promote_type(A,B)
iszero(x) = x == 0

export generators, ⊗, to_dense_monomials, max_variable_index, base_extend, iszero


deg(x) = throw(AssertionError("Not implemented"))
terms(x) = throw(AssertionError("Not implemented"))
basering(x) = throw(AssertionError("Not implemented"))
monomialtype(x) = throw(AssertionError("Not implemented"))

