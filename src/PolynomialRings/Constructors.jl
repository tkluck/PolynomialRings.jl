module Constructors

import PolynomialRings: generators
import PolynomialRings.Polynomials: Polynomial
import PolynomialRings.Terms: Term
import PolynomialRings.Monomials: TupleMonomial, VectorMonomial

free_generators(::Type{Val{N}}) where N = generators(Polynomial{Vector{Term{TupleMonomial{N,Int16}, Int}}, :degrevlex})

free_generators(::Type{Val{Inf}}) = generators(Polynomial{Vector{Term{VectorMonomial{SparseVector{Int,Int16}}, Int}}, :deglex})

free_generators() = free_generators(Val{Inf})
free_generators(i::Integer) = free_generators(Val{i})

end
