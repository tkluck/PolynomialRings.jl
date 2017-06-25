module PolynomialRings

generators(x) = throw(AssertionError("Not implemented"))
⊗(x) = throw(AssertionError("Not implemented"))
base_extend(::Type{A}, ::Type{B}) where {A,B} = promote_type(A,B)
iszero(x) = x == 0


include("PolynomialRings/Util.jl")

include("PolynomialRings/Monomials.jl")
include("PolynomialRings/Terms.jl")
include("PolynomialRings/Polynomials.jl")
include("PolynomialRings/MonomialOrderings.jl")
include("PolynomialRings/Operators.jl")
include("PolynomialRings/Constructors.jl")
include("PolynomialRings/NamedPolynomials.jl")
include("PolynomialRings/Conversions.jl")
include("PolynomialRings/Display.jl")

import .Monomials: TupleMonomial, VectorMonomial
import .Terms: Term
import .Polynomials: Polynomial, generators
import .Constructors: free_generators
import .NamedPolynomials: polynomial_ring, formal_coefficients

export TupleMonomial, Term, Polynomial, generators, free_generators, ⊗, polynomial_ring, formal_coefficients


end # module
