module PolynomialRings

generators(x) = throw(AssertionError("Not implemented"))

include("PolynomialRings/Util.jl")

include("PolynomialRings/Monomials.jl")
include("PolynomialRings/Terms.jl")
include("PolynomialRings/Polynomials.jl")
include("PolynomialRings/MonomialOrderings.jl")
include("PolynomialRings/Operators.jl")
include("PolynomialRings/Display.jl")
include("PolynomialRings/Constructors.jl")

import .Monomials: TupleMonomial, VectorMonomial
import .Terms: Term
import .Polynomials: Polynomial, generators
import .Constructors: free_generators

export TupleMonomial, Term, Polynomial, generators, free_generators


end # module
