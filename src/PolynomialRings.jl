module PolynomialRings

include("PolynomialRings/Methods.jl")
include("PolynomialRings/Util.jl")
include("PolynomialRings/Backends.jl")

include("PolynomialRings/VariableNames.jl")
include("PolynomialRings/Monomials.jl")
include("PolynomialRings/MonomialOrderings.jl")
include("PolynomialRings/Terms.jl")
include("PolynomialRings/Polynomials.jl")
include("PolynomialRings/Constants.jl")
include("PolynomialRings/Operators.jl")
include("PolynomialRings/NamedPolynomials.jl")
include("PolynomialRings/Constructors.jl")
include("PolynomialRings/Expansions.jl")
include("PolynomialRings/Arrays.jl")
include("PolynomialRings/Display.jl")
include("PolynomialRings/Modules.jl")
include("PolynomialRings/Groebner.jl")
include("PolynomialRings/Conversions.jl")

import .Monomials: TupleMonomial, VectorMonomial
import .Terms: Term
import .Polynomials: Polynomial, generators
import .Constructors: polynomial_ring, formal_coefficients, @ring, @ring!, @polynomial
import .Expansions: expansion, @expansion, @expand, coefficient, @coefficient, constant_coefficient, @constant_coefficient, coefficients, @coefficients, linear_coefficients, @linear_coefficients
import .Groebner: groebner_basis, groebner_transformation, syzygies
import .Arrays: flat_coefficients, @flat_coefficients

export TupleMonomial, Term, Polynomial, generators, ⊗, polynomial_ring, formal_coefficients, variablesymbols
export deg, expansion, @expansion, @expand, coefficient, @coefficient, constant_coefficient, @constant_coefficient, coefficients, @coefficients, linear_coefficients, @linear_coefficients, @ring, @ring!, @polynomial
export flat_coefficients, @flat_coefficients
export groebner_basis, groebner_transformation, syzygies

# TODO: needs a better place
construct_monomial(::Type{P}, e::T) where P<:Polynomial where T<:Tuple = P([termtype(P)(monomialtype(P)(e, sum(e)),one(basering(P)))])
construct_monomial(::Type{P}, e::T) where P<:Polynomial where T<:AbstractArray = P([termtype(P)(monomialtype(P)(ntuple(i->e[i], length(e)), sum(e)),one(basering(P)))])
export construct_monomial

import .Monomials: AbstractMonomial
const _P = Union{Polynomial,Term,AbstractMonomial}
generators(x::_P)    = generators(typeof(x))
basering(x::_P)      = basering(typeof(x))
monomialtype(x::_P)  = monomialtype(typeof(x))
monomialorder(x::_P) = monomialorder(typeof(x))
termtype(x::_P)      = termtype(typeof(x))
exptype(x::_P)       = exptype(typeof(x))
namestype(x::_P)     = namestype(typeof(x))

end # module
