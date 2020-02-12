module PolynomialRings

include("PolynomialRings/Methods.jl")
include("PolynomialRings/Util.jl")
include("PolynomialRings/Backends.jl")

include("NamingSchemes.jl")
include("MonomialOrderings.jl")
include("AbstractMonomials.jl")


include("PolynomialRings/NamedValues.jl")
include("PolynomialRings/Terms.jl")
include("PolynomialRings/Polynomials.jl")
include("PolynomialRings/Constants.jl")

include("StandardMonomialOrderings.jl")
include("Monomials.jl")
include("Expansions.jl")

include("PolynomialRings/Broadcast.jl")
include("PolynomialRings/Operators.jl")
include("PolynomialRings/NamedPolynomials.jl")
include("PolynomialRings/Arrays.jl")
include("TypeUpgrades.jl")
include("PolynomialRings/Display.jl")
include("PolynomialRings/Modules.jl")
include("PolynomialRings/Reductions.jl")
include("PolynomialRings/Groebner.jl")
include("PolynomialRings/GroebnerGWV.jl")
include("PolynomialRings/GroebnerSig.jl")
include("PolynomialRings/GroebnerM4GB.jl")
include("PolynomialRings/Conversions.jl")
include("PolynomialRings/Solve.jl")

# define this here to resolve a dependency cycle
basering(::Type{M}) where M <: AbstractMonomials.AbstractMonomial = Constants.One

import .NamingSchemes: @namingscheme, @nestednamingscheme
import .StandardMonomialOrderings: @lex, @deglex, @degrevlex
import .Monomials: TupleMonomial, VectorMonomial
import .Terms: Term
import .Polynomials: Polynomial, generators, map_coefficients
import .Polynomials: tosparse, todense
import .Expansions: @expansion, @expand, coefficient, @coefficient, constant_coefficient, @constant_coefficient, expandcoefficients, @expandcoefficients, linear_coefficients, @linear_coefficients, @deg, expansion_terms, @expansion_terms
import .Arrays: flat_coefficients, @flat_coefficients
import .Operators: content, common_denominator, integral_fraction
import .Reductions: interreduce, interreduce!
import .Solve: matrix_solve_affine
import .NamedPolynomials: minring, ofminring
import .Util: @assertvalid

export @namingscheme, @nestednamingscheme
export @lex, @deglex, @degrevlex
export TupleMonomial, Term, Polynomial, generators, ⊗, polynomial_ring, variablesymbols
export tosparse, todense
export expansion, expand, @expansion, @expand, coefficient, @coefficient, constant_coefficient, @constant_coefficient, expansion_terms, @expansion_terms
export expandcoefficients, @expandcoefficients, linear_coefficients, @linear_coefficients
export deg, @deg
export flat_coefficients, @flat_coefficients
export leaddiv, leadrem, leaddivrem, div!, rem!, xdiv!, xrem!, xdiv, xrem, xdivrem
export groebner_basis, groebner_transformation, gröbner_basis, gröbner_transformation, lift, syzygies
export content, common_denominator, integral_fraction, map_coefficients
export interreduce, interreduce!
export matrix_solve_affine
export minring, ofminring

import .AbstractMonomials: AbstractMonomial
const _P = Union{Polynomial,Term,AbstractMonomial}
generators(x::_P)    = generators(typeof(x))
basering(x::_P)      = basering(typeof(x))
monomialtype(x::_P)  = monomialtype(typeof(x))
monomialorder(x::_P) = monomialorder(typeof(x))
termtype(x::_P)      = termtype(typeof(x))
exptype(x::_P)       = exptype(typeof(x))
namingscheme(x::_P)  = namingscheme(typeof(x))

include("CommutativeAlgebras.jl")

include("EntryPoints.jl")
import .EntryPoints: polynomial_ring, formal_coefficients, formal_coefficient, @ring, @ring!, @polynomial, @polyvar, @numberfield, @numberfield!
export polynomial_ring, formal_coefficients, formal_coefficient, @ring, @ring!, @polynomial, @polyvar, @numberfield, @numberfield!

include("PolynomialRings/Library.jl")

end # module
