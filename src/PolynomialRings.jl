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
include("PolynomialRings/Expansions.jl")
include("PolynomialRings/Arrays.jl")
include("PolynomialRings/Display.jl")
include("PolynomialRings/Modules.jl")
include("PolynomialRings/Reductions.jl")
include("PolynomialRings/Groebner.jl")
include("PolynomialRings/GroebnerGWV.jl")
include("PolynomialRings/GroebnerSig.jl")
include("PolynomialRings/Conversions.jl")
include("PolynomialRings/Solve.jl")

import .Monomials: TupleMonomial, VectorMonomial
import .Terms: Term
import .Polynomials: Polynomial, generators, polynomial_ring
import .Expansions: expansion, @expansion, @expand, coefficient, @coefficient, constant_coefficient, @constant_coefficient, coefficients, @coefficients, linear_coefficients, @linear_coefficients, deg, @deg, expansion_terms, @expansion_terms
import .Arrays: flat_coefficients, @flat_coefficients
import .Operators: content, common_denominator, integral_fraction, map_coefficients
import .Solve: matrix_solve_affine

export TupleMonomial, Term, Polynomial, generators, ⊗, polynomial_ring, variablesymbols
export expansion, @expansion, @expand, coefficient, @coefficient, constant_coefficient, @constant_coefficient, expansion_terms, @expansion_terms
export coefficients, @coefficients, linear_coefficients, @linear_coefficients
export deg, @deg
export flat_coefficients, @flat_coefficients
export groebner_basis, groebner_transformation, gröbner_basis, gröbner_transformation, lift, syzygies
export content, common_denominator, integral_fraction, map_coefficients
export matrix_solve_affine

# TODO: needs a better place
import .Monomials: _construct
if VERSION < v"0.7-"
    import Base.SparseArrays: nonzeroinds
else
    import SparseArrays: nonzeroinds
    using SparseArrays: SparseVector
end
_nzindices(t::Tuple) = 1:length(t)
_nzindices(t::AbstractVector) = eachindex(t)
_nzindices(t::SparseVector) = nonzeroinds(t)
function construct_monomial(::Type{P}, e::T) where P<:Polynomial where T<:Union{Tuple,AbstractVector}
    @assert all(e.>=0)
    P([termtype(P)(_construct(monomialtype(P), i->e[i], _nzindices(e)),one(basering(P)))])
end
export construct_monomial
# --------------------------

import .Monomials: AbstractMonomial
const _P = Union{Polynomial,Term,AbstractMonomial}
generators(x::_P)    = generators(typeof(x))
basering(x::_P)      = basering(typeof(x))
monomialtype(x::_P)  = monomialtype(typeof(x))
monomialorder(x::_P) = monomialorder(typeof(x))
termtype(x::_P)      = termtype(typeof(x))
exptype(x::_P)       = exptype(typeof(x))
namestype(x::_P)     = namestype(typeof(x))

include("CommutativeAlgebras.jl")

include("EntryPoints.jl")
import .EntryPoints: formal_coefficients, formal_coefficient, @ring, @ring!, @polynomial, @polyvar, @numberfield, @numberfield!
export formal_coefficients, formal_coefficient, @ring, @ring!, @polynomial, @polyvar, @numberfield, @numberfield!

include("PolynomialRings/Library.jl")

end # module
