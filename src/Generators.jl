module Generators

import Base: show, zero, one

import ..Expansions: expansion, expansionorder
import ..MonomialOrderings: MonomialOrder
import ..NamingSchemes: Variable, variable, namingscheme, name
import ..Polynomials: Polynomial, isstrictlysparse, issparse, nztermscount, coefficients, _monomialbyindex, _leading_term_ix
import PolynomialRings: polynomialtype, monomialtype, monomialorder, basering

struct Generator{Var <: Variable, P, M, C} <: Polynomial{M, C}
    var :: Var
    p   :: P
end

polynomialtype(::Type{Generator{Var, P, M, C}}) where {Var, P, M, C} = P
polynomialtype(g::Generator) = polynomialtype(typeof(g))
variable(::Type{Generator{Var, P, M, C}}) where {Var, P, M, C} = Var.instance
variable(g::Generator) = variable(typeof(g))

Generator(var::Variable, p) = Generator{typeof(var), typeof(p), monomialtype(p), basering(p)}(var, p)
Generator(var::Symbol, p) = Generator(variable(var), p)

monomialorder(g::Generator) = monomialorder(g.p)
namingscheme(g::Generator) = namingscheme(g.p)

expansionorder(gs::Generator...) = monomialorder(map(name, map(variable, gs))...)

isstrictlysparse(::Type{<:Generator{Var, P}}) where {Var, P} = isstrictlysparse(P)
issparse(::Type{<:Generator{Var, P}}) where {Var, P} = issparse(P)

coefficients(g::Generator) = coefficients(g.p)
expansion(g::Generator, order::MonomialOrder=monomialorder(g.p); kwds...) = expansion(g.p, order; kwds...)
_monomialbyindex(g::Generator, ix) = _monomialbyindex(g.p, ix)
_leading_term_ix(g::Generator, order) = _leading_term_ix(g.p, order)
nztermscount(g::Generator) = nztermscount(g.p)

zero(G::Type{<:Generator}) = zero(polynomialtype(G))
one(G::Type{<:Generator}) = one(polynomialtype(G))

function show(io::IO, G::Type{<:Generator})
    if isconcretetype(G)
        print(io, "Generator{", variable(G), ", ", polynomialtype(G), "}")
    else
        invoke(show, Tuple{IO, Type}, io, G)
    end
end

end # module
