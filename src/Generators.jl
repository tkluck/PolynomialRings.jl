module Generators

import Base: show, zero, one, eltype, iterate, getindex, reset

import SparseArrays: spzeros

import ..Expansions: expansion, expansionorder
import ..MonomialOrderings: MonomialOrder
import ..NamingSchemes: Variable, variable, namingscheme, name, num_variables
import ..Polynomials: Polynomial, isstrictlysparse, issparse, nztermscount, exptype
import ..Polynomials: monomials, coefficients, _monomialbyindex, _leading_term_ix
import PolynomialRings: polynomialtype, monomialtype, monomialorder, basering

# -----------------------------------------------------------------------------
#
# An object that can be used as a polynomial (the .p member) and for
# specifying an expansion (e.g. `expansion(x^2 + y^2, x)`) in a type-stable way.
#
# -----------------------------------------------------------------------------
struct Generator{Var <: Variable, P, M, C} <: Polynomial{M, C}
    var :: Var
    p   :: P
end

polynomialtype(::Type{Generator{Var, P, M, C}}) where {Var, P, M, C} = P
polynomialtype(g::Generator) = polynomialtype(typeof(g))
variable(::Type{Generator{Var, P, M, C}}) where {Var, P, M, C} = Var.instance
variable(g::Generator) = variable(typeof(g))
name(g::Generator) = name(variable(g))

Generator(var::Variable, p) = Generator{typeof(var), typeof(p), monomialtype(p), basering(p)}(var, p)
Generator(var::Symbol, p) = Generator(variable(var), p)

monomialorder(g::Generator) = monomialorder(g.p)
namingscheme(g::Generator) = namingscheme(g.p)

expansionorder(gs::Generator...) = monomialorder(map(name, map(variable, gs))...)

isstrictlysparse(::Type{<:Generator{Var, P}}) where {Var, P} = isstrictlysparse(P)
issparse(::Type{<:Generator{Var, P}}) where {Var, P} = issparse(P)

coefficients(g::Generator) = coefficients(g.p)
monomials(g::Generator) = monomials(g.p)
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

diff(a::Number, x::Variable) = zero(a)
diff(a::Number, x::Generator) = zero(a)

# -----------------------------------------------------------------------------
#
# A similar object for numbered variables
#
# -----------------------------------------------------------------------------
mutable struct NumberedVariableGenerator{P, M}
    polynomialtype :: Type{P}
    monomialtype   :: Type{M}
    next           :: Int
end

NumberedVariableGenerator(P, M=monomialtype(P), startix=1) = NumberedVariableGenerator{P, M}(P, M, startix)

polynomialtype(g::NumberedVariableGenerator) = g.polynomialtype
monomialtype(g::NumberedVariableGenerator) = g.monomialtype
eltype(g::NumberedVariableGenerator) = g.polynomialtype

function (g::NumberedVariableGenerator)()
    ix = g.next
    g.next += 1
    return g[ix]
end

function getindex(g::NumberedVariableGenerator, ix::Integer)
    E = exptype(monomialtype(g))
    scheme = namingscheme(monomialtype(g))
    N = num_variables(scheme)
    ix <= N || throw(BoundsError(scheme, ix))
    e = spzeros(E, N < Inf ? N : ix)
    e[ix] = one(E)
    return polynomialtype(g)(exp(polynomialtype(monomialtype(g)), e))
end

getindex(g::NumberedVariableGenerator, ix::Integer...) = getindex.(Ref(g), ix)
getindex(g::NumberedVariableGenerator, ix) = getindex.(Ref(g), ix)
# backwards compatibility: g[] is an iterable, but nowadays g is iterable too
getindex(g::NumberedVariableGenerator) = NumberedVariableGenerator(g.polynomialtype, g.monomialtype)

iterate(g::NumberedVariableGenerator, state=1) = (g[state], state + 1)

reset(g::NumberedVariableGenerator) = (g.next = 1; g)

expansionorder(g::NumberedVariableGenerator) = monomialorder(monomialtype(g))

end # module
