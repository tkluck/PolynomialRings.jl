module Constructors

import PolynomialRings: generators, base_extend
import PolynomialRings.Polynomials: Polynomial
import PolynomialRings.NamedPolynomials: NamedPolynomial, names, polynomialtype
import PolynomialRings.Terms: Term, basering
import PolynomialRings.Monomials: TupleMonomial, VectorMonomial
import PolynomialRings.Util: lazymap

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: convert

# -----------------------------------------------------------------------------
#
# Constructing polynomial rings
#
# -----------------------------------------------------------------------------
"""
    polynomial_ring(symbols::Symbol...; basering=Rational{BigInt}, exptype=Int16, monomialorder=:degrevlex)

Create a type for the polynomial ring over `basering` in variables with names
specified by `symbols`, and return the type and a tuple of these variables.

The `exptype` parameter defines the integer type for the exponents.

The `monomialorder` defines an order for the monomials for e.g. Groebner basis computations;
it also defines the internal sort order. Built-in values are `:degrevlex`
and `:deglex`. This function will accept any symbol, though, and you can
define your own monomial order by implementing

    Base.Order.lt(::MonomialOrder{:myorder}, a::M, b::M) where M <: AbstractMonomial

See `PolynomialRings.MonomialOrderings` for examples.

# Examples
```jldoctest
julia> R,(x,y,z) = polynomial_ring(:x, :y, :z)
julia> x*y + z
1 z + 1 x y
```
"""
function polynomial_ring(symbols::Symbol...; basering::Type=Rational{BigInt}, exptype::Type=Int16, monomialorder::Symbol=:degrevlex)
    length(symbols)>0 || throw(ArgumentError("Need at least one variable name"))

    P = Polynomial{Vector{Term{TupleMonomial{length(symbols),exptype}, basering}}, monomialorder}
    gens = generators(P)
    NP = NamedPolynomial{P, symbols}

    return NP, map(g->NP(g), gens)
end

function convert(::Type{NP}, x::Symbol) where NP<:NamedPolynomial
    T = names(NP)
    for (i,s) in enumerate(T)
        if s == x
            return NP(generators(polynomialtype(NP))[i])
        end
    end
    throw(ArgumentError("Variable $x does not appear in $NP"))
end

"""
    formal_coefficients(R, name::Symbol)

Return a `Channel` with formal coefficients for the polynomial ring `R`.

Formal coefficients means that these are generators for a polynomial ring
`C` with an unbounded number of variables, and this polynomial ring is used
(through base extension) as the coefficients for `R`.

In other words, the channel yields `c_i⊗ 1` for `1 ∈ R` and generators `c_i ∈ C`.

# Examples
```jldoctest
julia> R = @ring ℤ[x];
julia> coeffs = formal_coefficients(R, :c);
julia> c() = take!(coeffs);
julia> [c()*x^2 + c()*x + c() , c()*x^2 + c()*x + c()]
2-element Array{(Polynomial over (Polynomial over Int64 in c0) in x),1}:
 1 c3 + 1 c2 x + 1 c1 x^2
 1 c6 + 1 c5 x + 1 c4 x^2
```
"""
function formal_coefficients(::Type{NP}, name::Symbol) where NP <: NamedPolynomial
    _C = Polynomial{Vector{Term{VectorMonomial{SparseVector{Int16,Int}}, Int}}, :degrevlex}
    CC = NamedPolynomial{_C, name}

    PP = base_extend(NP, CC)
    C = basering(PP)
    P = polynomialtype(C)

    return lazymap(g->PP(C(g)), generators(P))
end

_baserings = Dict(
    :ℚ => Rational{BigInt},
    :ℤ => BigInt,
    :ℝ => Float64,
    :ℂ => Complex{Float64},
)

"""
    @ring ℚ[x,y]

Define and return the specified polynomial ring, and bind the variable names to its generators.

Currently, the supported rings are: ℚ (`Rational{BigInt}`), ℤ (`BigInt`), ℝ (`Float64`) and
ℂ (`Complex{Float64}`).

If you need different coefficient rings, or need to specify a non-default monomial order or
exponent integer type, use `polynomial_ring` instead.

# Examples
```jldoctest
julia> using PolynomialRings
julia> @ring ℚ[x,y];
julia> x^3 + y
1 y + 1 x^3
```

# See also
`polynomial_ring`

"""
macro ring(definition)
    if(definition.head != :ref)
        throw(ArgumentError("@ring can only be used with a polynomial ring expression"))
    end

    basering = _baserings[definition.args[1]]
    variables = definition.args[2:end]

    variables_lvalue = :(())
    append!(variables_lvalue.args, variables)

    if all(v isa Symbol for v in variables)
        return quote
            R,vars = polynomial_ring($variables..., basering=$basering)
            ($(esc(variables_lvalue))) = vars
            R
        end
    elseif length(variables) == 1 && variables.head == :...
        @assert(false) # not implemented yet
    end
end

function _visit_symbols(f::Function, ex)
    if ex isa Symbol
        return f(ex)
    elseif ex isa Expr && ex.head == :call
        for i in 2:length(ex.args)
            ex.args[i] = _visit_symbols(f, ex.args[i])
        end
        return ex
    else
        return ex
    end
end

"""
    @polynomial x^3 + 3x^2 + 3x + 1

Create a multi-variate polynomial from an expression by creating the ring
generated by all symbols appearing in the expression.

# Examples
```jldoctest
julia> using PolynomialRings
julia> @polynomial x^3 + x^2*y + x*y^2 + y^3
1 y^3 + 1 x y^2 + 1 x^2 y + 1 x^3
julia> @polynomial x^3 + x^2*y + x*y^2 + y^3
1 y^3 + 1 x y^2 + 1 x^2 y + 1 x^3
```

# See also
`@ring`, `polynomial_ring`, `convert(R, symbol)`
"""
macro polynomial(expr)
    symbols = Symbol[]
    _visit_symbols(s->(push!(symbols,s);s), expr)

    R,vars=polynomial_ring(symbols..., basering=Int)

    _visit_symbols(s->convert(R,s), expr)
    expr
end

end
