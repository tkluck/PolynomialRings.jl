module Constructors

import PolynomialRings: generators, base_extend, variablesymbols, allvariablesymbols, ⊗
import PolynomialRings.Polynomials: Polynomial
import PolynomialRings.Terms: Term, basering
import PolynomialRings.Monomials: TupleMonomial, VectorMonomial
import PolynomialRings.VariableNames: Named, Numbered
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
    if any(s in allvariablesymbols(basering) for s in symbols) || !allunique(symbols)
        throw(ArgumentError("Duplicated symbols when extending $basering by $(Named{symbols})"))
    end

    P = Polynomial{Vector{Term{TupleMonomial{length(symbols),exptype, Named{symbols}}, basering}}, monomialorder}
    return P, generators(P)
end

function convert(::Type{P}, x::Symbol) where P<:Polynomial
    for (g,s) in zip(generators(P), variablesymbols(P))
        if s == x
            return g
        end
    end
    try
        return P(convert(basering(P), x))
    catch
        throw(ArgumentError("Variable $x does not appear in $P"))
    end
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
julia> R = @ring! ℤ[x];
julia> coeffs = formal_coefficients(R, :c);
julia> c() = take!(coeffs);
julia> [c()*x^2 + c()*x + c() , c()*x^2 + c()*x + c()]
2-element Array{(Polynomial over (Polynomial over Int64 in c0) in x),1}:
 1 c3 + 1 c2 x + 1 c1 x^2
 1 c6 + 1 c5 x + 1 c4 x^2
```
"""
function formal_coefficients(::Type{P}, name::Symbol) where P <: Polynomial
    CP = Polynomial{Vector{Term{VectorMonomial{SparseVector{Int16,Int}, Numbered{name}}, Int}}, :degrevlex}
    return lazymap(g->g⊗one(P), generators(CP))
end

function _variables_in_ring_definition(definition)
    if(definition.head != :ref)
        throw(ArgumentError("@ring can only be used with a polynomial ring expression"))
    end

    basering_spec = definition.args[1]
    variables = definition.args[2:end]

    if basering_spec isa Expr
        return union(variables, _variables_in_ring_definition(basering_spec))
    else
        return variables
    end
end

_baserings = Dict(
    :ℚ => Rational{BigInt},
    :ℤ => BigInt,
    :ℝ => BigFloat,
    :ℂ => Complex{BigFloat},
)

"""
    @ring! ℚ[x,y]

Define and return the specified polynomial ring, and bind the variable names to its generators.

Currently, the supported rings are: ℚ (`Rational{BigInt}`), ℤ (`BigInt`), ℝ (`BigFloat`) and
ℂ (`Complex{BigFloat}`).

Note: `@ring!` returns the ring and injects the variables. The macro `@ring` only returns
the ring.

If you need different coefficient rings, or need to specify a non-default monomial order or
exponent integer type, use `polynomial_ring` instead.

# Examples
```jldoctest
julia> using PolynomialRings
julia> @ring! ℚ[x,y];
julia> x^3 + y
1 y + 1 x^3
```

# See also
`polynomial_ring` `@ring`

"""
macro ring!(definition)
    variables = _variables_in_ring_definition(definition)
    variables_lvalue = :(())
    append!(variables_lvalue.args, variables)
    return quote
        R = $(esc( macroexpand(:(@ring $definition)) ))
        ($(esc(variables_lvalue))) = map(R, $variables)
        R
    end
end

"""
    @ring ℚ[x,y]

Define and return the specified polynomial ring.

Currently, the supported rings are: ℚ (`Rational{BigInt}`), ℤ (`BigInt`), ℝ (`BigFloat`) and
ℂ (`Complex{BigFloat}`).

Note: `@ring!` returns the ring and injects the variables into the surrounding
scope. The macro `@ring` only returns the ring.

If you need different coefficient rings, or need to specify a non-default monomial order or
exponent integer type, use `polynomial_ring` instead.

# Examples
```jldoctest
julia> using PolynomialRings
julia> @ring ℚ[x,y]
ℚ[x,y]
```

# See also
`polynomial_ring` `@ring!`

"""
macro ring(definition)
    if(definition.head != :ref)
        throw(ArgumentError("@ring can only be used with a polynomial ring expression"))
    end

    basering_spec = definition.args[1]
    variables = definition.args[2:end]

    if basering_spec isa Expr
        basering = esc( macroexpand(:(@ring $basering_spec)) )
    else
        basering = get(_baserings, basering_spec, esc(basering_spec))
    end

    if all(v isa Symbol for v in variables)
        return quote
            R,_ = polynomial_ring($variables..., basering=$basering)
            R
        end
    elseif length(variables) == 1 && variables.head == :...
        @assert(false) # not implemented yet
    end
end

# helper function for below
function _visit_symbols(f::Function, ex)
    if ex isa Symbol
        return f(ex)
    elseif ex isa Expr && ex.head == :call
        if ex.args[1] == :^
            ex.args[2] = _visit_symbols(f, ex.args[2])
        else
            for i in 2:length(ex.args)
                ex.args[i] = _visit_symbols(f, ex.args[i])
            end
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

!!! note
    In general, you cannot use variables from outside the macro expression;
    all symbols are interpreted as variables. For example:

        d = 4
        @polynomial d*x

    will give a polynomial in two variables, `d` and `x`.

    As a special exception, exponents are not interpreted, so

        @polynomial(x^d) == @polynomial(x)^d

    Unfortunately/confusingly, together, this gives

        @polynomial(d*x^(d-1))

    will have `d-1` interpreting `d` as an outer variable, and `d*x` is
    a monomial.

    This behaviour may (should?) change.

# See also
`@ring`, `polynomial_ring`, `convert(R, symbol)`
"""
macro polynomial(expr)
    symbols = Symbol[]
    expr = _visit_symbols(s->(push!(symbols,s);s), expr)

    R,vars=polynomial_ring(symbols..., basering=Int)

    expr = _visit_symbols(s->convert(R,s), expr)
    esc(expr)
end

"""
    @polyvar var [var...]

Define a polynomial ring in the given variables, and inject them into the surrounding scope.

This is equivalent to `@ring! Int[var...]`.

If you need different coefficient rings, or need to specify a non-default monomial order or
exponent integer type, use `@ring!` or `polynomial_ring` instead.

# Examples
```jldoctest
julia> using PolynomialRings
julia> @polyvar x y;
julia> x + 3y
3 y + x
```

# See also
`polynomial_ring` `@ring!`

"""
macro polyvar(expr...)
    if(!all(ex isa Symbol for ex in expr))
        throw(ArgumentError("The @polyvar macro can only be used with symbols. Example: @polyvar x y"))
    end
    definition = :( Int[] )
    append!(definition.args, expr)
    quote
        @ring! $(esc(definition))
    end
end

end
