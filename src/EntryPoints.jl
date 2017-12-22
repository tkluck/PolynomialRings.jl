module EntryPoints

import PolynomialRings: generators, base_extend, variablesymbols, allvariablesymbols, ⊗
import PolynomialRings: construct_monomial, exptype
import PolynomialRings.Polynomials: Polynomial, polynomial_ring, numbered_polynomial_ring
import PolynomialRings.NamedPolynomials: NamedPolynomial, NumberedPolynomial
import PolynomialRings.VariableNames: Numbered, numberedvariablename
import PolynomialRings.Terms: Term, basering
import PolynomialRings.Monomials: TupleMonomial, VectorMonomial
import PolynomialRings.Util: lazymap
import PolynomialRings.Ideals: Ideal
import PolynomialRings.NumberFields: NumberField

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: convert
import Base: getindex

# -----------------------------------------------------------------------------
#
# Constructing a polynomial from a symbol
#
# -----------------------------------------------------------------------------
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
        throw(ArgumentError("Can't find variables in $definition"))
    end

    basering_spec = definition.args[1]
    variable_spec = definition.args[2:end]

    if length(variable_spec) == 1 && variable_spec[1] isa Expr && variable_spec[1].head == :ref && length(variable_spec[1].args) == 1
        variables = [variable_spec[1].args[1]]
    elseif all(var isa Symbol for var in variable_spec)
        variables = variable_spec
    else
        throw(RuntimeError("Cannot find variables in $definition"))
    end

    if basering_spec isa Expr && basering_spec.head == :ref
        return union(variables, _variables_in_ring_definition(basering_spec))
    else
        return variables
    end
end

function _inject_var(::Type{Outer}, ::Type{Inner}, name) where Outer where Inner<:NamedPolynomial
    if name in variablesymbols(Inner)
        return Outer(convert(Inner, name))
    else
        return _inject_var(Outer, basering(Inner), name)
    end
end

function _inject_var(::Type{Outer}, ::Type{Inner}, name) where Outer where Inner<:NumberedPolynomial
    if name == numberedvariablename(Inner)
        return NumberedVariableGenerator{Outer,Inner}()
    else
        return _inject_var(Outer, basering(Inner), name)
    end
end

function _inject_vars(R, definition)
    if definition.head == :call && definition.args[1] == :/
        definition = definition.args[2]
    end
    variables = _variables_in_ring_definition(definition)
    variables_lvalue = :(())
    append!(variables_lvalue.args, variables)
    return quote
        ($(esc(variables_lvalue))) = map(sym->$_inject_var($R,$R,sym), $variables)
    end
end

function _ideal(expr)
    res = :( Ideal() )
    if expr isa Expr && expr.head == :tuple
        for ex in expr.args
            push!(res.args, macroexpand(:( @polynomial $ex )))
        end
    else
        push!(res.args, macroexpand(:( @polynomial $expr )))
    end
    res
end

_baserings = Dict(
    :ℚ => Rational{BigInt},
    :ℤ => BigInt,
    :ℝ => BigFloat,
    :ℂ => Complex{BigFloat},
)


function _polynomial_ring(definition)
    if(definition.head != :ref)
        throw(ArgumentError("@ring can only be used with a polynomial ring expression"))
    end

    basering_spec = definition.args[1]
    variables = definition.args[2:end]

    if basering_spec isa Expr
        basering = _polynomial_ring(basering_spec)
    else
        basering = get(_baserings, basering_spec, esc(basering_spec))
    end

    if all(v isa Symbol for v in variables)
        return quote
            $polynomial_ring($variables..., basering=$basering)[1]
        end
    elseif length(variables) == 1 && variables[1].head == :ref
        variable = QuoteNode( variables[1].args[1] )
        return quote
            $numbered_polynomial_ring($variable, basering=$basering)
        end
    else
        throw(ArgumentError("The specification $definition is not a valid list of variables"))
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
    if definition.head == :call && definition.args[1] == :/
        return quote
            R = $( _polynomial_ring(definition.args[2]))
            I = $( _ideal(definition.args[3]) )
            R / I
        end
    else
        return quote
            $(_polynomial_ring(definition))
        end
    end
end

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
`polynomial_ring` `@polynomialring`

"""
macro ring!(definition)
    if definition.head == :call && definition.args[1] == :/
        return quote
            R = $( _polynomial_ring(definition.args[2]))
            I = $( _ideal(definition.args[3]) )
            S = R/I
            $(_inject_vars(:S,definition))
            S
        end
    else
        return quote
            R = $(_polynomial_ring(definition))
            $(_inject_vars(:R,definition))
            R
        end
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
    symbols = Set{Symbol}()
    expr = _visit_symbols(s->(push!(symbols,s);s), expr)

    R,vars=polynomial_ring(sort(collect(symbols))..., basering=Int)

    expr = _visit_symbols(s->convert(R,s), expr)
    esc(expr)
end

macro numberfield(definition)
    quote
        R = $(esc(macroexpand(:(@ring $definition))))
        $NumberField(R)
    end

end

macro numberfield!(definition)
    quote
        R = $(esc(macroexpand(:(@ring $definition))))
        S = $NumberField(R)
        $(_inject_vars(:S,definition))
        S
    end
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

# -----------------------------------------------------------------------------
#
# An object representing numbered variables
#
# -----------------------------------------------------------------------------
mutable struct NumberedVariableGenerator{Outer,Inner}
    next::Int
    NumberedVariableGenerator{Outer,Inner}() where {Outer,Inner} = new(1)
end

function (g::NumberedVariableGenerator)()
    ix = g.next
    g.next += 1
    return g[ix]
end

function getindex(g::NumberedVariableGenerator{Outer,Inner}, i::Integer) where {Outer,Inner}
    E = exptype(Inner)
    e = spzeros(E, i)
    e[i] = one(E)
    return Outer(construct_monomial(Inner, e))
end


getindex(g::NumberedVariableGenerator) = Channel() do ch
    for i in 1:typemax(Int)
        push!(ch, g[i])
    end
end

end
