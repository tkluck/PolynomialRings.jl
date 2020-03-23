module EntryPoints

import Base: convert

import ..Generators: Generator, NumberedVariableGenerator
import ..Ideals: Ideal
import ..Monomials: TupleMonomial, VectorMonomial
import ..NamedPromotions: NamedPolynomial, NumberedPolynomial
import ..NamingSchemes: NamingScheme, Named, Numbered, numberedvariablename, parse_namingscheme, num_variables, namingscheme, nestednamingscheme
import ..NumberFields: NumberField
import ..Polynomials: Polynomial
import ..QuotientRings: QuotientRing
import ..StandardMonomialOrderings: MonomialOrdering
import ..Terms: Term, basering
import ..Util: lazymap, isdisjoint
import PolynomialRings: exptype, boundnames, monomialtype, polynomialtype
import PolynomialRings: generators, base_extend, variablesymbols, allvariablesymbols, ⊗

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

Return an object representing formal coefficients for the polynomial ring `R`.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x];


julia> c = formal_coefficients(R, :c);



julia> c[1:3]
3-element Array{@ring(ℤ[c[]][x]),1}:
 c[1]
 c[2]
 c[3]

julia> [c()*x^2 + c()*x + c() , c()*x^2 + c()*x + c()]
2-element Array{@ring(ℤ[c[]][x]),1}:
 c[1]*x^2 + c[2]*x + c[3]
 c[4]*x^2 + c[5]*x + c[6]
```
"""
function formal_coefficients(::Type{P}, name::Symbol) where P <: Polynomial
    R = numbered_polynomial_ring(name, basering=Int)
    PP = base_extend(P, R)
    return NumberedVariableGenerator(PP, monomialtype(R))
end

function formal_coefficient(::Type{P}) where P <: Polynomial
    name = :αβγ # poor man's version of 'guaranteeing no clash'
    R, _ = polynomial_ring(name, basering=Int)
    RR = base_extend(P, R)
    return name, RR(name)
end

function _variables_in_ring_definition(definition)
    if(definition.head != :ref)
        throw(ArgumentError("Can't find variables in $definition"))
    end

    basering_spec = definition.args[1]
    variable_spec = definition.args[2:end]

    if length(variable_spec) == 1 && variable_spec[1] isa Expr && variable_spec[1].head == :ref
        variables = [variable_spec[1].args[1]]
    elseif all(var isa Symbol for var in variable_spec)
        variables = variable_spec
    else
        error("Cannot find variables in $definition")
    end

    if basering_spec isa Expr && basering_spec.head == :ref
        return union(variables, _variables_in_ring_definition(basering_spec))
    else
        return variables
    end
end

function _inject_var(::Type{Outer}, ::Type{Inner}, name) where Outer where Inner<:Union{QuotientRing,NumberField}
    if name in allvariablesymbols(Inner)
        return Outer(convert(Inner, name))
    else
        error("Cannot find variable $name in $Inner")
    end
end

function _inject_var(::Type{Outer}, ::Type{Inner}, name) where Outer where Inner<:NamedPolynomial
    if name in variablesymbols(Inner)
        val = Outer(convert(Inner, name))
        return Generator(name, val)
    else
        return _inject_var(Outer, basering(Inner), name)
    end
end

function _inject_var(::Type{Outer}, ::Type{Inner}, name) where Outer where Inner<:NumberedPolynomial
    if name == numberedvariablename(Inner)
        return NumberedVariableGenerator(Outer, monomialtype(Inner))
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

function _ideal(R, expr)
    res = :( Ideal() )
    symbol_to_variable(sym) = :($R($(QuoteNode(sym))))

    if expr isa Expr && expr.head == :tuple
        for ex in expr.args
            push!(res.args, _visit_symbols(symbol_to_variable, ex))
        end
    else
        push!(res.args, _visit_symbols(symbol_to_variable, expr))
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
    variable_spec = length(definition.args) > 2 || definition.args[2] isa Symbol ?
                    Expr(:tuple, definition.args[2:end]...) :
                    definition.args[2]

    if basering_spec isa Expr
        basering = _ring(basering_spec)
    else
        basering = get(_baserings, basering_spec, esc(basering_spec))
    end

    scheme = parse_namingscheme(variable_spec)
    return quote
        $polynomial_ring($scheme, basering=$basering)
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
@ring(ℚ[x,y])
```

# See also
`polynomial_ring` `@ring!`

"""
macro ring(definition)
    return _ring(definition)
end

function _ring(definition)
    if definition.head == :call && definition.args[1] == :/
        return quote
            R = $( _polynomial_ring(definition.args[2]))
            I = $( _ideal(:R, definition.args[3]) )
            R / I
        end
    elseif definition.head == :curly
        return definition
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
x^3 + y
```

# See also
`polynomial_ring`

"""
macro ring!(definition)
    if definition.head == :call && definition.args[1] == :/
        return quote
            R = $( _polynomial_ring(definition.args[2]))
            I = $( _ideal(:R, definition.args[3]) )
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
x^3 + x^2*y + x*y^2 + y^3

julia> @polynomial x^3 + x^2*y + x*y^2 + y^3
x^3 + x^2*y + x*y^2 + y^3
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
        R = @ring $definition
        $NumberField(R)
    end

end

macro numberfield!(definition)
    quote
        R = @ring $definition
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
x + 3*y

julia> @polyvar ε[];

julia> 1 + ε()*x + ε()*y
ε[1]*x + ε[2]*y + 1
```

# See also
`polynomial_ring` `@ring!`

"""
macro polyvar(expr...)
    if(!all(ex isa Symbol || (ex.head == :ref && length(ex.args) == 1 && ex.args[1] isa Symbol) for ex in expr))
        throw(ArgumentError("The @polyvar macro can only be used with symbols. Example: @polyvar x y"))
    end
    definition = :( Int64[] )
    append!(definition.args, expr)
    esc(:( @ring! $definition ))
end

# -----------------------------------------------------------------------------
#
# Constructor function
#
# -----------------------------------------------------------------------------
"""
    polynomial_ring(symbols::Symbol...; basering=Rational{BigInt}, exptype=Int16, monomialorder=:degrevlex)

Create a type for the polynomial ring over `basering` in variables with names
specified by `symbols`, and return the type and a tuple of these variables.

The `exptype` parameter defines the integer type for the exponents.

The `monomialorder` defines an order for the monomials for e.g. Gröbner basis computations;
it also defines the internal sort order. Built-in values are `:degrevlex`,
`:deglex` and `:lex`. This function will accept any symbol, though, and you can
define your own monomial order by implementing

    Base.Order.lt(::MonomialOrder{:myorder}, a::M, b::M) where M <: AbstractMonomial

See `PolynomialRings.MonomialOrderings` for examples.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R,(x,y,z) = polynomial_ring(:x, :y, :z);

julia> x*y + z
x*y + z
```
"""
function polynomial_ring(symbols::Symbol...; basering::Type=Rational{BigInt}, exptype::Type=Int16, monomialorder::Symbol=:degrevlex, sparse=true)
    length(symbols) > 0 || throw(ArgumentError("Need at least one variable name"))
    allunique(symbols) || throw(ArgumentError("Duplicated symbols when extending $basering by $(Named{symbols}())"))
    scheme = Named{symbols}()
    P = polynomial_ring(scheme, basering=basering, exptype=exptype, monomialorder=monomialorder, sparse=sparse)
    return P, Generator.(symbols, tuple(generators(P)...))
end

function numbered_polynomial_ring(symbol::Symbol; basering::Type=Rational{BigInt}, exptype::Type=Int16, monomialorder::Symbol=:degrevlex, sparse=true)
    scheme =  Numbered{symbol, Inf}()
    P = polynomial_ring(scheme, basering=basering, exptype=exptype, monomialorder=monomialorder, sparse=sparse)
    return P
end

function numbered_polynomial_ring(symbol::Symbol, n::Integer; basering::Type=Rational{BigInt}, exptype::Type=Int16, monomialorder::Symbol=:degrevlex, sparse=true)
    scheme =  Numbered{symbol, n}()
    P = polynomial_ring(scheme, basering=basering, exptype=exptype, monomialorder=monomialorder, sparse=sparse)
    return P, generators(P)
end

function polynomial_ring(scheme::NamingScheme; basering::Type=Rational{BigInt}, exptype::Type=Int16, monomialorder::Symbol=:degrevlex, sparse=true)
    if !isdisjoint(scheme, nestednamingscheme(basering)) || !isdisjoint(scheme, boundnames(basering)) || !isvalid(scheme)
        throw(ArgumentError("Duplicated symbols when extending $basering by $scheme"))
    end
    order = MonomialOrdering{monomialorder, typeof(scheme)}()
    M = monomialtype(order, exptype)
    return polynomialtype(M, basering, sparse=sparse)
end


end
