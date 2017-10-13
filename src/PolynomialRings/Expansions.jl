module Expansions

import PolynomialRings.Constructors: polynomial_ring
import PolynomialRings.NamedPolynomials: _convert_monomial, _lossy_convert_monomial
import PolynomialRings.Polynomials: Polynomial, termtype, monomialtype, terms
import PolynomialRings.Terms: Term, monomial, coefficient
import PolynomialRings: basering, namestype, variablesymbols
import PolynomialRings.Monomials: AbstractMonomial, TupleMonomial, exptype
import PolynomialRings.VariableNames: Named
import PolynomialRings.MonomialOrderings: MonomialOrder

import Iterators: groupby

"""
    monomialtype, coefficienttype = _expansion_types(R, Named{tuple(symbols...)})
"""
function _expansion_types(::Type{P}, ::Type{Named{vars}}) where P <: Polynomial where vars
    all_vars = variablesymbols(P)
    remaining_vars = [v for v in all_vars if !(v in vars)]
    N = length(vars)
    M = length(remaining_vars)
    ExpType = exptype(P)
    ExpansionType = NTuple{N,ExpType}
    C = basering(P)
    if M == 0
        CoeffType = C
    else
        NamesCoefficient = Named{tuple(remaining_vars...)}
        CoeffType = Polynomial{Vector{Term{TupleMonomial{M,ExpType,NamesCoefficient},C}},:degrevlex}
    end
    return ExpansionType, CoeffType

end


"""
    expansion(f, symbol, [symbol...])

Return a collection of (exponent_tuple, coefficient) tuples decomposing f
into its consituent parts.

In the REPL, you likely want to use the friendlier version `@expansion` instead.

# Examples
```jldoctest
julia> R = @ring ℤ[x,y];
julia> collect(expansion(x^3 + y^2, :y))
[((0,), 1 x^3), ((2,), 1)]
julia> collect(expansion(x^3 + y^2, :x, :y))
[((3,0), 1), ((0,2), 1)]
```
# See also
`@expansion(...)`, `@coefficient` and `coefficient`
"""
function expansion(p::P, variables::Type{Named{vars}}) where P <: Polynomial where vars
    all_vars = variablesymbols(P)
    remaining_vars = [v for v in all_vars if !(v in vars)]

    if length(remaining_vars) == 0
        N = length(vars)
        ExpType = exptype(P)
        MonomialType = TupleMonomial{N,ExpType,Named{tuple(vars...)}}
        ExpansionType = NTuple{N,ExpType}
        ResultType = Tuple{ExpansionType, basering(P)}
        one_ = one(basering(p))

        f = t->_convert_monomial(MonomialType, monomial(t))

        return Channel(ctype=ResultType) do ch
            for t in terms(p)
                push!(ch, (f(t).e, coefficient(t)))
            end
        end
    else
        ExpType = exptype(P)
        MonomialExpansion = TupleMonomial{length(vars),ExpType,Named{tuple(vars...)}}
        MonomialCoefficient = TupleMonomial{length(remaining_vars),ExpType,Named{tuple(remaining_vars...)}}
        N = length(vars)
        M = length(remaining_vars)

        C = basering(P)
        ExpansionType = NTuple{N,ExpType}
        CoeffType = Polynomial{Vector{Term{MonomialCoefficient,C}},:degrevlex}
        ResultType = Tuple{ExpansionType, CoeffType}

        f = t->_lossy_convert_monomial(MonomialExpansion,   monomial(t))
        g = t->_lossy_convert_monomial(MonomialCoefficient, monomial(t))

        return Channel(ctype=ResultType) do ch
            separated_terms = [(f(t), g(t), coefficient(t)) for t in terms(p)]
            sort!(separated_terms, lt=(a,b)->Base.Order.lt(MonomialOrder{:degrevlex}(),a[1],b[1]))
            for term_group in groupby(x->x[1], separated_terms)
                expand_exponents = term_group[1][1].e
                coeff_terms = [Term(t[2], t[3]) for t in term_group]
                sort!(coeff_terms, order=MonomialOrder{:degrevlex}())
                p = CoeffType(coeff_terms)

                push!(ch, (expand_exponents, p))
            end
        end
    end
end

"""
    coefficients(f, symbol, [symbol...])

Return the coefficients of `f` when expanded as a polynomial in the given
variables.

# Examples
```jldoctest
julia> R = @ring ℤ[x,y];
julia> collect(coefficients(x^3 + y^2, :y))
[1 x^3, 1]
julia> collect(coefficients(x^3 + y^2, :x, :y))
[1, 1]
```
# See also
`@coefficients`, `@expansion`, `expansion`, `@coefficient` and `coefficient`
"""
function coefficients(p::P, variables::Type{Named{vars}}) where P <: Polynomial where vars
    return [c for (p,c) in expansion(p, Named{vars})]
end

@inline expansion(p::Polynomial, variables::Symbol...) = expansion(p, Named{variables})
@inline coefficients(p::Polynomial, variables::Symbol...) = coefficients(p, Named{variables})


"""
    f(var1=...,var2=...)

Substitute variables with Numbers

"""
function (p::Polynomial)(; kwargs...)
    vars = [k for (k,v) in kwargs]
    values = [v for (k,v) in kwargs]

    ExpansionType, CoeffType = _expansion_types(typeof(p), Named{tuple(vars...)})
    ReturnType = promote_type(eltype(values), CoeffType)
    if iszero(p)
        return zero(ReturnType)
    end
    # TODO: type stability even in corner cases
    sum( p * prod(v^k for (v,k) in zip(values,w)) for (w,p) in expansion(p, vars...) )
end

function (p::Array{P})(; kwargs...) where P <: Polynomial
    map(p_i -> p_i(;kwargs...), p)
end

import Base: diff

function diff(p::Polynomial, variable::Symbol)
    for (i,s) in enumerate(variablesymbols(typeof(p)))
        if s == variable
            return diff(p, i)
        end
    end
    throw(ArgumentError("Variable $variable does not appear in $(typeof(p))"))
end

"""
    coefficient(f, exponent_tuple, symbol, [symbol...])

Return a the coefficient of f at monomial. In the REPL, you likely want
to use the friendlier version `@coefficient`.

# Examples
```jldoctest
julia> R = @ring ℤ[x,y];
julia> coefficient(x^3*y + x, (1,), :x)
1
julia> coefficient(x^3*y + x, (3,), :x)
1 y
julia> coefficient(x^3*y + x, (3,0), :x, :y)
0
julia> coefficient(x^3*y + x, (3,1), :x, :y)
1
```
# See also
`@coefficient`, `expansion` and `@expansion`
"""
function coefficient(f::Polynomial, t::Tuple, vars::Symbol...)
    for (w,p) in expansion(f, vars...)
        if w == t
            return p
        end
    end
    ExpansionType, CoeffType = _expansion_types(typeof(f), Named{vars})
    return zero(CoeffType)
end

function coefficient(f::Polynomial, t::Polynomial, vars::Symbol...)
    ((w,p),) = expansion(t, vars...)
    p == 1 || throw(ArgumentError("Cannot get a coefficient for $t when symbols are $vars"))

    coefficient(f, w, vars...)
end

"""
    constant_coefficient(f, vars...)

Return the constant coefficient of `f` as a function of `vars`.

!!! note
    `vars` need to be symbols; e.g. they cannot be the polynomial `x`.

# Examples
```jldoctest
julia> R = @ring ℤ[x,y];
julia> constant_coefficient(x^3*y + x + y + 1, :x)
1 + 1 y
julia> constant_coefficient(x^3*y + x + y + 1, :x, :y)
1
```
# See also
`@constant_coefficient`, `@coefficient`, and `@expansion`
"""
function constant_coefficient(f::Polynomial, vars::Symbol...)
    return coefficient(f, ntuple(i->0, length(vars)), vars...)
end

"""
    linear_coefficients(f, vars...)

Return the linear coefficients of `f` as a function of `vars`.

!!! note
    `vars` need to be symbols; e.g. they cannot be the polynomial `x`.

# Examples
```jldoctest
julia> R = @ring ℤ[x,y];
julia> linear_coefficients(x^3*y + x + y + 1, :x)
[1]
julia> linear_coefficients(x^3*y + x + y + 1, :x, :y)
[1,x^3+1]
```
# See also
`@constant_coefficient`, `@coefficient`, and `@expansion`
"""
function linear_coefficients(f::Polynomial, vars::Symbol...)
    return [
        coefficient(f, ntuple(i->(i==j)?1:0, length(vars)), vars...)
        for j = 1:length(vars)
    ]
end

function _parse_monomial_expression(expr)
    if expr isa Symbol
        return (1,), (expr,)
    elseif expr.head == :call && expr.args[1] == :^ && expr.args[2] isa Symbol
        return (expr.args[3],), (expr.args[2],)
    elseif expr.head == :call && expr.args[1] == :*
        ts = Int[]
        ss = Symbol[]
        for e in expr.args[2:end]
            ((t,),(s,)) =_parse_monomial_expression(e)
            push!(ts, t)
            push!(ss, s)
        end
        return ntuple(i->ts[i], length(ts)), ss
    end
end

"""
    @coefficient(f, monomial)

Return a the coefficient of `f` at `monomial`.

!!! note
    `monomial` needs to be a literal monomial; it cannot be a variable containing a
    monomial.  This macro has a rather naive parser that gets exponents and
    variable names from `monomial`.

    This is considered a feature (not a bug) because it is only as a literal
    monomial that we can distinguish e.g. `x^4` from `x^4*y^0`.

# Examples
```jldoctest
julia> R = @ring ℤ[x,y];
julia> @coefficient(x^3*y + x, x)
1
julia> @coefficient(x^3*y + x, x^3)
1 y
julia> @coefficient(x^3*y + x, x^3*y^0)
0
julia> @coefficient(x^3*y + x, x^3*y^1)
1
```
# See also
`coefficient`, `expansion` and `@expansion`
"""
macro coefficient(f, monomial)
    t,vars = _parse_monomial_expression(monomial)
    quote
        coefficient($(esc(f)), $t, $vars...)
    end
end

"""
    @constant_coefficient(f, vars...)

Return the constant coefficient of `f` as a function of `vars`.

!!! note
    `vars` need to be literal variable names; it cannot be a variable containing
    it.

# Examples
```jldoctest
julia> R = @ring ℤ[x,y];
julia> @constant_coefficient(x^3*y + x + y + 1, x)
1 + 1 y
julia> @constant_coefficient(x^3*y + x + y + 1, x, y)
1
```
# See also
`constant_coefficient`, `@coefficient`, and `@expansion`
"""
macro constant_coefficient(f, vars...)
    quote
        constant_coefficient($(esc(f)), $vars...)
    end
end

"""
    @linear_coefficient(f, vars...)
    linear_coefficients(f, vars...)

Return the linear coefficients of `f` as a function of `vars`.

!!! note
    `vars` need to be symbols; e.g. they cannot be the polynomial `x`.

# Examples
```jldoctest
julia> R = @ring ℤ[x,y];
julia> @linear_coefficients(x^3*y + x + y + 1, x)
[1]
julia> @linear_coefficients(x^3*y + x + y + 1, x, y)
[1,x^3+1]
```
# See also
`@constant_coefficient`, `@coefficient`, and `@expansion`
"""
macro linear_coefficients(f, vars...)
    quote
        linear_coefficients($(esc(f)), $vars...)
    end
end

"""
    @expansion(f, var, [var...])

Return a collection of (monomial, coefficient) tuples decomposing f
into its consituent parts.

# Examples
```jldoctest
julia> R = @ring ℤ[x,y];
julia> collect(@expansion(x^3 + y^2, y))
[(1, 1 x^3), (1 y^2, 1)]
julia> collect(@expansion(x^3 + y^2, x, y))
[(1 x^3, 1), (1 y^2, 1)]
```
# See also
`expansion(...)`, `@coefficient` and `coefficient`
"""
macro expansion(f, symbols...)
    R,vars = polynomial_ring(symbols..., basering=Int)
    quote
        [
            (prod(v^k for (v,k) in zip($vars,w)), p)
            for (w,p) in expansion($(esc(f)), $symbols...)
        ]
    end
end

"""
    @coefficients(f, vars...)

Return the coefficients of `f` when expanded as a polynomial in the given
variables.

!!! note
    `vars` need to be literal variable names; it cannot be a variable containing
    it.

# Examples
```jldoctest
julia> R = @ring ℤ[x,y];
julia> collect(@coefficients(x^3 + y^2, y))
[1 x^3, 1]
julia> collect(@coefficients(x^3 + y^2, x, y))
[1, 1]
```
# See also
`coefficients`, `@expansion`, `expansion`, `@coefficient` and `coefficient`
"""
macro coefficients(f, symbols...)
    quote
        coefficients($(esc(f)), $symbols...)
    end
end

end
