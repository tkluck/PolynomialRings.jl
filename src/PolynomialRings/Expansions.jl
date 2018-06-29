module Expansions

import PolynomialRings.NamedPolynomials: NamedPolynomial, _lossy_convert_monomial
import PolynomialRings.Polynomials: Polynomial, termtype, monomialtype, terms, polynomial_ring
import PolynomialRings.Terms: Term, monomial, coefficient
import PolynomialRings: basering, namestype, variablesymbols
import PolynomialRings.Monomials: AbstractMonomial, TupleMonomial, exptype, expstype, enumeratenz
import PolynomialRings.VariableNames: Named, Numbered
import PolynomialRings.MonomialOrderings: MonomialOrder
import PolynomialRings.Util: lazymap, TrivialIter
import PolynomialRings.Constants: One

import Iterators: groupby

if VERSION < v"0.7-"
    isconcretetype(x) = isleaftype(x)
else
    using SparseArrays: spzeros, SparseVector
end

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: promote_rule, convert

# -----------------------------------------------------------------------------
#
# Expansions: named variables
#
# -----------------------------------------------------------------------------

_expansion_types(::Type{N}, ::Type) where N = (One, N)
_lossy_convert_monomial(::Type{M}, ::One) where M<:AbstractMonomial = one(M)

"""
    monomialtype, coefficienttype = _expansion_types(R, Named{tuple(symbols...)})
"""
function _expansion_types(::Type{P}, ::Type{Named{vars}}) where P <: NamedPolynomial where vars
    available_vars = variablesymbols(P)
    unspecified_vars = tuple(setdiff(available_vars, vars)...)
    unknown_vars = tuple(setdiff(vars, available_vars)...)

    CoeffMonomialType, CoeffCoeffType = _expansion_types(basering(P), Named{unknown_vars})

    N = length(vars)
    M = length(unspecified_vars)
    ExpType = exptype(P)
    MonomialType = TupleMonomial{N,ExpType,MonomialOrder{:degrevlex,Named{vars}}}
    if M == 0
        CoeffType = CoeffCoeffType
    else
        CoeffType = promote_type(
            CoeffCoeffType,
            Polynomial{Vector{Term{TupleMonomial{M,ExpType,MonomialOrder{:degrevlex,Named{unspecified_vars}}},One}}},
        )
    end
    if !isconcretetype(CoeffType)
        throw(ArgumentError("Cannot expand $P in variables $(Named{vars}); would result in $CoeffType"))
    end
    return MonomialType, CoeffType

end

_expansion(p, T::Type) = ((M,C) = _expansion_types(typeof(p), T); TrivialIter((one(M), p)))

"""
    expansion(f, symbol, [symbol...])

Return a collection of (exponent_tuple, coefficient) tuples decomposing f
into its consituent parts.

In the REPL, you likely want to use the friendlier version `@expansion` instead.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> collect(expansion(x^3 + y^2, :y))
[((0,), x^3), ((2,), 1)]

julia> collect(expansion(x^3 + y^2, :x, :y))
[((3,0), 1), ((0,2), 1)]
```
# See also
`@expansion(...)`, `@coefficient` and `coefficient`
"""
function expansion(p::P, args...) where P <: Polynomial
    MonomialType, CoeffType = _expansion_types(P, args...)
    return Channel(ctype=Tuple{expstype(MonomialType), CoeffType}) do ch
        for (w,c) in _expansion(p, args...)
            push!(ch, (w.e, c))
        end
    end
end


function _expansion(p::P, ::Type{Named{vars}}) where P <: NamedPolynomial where vars
    available_vars = variablesymbols(P)
    unspecified_vars = tuple(setdiff(available_vars, vars)...)
    unknown_vars = tuple(setdiff(vars, available_vars)...)

    MonomialType, CoeffType = _expansion_types(P, Named{vars})
    ResultType = Tuple{MonomialType, CoeffType}
    f(m) = _lossy_convert_monomial(MonomialType, m)

    if length(unspecified_vars) == 0
        return Channel(ctype=ResultType) do ch
            for t in terms(p)
                outer_monomial = monomial(t)
                for (inner_monomial,c) in _expansion(coefficient(t), Named{unknown_vars})
                    push!(ch, (f(inner_monomial)*f(outer_monomial), c))
                end
            end
        end
    else
        ExpType = exptype(P)
        UnspecifiedMonomial = TupleMonomial{length(unspecified_vars),ExpType,MonomialOrder{:degrevlex,Named{unspecified_vars}}}
        g(m) = _lossy_convert_monomial(monomialtype(CoeffType), m)
        h(m) = convert(MonomialType, m)

        return Channel(ctype=ResultType) do ch
            iszero(p) && return
            separated_terms = [
                (f(monomial(t))*h(inner_monomial), CoeffType(g(monomial(t))) * c)
                for t in terms(p)
                for (inner_monomial,c) in _expansion(coefficient(t), Named{unknown_vars})
            ]
            sort!(separated_terms, lt=(a,b)->a[1]<b[1])
            for term_group in groupby(x->x[1], separated_terms)
                m = term_group[1][1]
                p = sum(t[2] for t in term_group)
                push!(ch, (m, p))
            end
        end
    end
end

# -----------------------------------------------------------------------------
#
# Expansions: numbered variables
#
# -----------------------------------------------------------------------------
function _expansion_types(::Type{P}, ::Type{Numbered{name}}) where P <: Polynomial where name
    @assert namestype(P) == Numbered{name}

    return (monomialtype(P), basering(P))
end

function _expansion(p::P, ::Type{Numbered{name}}) where P <: Polynomial where name
    @assert namestype(p) == Numbered{name}

    return Channel(ctype=Tuple{monomialtype(P), basering(P)}) do ch
        for t in terms(p)
            push!(ch, (monomial(t), coefficient(t)))
        end
    end

end

function _expansion_types(::Type{P}, ::Type{Numbered{name}}) where P <: NamedPolynomial where name

    CoeffMonomialType, CoeffCoeffType = _expansion_types(basering(P), Numbered{name})

    PP,_ = polynomial_ring(variablesymbols(P)..., basering=CoeffCoeffType)

    return (CoeffMonomialType, PP)
end

function _expansion(p::P, ::Type{Numbered{name}}) where P <: NamedPolynomial where name

    MonomialType, CoeffType = _expansion_types(P, Numbered{name})

    return Channel(ctype=Tuple{MonomialType, CoeffType}) do ch
        iszero(p) && return
        separated_terms = [
            (inner_monomial,c*CoeffType(monomial(t)))
            for t in terms(p)
            for (inner_monomial,c) in _expansion(coefficient(t), Numbered{name})
        ]
        sort!(separated_terms, lt=(a,b)->a[1]<b[1])
        for term_group in groupby(x->x[1], separated_terms)
            m = term_group[1][1]
            p = sum(t[2] for t in term_group)
            push!(ch, (m, p))
        end
    end
end

# -----------------------------------------------------------------------------
#
# Functions based on expansions: coefficients(), variable substitution, etc.
#
# -----------------------------------------------------------------------------
"""
    coefficients(f, symbol, [symbol...])

Return the coefficients of `f` when expanded as a polynomial in the given
variables.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> collect(coefficients(x^3 + y^2, :y))
[x^3, 1]

julia> collect(coefficients(x^3 + y^2, :x, :y))
[1, 1]
```
# See also
`@coefficients`, `@expansion`, `expansion`, `@coefficient` and `coefficient`
"""
function coefficients(p::P, variables) where P <: Polynomial
    return [c for (p,c) in expansion(p, variables)]
end

"""
    expansion_terms(f, symbol, [symbol...])

Return the terms of `f` when expanded as a polynomial in the given
variables.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> collect(expansion_terms(x^3 + y^2 + 1, :y))
[x^3 + 1, y^2]

julia> collect(expansion_terms(x^3 + y^2 + 1, :x, :y))
[1, y^2, x^3]
```
# See also
`@coefficients`, `@expansion`, `expansion`, `@coefficient` and `coefficient`
"""
function expansion_terms(p::P, variables) where P <: Polynomial
    MonomialType, CoeffType =_expansion_types(P, args...)
    return [
        convert(MonomialType, w)*c
        for (w,c) in expansion(p, variables)
    ]
end

@inline expansion(p::Polynomial, variables::Symbol...) = expansion(p, Named{variables})
@inline coefficients(p::Polynomial, variables::Symbol...) = coefficients(p, Named{variables})
@inline linear_coefficients(p::Polynomial, variables::Symbol...) = linear_coefficients(p, Named{variables})
@inline coefficient(p::Polynomial, exponent_tuple::Tuple, variables::Symbol...) = coefficient(p, exponent_tuple, Named{variables})

@inline _expansion_types(t::Type, variables::Symbol...) = _expansion_types(t, Named{variables})

function _substitute(p::Polynomial, ::Type{Named{Names}}, values) where Names
    ExpansionType, CoeffType = _expansion_types(typeof(p), Named{Names})
    SubstitutionType = eltype(values)
    ReturnType = promote_type(SubstitutionType, CoeffType)
    if !isconcretetype(ReturnType)
        throw(ArgumentError("Cannot substitute $SubstitutionType for $(Named{Names}) into $p; result no more specific than $ReturnType"))
    end
    return reduce(+, zero(ReturnType),
        reduce(*, c, v^k for (v,k) in zip(values,w))
        for (w,c) in expansion(p, Named{Names})
    )
end

function _substitute(p::Polynomial, ::Type{Numbered{Name}}, values) where Name
    ExpansionType, CoeffType = _expansion_types(typeof(p), Numbered{Name})
    SubstitutionType = typeof(values(1))
    ReturnType = promote_type(SubstitutionType, CoeffType)
    if !isconcretetype(ReturnType)
        throw(ArgumentError("Cannot substitute $SubstitutionType for $(Numbered{Name}) into $p; result no more specific than $ReturnType"))
    end
    return reduce(+, zero(ReturnType),
        reduce(*, c, values(i)^k for (i,k) in enumeratenz(m))
        for (m,c) in _expansion(p, Numbered{Name})
    )
end

"""
    f(var1=...,var2=...)

Substitute variables with Numbers

"""
function (p::Polynomial)(; kwargs...)
    vars = Symbol[k for (k,v) in kwargs]
    values = [v for (k,v) in kwargs]

    if !any(v isa Function for v in values)
        return _substitute(p, Named{tuple(vars...)}, values)
    elseif length(kwargs) == 1 && values[1] isa Function
        return _substitute(p, Numbered{vars[1]}, values[1])
    else
        throw(ArgumentError("Don't know how to substitute $kwargs"))
    end

end

import Base: diff

"""
    diff(polynomial, variable)

Return the derivative of `polynomial` w.r.t. `variable`.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> diff(x^3, :x)
3*x^2

julia> diff(x^3, :y)
0
```
"""
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
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> coefficient(x^3*y + x, (1,), :x)
1

julia> coefficient(x^3*y + x, (3,), :x)
y

julia> coefficient(x^3*y + x, (3,0), :x, :y)
0

julia> coefficient(x^3*y + x, (3,1), :x, :y)
1
```
# See also
`@coefficient`, `expansion` and `@expansion`
"""
function coefficient(f::Polynomial, t::Tuple, vars...)
    for (w,p) in expansion(f, vars...)
        if w == t
            return p
        end
    end
    ExpansionType, CoeffType = _expansion_types(typeof(f), vars...)
    return zero(CoeffType)
end

function coefficient(f::Polynomial, t::Polynomial, vars...)
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
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> constant_coefficient(x^3*y + x + y + 1, :x)
y + -1

julia> constant_coefficient(x^3*y + x + y + 1, :x, :y)
1
```
# See also
`@constant_coefficient`, `@coefficient`, and `@expansion`
"""
function constant_coefficient(f::Polynomial, vars...)
    for (w,p) in expansion(f, vars...)
        if sum(w) == 0
            return p
        end
    end
    ExpansionType, CoeffType = _expansion_types(typeof(f), vars...)
    return zero(CoeffType)
end

"""
    linear_coefficients(f, vars...)

Return the linear coefficients of `f` as a function of `vars`.

!!! note
    `vars` need to be symbols; e.g. they cannot be the polynomial `x`.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> linear_coefficients(x^3*y + x + y + 1, :x)
[1]

julia> linear_coefficients(x^3*y + x + y + 1, :x, :y)
[1,x^3 + 1]
```
# See also
`@constant_coefficient`, `@coefficient`, and `@expansion`
"""
function linear_coefficients(f::Polynomial, ::Type{Named{Names}}) where Names
    ExpansionType, CoeffType = _expansion_types(typeof(f), Named{Names})

    res = zeros(CoeffType, length(Names))
    for (w, p) in expansion(f, Named{Names})
        if sum(w) == 1
            res[findfirst(w)] = p
        end
    end

    return res
end

function linear_coefficients(f::Polynomial, ::Type{Numbered{Name}}) where Name
    ExpansionType, CoeffType = _expansion_types(typeof(f), Numbered{Name})

    res = spzeros(CoeffType, 0)
    for (w, p) in expansion(f, Numbered{Name})
        if sum(w) == 1
            ix = findfirst(w)
            newlength = max(ix, length(res))
            # there is no resize!() because SparseVector is an
            # immutable struct
            res = SparseVector(newlength, res.nzind, res.nzval)
            res[ix] = p
        end
    end

    return res
end

"""
    deg(f, vars...)

Return the total degree of `f` when regarded as a polynomial in `vars`. Returns
-1 for the zero polynomial.

```jldoctest
julia> using PolynomialRings

julia> R = @ring ℤ[x,y];

julia> deg(x^2, :x)
2

julia> deg(x^2, :x, :y)
2

julia> deg(x^2, :y)
0
```
"""
function deg(f::Polynomial, args...)
    iszero(f) && return -1
    return maximum(sum(w) for (w,p) in expansion(f, args...))
end

# -----------------------------------------------------------------------------
#
# Helper functions for some of the macros below
#
# -----------------------------------------------------------------------------

_expansion_expr(vars::NTuple{N,Symbol}) where N = Named{vars}
_expansion_expr(vars::Tuple{Expr}) = (v = vars[1]; @assert(v.head == :ref && length(v.args) == 1); Numbered{v.args[1]})

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

# -----------------------------------------------------------------------------
#
# Wrapper macros for some of the functions above
#
# -----------------------------------------------------------------------------

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
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> @coefficient(x^3*y + x, x)
1

julia> @coefficient(x^3*y + x, x^3)
y

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
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> @constant_coefficient(x^3*y + x + y + 1, x)
y + -1

julia> @constant_coefficient(x^3*y + x + y + 1, x, y)
1
```
# See also
`constant_coefficient`, `@coefficient`, and `@expansion`
"""
macro constant_coefficient(f, symbols...)
    expansion_expr = _expansion_expr(symbols)
    quote
        constant_coefficient($(esc(f)), $expansion_expr)
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
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> @linear_coefficients(x^3*y + x + y + 1, x)
[1]

julia> @linear_coefficients(x^3*y + x + y + 1, x, y)
[1,x^3 + 1]
```
# See also
`@constant_coefficient`, `@coefficient`, and `@expansion`
"""
macro linear_coefficients(f, symbols...)
    expansion_expr = _expansion_expr(symbols)
    quote
        linear_coefficients($(esc(f)), $expansion_expr)
    end
end

"""
    @expansion(f, var, [var...])

Return a collection of (exponent tuple, coefficient) tuples decomposing f
into its consituent parts.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> collect(@expansion(x^3 + y^2, y))
[((0,), x^3), ((2,), 1)]

julia> collect(@expansion(x^3 + y^2, x, y))
[((3,0), 1), ((0,2), 1)]
```
# See also
`@expand`, `expansion(...)`, `@coefficient` and `coefficient`
"""
macro expansion(f, symbols...)
    expansion_expr = _expansion_expr(symbols)
    quote
        expansion($(esc(f)), $expansion_expr)
    end
end

"""
    @expand(f, var, [var...])

Return a collection of (monomial, coefficient) tuples decomposing f
into its consituent parts.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> collect(@expand(x^3 + y^2, y))
[(1, x^3), (y^2, 1)]

julia> collect(@expand(x^3 + y^2, x, y))
[(x^3, 1), (y^2, 1)]
```
# See also
`expansion(...)`, `@coefficient` and `coefficient`
"""
macro expand(f, symbols...)
    expansion_expr = _expansion_expr(symbols)
    R,vars = polynomial_ring(symbols..., basering=Int)
    quote
        [
            (prod(v^k for (v,k) in zip($vars,w)), p)
            for (w,p) in expansion($(esc(f)), $expansion_expr)
        ]
    end
end

macro expansion_terms(f, symbols...)
    quote
        expansion_terms($(esc(f)), $symbols...)
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
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> collect(@coefficients(x^3 + y^2, y))
[x^3, 1]

julia> collect(@coefficients(x^3 + y^2, x, y))
[1, 1]
```
# See also
`coefficients`, `@expansion`, `expansion`, `@coefficient` and `coefficient`
"""
macro coefficients(f, symbols...)
    expansion_expr = _expansion_expr(symbols)
    quote
        coefficients($(esc(f)), $expansion_expr)
    end
end

"""
    @deg(f, vars...)

Return the total degree of `f` when expanded as a polynomial in the given
variables.

!!! note
    `vars` need to be literal variable names; it cannot be a variable containing
    it.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> @deg (x^2 + x*y - 1) x
2

julia> @deg (x^2 + x*y - 1) y
1
```
# See also
`deg`, `@expansion`
"""
macro deg(f, symbols...)
    expansion_expr = _expansion_expr(symbols)
    quote
        deg($(esc(f)), $expansion_expr)
    end
end

end
