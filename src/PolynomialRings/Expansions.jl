module Expansions

import Base: diff
import Base: promote_rule, convert
import SparseArrays: spzeros, SparseVector

import IterTools: groupby

import ..Constants: One
import ..MonomialOrderings: MonomialOrder, NamedMonomialOrder, NumberedMonomialOrder
import ..Monomials: AbstractMonomial, TupleMonomial, exptype, expstype, enumeratenz
import ..NamedPolynomials: NamedPolynomial, _lossy_convert_monomial
import ..Polynomials: Polynomial, termtype, monomialtype, monomialorder, terms, polynomial_ring, PolynomialBy
import ..Terms: Term, monomial, coefficient
import ..Util: SingleItemIter
import ..NamingSchemes: Named, Numbered, NamingScheme, remove_variables
import PolynomialRings: basering, namingscheme, variablesymbols

# -----------------------------------------------------------------------------
#
# Expansions: named variables
#
# -----------------------------------------------------------------------------

_expansion_expr(vars::NTuple{N,Symbol}) where N = MonomialOrder{:degrevlex, Named{vars}}()
_expansion_expr(vars::Tuple{Expr}) = (v = vars[1]; @assert(v.head == :ref && length(v.args) == 1); MonomialOrder{:degrevlex, Numbered{v.args[1], Inf}}())


function _expansion_types(::Type{P}, order::MonomialOrder) where P <: NamedPolynomial
    C = remove_variables(P, namingscheme(order))
    M = monomialtype(order, exptype(P, namingscheme(order)))
    return M, C
end

_expansionspec(sym::Symbol...) = _expansionspec(Named{sym}())
_expansionspec(scheme::NamingScheme) = _expansionspec(MonomialOrder{:degrevlex, typeof(scheme)}())
_expansionspec(spec::MonomialOrder) = spec
_coefftype(::Type{P}, spec...) where P <: Polynomial = remove_variables(P, namingscheme(_expansionspec(spec...)))

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
2-element Array{Tuple{Tuple{Int16},ℤ[x]},1}:
 ((0,), x^3)
 ((2,), 1)

julia> collect(expansion(x^3 + y^2, :x, :y))
2-element Array{Tuple{Tuple{Int16,Int16},BigInt},1}:
 ((0, 2), 1)
 ((3, 0), 1)
```
# See also
`@expansion(...)`, `@coefficient` and `coefficient`
"""
expansion(p::Polynomial, spec...) = [(m.e, c) for (c,(m,)) in _expansion2(p, _expansionspec(spec...))]

_expansion2(p) = [(p, tuple())]
# TODO: this does not respect the exptype for one(monomialtype(spec)), but
# I also run into issues when I try to make it do that.
_expansion2(p, spec::MonomialOrder, specs::MonomialOrder...) = (((c, ms),) = _expansion2(p, specs...); [(c, tuple(one(monomialtype(spec)), ms...))])
# TODO: should we return owned copies?
_expansion2(p::PolynomialBy{Order}, spec::Order) where Order <: MonomialOrder = map(t -> (coefficient(t), (monomial(t),)), terms(p))
_ofpolynomialtype(m::AbstractMonomial, c) = _ofpolynomialtype(Term(m, c))
_ofpolynomialtype(m, c) = m * c
_ofpolynomialtype(t::Term{M,C}) where {M,C} = Polynomial{M,C}([t])
function _expansion2(p::Polynomial, spec::MonomialOrder)
    C = remove_variables(typeof(p), namingscheme(spec))
    M = monomialtype(spec, exptype(typeof(p), namingscheme(spec)))
    M′ = remove_variables(monomialtype(p), namingscheme(spec))
    exploded = Tuple{C, Tuple{M}}[
        (
            m = _lossy_convert_monomial(M, monomial(t));
            m′ = _lossy_convert_monomial(M′, monomial(t));
            c′ = _ofpolynomialtype(m′, c);
            (c′, (m * m2,))
        )
        for t in terms(p)
        for (c, (m2,)) in _expansion2(coefficient(t), spec)
    ]
    sort!(exploded, by = i -> i[2])
    collected = [
        (sum(i -> i[1], grp), grp[1][2])
        for grp in groupby(i -> i[2], exploded)
    ]
    return collected
end

_monomialtypes(P::Type{<:Polynomial}, spec::MonomialOrder) = tuple(monomialtype(spec, exptype(P, namingscheme(spec))))
_monomialtypes(P::Type{<:Polynomial}, spec::MonomialOrder, specs::MonomialOrder...) = tuple(_monomialtypes(P, spec)..., _monomialtypes(P, specs...)...)
_remove_variables(t::Type) = t
_remove_variables(t::Type, spec::MonomialOrder, specs::MonomialOrder...) = _remove_variables(remove_variables(t, namingscheme(spec)), specs...)
function _expansion2(p::Polynomial, spec::MonomialOrder, specs::MonomialOrder...)
    C = _remove_variables(typeof(p), spec, specs...)
    return Tuple{C, Tuple{_monomialtypes(typeof(p), spec, specs...)...}}[
        (c2, tuple(m, ms...))
        for (c1, ms) in _expansion2(p, specs...)
        for (c2, (m,)) in _expansion2(c1, spec)
    ]
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
2-element Array{ℤ[x],1}:
 x^3
 1

julia> collect(coefficients(x^3 + y^2, :x, :y))
2-element Array{BigInt,1}:
 1
 1
```
# See also
`@coefficients`, `@expansion`, `expansion`, `@coefficient` and `coefficient`
"""
function coefficients(p::P, spec...) where P <: Polynomial
    return [c for (p,c) in expansion(p, spec...)]
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
function expansion_terms(p::P, spec...) where P <: Polynomial
    return [
        _ofpolynomialtype(m * c)
        for (m,c) in _expansion2(p, spec...)
    ]
end

@inline _expansion_types(t::Type, variables::Symbol...) = _expansion_types(t, _expansionspec(variables...))

_substitute(p::Polynomial, names::Named, values...) = _substitute(p, names, promote(values...)...)

function _substitute(p::Polynomial, names::Named, values::SubstitutionType...) where SubstitutionType
    ReturnType = promote_type(SubstitutionType, _coefftype(typeof(p), names))
    if !isconcretetype(ReturnType)
        throw(ArgumentError("Cannot substitute $SubstitutionType for $names into $p; result no more specific than $ReturnType"))
    end
    return reduce(
        +,
        (
            reduce(*, (v^k for (v,k) in zip(values,w)), init=c)
            for (w,c) in expansion(p, MonomialOrder{:degrevlex, typeof(names)}())
        ),
        init=zero(ReturnType)
    )::ReturnType
end

function _substitute(p::Polynomial, names::Numbered, valuesfunc)
    SubstitutionType = typeof(valuesfunc(1))
    ReturnType = promote_type(SubstitutionType, _coefftype(typeof(p), names))
    if !isconcretetype(ReturnType)
        throw(ArgumentError("Cannot substitute $SubstitutionType for $names into $p; result no more specific than $ReturnType"))
    end
    return reduce(
        +,
        (
            reduce(*, (valuesfunc(i)^k for (i,k) in enumeratenz(m)), init=c)
            for (c,(m,)) in _expansion2(p, MonomialOrder{:degrevlex, typeof(names)}())
        ),
        init=zero(ReturnType)
    )::ReturnType
end

# helper for inspecting the types of substitution values
_kwtupletype(::Type{Base.Iterators.Pairs{K, V, I, A}}) where {K, V, I, A} = A

"""
    f(var1=...,var2=...)

Substitute variables with Numbers

"""
function (p::Polynomial)(; kwargs...)
    kwtupletype = _kwtupletype(typeof(kwargs))
    vars = fieldnames(kwtupletype)
    valtypes = fieldtypes(kwtupletype)
    values = [v for (k,v) in kwargs]

    if !any(v <: Function for v in valtypes)
        return _substitute(p, Named{tuple(vars...)}(), values...)
    elseif length(kwargs) == 1 && valtypes[1] <: Function
        return _substitute(p, Numbered{vars[1], Inf}(), values[1])
    else
        throw(ArgumentError("Don't know how to substitute $kwargs"))
    end

end


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
    return zero(_coefftype(typeof(f), vars...))
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
y + 1

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
    return zero(_coefftype(typeof(f), vars...))
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
1-element Array{ℤ[y],1}:
 1

julia> linear_coefficients(x^3*y + x + y + 1, :x, :y)
2-element Array{BigInt,1}:
 1
 1
```
# See also
`@constant_coefficient`, `@coefficient`, and `@expansion`
"""
linear_coefficients(f::Polynomial, spec...) = linear_coefficients(f, _expansionspec(spec...))

function linear_coefficients(f::Polynomial, spec::NamedMonomialOrder)
    res = zeros(_coefftype(typeof(f), spec), length(variablesymbols(spec)))
    for (w, p) in expansion(f, spec)
        if sum(w) == 1
            res[findfirst(!iszero,w)] = p
        end
    end

    return res
end

function linear_coefficients(f::Polynomial, spec::NumberedMonomialOrder)
    res = spzeros(_coefftype(typeof(f), spec), 0)
    for (w, p) in expansion(f, spec)
        if sum(w) == 1
            ix = findfirst(!iszero,w)
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

julia> R = @ring! ℤ[x,y];

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
y + 1

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
1-element Array{ℤ[y],1}:
 1

julia> @linear_coefficients(x^3*y + x + y + 1, x, y)
2-element Array{BigInt,1}:
 1
 1
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
2-element Array{Tuple{Tuple{Int16},ℤ[x]},1}:
 ((0,), x^3)
 ((2,), 1)

julia> collect(@expansion(x^3 + y^2, x, y))
2-element Array{Tuple{Tuple{Int16,Int16},BigInt},1}:
 ((0, 2), 1)
 ((3, 0), 1)
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
2-element Array{Tuple{Int64[y],ℤ[x]},1}:
 (1, x^3)
 (y^2, 1)

julia> collect(@expand(x^3 + y^2, x, y))
2-element Array{Tuple{Int64[x,y],BigInt},1}:
 (y^2, 1)
 (x^3, 1)
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
2-element Array{ℤ[x],1}:
 x^3
 1

julia> collect(@coefficients(x^3 + y^2, x, y))
2-element Array{BigInt,1}:
 1
 1
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
