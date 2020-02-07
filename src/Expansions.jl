module Expansions

import Base: @pure
import Base: diff
import SparseArrays: spzeros, SparseVector

import IterTools: groupby

import ..AbstractMonomials: AbstractMonomial, exptype, exponents
import ..Constants: One
import ..MonomialOrderings: MonomialOrder, NamedMonomialOrder, NumberedMonomialOrder
import ..NamingSchemes: Named, Numbered, NamingScheme, remove_variables
import ..NamingSchemes: NamedVariable
import ..Polynomials: Polynomial, monomialtype, monomialorder, SparsePolynomial
import ..Terms: Term, monomial, coefficient
import ..Util: @assertvalid
import PolynomialRings: deg
import PolynomialRings: namingscheme, variablesymbols, expansion, expand, polynomialtype

# -----------------------------------------------------------------------------
#
# Expansions: named variables
#
# -----------------------------------------------------------------------------

@pure function expansiontypes(::Type{P}, order::MonomialOrder) where P <: Polynomial
    C = remove_variables(P, namingscheme(order))
    M = monomialtype(order, exptype(P, namingscheme(order)))
    return M, C
end

_expansionspec(sym::Symbol...) = _expansionspec(Named{sym}())
_expansionspec(scheme::NamingScheme) = _expansionspec(MonomialOrder{:degrevlex, typeof(scheme)}())
_expansionspec(spec::MonomialOrder) = spec
_coefftype(::Type{P}, spec...) where P <: Polynomial = expansiontypes(P, _expansionspec(spec...))[2]

"""
    expansion(f, symbol, [symbol...])

Return a collection of (monomial, coefficient) tuples decomposing f
into its consituent parts.

In the REPL, you likely want to use the friendlier version `@expansion` instead.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> collect(expansion(x^3 + y^2, :y))
2-element Array{Tuple{TupleMonomial{1,Int16,PolynomialRings.MonomialOrderings.MonomialOrder{:degrevlex,PolynomialRings.NamingSchemes.Named{(:y,)}}},ℤ[x]},1}:
 (1, x^3)
 (y^2, 1)

julia> collect(expansion(x^3 + y^2, :x, :y))
2-element Array{Tuple{TupleMonomial{2,Int16,PolynomialRings.MonomialOrderings.MonomialOrder{:degrevlex,PolynomialRings.NamingSchemes.Named{(:x, :y)}}},BigInt},1}:
 (y^2, 1)
 (x^3, 1)
```
# See also
`@expansion(...)`, `@coefficient` and `coefficient`
"""
expand(p, spec...) = (
    (exponents(m, namingscheme(m)), c)
    for (m, c) in expansion(p, spec...)
)

"""
    expansion(f, symbol, [symbol...])

Return a collection of (monomial, coefficient) tuples decomposing f
into its consituent parts.

In the REPL, you likely want to use the friendlier version `@expansion` instead.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> collect(expansion(x^3 + y^2, :y))
2-element Array{Tuple{TupleMonomial{1,Int16,PolynomialRings.MonomialOrderings.MonomialOrder{:degrevlex,PolynomialRings.NamingSchemes.Named{(:y,)}}},ℤ[x]},1}:
 (1, x^3)
 (y^2, 1)

julia> collect(expansion(x^3 + y^2, :x, :y))
2-element Array{Tuple{TupleMonomial{2,Int16,PolynomialRings.MonomialOrderings.MonomialOrder{:degrevlex,PolynomialRings.NamingSchemes.Named{(:x, :y)}}},BigInt},1}:
 (y^2, 1)
 (x^3, 1)
```
# See also
`@expansion(...)`, `@coefficient` and `coefficient`
"""
expansion(p::Polynomial, spec...) = expansion(p, _expansionspec(spec...))
expansion(p::Term, spec...) = expansion(p, _expansionspec(spec...))
expansion(p::AbstractMonomial, spec...) = expansion(p, _expansionspec(spec...))
expansion(p::Number, spec...) = ((one(monomialtype(spec...)), p),)

function _splitmonomial(M1, M2, m)
    m1 = exp(M1, exponents(m, namingscheme(M1)))
    m2 = exp(M2, exponents(m, namingscheme(M2)))
    return (m1, m2)
end

function _splitmonomial(M1, M2::Type{One}, m)
    return (convert(M1, m), One())
end

function _splitmonomial(M1::Type{One}, M2, m)
    return (One(), convert(M2, m))
end

_ofpolynomialtype(m::AbstractMonomial, c) = _ofpolynomialtype(Term(m, c))
_ofpolynomialtype(m, c) = m * c
_ofpolynomialtype(t::Term{M,C}) where {M,C} = @assertvalid SparsePolynomial(M[monomial(t)], C[coefficient(t)])
function expansion(p::Polynomial, spec::MonomialOrder)
    C = remove_variables(typeof(p), namingscheme(spec))
    M = monomialtype(spec, exptype(typeof(p), namingscheme(spec)))
    M′ = remove_variables(monomialtype(p), namingscheme(spec))
    exploded = Tuple{M, C}[
        (
            (m, m′) = _splitmonomial(M, M′, m1);
            c′ = _ofpolynomialtype(m′, c);
            (m * m2, c′)
        )
        for (m1, c1) in expansion(p, monomialorder(p))
        for (m2,  c) in expansion(c1, spec)
    ]
    sort!(exploded, by = i -> i[1])
    collected = [
        (grp[1][1], sum(i -> i[2], grp))
        for grp in groupby(i -> i[1], exploded)
    ]
    return collected
end

function expansion(t::Term, spec::MonomialOrder)
    return expansion(polynomialtype(typeof(t))(t), spec)
end

function expansion(a::AbstractMonomial, spec::MonomialOrder)
    C = remove_variables(typeof(a), namingscheme(spec))
    M = monomialtype(spec, exptype(typeof(a), namingscheme(spec)))
    c, m = _splitmonomial(C, M, a)
    return ((m, c),)
end

# -----------------------------------------------------------------------------
#
# Functions based on expansions: coefficients(), variable substitution, etc.
#
# -----------------------------------------------------------------------------
"""
    expandcoefficients(f, symbol, [symbol...])

Return the coefficients of `f` when expanded as a polynomial in the given
variables.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> collect(expandcoefficients(x^3 + y^2, :y))
2-element Array{ℤ[x],1}:
 x^3
 1

julia> collect(expandcoefficients(x^3 + y^2, :x, :y))
2-element Array{BigInt,1}:
 1
 1
```
# See also
`@expandcoefficients`, `@expansion`, `expansion`, `@coefficient` and `coefficient`
"""
function expandcoefficients(p::P, spec...) where P <: Polynomial
    return [c for (_,c) in expansion(p, spec...)]
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
2-element Array{ℤ[x,y],1}:
 x^3 + 1
 y^2

julia> collect(expansion_terms(x^3 + y^2 + 1, :x, :y))
3-element Array{ℤ[x,y],1}:
 1
 y^2
 x^3
```
# See also
`@expandcoefficients`, `@expansion`, `expansion`, `@coefficient` and `coefficient`
"""
function expansion_terms(p::P, spec...) where P <: Polynomial
    return [
        P(m * c)
        for (m,c) in expansion(p, spec...)
    ]
end

@inline expansiontypes(t::Type, variables::Symbol...) = expansiontypes(t, _expansionspec(variables...))

_substitute(p::Polynomial, names::Named, values...) = _substitute(p, names, promote(values...)...)

function _substitute(p::Polynomial, names::Named, values::SubstitutionType...) where SubstitutionType
    ReturnType = promote_type(SubstitutionType, _coefftype(typeof(p), names))
    if !isconcretetype(ReturnType)
        throw(ArgumentError("Cannot substitute $SubstitutionType for $names into $p; result no more specific than $ReturnType"))
    end
    res = zero(ReturnType)
    for (m, c) in expansion(p, names)
        powers = values .^ exponents(m, names)
        res += *(c, powers...)
    end
    return res::ReturnType
end

function _substitute(p::Polynomial, names::Numbered, valuesfunc)
    SubstitutionType = typeof(valuesfunc(1))
    ReturnType = promote_type(SubstitutionType, _coefftype(typeof(p), names))
    if !isconcretetype(ReturnType)
        throw(ArgumentError("Cannot substitute $SubstitutionType for $names into $p; result no more specific than $ReturnType"))
    end
    res = zero(ReturnType)
    for (m, c) in expansion(p, names)
        term = c
        exps = exponents(m, names)
        ix = findfirst(!iszero, exps)
        while !isnothing(ix)
            term *= valuesfunc(ix) ^ exps[ix]
            ix = findnext(!iszero, exps, nextind(exps, ix))
        end
        res += term
    end
    return res::ReturnType
end

# helper for inspecting the types of substitution values
_kwtupletype(::Type{Base.Iterators.Pairs{K, V, I, A}}) where {K, V, I, A} = A

function substitutedtype(P::Type; kwargs...)
    kwtupletype = _kwtupletype(typeof(kwargs))
    vars = fieldnames(kwtupletype)
    valtypes = fieldtypes(kwtupletype)
    if length(kwargs) == 1 && valtypes[1] <: Function
        CoeffType = _coefftype(P, Numbered{vars[1], Inf}())
        return promote_type(CoeffType, typeof(last(first(kwargs))(1)))
    else
        return promote_type(_coefftype(P, vars...), valtypes...)
    end
end

"""
    f(var1=...,var2=...)

Substitute variables with Numbers

"""
function (p::Polynomial)(; kwargs...)
    kwtupletype = _kwtupletype(typeof(kwargs))
    vars = fieldnames(kwtupletype)
    valtypes = fieldtypes(kwtupletype)

    if isempty(kwargs)
        return copy(p)
    elseif !any(v <: Function for v in valtypes)
        return _substitute(p, Named{tuple(vars...)}(), values(kwargs)...)
    elseif length(kwargs) == 1 && valtypes[1] <: Function
        return _substitute(p, Numbered{vars[1], Inf}(), kwargs[1])
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
diff(p::Polynomial, variable::Symbol) = diff(p, NamedVariable{variable}())

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
    spec = _expansionspec(vars...)
    for (w,p) in expansion(f, spec)
        if exponents(w, namingscheme(spec)) == t
            return p
        end
    end
    return zero(_coefftype(typeof(f), spec))
end

function coefficient(f::Polynomial, t::Polynomial, vars...)
    ((w,p),) = expansion(t, vars...)
    p == 1 || throw(ArgumentError("Cannot get a coefficient for $t when symbols are $vars"))

    coefficient(f, w.e, vars...)
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
        if isone(w)
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
        if deg(w, namingscheme(spec)) == 1
            res[findfirst(!iszero,w.e)] = p
        end
    end

    return res
end

function linear_coefficients(f::Polynomial, spec::NumberedMonomialOrder)
    res = spzeros(_coefftype(typeof(f), spec), 0)
    for (w, p) in expansion(f, spec)
        if deg(w, namingscheme(spec)) == 1
            ix = findfirst(!iszero,w.e)
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
    spec = _expansionspec(args...)
    return maximum(deg(w, namingscheme(spec)) for (w,p) in expansion(f, spec))
end

# -----------------------------------------------------------------------------
#
# Helper functions for some of the macros below
#
# -----------------------------------------------------------------------------

_expansion_expr(vars::NTuple{N,Symbol}) where N = MonomialOrder{:degrevlex, Named{vars}}()
_expansion_expr(vars::Tuple{Expr}) = (v = vars[1]; @assert(v.head == :ref && length(v.args) == 1); MonomialOrder{:degrevlex, Numbered{v.args[1], Inf}}())


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

Return a collection of (monomial, coefficient) tuples decomposing f
into its consituent parts.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> collect(@expand(x^3 + y^2, y))
2-element Array{Tuple{Tuple{Int16},ℤ[x]},1}:
 ((0,), x^3)
 ((2,), 1)

julia> collect(@expand(x^3 + y^2, x, y))
2-element Array{Tuple{Tuple{Int16,Int16},BigInt},1}:
 ((0, 2), 1)
 ((3, 0), 1)
```
# See also
`expansion(...)`, `@coefficient` and `coefficient`
"""
macro expansion(f, symbols...)
    expansion_expr = _expansion_expr(symbols)
    quote
        expansion($(esc(f)), $expansion_expr)
    end
end

"""
    @expand(f, var, [var...])

Return a collection of (exponent tuple, coefficient) tuples decomposing f
into its consituent parts.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> collect(@expand(x^3 + y^2, y))
2-element Array{Tuple{Tuple{Int16},ℤ[x]},1}:
 ((0,), x^3)
 ((2,), 1)

julia> collect(@expand(x^3 + y^2, x, y))
2-element Array{Tuple{Tuple{Int16,Int16},BigInt},1}:
 ((0, 2), 1)
 ((3, 0), 1)
```
# See also
`@expansion`, `expand(...)`, `@coefficient` and `coefficient`
"""
macro expand(f, symbols...)
    expansion_expr = _expansion_expr(symbols)
    quote
        expand($(esc(f)), $expansion_expr)
    end
end

macro expansion_terms(f, symbols...)
    quote
        expansion_terms($(esc(f)), $symbols...)
    end
end

"""
    @expandcoefficients(f, vars...)

Return the coefficients of `f` when expanded as a polynomial in the given
variables.

!!! note
    `vars` need to be literal variable names; it cannot be a variable containing
    it.

# Examples
```jldoctest
julia> using PolynomialRings

julia> R = @ring! ℤ[x,y];

julia> collect(@expandcoefficients(x^3 + y^2, y))
2-element Array{ℤ[x],1}:
 x^3
 1

julia> collect(@expandcoefficients(x^3 + y^2, x, y))
2-element Array{BigInt,1}:
 1
 1
```
# See also
`expandcoefficients`, `@expansion`, `expansion`, `@coefficient` and `coefficient`
"""
macro expandcoefficients(f, symbols...)
    expansion_expr = _expansion_expr(symbols)
    quote
        expandcoefficients($(esc(f)), $expansion_expr)
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
