module Expansions

import Base: @pure
import Base: diff
import SparseArrays: spzeros, SparseVector, AbstractSparseArray

import InPlace: @inplace
import IterTools: groupby

import ..AbstractMonomials: AbstractMonomial, exptype, exponents
import ..Constants: One
import ..MonomialOrderings: MonomialOrder, NamedMonomialOrder, NumberedMonomialOrder
import ..MonomialOrderings: monomialorderkeytype, monomialordereltype
import ..NamingSchemes: Named, Numbered, NamingScheme, remove_variables
import ..NamingSchemes: NamedVariable
import ..Polynomials: Polynomial, monomialtype, monomialorder, SparsePolynomial, nzterms
import ..StandardMonomialOrderings: MonomialOrdering, LexCombinationOrder, KeyOrder
import ..StandardMonomialOrderings: maybeunwrap
import ..Terms: Term, monomial, coefficient
import ..Util: @assertvalid, nzpairs
import PolynomialRings: deg, generators, max_variable_index
import PolynomialRings: namingscheme, variablesymbols, expansion, expand, polynomialtype

# -----------------------------------------------------------------------------
#
# Expansions: named variables
#
# -----------------------------------------------------------------------------

const EmptyLexCombinationOrder = LexCombinationOrder{Tuple{}}
const KeyLexCombinationOrder = LexCombinationOrder{<:Tuple{KeyOrder, Vararg}}
const SingleLexCombinationOrder = LexCombinationOrder{<:Tuple{Any}}
const OtherLexCombinationOrder = LexCombinationOrder{<:Tuple}

withkeys(o, P, M) = M
withkeys(o::EmptyLexCombinationOrder, P, M) = M
withkeys(o::OtherLexCombinationOrder, P, M) = withkeys(Base.tail(o), P, M)
withkeys(o::KeyLexCombinationOrder, P, M) = Pair{
    monomialorderkeytype(P),
    withkeys(Base.tail(o), monomialordereltype(P), M),
}

atomicorders() = ()
atomicorders(o::KeyOrder, os...) = atomicorders(os...)
atomicorders(o, os...) = (o, atomicorders(os...)...)
atomicorder(o) = o
atomicorder(o::LexCombinationOrder) = maybeunwrap(LexCombinationOrder(atomicorders(o.orders...)...))

removenesting(o, C) = C
removenesting(o::EmptyLexCombinationOrder, C) = C
removenesting(o::OtherLexCombinationOrder, C) = removenesting(Base.tail(o), C)
removenesting(o::KeyLexCombinationOrder, C) = removenesting(Base.tail(o), monomialordereltype(C))

function expansiontypes(P, spec...)
    order = monomialorder(spec...)
    if order isa KeyOrder
        return monomialorderkeytype(P), monomialordereltype(P)
    else
        C = remove_variables(P, namingscheme(order))
        M = monomialtype(atomicorder(order), exptype(P, namingscheme(order)))
        KeyedM = withkeys(order, P, M)
        UnnestedC = removenesting(order, C)
        return KeyedM, UnnestedC
    end
end

_coefftype(P, spec...) = expansiontypes(P, spec...)[2]

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
function expansion end

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

zerocoeff(m::Pair,    C::Type{<:AbstractArray}, a) = zerocoeff(m.second, C, a[m.first])
zerocoeff(m,          C,                        a) = zero(C)
zerocoeff(m,          C::Type{<:AbstractArray}, a) = [zerocoeff(m, eltype(C), ai) for ai in a]
function zerocoeff(m, C::Type{<:AbstractSparseArray}, a)
    res = spzeros(eltype(C), size(a)...)
    for (i, ai) in nzpairs(a)
        res[i] = zerocoeff(m, eltype(C), ai)
    end
    return res
end

keytype(::Type{Pair{S,T}}) where {S, T} = S
valtype(::Type{Pair{S,T}}) where {S, T} = T

splitkeyorders(::Type{M}, item::Pair{M}) where M = item.first, nothing, item.second

function splitkeyorders(M::Type, item::Pair)
    m1, m2, val = splitkeyorders(M, item.second)
    return m1, item.first => m2, val
end

function splitkeyorders(M::Type{<:Pair}, item::Pair)
    m1, m2, val = splitkeyorders(valtype(M), item.second)
    return item.first => m1, m2, val
end

reconstructone!(a, key::Nothing, val) = @inplace a += val
reconstructone!(a, key::Pair, val) = (a[key.first] = reconstructone!(a[key.first], key.second, val); a)

function reconstruct!(dest::Vector{Tuple{M, C}}, p, deconstructed, order) where {M, C}
    isempty(deconstructed) && return dest

    key(item) = begin
        m1, m2, val = splitkeyorders(M, item)
        # FIXME: this smells. Can I re-organize things
        # so this is not needed?
        if order isa KeyOrder
            m1 => nothing
        else
            m1
        end
    end

    sort!(deconstructed, lt=(a, b) -> Base.Order.lt(order, key(a), key(b)))

    curitem = popfirst!(deconstructed)
    curm1, curm2, curval = splitkeyorders(M, curitem)
    curc = zerocoeff(curm1, C, p)
    curc = reconstructone!(curc, curm2, curval)

    while !isempty(deconstructed)
        curitem = popfirst!(deconstructed)
        nextm1, curm2, curval = splitkeyorders(M, curitem)
        if curm1 != nextm1
            push!(dest, (curm1, curc))
            curm1 = nextm1
            curc = zerocoeff(curm1, C, p)
        end
        curc = reconstructone!(curc, curm2, curval)
    end
    push!(dest, (curm1, curc))
    return dest
end

_ofpolynomialtype(m, c) = m * c
_ofpolynomialtype(m::AbstractMonomial, c::AbstractArray) = m .* c
_ofpolynomialtype(m::AbstractMonomial, c) = _ofpolynomialtype(Term(m, c))
_ofpolynomialtype(t::Term{M,C}) where {M,C} = @assertvalid SparsePolynomial(M[monomial(t)], C[coefficient(t)])

deconstructmonomial(innerorder, m::AbstractMonomial) = begin
    M1 = monomialtype(innerorder, exptype(typeof(m), namingscheme(innerorder)))
    M2 = remove_variables(typeof(m), namingscheme(innerorder))
    return _splitmonomial(M1, M2, m)
end
deconstruct(innerorder, t::Term) = begin
    m1, c1 = deconstructmonomial(innerorder, monomial(t))
    return ((m1 * m2 => _ofpolynomialtype(c1, c2)) for (m2, c2) in deconstruct(innerorder, coefficient(t)))
end
deconstruct(innerorder, p::Polynomial) = (item for t in nzterms(p, order=monomialorder(p)) for item in deconstruct(innerorder, t))
deconstruct(innerorder, a::Number) = ((one(monomialtype(innerorder)), a),)
deconstruct(innerorder, a) = (
    m isa One ? (i => c) : (i => m => c)
    for (i, ai) in pairs(a) for (m, c) in deconstruct(innerorder, ai)
)

function expansion(p, spec...)
    order = monomialorder(spec...)
    M, C = expansiontypes(typeof(p), order)
    result = Tuple{M, C}[]

    deconstructed = collect(deconstruct(atomicorder(order), p))
    reconstruct!(result, p, deconstructed, order)

    return result
end

function expansion(t::Term, order::MonomialOrder)
    return expansion(polynomialtype(typeof(t))(t), order)
end

function expansion(a::AbstractMonomial, spec...)
    M, C = expansiontypes(typeof(a), spec...)
    c, m = _splitmonomial(C, M, a)
    return ((m, c),)
end

# -----------------------------------------------------------------------------
#
# Functions based on expansions: coefficients(), variable substitution, etc.
#
# -----------------------------------------------------------------------------

expand(p, spec...) = (
    (exponents(m, namingscheme(m)), c)
    for (m, c) in expansion(p, spec...)
)

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
function expandcoefficients(p, spec...)
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
function expansion_terms(p, spec...)
    return [
        _ofpolynomialtype(m, c)
        for (m,c) in expansion(p, spec...)
    ]
end

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
function coefficient(f, t::Union{<:Tuple, <:AbstractVector}, spec...)
    order = monomialorder(spec...)
    m = exp(monomialtype(order), t)
    for (w,p) in expansion(f, order)
        if w == m
            return p
        end
    end
    return zerocoeff(m, _coefftype(typeof(f), order), f)
end

function coefficient(f::Polynomial, t::Polynomial, spec...)
    ((w,p),) = expansion(t, spec...)
    p == 1 || throw(ArgumentError("Cannot get a coefficient for $t when symbols are $vars"))

    coefficient(f, w.e, spec...)
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
function constant_coefficient(f, spec...)
    order = monomialorder(spec...)
    for (w,p) in expansion(f, order)
        if isone(w)
            return p
        end
    end
    return zerocoeff(one(monomialtype(order)), _coefftype(typeof(f), order), f)
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
linear_coefficients(f, spec...) = linear_coefficients(f, monomialorder(spec...))

function linear_coefficients(f, spec::NamedMonomialOrder)
    return map(generators(monomialtype(spec))) do m
        coefficient(f, exponents(m, namingscheme(spec)), spec)
    end
end

function linear_coefficients(f, spec::NumberedMonomialOrder)
    res = spzeros(_coefftype(typeof(f), spec), 0)
    N = max_variable_index(namingscheme(spec), f)
    for (n, m) in enumerate(generators(monomialtype(spec)))
        n > N && break

        c = coefficient(f, exponents(m, namingscheme(spec)), spec)
        if !iszero(c)
            newlength = n
            # there is no resize!() because SparseVector is an
            # immutable struct
            res = SparseVector(newlength, res.nzind, res.nzval)
            res[n] = c
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
function deg(f::Polynomial, spec...)
    iszero(f) && return -1
    order = monomialorder(spec...)
    return maximum(deg(w, namingscheme(order)) for (w,p) in expansion(f, order))
end

deg(f::Number, spec...) = iszero(f) ? -1 : 0

# -----------------------------------------------------------------------------
#
# Helper functions for some of the macros below
#
# -----------------------------------------------------------------------------

order_from_expr(vars::NTuple{N,Symbol}) where N = monomialorder(vars...)
order_from_expr(vars::Tuple{Expr}) = (v = vars[1]; @assert(v.head == :ref && length(v.args) == 1); monomialorder(v.args[1], Inf))

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
    order = order_from_expr(symbols)
    quote
        constant_coefficient($(esc(f)), $order)
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
    order = order_from_expr(symbols)
    quote
        linear_coefficients($(esc(f)), $order)
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
    order = order_from_expr(symbols)
    quote
        expansion($(esc(f)), $order)
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
    order = order_from_expr(symbols)
    quote
        expand($(esc(f)), $order)
    end
end

macro expansion_terms(f, symbols...)
    order = order_from_expr(symbols)
    quote
        expansion_terms($(esc(f)), $order)
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
    order = order_from_expr(symbols)
    quote
        expandcoefficients($(esc(f)), $order)
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
    order = order_from_expr(symbols)
    quote
        deg($(esc(f)), $order)
    end
end

end
