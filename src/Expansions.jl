module Expansions

import Base: @pure
import Base: diff
import SparseArrays: spzeros, SparseVector, AbstractSparseArray

import InPlace: @inplace

import ..AbstractMonomials: AbstractMonomial, exptype, exponents
import ..Constants: One
import ..MonomialOrderings: MonomialOrder, NamedMonomialOrder, NumberedMonomialOrder
import ..MonomialOrderings: monomialorderkeytype, monomialordereltype
import ..NamingSchemes: Named, Numbered, NamingScheme, EmptyNamingScheme, remove_variables
import ..NamingSchemes: NamedVariable, variable
import ..Polynomials: Polynomial, PolynomialIn, monomialtype, monomialorder, SparsePolynomial
import ..Signatures: Sig
import ..StandardMonomialOrderings: MonomialOrdering, LexCombinationOrder, KeyOrder
import ..StandardMonomialOrderings: maybeunwrap
import ..Terms: Term, monomial, coefficient
import ..Util: @assertvalid, nzpairs, similarzeros
import PolynomialRings: deg, generators, max_variable_index, basering
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
withkeys(o::KeyLexCombinationOrder, P, M) = Sig{
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

function expansiontype(P, spec...)
    order = expansionorder(spec...)
    if order isa KeyOrder
        return Sig{monomialorderkeytype(P), monomialordereltype(P)}
    else
        C = remove_variables(P, namingscheme(order))
        M = monomialtype(atomicorder(order), exptype(P, namingscheme(order)))
        UnnestedC = removenesting(order, C)
        KeyedM = withkeys(order, P, Term{M, UnnestedC})
        return KeyedM
    end
end

_coefftype(P, spec...) = basering(expansiontype(P, spec...))

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

expansionorder(spec...) = monomialorder(spec...)
expansionorder(spec::Polynomial...) = expansionorder(map(variable, spec)...)

expansion(p::Number, spec...) = (Term(one(monomialtype(spec...)), p),)

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

keytype(::Type{Sig{S,T}}) where {S, T} = S
valtype(::Type{Sig{S,T}}) where {S, T} = T

leaf(s) = s
leaf(s::Sig) = leaf(s.second)
mapleaf(f, s) = f(s)
mapleaf(f, s::Sig) = Sig(s.first => mapleaf(f, s.second))

createitem(T::Type,                item, a) = convert(T, item)
createitem(T::Type{<:Term},          item, a) = Term(monomial(leaf(item)), createitem(basering(T), mapleaf(coefficient, item), a))

createitem(T::Type{<:Sig},           item::Sig, a) = Sig(item.first => createitem(valtype(T), item.second, a[item.first]))
createitem(T::Type{<:AbstractArray}, item::Sig, a) = begin
    res = T <: AbstractSparseArray ?
          spzeros(eltype(T), size(a)...) :
          zeros(eltype(T), size(a)...)
    res[item.first] = createitem(eltype(T), item.second, a[item.first])
    res
end

additem!(dest, src) = dest += src
additem!(dest::Term, src::Term) = begin
    @assert monomial(dest) == monomial(src)
    return Term(monomial(dest), coefficient(dest) + coefficient(src))
end
additem!(dest,      src::Sig) = (dest[src.first] = additem!(dest[src.first], src.second); dest)
additem!(dest::Sig, src::Sig) = Sig(dest.first => additem!(dest.second, src.second))

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

function reconstruct!(dest, p, deconstructed, order)
    T = expansiontype(typeof(p), order)
    C = basering(T)
    isempty(deconstructed) && return dest

    sort!(deconstructed, order=order)
    #@info "deconstructed" T deconstructed keys=map(i -> splitkeyorders(T, i), deconstructed) created=map(i -> createitem(T, i, p), deconstructed)

    cur = popfirst!(deconstructed)
    curitem = createitem(T, cur, p)::T
    #@info "first step" cur curitem
    while !isempty(deconstructed)
        nxt = popfirst!(deconstructed)
        nxtitem = createitem(T, nxt, p)::T
        if Base.Order.lt(order, cur, nxt)
            push!(dest, curitem)
            cur, curitem = nxt, nxtitem
        else
            #@info "update" curitem nxtitem
            curitem = additem!(curitem, nxtitem)::T
        end
    end
    push!(dest, curitem)
    return dest
end

_oftermtype(t::Term{M, C}, c::C) where {M, C} = Term(monomial(t), coefficient(t) * c)
_oftermtype(m::AbstractMonomial, c) = _oftermtype(Term(m, _ofpolynomialtype(c)))
_oftermtype(m::Sig, c) = Sig(m.first => _oftermtype(m.second, c))
_oftermtype(t::Term) = t
_ofpolynomialtype(c) = c
_ofpolynomialtype(m, c) = m * c
_ofpolynomialtype(m::AbstractMonomial, c::AbstractArray) = _ofpolynomialtype.(m, c)
_ofpolynomialtype(m::AbstractMonomial, c) = _ofpolynomialtype(Term(m, c))
_ofpolynomialtype(t::Term{M,C}) where {M,C} = @assertvalid SparsePolynomial(M[monomial(t)], C[coefficient(t)])

deconstructmonomial(M1, m::AbstractMonomial) = begin
    M2 = remove_variables(typeof(m), namingscheme(M1))
    return _splitmonomial(M1, M2, m)
end
deconstruct(M, t::Term) = begin
    m1, c1 = deconstructmonomial(M, monomial(t))
    # TODO: how to handle coefficients of array type?
    return (_oftermtype(m1 * monomial(c), _ofpolynomialtype(c1, coefficient(c))) for c in deconstruct(M, coefficient(t)))
end
deconstruct(M, p::Polynomial) = (
    item for t in expansion(p)
    for item in deconstruct(M, t)
)
deconstruct(M::Type{One}, a) = (a,)
deconstruct(M::Type{One}, t::Term) = (t,)
deconstruct(M::Type{One}, p::Polynomial) = (p,)
deconstruct(M, a) = (Term(one(M), a),)
deconstruct(M, a::Union{<:Tuple, <:AbstractArray, <:AbstractDict}) = (
    Sig(i => t)
    for (i, ai) in pairs(a) for t in deconstruct(M, ai)
)
deconstruct(M::Type{One}, a::Union{<:Tuple, <:AbstractArray, <:AbstractDict}) = (
    Sig(i => t)
    for (i, ai) in pairs(a) for t in deconstruct(M, ai)
)

expansion(p, spec...; kwds...) = expansion(p, expansionorder(spec...); kwds...)

function expansion(p, order::MonomialOrder; rev=false, tail=false)
    T = expansiontype(typeof(p), order)
    result = T[]
    innerorder = atomicorder(order)
    M1 = monomialtype(innerorder, exptype(typeof(p), namingscheme(innerorder)))

    deconstructed = collect(deconstruct(M1, p))
    reconstruct!(result, p, deconstructed, order)
    # The tail is everything but the leading monomial, which is in the end.
    # So confusingly, if `tail` is true we need to remove the _last_ element.
    tail && pop!(result)
    rev && reverse!(result)

    return result
end

function expansion(t::Term, order::MonomialOrder; kwds...)
    return expansion(polynomialtype(typeof(t))(t), order; kwds...)
end

function expansion(m::AbstractMonomial, order::MonomialOrder; kwds...)
    return expansion(polynomialtype(typeof(m))(m), order; kwds...)
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
    return [coefficient(t) for t in expansion(p, spec...)]
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
        for (m, c) in expansion(p, spec...)
    ]
end

_substitute(p::Polynomial, names::Named, values...) = _substitute(p, names, promote(values...)...)
_substitute(p::Polynomial, names::EmptyNamingScheme) = deepcopy(p)

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
_anyfn() = false
_anyfn(val::Function, vals...) = true
_anyfn(val, vals...) = _anyfn(vals...)

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

    if kwtupletype == NamedTuple{(),Tuple{}}
        return copy(p)
    elseif !_anyfn(values(kwargs)...)
        return _substitute(p, Named{tuple(vars...)}(), values(kwargs)...)
    elseif length(kwargs) == 1
        return _substitute(p, Numbered{vars[1], Inf}(), kwargs[1])
    else
        throw(ArgumentError("Don't know how to substitute $kwargs"))
    end

end

function substitute(p, substitutions::Pair...)
    order = expansionorder(map(first, substitutions)...)
    return _substitute(p, namingscheme(order), map(last, substitutions)...)
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
    order = expansionorder(spec...)
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
constant_coefficient(f, spec...) = constant_coefficient(f, namingscheme(expansionorder(spec...)))

function constant_coefficient(f, scheme::NamingScheme)
    for (w,p) in expansion(f, scheme)
        if isone(w)
            return p
        end
    end
    return zerocoeff(one(monomialtype(scheme)), _coefftype(typeof(f), scheme), f)
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
linear_coefficients(f, spec...) = linear_coefficients(f, expansionorder(spec...))

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
function deg(f::Polynomial, scheme::NamingScheme)
    iszero(f) && return -1
    return maximum(deg(t, scheme) for t in expansion(f))
end

deg(f::Polynomial, spec...) = deg(f, namingscheme(expansionorder(spec...)))
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

# -----------------------------------------------------------------------------
#
# Optimized versions for when storage format is the same as the requested one
#
# -----------------------------------------------------------------------------
function constant_coefficient(f::PolynomialIn{Scheme}, scheme::Scheme) where Scheme <: NamingScheme
    return f[one(monomialtype(f))]
end

function constant_coefficient(a::AbstractArray{<:Polynomial}, scheme::NamingScheme)
    C = _coefftype(eltype(a), scheme)
    res = similarzeros(a, C)
    for (i, ai) in nzpairs(a)
        res[i] = constant_coefficient(ai, scheme)
    end
    return res
end

end # module
