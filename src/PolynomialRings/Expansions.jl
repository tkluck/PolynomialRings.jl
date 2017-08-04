module Expansions

import PolynomialRings.NamedPolynomials: NamedPolynomial, polynomial_ring
import PolynomialRings.NamedPolynomials: _convert_monomial, _lossy_convert_monomial, names, polynomialtype
import PolynomialRings.Polynomials: Polynomial, termtype, monomialtype, terms
import PolynomialRings.Terms: Term, monomial, coefficient
import PolynomialRings: basering
import PolynomialRings.Monomials: AbstractMonomial, TupleMonomial, exptype
import PolynomialRings.MonomialOrderings: MonomialOrder

import Iterators: groupby

"""
    monomialtype, coefficienttype = _expansion_types(R, Val{tuple(symbols...)})
"""
function _expansion_types(::Type{NP}, ::Type{Val{vars}}) where NP <: NamedPolynomial where vars
    all_vars = names(NP)
    remaining_vars = [v for v in all_vars if !(v in vars)]
    N = length(vars)
    M = length(remaining_vars)
    ExpType = exptype(monomialtype(polynomialtype(NP)))
    ExpansionType = NTuple{N,ExpType}
    C = basering(NP)
    if M == 0
        CoeffType = C
    else
        NamesCoefficient = tuple(remaining_vars...)
        CoeffType = NamedPolynomial{Polynomial{Vector{Term{TupleMonomial{M,ExpType},C}},:degrevlex},NamesCoefficient}
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
julia> R,(x,y) = polynomial_ring(Int, :x, :y);
julia> collect(expansion(x^3 + y^2, :y))
[((0,), 1 x^3), ((2,), 1)]
julia> collect(expansion(x^3 + y^2, :x, :y))
[((3,0), 1), ((0,2), 1)]
```
# See also
`@expansion(...)`, `@coefficient` and `coefficient`
"""
function expansion(p::NP, variables::Type{Val{vars}}) where NP <: NamedPolynomial where vars
    all_vars = names(NP)
    remaining_vars = [v for v in all_vars if !(v in vars)]

    if length(remaining_vars) == 0
        N = length(vars)
        NamesExpansion = tuple(vars...)
        ExpType = exptype(monomialtype(polynomialtype(NP)))
        ExpansionType = NTuple{N,ExpType}
        ResultType = Tuple{ExpansionType, basering(NP)}
        P = polynomialtype(NP)
        one_ = one(basering(p))

        f = t->_convert_monomial(Val{NamesExpansion}, Val{names(NP)}, monomial(t))

        return Channel(ctype=ResultType) do ch
            for t in terms(p.p)
                push!(ch, (f(t).e, coefficient(t)))
            end
        end
    else
        NamesExpansion = tuple(vars...)
        NamesCoefficient = tuple(remaining_vars...)
        N = length(vars)
        M = length(remaining_vars)

        C = basering(NP)
        ExpType = exptype(monomialtype(polynomialtype(NP)))
        ExpansionType = NTuple{N,ExpType}
        CoeffType = NamedPolynomial{Polynomial{Vector{Term{TupleMonomial{M,ExpType},C}},:degrevlex},NamesCoefficient}
        ResultType = Tuple{ExpansionType, CoeffType}

        f = t->_lossy_convert_monomial(Val{NamesExpansion},   Val{names(NP)}, monomial(t))
        g = t->_lossy_convert_monomial(Val{NamesCoefficient}, Val{names(NP)}, monomial(t))

        return Channel(ctype=ResultType) do ch
            separated_terms = [(f(t), g(t), coefficient(t)) for t in terms(p.p)]
            sort!(separated_terms, lt=(a,b)->Base.Order.lt(MonomialOrder{:degrevlex}(),a[1],b[1]))
            for term_group in groupby(x->x[1], separated_terms)
                expand_exponents = term_group[1][1].e
                coeff_terms = [Term(t[2], t[3]) for t in term_group]
                sort!(coeff_terms, order=MonomialOrder{:degrevlex}())
                p = CoeffType(polynomialtype(CoeffType)(coeff_terms))

                push!(ch, (expand_exponents, p))
            end
        end
    end
end

@inline expansion(p::NamedPolynomial, variables::Symbol...) = expansion(p, Val{variables})

function (p::NamedPolynomial)(; kwargs...)
    vars = [k for (k,v) in kwargs]
    values = [v for (k,v) in kwargs]
    sum( p * prod(v^k for (v,k) in zip(values,w)) for (w,p) in expansion(p, vars...) )
end

function (p::Array{NP})(; kwargs...) where NP <: NamedPolynomial
    map(p_i -> p_i(;kwargs...), p)
end

import Base: diff

function diff(p::NamedPolynomial, variable::Symbol)
    for (i,s) in enumerate(names(typeof(p)))
        if s == variable
            return typeof(p)(diff(p.p, i))
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
julia> R,(x,y) = polynomial_ring(Int, :x, :y);
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
function coefficient(f::NamedPolynomial, t::Tuple, vars::Symbol...)
    for (w,p) in expansion(f, vars...)
        if w == t
            return p
        end
    end
    ExpansionType, CoeffType = _expansion_types(typeof(f), Val{vars})
    return zero(CoeffType)
end

function coefficient(f::NamedPolynomial, t::NamedPolynomial, vars::Symbol...)
    ((w,p),) = expansion(t, vars...)
    p == 1 || throw(ArgumentError("Cannot get a coefficient for $t when symbols are $vars"))

    coefficient(f, w, vars...)
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
julia> R,(x,y) = polynomial_ring(Int, :x, :y);
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
    @expansion(f, var, [var...])

Return a collection of (monomial, coefficient) tuples decomposing f
into its consituent parts.

# Examples
```jldoctest
julia> R,(x,y) = polynomial_ring(Int, :x, :y);
julia> collect(@expansion(x^3 + y^2, y))
[(1, 1 x^3), (1 y^2, 1)]
julia> collect(@expansion(x^3 + y^2, x, y))
[(1 x^3, 1), (1 y^2, 1)]
```
# See also
`expansion(...)`, `@coefficient` and `coefficient`
"""
macro expansion(f, symbols...)
    R,vars = polynomial_ring(Int, symbols...)
    quote
        [
            (prod(v^k for (v,k) in zip($vars,w)), p)
            for (w,p) in expansion($(esc(f)), $symbols...)
        ]
    end
end

end
