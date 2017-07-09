module Expansions

import PolynomialRings.NamedPolynomials: NamedPolynomial
import PolynomialRings.NamedPolynomials: _lossy_convert_monomial, names, polynomialtype
import PolynomialRings.Polynomials: Polynomial, termtype, monomialtype, terms
import PolynomialRings.Terms: Term, monomial, coefficient
import PolynomialRings: basering
import PolynomialRings.Monomials: AbstractMonomial, TupleMonomial, exptype

import Iterators: groupby


function expansion(p::NP, variables::Type{T}) where NP <: NamedPolynomial where T <: Tuple
    all_vars = Symbol[fieldtype(names(NP),i) for i in 1:nfields(names(NP))]
    vars = Symbol[fieldtype(T,i) for i in 1:nfields(T)]
    remaining_vars = [v for v in all_vars if !(v in vars)]

    if length(remaining_vars) == 0
        ResultType = Tuple{NP, basering(NP)}
        P = polynomialtype(NP)
        one_ = one(basering(p))
        return Channel(ctype=ResultType) do ch
            for t in terms(p.p)
                push!(ch, (NP(P([ termtype(P)(monomial(t), one_) ])), coefficient(t)))
            end
        end
    else
        NamesExpansion = Tuple{vars...}
        NamesCoefficient = Tuple{remaining_vars...}
        N = length(vars)
        M = length(remaining_vars)

        C = basering(NP)
        ExpType = exptype(monomialtype(polynomialtype(NP)))
        ExpansionType = NamedPolynomial{Polynomial{Vector{Term{TupleMonomial{N,ExpType},Int}},:degrevlex},NamesExpansion}
        CoeffType = NamedPolynomial{Polynomial{Vector{Term{TupleMonomial{M,ExpType},C}},:degrevlex},NamesCoefficient}
        ResultType = Tuple{ExpansionType, CoeffType}

        f = t->_lossy_convert_monomial(NamesExpansion,   names(NP), monomial(t))
        g = t->_lossy_convert_monomial(NamesCoefficient, names(NP), monomial(t))

        return Channel(ctype=ResultType) do ch
            separated_terms = [(f(t), g(t), coefficient(t)) for t in terms(p.p)]
            sort!(separated_terms, lt=(a,b)->isless(a[1],b[1],Val{:degrevlex}))
            for term_group in groupby(x->x[1], separated_terms)
                expand_term = Term(term_group[1][1], 1)
                coeff_terms = [Term(t[2], t[3]) for t in term_group]
                sort!(coeff_terms, lt=(a,b)->isless(monomial(a),monomial(b),Val{:degrevlex}))
                w = ExpansionType(polynomialtype(ExpansionType)([ expand_term ]))
                p = CoeffType(polynomialtype(CoeffType)(coeff_terms))

                push!(ch, (w, p))
            end
        end
    end
end

expansion(p::NamedPolynomial, variables::Symbol...) = expansion(p, Tuple{variables...})

function (p::NamedPolynomial)(; kwargs...)
    vars = [k for (k,v) in kwargs]
    values = [v for (k,v) in kwargs]
    sum( w.p.terms[1](values...)*p for (w,p) in expansion(p, vars...) )
end

function (p::Array{NP})(; kwargs...) where NP <: NamedPolynomial
    map(p_i -> p_i(;kwargs...), p)
end

import Base: diff

function diff(p::NamedPolynomial, variable::Symbol)
    T = names(typeof(p))

    for i in 1:nfields(T)
        if fieldtype(T,i) == variable
            return typeof(p)(diff(p.p, i))
        end
    end
    throw(ArgumentError("Variable $variable does not appear in $(typeof(p))"))
end

function coefficient(f::NamedPolynomial, t::Tuple, vars::Symbol...)
    for (w,p) in expansion(f, vars...)
        m =monomial(w.p.terms[1])
        if all(m[i] == t_i for (i,t_i) in enumerate(t))
            return p
        end
    end
    return zero(typeof(p))
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

macro coefficient(f, monomial)
    t,vars = _parse_monomial_expression(monomial)
    quote
        coefficient($(esc(f)), $t, $vars...)
    end
end

function coefficient(f::NamedPolynomial, t::NamedPolynomial, vars::Symbol...)
    ((w,p),) = expansion(t, vars...)
    p == 1 || throw(ArgumentError("Cannot get a coefficient for $t when symbols are $vars"))

    m = monomial(w.p.terms[1])
    tt = ntuple(i -> m[i], length(vars))

    coefficient(f, tt, vars...)
end

end
