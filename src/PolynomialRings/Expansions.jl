module Expansions

import PolynomialRings.NamedPolynomials: NamedPolynomial
import PolynomialRings.NamedPolynomials: _lossy_convert_monomial, names, polynomialtype
import PolynomialRings.Polynomials: Polynomial, termtype, monomialtype, terms
import PolynomialRings.Terms: Term, monomial, coefficient
import PolynomialRings: basering
import PolynomialRings.Monomials: AbstractMonomial, TupleMonomial

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
        # TODO: keep monomial exponent type
        ExpansionType = NamedPolynomial{Polynomial{Vector{Term{TupleMonomial{N,Int},Int}},:degrevlex},NamesExpansion}
        CoeffType = NamedPolynomial{Polynomial{Vector{Term{TupleMonomial{M,Int},C}},:degrevlex},NamesCoefficient}
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


end
