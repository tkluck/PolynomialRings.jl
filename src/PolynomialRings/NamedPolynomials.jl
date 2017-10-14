module NamedPolynomials

import PolynomialRings: termtype, terms, namestype, variablesymbols, exptype, monomialtype
import PolynomialRings.Polynomials: Polynomial, monomialorder
import PolynomialRings.Terms: Term, basering, monomial, coefficient
import PolynomialRings.Monomials: TupleMonomial, AbstractMonomial
import PolynomialRings.VariableNames: Named

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: promote_rule, convert

# -----------------------------------------------------------------------------
#
# Promotions for different variable name sets
#
# -----------------------------------------------------------------------------

@generated function _convert_monomial(::Type{M}, monomial::AbstractMonomial) where M
    src = variablesymbols(monomial)
    dest = variablesymbols(M)
    for s in src
        if !(s in dest)
            throw(ArgumentError("Cannot convert variables $src to variables $dest"))
        end
    end
    :( _lossy_convert_monomial(M, monomial) )
end

@generated function _lossy_convert_monomial(::Type{M}, monomial::AbstractMonomial) where M
    src = variablesymbols(monomial)
    dest = variablesymbols(M)
    # create an expression that calls the tuple constructor. No arguments -- so far
    converter = :( tuple() )
    degree = :( +(0) )
    for d in dest
        # for every result field, add the constant 0 as an argument
        push!(converter.args, :( zero(exptype(monomial)) ))
        for (j,s) in enumerate(src)
            if d == s
                # HOWEVER, if it actually also exists in src, then replace the 0
                # by reading from exponent_tuple
                converter.args[end]= :( monomial[$j] )
                push!(degree.args,:( monomial[$j] ))
                break
            end
        end
    end
    return :( M($converter, $degree ) )
end

NamedPolynomial = Polynomial{<:AbstractVector{<:Term{<:AbstractMonomial{<:Named},C}}} where C
_allnames(x::Type) = []
_allnames(::Type{P}) where P<:NamedPolynomial = union(_allnames(basering(P)), variablesymbols(P))

function promote_rule(::Type{P1}, ::Type{P2}) where P1 <: Polynomial where P2 <: Polynomial
    if namestype(P1) <: Named && namestype(P2) <: Named
        AllNames = Set()
        union!(AllNames, _allnames(P1))
        union!(AllNames, _allnames(P2))
        Symbols = sort(collect(AllNames))
        Names = tuple(Symbols...)
        N = length(Symbols)
        C = promote_type(basering(P1), basering(P2))
        I = promote_type(exptype(P1), exptype(P2))

        return Polynomial{Vector{Term{TupleMonomial{N, I, Named{Names}}, C}}, :degrevlex}
    else
        return Union{}
    end
end

using PolynomialRings

function convert(::Type{P1}, a::P2) where P1 <: NamedPolynomial where P2 <: Polynomial
    T = termtype(P1)
    # there used to be map(f, terms(a)) here, but type inference makes that an
    # Array{Any}. That's why we explicitly write termtype(P1)[ .... ] .
    converted_terms = T[ T(m,c) for (m,c) in PolynomialRings.Expansions._expansion(a, namestype(P1)) ]
    sort!(converted_terms, order=monomialorder(P1))
    P1(converted_terms)
end

convert(::Type{P}, a::P) where P <: NamedPolynomial = a
end
