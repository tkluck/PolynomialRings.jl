module NamedPolynomials

import PolynomialRings: termtype, terms, namestype, variablesymbols, exptype, monomialtype, allvariablesymbols
import PolynomialRings.Polynomials: Polynomial, monomialorder
import PolynomialRings.Terms: Term, basering, monomial, coefficient
import PolynomialRings.Monomials: TupleMonomial, AbstractMonomial
import PolynomialRings.VariableNames: Named, Numbered

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: promote_rule, convert

# -----------------------------------------------------------------------------
#
# Type definitions
#
# -----------------------------------------------------------------------------

NamedMonomial    = AbstractMonomial{<:Named}
NumberedMonomial = AbstractMonomial{<:Numbered}
NamedPolynomial    = Polynomial{<:AbstractVector{<:Term{<:NamedMonomial,   C}}} where C
NumberedPolynomial = Polynomial{<:AbstractVector{<:Term{<:NumberedMonomial,C}}} where C

# -----------------------------------------------------------------------------
#
# Promotions for different variable name sets
#
# -----------------------------------------------------------------------------

convert(::Type{M}, monomial::M) where M<:NamedMonomial = monomial

@generated function convert(::Type{M}, monomial::AbstractMonomial) where M<:NamedMonomial
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

_coeff(x::Type) = x
_coeff(::Type{P}) where P<:NamedPolynomial = _coeff(basering(P))
_exptype(x::Type) = Union{}
_exptype(::Type{P}) where P<:NamedPolynomial = promote_type(exptype(P), _exptype(basering(P)))

function promote_rule(::Type{P1}, ::Type{P2}) where P1 <: Polynomial where P2 <: Polynomial
    if namestype(P1) <: Named && namestype(P2) <: Named
        AllNames = Set()
        union!(AllNames, allvariablesymbols(P1))
        union!(AllNames, allvariablesymbols(P2))
        Symbols = sort(collect(AllNames))
        Names = tuple(Symbols...)
        N = length(Symbols)
        C = promote_type(_coeff(P1), _coeff(P2))
        I = promote_type(_exptype(P1), _exptype(P2))

        return Polynomial{Vector{Term{TupleMonomial{N, I, Named{Names}}, C}}, :degrevlex}
    else
        return Union{}
    end
end

function promote_rule(::Type{P1}, ::Type{P2}) where P1 <: NamedPolynomial where P2 <: NumberedPolynomial
    return P2 ⊗ P1
end

using PolynomialRings

function convert(::Type{P1}, a::P2) where P1 <: NamedPolynomial where P2 <: Polynomial
    T = termtype(P1)
    # Without the leading T[ ... ], type inference makes this an Array{Any}, so
    # it can't be omitted.
    converted_terms = T[ T(m,c) for (m,c) in PolynomialRings.Expansions._expansion(a, namestype(P1)) ]
    sort!(converted_terms, order=monomialorder(P1))
    P1(converted_terms)
end

convert(::Type{P}, a::P) where P <: NamedPolynomial = a
end
