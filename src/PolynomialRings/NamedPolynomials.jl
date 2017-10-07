module NamedPolynomials

import PolynomialRings: termtype, terms, namestype, variablesymbols, exptype
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

@generated function _convert_monomial(::Type{Named{dest}}, ::Type{Named{src}}, monomial::AbstractMonomial) where dest where src
    for s in src
        if !(s in dest)
            throw(ArgumentError("Cannot convert variables $src to variables $dest"))
        end
    end
    :( _lossy_convert_monomial(Named{dest}, Named{src}, monomial) )
end

@generated function _lossy_convert_monomial(::Type{Named{dest}}, ::Type{Named{src}}, monomial::AbstractMonomial) where dest where src
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
    T = TupleMonomial{length(dest), exptype(monomial), Named{dest}}
    return :( $T($converter, $degree ) )
end

function promote_rule(::Type{P1}, ::Type{P2}) where P1 <: Polynomial where P2 <: Polynomial
    if basering(P1) <: Polynomial && namestype(basering(P1)) === namestype(P2)
        return P1
    elseif basering(P2) <: Polynomial && namestype(basering(P2)) === namestype(P1)
        return P2
    elseif namestype(P1) <: Named && namestype(P2) <: Named
        AllNames = Set()
        union!(AllNames, variablesymbols(P1))
        union!(AllNames, variablesymbols(P2))
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

function convert(::Type{P1}, a::P2) where P1 <: Polynomial where P2 <: Polynomial
    f = t->termtype(P1)( _convert_monomial(namestype(P1), namestype(P2), monomial(t)), coefficient(t) )
    # there used to be map(f, terms(a)) here, but type inference makes that an
    # Array{Any}. That's why we explicitly write termtype(P1)[ .... ] .
    converted_terms = termtype(P1)[f(t) for t in terms(a)]
    sort!(converted_terms, order=monomialorder(P1))
    P1(converted_terms)
end

end
