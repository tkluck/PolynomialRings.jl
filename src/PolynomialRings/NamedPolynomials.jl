module NamedPolynomials

import Base: promote_rule, convert

import ..Constants: One
import ..MonomialOrderings: MonomialOrder, rulesymbol
import ..Monomials: TupleMonomial, AbstractMonomial, _construct, exptype
import ..Polynomials:  NamedMonomial, NumberedPolynomial, monomialorder, NamedOrder, NumberedOrder
import ..Polynomials: Polynomial, PolynomialOver, NamedPolynomial, NumberedPolynomial, PolynomialBy, PolynomialIn
import ..Terms: Term, basering, monomial, coefficient
import ..NamingSchemes: Named, Numbered
import PolynomialRings: termtype, terms, namingscheme, variablesymbols, exptype, monomialtype, allvariablesymbols

# -----------------------------------------------------------------------------
#
# Generating symbols that do not conflict with existing ones
#
# -----------------------------------------------------------------------------
function unused_variable(P, a)
    E = exptype(P)
    N = max_variable_index(a)
    P(_construct(monomialtype(P), i->i==(N+1) ? one(E) : zero(E), N+1:N+1))
end
unused_variable(p::Polynomial)                  = unused_variable(typeof(p), p)
unused_variable(a::AbstractArray{<:Polynomial}) = unused_variable(eltype(a), a)

# -----------------------------------------------------------------------------
#
# Coefficient promotions when monomial type is the same
#
# -----------------------------------------------------------------------------
function promote_rule(P1::Type{<:PolynomialIn{M}}, P2::Type{<:PolynomialIn{M}}) where M<:AbstractMonomial
    return base_extend(P1, basering(P2))
end

# separate versions for N<:Named and N<:Numbered to resolve method ambiguity
# with the version for which P and p do not have the same names.
function convert(P::Type{<:PolynomialOver{C,O}}, p::PolynomialOver{D,O}) where {C,D,O<:NamedOrder}
    T = termtype(P)
    newterms = T[T(monomial(t), convert(C, coefficient(t))) for t in terms(p, order=O())]
    # in positive charactestic (e.g. C = ℤ/5ℤ), we may need to filter
    # terms that are zero from conversion.
    filter!(!iszero, newterms)
    P(newterms)
end
function convert(P::Type{<:PolynomialOver{C,O}}, p::PolynomialOver{D,O}) where {C,D,O<:NumberedOrder}
    T = termtype(P)
    newterms = T[T(monomial(t), convert(C, coefficient(t))) for t in terms(p, order=O())]
    # in positive charactestic (e.g. C = ℤ/5ℤ), we may need to filter
    # terms that are zero from conversion.
    filter!(!iszero, newterms)
    P(newterms)
end
# and short-circuit the non-conversions
convert(P::Type{<:PolynomialOver{C,O}}, p::PolynomialOver{C,O}) where {C,O<:NamedOrder} = p
convert(P::Type{<:PolynomialOver{C,O}}, p::PolynomialOver{C,O}) where {C,O<:NumberedOrder} = p
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

function promote_rule(::Type{P1}, ::Type{P2}) where P1 <: Polynomial where P2 <: Polynomial
    T = promote_rule(termtype(P1), termtype(P2))
    M = monomialtype(T)
    C = basering(T)
    return Polynomial{M, C}
end

_allfreevars(x::Type) = Set()
_allfreevars(x::Type{T}) where T<:Term{<:NamedMonomial} = union(variablesymbols(T), _allfreevars(basering(T)))
_allfreevars(x::Type{P}) where P<:NamedPolynomial = _allfreevars(termtype(P))
# all other vars are e.g. variables in a quotient ring or a number field. They
# can't be freely shuffled around and typically stay in the base ring when
# promotions need to happen
_allothervars(x::Type) = setdiff(allvariablesymbols(x), _allfreevars(x))
_coeff(x::Type) = x
_coeff(::Type{T}) where T<:Term = _coeff(basering(T))
_coeff(::Type{P}) where P<:NamedPolynomial = _coeff(basering(P))
_monomialtype(x::Type) = One
_monomialtype(x::Type{P}) where P<:NamedPolynomial = promote_type(monomialtype(P), _monomialtype(basering(P)))

function remove_variables(N::Named, vars...)
    result = [x for x in variablesymbols(N) if !(x in vars)]
    Named{tuple(result...)}()
end

function remove_variables(O::NamedOrder, vars...)
    O′ = remove_variables(namingscheme(O), vars...)
    MonomialOrder{rulesymbol(O), typeof(O′)}()
end

function remove_variables(::Type{M}, vars...) where M <: TupleMonomial
    O = remove_variables(monomialorder(M), vars...)
    N = length(variablesymbols(O))
    TupleMonomial{N, exptype(M), typeof(O)}
 end

function promote_rule(::Type{T1}, ::Type{T2}) where T1 <: Term where T2 <: Term
    C = promote_type(_coeff(T1), _coeff(T2))
    M = promote_type(
        monomialtype(T1), _monomialtype(basering(T1)),
        monomialtype(T2), _monomialtype(basering(T2)),
    )
    if !isempty(_allothervars(C))
        M = remove_variables(M, _allothervars(C)...)
    end
    return Term{M,C}
end

function promote_rule(::Type{M1}, ::Type{M2}) where M1 <: AbstractMonomial where M2 <: AbstractMonomial
    O = promote_rule(typeof(monomialorder(M1)), typeof(monomialorder(M2)))
    if O <: MonomialOrder
        N = length(variablesymbols(O))
        I = promote_type(exptype(M1), exptype(M2))
        return TupleMonomial{N, I, O}
    else
        return Union{}
    end
end

function promote_rule(::Type{P1}, ::Type{P2}) where P1 <: NamedPolynomial where P2 <: NumberedPolynomial
    return P2 ⊗ P1
end

function promote_rule(::Type{P1}, ::Type{P2}) where P1 <: NumberedPolynomial where P2 <: NamedPolynomial
    return promote_rule(P2, P1)
end

using PolynomialRings

function convert(::Type{P1}, a::P2) where P1 <: NamedPolynomial where P2 <: Polynomial
    T = termtype(P1)
    # Without the leading T[ ... ], type inference makes this an Array{Any}, so
    # it can't be omitted.
    converted_terms = T[ T(m,c) for (m,c) in PolynomialRings.Expansions._expansion(a, monomialorder(P1)) ]
    # zero may happen if conversion to the basering is lossy; e.g. mapping ℚ[α]
    # to the number field ℚ[α]/Ideal(α^2-2)
    # TODO: needs testing as soon as number fields are part of this package.
    filter!(!iszero, converted_terms)
    sort!(converted_terms, order=monomialorder(P1))
    P1(converted_terms)
end

convert(::Type{P}, a::P) where P <: NamedPolynomial = a
end
