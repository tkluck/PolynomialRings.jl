module NamedPolynomials

import Base: promote_rule, convert, Bottom
import SparseArrays: SparseVector

import ..Constants: One
import ..MonomialOrderings: MonomialOrder, rulesymbol
import ..Monomials: TupleMonomial, VectorMonomial, AbstractMonomial, _construct, exptype, num_variables
import ..NamingSchemes: Named, Numbered, NamingScheme, numberedvariablename, remove_variables, isdisjoint, boundnames, ≺
import ..Polynomials:  NamedMonomial, NumberedMonomial, NamedTerm, NumberedTerm, TermOver, monomialorder, NamedOrder, NumberedOrder, polynomial_ring
import ..Polynomials: Polynomial, PolynomialOver, NamedPolynomial, NumberedPolynomial, PolynomialBy, PolynomialIn
import ..Terms: Term, basering, monomial, coefficient
import PolynomialRings: termtype, terms, namingscheme, variablesymbols, exptype, monomialtype, allvariablesymbols, iscanonical, canonicaltype, fullnamingscheme, fullboundnames

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

# fix method ambiguity
promote_rule(::Type{P}, ::Type{C}) where P<:PolynomialOver{C} where C <: Polynomial = P

function remove_variables(O::MonomialOrder, vars)
    O′ = remove_variables(namingscheme(O), vars)
    O′ == nothing && return nothing
    return MonomialOrder{rulesymbol(O), typeof(O′)}()
end

function remove_variables(::Type{M}, vars) where M <: TupleMonomial
    O = remove_variables(monomialorder(M), vars)
    O == nothing && return One
    N = length(variablesymbols(O))
    return TupleMonomial{N, exptype(M), typeof(O)}
 end

function remove_variables(::Type{T}, vars) where T <: Term
    M = remove_variables(monomialtype(T), vars)
    C = remove_variables(basering(T), vars)
    M == One && return C
    return Term{M, C}
end
function remove_variables(::Type{P}, vars) where P <: Polynomial
    M = remove_variables(monomialtype(P), vars)
    C = remove_variables(basering(P), vars)
    M == One && return C
    return Polynomial{M, C}
end
remove_variables(T::Type, vars) = T

fullnamingscheme(T::Type{<:Term}) = fullnamingscheme(basering(T)) * namingscheme(T)
fullnamingscheme(T::Type{<:Polynomial}) = fullnamingscheme(basering(T)) * namingscheme(T)
fullboundnames(T::Type{<:Term}) = boundnames(basering(T))
fullboundnames(T::Type{<:Polynomial}) = boundnames(basering(T))

_promote_rule(T1::Type{<:Polynomial}, T2::Type) = promote_rule(T1, T2)
_promote_rule(T1::Type, T2::Type) = promote_type(T1, T2)

function promote_rule(T1::Type{<:Polynomial}, T2::Type)
    if !isdisjoint(namingscheme(T1), fullboundnames(T2))
        T1′ = remove_variables(T1, fullboundnames(T2))
        return _promote_rule(T1′, T2)
    elseif fullnamingscheme(T1) ⊆ fullnamingscheme(T2)
        return _promote_rule(basering(T1), T2)
    elseif isdisjoint(namingscheme(T1), fullnamingscheme(T2))
        if (C = _promote_rule(basering(T1), T2)) != Bottom
            return Polynomial{monomialtype(T1), C}
        end
    end
    return Bottom
end

# -----------------------------------------------------------------------------
#
# Canonical types
#
# -----------------------------------------------------------------------------

promote_canonical_type(T1::Type, T2::Type) = promote_type(T1, T2)

function promote_canonical_type(T1::Type{<:Polynomial}, T2::Type)
    if !isdisjoint(namingscheme(T1), fullboundnames(T2))
        T1′ = remove_variables(T1, fullboundnames(T2))
        return promote_canonical_type(T1′, T2)
    else
        M = monomialtype(T1)
        C = promote_canonical_type(basering(T1), T2)
        return Polynomial{M, C}
    end
end

promote_canonical_type(T1::Type, T2::Type{<:Polynomial}) = promote_canonical_type(T2, T1)

function promote_canonical_type(T1::Type{<:Polynomial}, T2::Type{<:Polynomial})
    @assert iscanonical(T1) && iscanonical(T2)

    if !isdisjoint(namingscheme(T1), fullboundnames(T2))
        T1′ = remove_variables(T1, fullboundnames(T2))
        return promote_canonical_type(T1′, T2)
    elseif !isdisjoint(namingscheme(T2), fullboundnames(T1))
        T2′ = remove_variables(T2, fullboundnames(T1))
        return promote_canonical_type(T1, T2′)
    elseif namingscheme(T1) ≺ namingscheme(T2)
        M = monomialtype(T2)
        C = promote_canonical_type(T1, basering(T2))
        return Polynomial{M, C}
    elseif namingscheme(T2) ≺ namingscheme(T1)
        M = monomialtype(T1)
        C = promote_canonical_type(basering(T1), T2)
        return Polynomial{M, C}
    else
        M = promote_type(monomialtype(T1), monomialtype(T2))
        C = promote_type(basering(T1), basering(T2))
        return Polynomial{M, C}
    end
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

polynomialtype(T::Type{<:Term}) = Polynomial{monomialtype(T), basering(T)}

function canonicaltype(P::Type{<:PolynomialOver{<:Polynomial}})
    C = canonicaltype(basering(P))
    M1 = monomialtype(C)
    M2 = canonicaltype(monomialtype(P))
    if namingscheme(M1) ≺ namingscheme(M2)
        P′ = Polynomial{M2, C}
    elseif namingscheme(M2) ≺ namingscheme(M1)
        C1 = basering(C)
        P′ = Polynomial{M1, Polynomial{M2, C1}}
    else
        M = promote_type(M1, M2)
        C1 = basering(C)
        P′ = Polynomial{M, C1}
    end
    if P′ == P
        return P
    else
        # recursive sort
        return canonicaltype(P′)
    end
end
function canonicaltype(P::Type{<:Polynomial})
    C = canonicaltype(basering(P))
    M = canonicaltype(monomialtype(P))
    return Polynomial{M, C}
end
@generated function canonicaltype(::Type{M}) where M <: NamedMonomial
    N = num_variables(M)
    I = exptype(M)
    names = tuple(sort(collect(variablesymbols(M)))...)
    res = TupleMonomial{N, I, MonomialOrder{:degrevlex, Named{names}}}
    return :($res)
end
function canonicaltype(M::Type{<:NumberedMonomial})
    I = exptype(M)
    name = numberedvariablename(M)
    VectorMonomial{SparseVector{I,Int}, I, MonomialOrder{:degrevlex, Numbered{name, Inf}}}
end
canonicaltype(T::Type{<:Term}) = termtype(canonicaltype(polynomialtype(T)))
canonicaltype(T::Type) = T

iscanonical(::Type) = true
iscanonical(M::Type{<:AbstractMonomial}) = iscanonical(namingscheme(M)) && rulesymbol(monomialorder(M)) == :degrevlex

function _promote_result(T, S, LTR, RTL)
    if LTR == RTL
        return LTR
    else
        @assert canonicaltype(LTR) == canonicaltype(RTL)
        return canonicaltype(LTR)
    end
end

for T in [Term, Polynomial]
    @eval begin
        iscanonical(T::Type{<:$T}) = iscanonical(fullnamingscheme(T))

        Base.promote_result(T::Type{<:$T}, S::Type{<:$T}, LTR::Type{Bottom}, RTL::Type{<:$T}) = RTL
        Base.promote_result(T::Type{<:$T}, S::Type{<:$T}, LTR::Type{<:$T}, RTL::Type{Bottom}) = LTR
        Base.promote_result(T::Type, S::Type{<:$T}, LTR::Type{Bottom}, RTL::Type{<:$T}) = RTL
        Base.promote_result(T::Type{<:$T}, S::Type, LTR::Type{<:$T}, RTL::Type{Bottom}) = LTR
        Base.promote_result(T::Type, S::Type{<:$T}, LTR::Type{Bottom}, RTL::Type{Bottom}) = promote_canonical_type(canonicaltype(T), canonicaltype(S))
        Base.promote_result(T::Type{<:$T}, S::Type, LTR::Type{Bottom}, RTL::Type{Bottom}) = promote_canonical_type(canonicaltype(T), canonicaltype(S))
        Base.promote_result(T::Type{<:$T}, S::Type{<:$T}, LTR::Type{Bottom}, RTL::Type{Bottom}) = promote_canonical_type(canonicaltype(T), canonicaltype(S))
        Base.promote_result(T::Type{<:$T}, S::Type{<:$T}, LTR::Type{<:$T}, RTL::Type{<:$T}) = _promote_result(T, S, LTR, RTL)
        Base.promote_result(T::Type{<:$T}, S::Type, LTR::Type{<:$T}, RTL::Type{<:$T}) = _promote_result(T, S, LTR, RTL)
        Base.promote_result(T::Type, S::Type{<:$T}, LTR::Type{<:$T}, RTL::Type{<:$T}) = _promote_result(T, S, LTR, RTL)

    end
end

end
