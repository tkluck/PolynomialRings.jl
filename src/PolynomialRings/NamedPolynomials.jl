module NamedPolynomials

import Base: promote_rule, convert, Bottom
import SparseArrays: SparseVector, issparse

import ..AbstractMonomials: AbstractMonomial, exptype, num_variables
import ..Constants: One
import ..MonomialOrderings: MonomialOrder, NamedMonomialOrder, NumberedMonomialOrder
import ..Monomials.TupleMonomials: TupleMonomial
import ..Monomials.VectorMonomials: VectorMonomial
import ..NamingSchemes: Named, Numbered, NamingScheme, EmptyNamingScheme
import ..NamingSchemes: numberedvariablename, remove_variables, isdisjoint, boundnames, canonicalscheme
import ..Polynomials:  NamedMonomial, NumberedMonomial, NamedTerm, NumberedTerm, TermOver, monomialorder
import ..Polynomials: Polynomial, PolynomialOver, NamedPolynomial, NumberedPolynomial, PolynomialBy, PolynomialIn, nzterms, SparsePolynomialOver, DensePolynomialOver
import ..StandardMonomialOrderings: MonomialOrdering, rulesymbol
import ..Terms: Term, basering, monomial, coefficient
import PolynomialRings: expansion
import PolynomialRings: termtype, namingscheme, variablesymbols, exptype, monomialtype, allvariablesymbols, iscanonical, canonicaltype, nestednamingscheme, fullboundnames, max_variable_index, polynomialtype

# short-circuit the non-conversions
convert(::Type{P}, p::P) where P <: SparsePolynomialOver{C,O} where {C,O<:NamedMonomialOrder} = p
convert(::Type{P}, p::P) where P <: SparsePolynomialOver{C,O} where {C,O<:NumberedMonomialOrder} = p
convert(::Type{P}, p::P) where P <: DensePolynomialOver{C,O} where {C,O<:NamedMonomialOrder} = p
convert(::Type{P}, p::P) where P <: DensePolynomialOver{C,O} where {C,O<:NumberedMonomialOrder} = p

# -----------------------------------------------------------------------------
#
# Promotions for different variable name sets
#
# -----------------------------------------------------------------------------

# fix method ambiguity
promote_rule(::Type{P}, ::Type{C}) where P<:PolynomialOver{C} where C <: Polynomial = P

function remove_variables(O::MonomialOrder, vars)
    O′ = remove_variables(namingscheme(O), vars)
    O′ == nothing && return nothing
    return MonomialOrdering{rulesymbol(O), typeof(O′)}()
end

function remove_variables(::Type{M}, vars) where M <: AbstractMonomial
    O = remove_variables(monomialorder(M), vars)
    O == nothing && return One
    return monomialtype(O, exptype(M))
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
    return polynomialtype(M, C, sparse=issparse(P))
end
remove_variables(T::Type, vars) = T

nestednamingscheme(T::Type{<:Term}) = nestednamingscheme(basering(T)) * namingscheme(T)
nestednamingscheme(T::Type{<:Polynomial}) = nestednamingscheme(basering(T)) * namingscheme(T)
fullboundnames(T::Type{<:Term}) = fullboundnames(basering(T))
fullboundnames(T::Type{<:Polynomial}) = fullboundnames(basering(T))

_promote_rule(T1::Type{<:Polynomial}, T2::Type) = promote_rule(T1, T2)
_promote_rule(T1::Type,               T2::Type) = (res = promote_type(T1, T2); res === Any ? Bottom : res)

@generated function promote_rule(::Type{T1}, ::Type{T2}) where T1 <: Polynomial where T2
    if !isdisjoint(namingscheme(T1), fullboundnames(T2))
        # FIXME(tkluck): this loses information on the exptype associated to
        # the namingscheme of T1.
        T1′ = remove_variables(T1, fullboundnames(T2))
        return _promote_rule(T1′, T2)
    elseif nestednamingscheme(T1) ⊆ nestednamingscheme(T2)
        # FIXME(tkluck): this loses information on the exptype associated to
        # the namingscheme of T1.
        return polynomialtype(_promote_rule(basering(T1), T2))
    elseif isdisjoint(namingscheme(T1), nestednamingscheme(T2))
        if (C = _promote_rule(basering(T1), T2)) !== Bottom
            return polynomialtype(monomialtype(T1), C, sparse=issparse(T1))
        end
    end
    return Bottom
end

function promote_rule(T1::Type{<:Term}, T2::Type)
    if !isdisjoint(namingscheme(T1), fullboundnames(T2))
        T1′ = remove_variables(T1, fullboundnames(T2))
        return _promote_rule(T1′, T2)
    elseif nestednamingscheme(T1) ⊆ nestednamingscheme(T2)
        return _promote_rule(basering(T1), T2)
    elseif isdisjoint(namingscheme(T1), nestednamingscheme(T2))
        if (C = _promote_rule(basering(T1), T2)) !== Bottom
            # TODO: replace by termtype(m, c) function
            return Term{monomialtype(T1), C}
        end
    end
    return Bottom
end


# -----------------------------------------------------------------------------
#
# Canonical types
#
# -----------------------------------------------------------------------------

joinsparse(x, y) = true
joinsparse(x::Type{<:Polynomial}, y) = issparse(x)
joinsparse(x, y::Type{<:Polynomial}) = issparse(y)
joinsparse(x::Type{<:Polynomial}, y::Type{<:Polynomial}) = issparse(x) && issparse(y)

≺(a::Numbered, b::Named) = !isempty(b)
≺(a::Numbered, b::Numbered) = numberedvariablename(a) < numberedvariablename(b)
≺(a::Named, b::Named) = isempty(a) && !isempty(b)
≺(a::Named, b::Numbered) = isempty(a)

promote_canonical_type(T1::Type, T2::Type) = promote_type(T1, T2)

promote_canonical_type(T1::Type, T2::Type{<:Polynomial}) = promote_canonical_type(T2, T1)

promote_canonical_type(T1::Type{<:Polynomial}, T2::Type{<:Polynomial}) = invoke(promote_canonical_type, Tuple{Type{<:Polynomial}, Type}, T1, T2)

function promote_canonical_type(T1::Type{<:Polynomial}, T2::Type)
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
        return polynomialtype(M, C, sparse=issparse(T2))
    elseif namingscheme(T2) ≺ namingscheme(T1)
        M = monomialtype(T1)
        C = promote_canonical_type(basering(T1), T2)
        return polynomialtype(M, C, sparse=issparse(T1))
    else
        M = promote_type(monomialtype(T1), monomialtype(T2))
        C = promote_type(basering(T1), basering(T2))
        return polynomialtype(M, C, sparse=joinsparse(T1, T2))
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

function convert(::Type{P1}, a::P2) where P1 <: Polynomial where P2 #<: Polynomial
    res = zero(P1)
    for (m, c) in expansion(a, monomialorder(P1))
        push!(res, Term(m, c))
    end
    return res
end

function canonicaltype(P::Type{<:PolynomialOver{<:Polynomial}})
    C = canonicaltype(basering(P))
    M1 = monomialtype(C)
    M2 = canonicaltype(monomialtype(P))
    if namingscheme(M1) ≺ namingscheme(M2)
        P′ = polynomialtype(M2, C, sparse=issparse(P))
    elseif namingscheme(M2) ≺ namingscheme(M1)
        C1 = basering(C)
        P′ = polynomialtype(M1, polynomialtype(M2, C1), sparse=issparse(C))
    else
        M = promote_type(M1, M2)
        C1 = basering(C)
        P′ = polynomialtype(M, C1, sparse=joinsparse(P, C))
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
    return polynomialtype(M, C, sparse=issparse(P))
end
@generated function canonicaltype(::Type{M}) where M <: NamedMonomial
    N = num_variables(M)
    I = exptype(M)
    names = tuple(sort(collect(variablesymbols(M)))...)
    res = TupleMonomial{N, I, MonomialOrdering{:degrevlex, Named{names}}}
    return :($res)
end
function canonicaltype(M::Type{<:NumberedMonomial})
    I = exptype(M)
    name = numberedvariablename(M)
    VectorMonomial{SparseVector{I,Int}, I, MonomialOrdering{:degrevlex, Numbered{name, Inf}}}
end
canonicaltype(T::Type{<:Term}) = termtype(canonicaltype(polynomialtype(T)))
canonicaltype(T::Type) = T

iscanonical(::Type) = true
iscanonical(M::Type{<:AbstractMonomial}) = iscanonical(namingscheme(M)) && rulesymbol(monomialorder(M)) == :degrevlex

iscanonical(T::Type{<:Term})       = iscanonical(nestednamingscheme(T))
iscanonical(P::Type{<:Polynomial}) = iscanonical(nestednamingscheme(P))

@generated function _promote_result(::Type{T}, ::Type{S}, ::Type{LTR}, ::Type{RTL}) where {T, S, LTR, RTL}
    if LTR == Bottom && RTL != Bottom
        return RTL
    elseif RTL == Bottom && LTR != Bottom
        return LTR
    elseif LTR == RTL && LTR != Bottom
        return LTR
    else
        if namingscheme(T) == namingscheme(S)
            M = promote_type(monomialtype(T), monomialtype(S))
            C = promote_type(basering(T), basering(S))
            return polynomialtype(M, C, sparse=joinsparse(T, S))
        else
            return promote_canonical_type(canonicaltype(T), canonicaltype(S))
        end
    end
end

_promote_type(T, S) = _promote_result(T, S, promote_rule(T, S), promote_rule(S, T))

for T in [Term, Polynomial]
    @eval begin
        Base.promote_type(T::Type{<:$T}, S::Type)         = _promote_type(T, S)
        Base.promote_type(T::Type,       S::Type{<:$T})   = _promote_type(T, S)
        Base.promote_type(T::Type{<:$T}, S::Type{<:$T})   = _promote_type(T, S)

        Base.promote_type(T::Type{<:$T}, S::Type{Bottom}) = T
        Base.promote_type(T::Type{Bottom}, S::Type{<:$T}) = S
    end
end
for (T1, T2) in [(Term, Polynomial), (Polynomial, Term)]
    @eval begin
        Base.promote_type(T::Type{<:$T1}, S::Type{<:$T2}) = _promote_type(T, S)
    end
end

"""
    R = minring(f)

The smallest ring that faithfully contains `f`, i.e. the
intersection of all rings `R` that faithfully contain `f`.
"""
function minring end

minring(x::Integer) = typemin(Int) <= x <= typemax(Int) ? Int : BigInt
minring(x::Rational) = denominator(x) == 1 ? minring(numerator(x)) : typeof(x)
minring(x::Real) = round(x) ≈ x ? minring(Integer(x)) : typeof(x)
minring(x::Complex) = real(x) ≈ x ? minring(real(x)) : typeof(x)
minring(x) = typeof(x)

function minring(f::NamedPolynomial)
    base = minring(f.coeffs...)

    m = prod(monomial(t) for t in nzterms(f))
    nz = findall(!iszero, m.e)
    syms = variablesymbols(namingscheme(f))
    isempty(nz) ? base : polynomialtype(Named{syms[nz]}(), base, sparse=issparse(f))
end

function minring(f::NumberedPolynomial)
    base = minring(f.coeffs...)

    m = prod(monomial(t) for t in nzterms(f))
    isone(m) ? base : polynomialtype(namingscheme(f), base, sparse=issparse(f))
end

"""
    R = minring(fs...)

The smallest ring that faithfully contains all `f ∈ fs`
"""
minring(fs...) = promote_type(minring.(fs)...)


"""
    g = ofminring(f)

Shorthand for `convert(minring(f), f)`
"""
ofminring(f) = convert(minring(f), f)

end
