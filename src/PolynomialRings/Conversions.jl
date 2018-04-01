module Conversions

import PolynomialRings.Polynomials: Polynomial, termtype, monomialtype, basering, terms
import PolynomialRings.Polynomials: PolynomialOver
import PolynomialRings.Terms: Term, monomial, coefficient
import PolynomialRings.Monomials: AbstractMonomial, total_degree
import PolynomialRings.Operators: RedType
import PolynomialRings: fraction_field, integers, base_extend, base_restrict, namestype

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: promote_rule, convert
import Base: +,*,-,==,/,//
import PolynomialRings: ⊗, base_extend, base_restrict
import Base: div, rem, divrem

# -----------------------------------------------------------------------------
#
# No-op promotions
#
# -----------------------------------------------------------------------------
(::Type{P})(a::P) where P <: Polynomial = a
convert(::Type{P}, x::P) where P <: Polynomial = x

# -----------------------------------------------------------------------------
#
# Promoting coefficients to polynomials
#
# -----------------------------------------------------------------------------

promote_rule(::Type{Polynomial{V,O}}, ::Type{C}) where V <: AbstractVector{T} where T <: Term{M,C} where {O,M,C} = Polynomial{V,O}

function convert(::Type{P}, a::C) where P<:Polynomial{V} where V <: AbstractVector{T} where T <: Term{M,C} where {M,C}
    if iszero(a)
        return zero(P)
    else
        return P([T(one(M),a)])
    end
end

# -----------------------------------------------------------------------------
#
# Base restriction
#
# -----------------------------------------------------------------------------
base_restrict(::Type{Term{M,C1}}, ::Type{C2}) where {M,C1,C2} = Term{M, base_restrict(C1,C2)}
base_restrict(::Type{Polynomial{V,O}}, ::Type{C}) where V<:AbstractVector{T} where {O,T,C} = Polynomial{Vector{base_restrict(T,C)}, O}

function base_restrict(t::T, ::Type{C}) where T<:Term where C
    TT = base_restrict(T, C)
    CC = basering(TT)
    return TT(monomial(t), CC(coefficient(t)))
end

function base_restrict(p::P, ::Type{C}) where P<:Polynomial where C
    PP = base_restrict(P, C)
    T = termtype(PP)
    return PP(T[ base_restrict(t, C) for t in terms(p) ])
end

base_restrict(p::P)      where P <: Union{Term,Polynomial} = base_restrict(p, integers(basering(p)))
base_restrict(::Type{P}) where P <: Union{Term,Polynomial} = base_restrict(P, integers(basering(P)))
# -----------------------------------------------------------------------------
#
# Base extension
#
# -----------------------------------------------------------------------------
base_extend(::Type{Term{M,C1}}, ::Type{C2}) where {M,C1,C2} = Term{M, base_extend(C1,C2)}
base_extend(::Type{Polynomial{V,O}}, ::Type{C}) where V<:AbstractVector{T} where {O,T,C} = Polynomial{Vector{base_extend(T,C)}, O}

function base_extend(t::T, ::Type{C}) where T<:Term where C
    TT = base_extend(T, C)
    CC = basering(TT)
    return TT(monomial(t), CC(coefficient(t)))
end

function base_extend(p::P, ::Type{C}) where P<:Polynomial where C
    PP = base_extend(P, C)
    T = termtype(PP)
    return PP(T[ base_extend(t, C) for t in terms(p) ])
end

base_extend(p::P)      where P <: Union{Term,Polynomial} = base_extend(p, fraction_field(basering(p)))
base_extend(::Type{P}) where P <: Union{Term,Polynomial} = base_extend(P, fraction_field(basering(P)))

# -----------------------------------------------------------------------------
#
# Operations (potentially) needing base extension
#
# -----------------------------------------------------------------------------
/(a::T,b::Number)   where T <: Term = base_extend(T,    float(typeof(b)))(a.m, a.c/b)
//(a::T,b::Number)  where T <: Term = base_extend(T, fraction_field(typeof(b)))(a.m, a.c//b)
/(a::P,b::Number)   where P <: Polynomial = base_extend(P,   float(typeof(b)))([t/b  for t in terms(a)])
//(a::P,b::Number)  where P <: Polynomial = base_extend(P,fraction_field(typeof(b)))([t//b for t in terms(a)])

# -----------------------------------------------------------------------------
#
# Promoting numbers to polynomials (possibly using base extension)
#
# -----------------------------------------------------------------------------
promote_rule(::Type{P}, ::Type{C}) where {P <: Polynomial, C<:Number} = base_extend(P,C)
convert(::Type{P}, a::C) where {P <: Polynomial, C<:Number} = P(basering(P)(a))

# resolve ambiguity between C a coefficient and C a number
promote_rule(::Type{Polynomial{V,O}}, ::Type{C}) where V <: AbstractVector{T} where T <: Term{M,C} where {O,M,C<:Number} = Polynomial{V,O}
function convert(::Type{P}, a::C) where P<:Polynomial{V,O} where V <: AbstractVector{T} where T <: Term{M,C} where {O,M,C<:Number}
    if iszero(a)
        return zero(P)
    else
        return P([T(one(M),a)])
    end
end

# -----------------------------------------------------------------------------
#
# Promoting scalars to terms
#
# -----------------------------------------------------------------------------

promote_rule(::Type{T}, ::Type{C}) where T <: Term where C<:Number = base_extend(T,C)

convert(::Type{T}, a::C) where T <: Term{M} where M where C<:Number = base_extend(T,C)(one(M), a)

# -----------------------------------------------------------------------------
#
# Promoting scalar + monomial to a term
#
# -----------------------------------------------------------------------------

promote_rule(::Type{M}, ::Type{C}) where M <: AbstractMonomial where C<:Number = Term{M,C}

# -----------------------------------------------------------------------------
#
# Promoting terms to polynomials
#
# -----------------------------------------------------------------------------

promote_rule(::Type{P}, ::Type{T}) where P <: Polynomial{<:AbstractArray{T}} where T <: Term = P

convert(::Type{P}, a::T) where P <: Polynomial{<:AbstractArray{T}} where T <: Term = iszero(a) ? zero(P) : P([a])


# -----------------------------------------------------------------------------
#
# Promoting monomials to terms
#
# -----------------------------------------------------------------------------

promote_rule(::Type{T}, ::Type{M}) where T <: Term{M,C} where {M<:AbstractMonomial,C} = T

convert(::Type{T}, a::M) where T <: Term{M,C} where {M<:AbstractMonomial,C} = T(a,one(C))

# -----------------------------------------------------------------------------
#
# Promoting monomials to polynomials
#
# -----------------------------------------------------------------------------

promote_rule(::Type{P}, ::Type{M}) where P <: Polynomial{<:AbstractArray{T}} where T <: Term{M} where M<:AbstractMonomial = P

convert(::Type{P}, a::M) where P <: Polynomial{<:AbstractArray{T}} where T <: Term{M} where M<:AbstractMonomial = P([convert(T, a)])

# -----------------------------------------------------------------------------
#
# Converting constant polynomials to the basering
#
# -----------------------------------------------------------------------------
function convert(::Type{C}, a::P) where P <: PolynomialOver{C} where C
    if length(terms(a)) == 0
        return zero(C)
    elseif length(terms(a)) == 1 && total_degree(monomial(terms(a)[1])) == 0
        return coefficient(terms(a)[1])
    else
        throw(InexactError())
    end
end


# -----------------------------------------------------------------------------
#
# Implicit typecasts (like what we'd get if Polynomial <: Number)
#
# -----------------------------------------------------------------------------
+(a::P1,b::P2) where {P1<:Polynomial,P2<:Polynomial} = +(promote(a,b)...)
*(a::P1,b::P2) where {P1<:Polynomial,P2<:Polynomial} = *(promote(a,b)...)
-(a::P1,b::P2) where {P1<:Polynomial,P2<:Polynomial} = -(promote(a,b)...)
==(a::P1,b::P2) where {P1<:Polynomial,P2<:Polynomial} = ==(promote(a,b)...)

_C = Union{Number, AbstractMonomial, Term}
_P = Union{Term,Polynomial}
+(a::C,b::P) where P<:_P where C<:_C = +(promote(a,b)...)
+(a::P,b::C) where P<:_P where C<:_C = +(promote(a,b)...)
*(a::C,b::P) where P<:_P where C<:_C = *(promote(a,b)...)
*(a::P,b::C) where P<:_P where C<:_C = *(promote(a,b)...)
-(a::C,b::P) where P<:_P where C<:_C = -(promote(a,b)...)
-(a::P,b::C) where P<:_P where C<:_C = -(promote(a,b)...)
==(a::P,b::C) where P<:_P where C<:_C = ==(promote(a,b)...)
==(a::C,b::P) where P<:_P where C<:_C = ==(promote(a,b)...)

+(a::Number,b::AbstractMonomial) = +(promote(a,b)...)
+(a::AbstractMonomial,b::Number) = +(promote(a,b)...)
*(a::Number,b::AbstractMonomial) = *(promote(a,b)...)
*(a::AbstractMonomial,b::Number) = *(promote(a,b)...)
-(a::Number,b::AbstractMonomial) = -(promote(a,b)...)
-(a::AbstractMonomial,b::Number) = -(promote(a,b)...)
==(a::AbstractMonomial,b::Number) = ==(promote(a,b)...)
==(a::Number,b::AbstractMonomial) = ==(promote(a,b)...)
# -----------------------------------------------------------------------------
#
# Polynomials with polynomial coefficients
#
# -----------------------------------------------------------------------------
"""
    ⊗(a::Polynomial, b::Polynomial)

Construct a polynomial with polynomial coefficients, by promoting a with the type of the coefficients of b.
"""

function ⊗(a::P1, b::P2) where P1 <: Polynomial where P2 <: Polynomial
    P = P1⊗P2
    @assert basering(P) === base_extend(P1, basering(P2))
    l = P(base_extend(a, basering(P2)))
    r = base_extend(b, P1)
    @assert typeof(l) === typeof(r)
    l * r
end

⊗(::Type{P1}, ::Type{P2}) where P1 <: Polynomial where P2 <: Polynomial{<:AbstractVector{T}} where T = base_extend(P2, P1)

# -----------------------------------------------------------------------------
#
# Polynomials with polynomial coefficients: resolve ambiguities
#
# -----------------------------------------------------------------------------

# Resolve ambiguity with the convert method that takes care of canonical mappings
# between polynomial rings
function convert(::Type{P}, a::C) where P<:Polynomial{V} where V <: AbstractVector{T} where T <: Term{M,C} where {M,C<:Polynomial}
    if iszero(a)
        return zero(P)
    else
        return P([T(one(M),a)])
    end
end

# Don't duplicate variable names as a result of base_extend
function base_extend(::Type{Term{M,C1}}, ::Type{C2}) where {M,C1,C2<:Polynomial}
    if namestype(C2) == namestype(M)
        Term{M, base_extend(C1,basering(C2))}
    else
        Term{M, base_extend(C1,C2)}
    end
end


# -----------------------------------------------------------------------------
#
# Use Term as a polynomial
#
# -----------------------------------------------------------------------------
promote_rule(::Type{P}, ::Type{T}) where P <: Polynomial{V} where V <: AbstractVector{T} where T <: Term = P
convert(::Type{P}, a::T) where P <: Polynomial{V} where V <: AbstractVector{T} where T <: Term = P([a])


# -----------------------------------------------------------------------------
#
# Promotions for more complicated functions
#
# -----------------------------------------------------------------------------
function promote_vector(a::S,b::AbstractVector{T}) where {S,T<:Polynomial}
    U = typejoin(promote_rule(S,T), promote_rule(T,S))
    if U === Union{}
        throw(TypeError())
    else
        return (U(a), map(U,b))
    end
end

div(a::Polynomial, b::AbstractVector{<:Polynomial})    = div(promote_vector(a, b)...)
rem(a::Polynomial, b::AbstractVector{<:Polynomial})    = rem(promote_vector(a, b)...)
divrem(a::Polynomial, b::AbstractVector{<:Polynomial}) = divrem(promote_vector(a, b)...)
div(a::Number, b::AbstractVector{<:Polynomial})    = div(promote_vector(a, b)...)
rem(a::Number, b::AbstractVector{<:Polynomial})    = rem(promote_vector(a, b)...)
divrem(a::Number, b::AbstractVector{<:Polynomial}) = divrem(promote_vector(a, b)...)


# -----------------------------------------------------------------------------
#
# Avoid Matrix{Any} results arising from the use of promote_op in the
# Base implementation
#
# -----------------------------------------------------------------------------
import Base: promote_op
promote_op(f, ::Type{P}, ::Type{Q}) where P<:Polynomial where Q<:Polynomial = promote_type(P,Q)

end
