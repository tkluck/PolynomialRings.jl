module Conversions

import Base: +,*,-,==,/,//
import Base: div, rem, divrem
import Base: promote_op
import Base: promote_rule, convert

import ..Modules: AbstractModuleElement
import ..Monomials: AbstractMonomial, total_degree
import ..Operators: RedType
import ..Polynomials: Polynomial, termtype, monomialtype, basering, terms
import ..Polynomials: PolynomialOver, NamedPolynomial
import ..Terms: Term, monomial, coefficient
import PolynomialRings: fraction_field, integers, base_extend, base_restrict, namestype
import PolynomialRings: ⊗, base_extend, base_restrict

# -----------------------------------------------------------------------------
#
# Fallback for v0.7
#
# -----------------------------------------------------------------------------
(::Type{P})(a) where P <: Polynomial = convert(P, a)

# -----------------------------------------------------------------------------
#
# No-op promotions
#
# -----------------------------------------------------------------------------
(::Type{P})(a::P) where P <: Polynomial = a
convert(::Type{P}, x::P) where P <: Polynomial = x

# -----------------------------------------------------------------------------
#
# Convert and un-alias when necessary
#
# -----------------------------------------------------------------------------
unalias(::Type{T}, a::T) where T = deepcopy(a)
unalias(::Type{T}, a::S) where {T,S} = T(a)

# -----------------------------------------------------------------------------
#
# Promoting coefficients to polynomials
#
# -----------------------------------------------------------------------------

promote_rule(::Type{P}, ::Type{C}) where P<:PolynomialOver{C} where C = P

function convert(::Type{P}, a::C) where P<:PolynomialOver{C} where C
    if iszero(a)
        return zero(P)
    else
        T = termtype(P)
        M = monomialtype(P)
        return P([T(one(M),deepcopy(a))])
    end
end

# -----------------------------------------------------------------------------
#
# Base restriction
#
# -----------------------------------------------------------------------------
base_restrict(::Type{Term{M,C1}}, ::Type{C2}) where {M,C1,C2} = Term{M, base_restrict(C1,C2)}
base_restrict(::Type{Polynomial{M,C1}}, ::Type{C2}) where {M,C1,C2} = Polynomial{M, base_restrict(C1,C2)}

function base_restrict(t::T, ::Type{C}) where T<:Term where C
    TT = base_restrict(T, C)
    CC = basering(TT)
    return TT(monomial(t), unalias(CC, coefficient(t)))
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
base_extend(::Type{Polynomial{M,C1}}, ::Type{C2}) where {M,C1,C2} = Polynomial{M, base_extend(C1,C2)}

function base_extend(t::T, ::Type{C}) where T<:Term where C
    TT = base_extend(T, C)
    CC = basering(TT)
    return TT(monomial(t), unalias(CC, coefficient(t)))
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

function convert(::Type{T1}, t::T2) where T1<:Term{M} where T2<:Term{M} where M
    T1(monomial(t), convert(basering(T1), coefficient(t)))
end

# -----------------------------------------------------------------------------
#
# Promoting numbers to polynomials (possibly using base extension)
#
# -----------------------------------------------------------------------------
promote_rule(::Type{P}, ::Type{C}) where {P <: Polynomial, C<:Number} = base_extend(P,C)
convert(::Type{P}, a::C) where P <: Polynomial where C<:Number = P(basering(P)(a))

# resolve ambiguity between C a coefficient and C a number
promote_rule(::Type{P}, ::Type{C}) where P<:PolynomialOver{C} where C<:Number = P
function convert(::Type{P}, a::C)  where P<:PolynomialOver{C} where C<:Number
    if iszero(a)
        return zero(P)
    else
        T = termtype(P)
        M = monomialtype(P)
        return P([T(one(M),deepcopy(a))])
    end
end

# -----------------------------------------------------------------------------
#
# Promoting scalars to terms
#
# -----------------------------------------------------------------------------

promote_rule(::Type{T}, ::Type{C}) where T <: Term where C<:Number = base_extend(T,C)

convert(::Type{T}, a::C) where T <: Term{M} where M where C<:Number = base_extend(T,C)(one(M), deepcopy(a))

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

promote_rule(::Type{P}, ::Type{T}) where P <: Polynomial{M,C} where T <: Term{M,C} where {M,C} = P

convert(::Type{P}, a::T) where P <: Polynomial{M,C} where T <: Term{M,C} where {M,C}  = iszero(a) ? zero(P) : P([deepcopy(a)])


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

promote_rule(::Type{P}, ::Type{M}) where P <: Polynomial{M} where M = P

convert(::Type{P}, a::M) where P <: Polynomial{M} where M = P([convert(termtype(P), a)])

# -----------------------------------------------------------------------------
#
# Converting constant polynomials to the basering
#
# -----------------------------------------------------------------------------
function convert(::Type{C}, a::P) where P <: PolynomialOver{C} where C
    if length(terms(a)) == 0
        return zero(C)
    elseif length(terms(a)) == 1 && total_degree(monomial(terms(a)[1])) == 0
        return deepcopy(coefficient(terms(a)[1]))
    else
        throw(InexactError(:convert, C, a))
    end
end


# -----------------------------------------------------------------------------
#
# Implicit typecasts (like what we'd get if Polynomial <: Number)
#
# -----------------------------------------------------------------------------
for op in [:+, :*, :-, :(==)]
    for C in [Number, AbstractMonomial, Term] @eval begin
        $op(a::$C,b::Polynomial)  = $op(promote(a,b)...)
        $op(a::Polynomial,b::$C)  = $op(promote(a,b)...)
    end end
    for C in [Number, AbstractMonomial] @eval begin
        $op(a::$C,b::Term)  = $op(promote(a,b)...)
        $op(a::Term,b::$C)  = $op(promote(a,b)...)
    end end
    for C in [Number] @eval begin
        $op(a::$C,b::AbstractMonomial)  = $op(promote(a,b)...)
        $op(a::AbstractMonomial,b::$C)  = $op(promote(a,b)...)
    end end
    @eval $op(a::Polynomial, b::Polynomial) = $op(promote(a,b)...)
end

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

⊗(::Type{P1}, ::Type{P2}) where P1 <: Polynomial where P2 <: Polynomial = base_extend(P2, P1)

# -----------------------------------------------------------------------------
#
# Polynomials with polynomial coefficients: resolve ambiguities
#
# -----------------------------------------------------------------------------

# Resolve ambiguity with the convert method that takes care of canonical mappings
# between polynomial rings
function convert(::Type{P}, a::C) where P <: NamedPolynomial{C} where C<:Polynomial
    if iszero(a)
        return zero(P)
    else
        T = termtype(P)
        M = monomialtype(P)
        return P([T(one(M),deepcopy(a))])
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

div(a::AbstractModuleElement, b::AbstractVector{<:AbstractModuleElement})    = div(promote_vector(a, b)...)
rem(a::AbstractModuleElement, b::AbstractVector{<:AbstractModuleElement})    = rem(promote_vector(a, b)...)
divrem(a::AbstractModuleElement, b::AbstractVector{<:AbstractModuleElement}) = divrem(promote_vector(a, b)...)
div(a::Number, b::AbstractVector{<:Polynomial})    = div(promote_vector(a, b)...)
rem(a::Number, b::AbstractVector{<:Polynomial})    = rem(promote_vector(a, b)...)
divrem(a::Number, b::AbstractVector{<:Polynomial}) = divrem(promote_vector(a, b)...)


# -----------------------------------------------------------------------------
#
# Avoid Matrix{Any} results arising from the use of promote_op in the
# Base implementation
#
# -----------------------------------------------------------------------------
promote_op(f, ::Type{P}, ::Type{Q}) where P<:Polynomial where Q<:Polynomial = promote_type(P,Q)

end
