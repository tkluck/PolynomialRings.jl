module Conversions

import Base: +,*,-,==,/,//
import Base: div, rem, divrem
import Base: promote_op, promote
import Base: promote_rule, convert, Bottom
import LinearAlgebra: UniformScaling

import ..Modules: AbstractModuleElement
import ..Monomials: AbstractMonomial, total_degree
import ..Operators: RedType
import ..Polynomials: Polynomial, termtype, monomialtype, basering, terms
import ..Polynomials: PolynomialOver, NamedPolynomial
import ..Terms: Term, monomial, coefficient
import PolynomialRings: fraction_field, integers, base_extend, base_restrict, namingscheme
import PolynomialRings: ⊗, base_extend, base_restrict
import PolynomialRings: xdiv, xrem, xdivrem

# -----------------------------------------------------------------------------
#
# Contructor-style conversions
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

function convert(::Type{P}, a::C) where P<:PolynomialOver{C} where C <: Polynomial
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
function base_extend(t::T, ::Type{C}) where T<:Term where C
    TT = promote_type(T, C)
    CC = basering(TT)
    return TT(monomial(t), unalias(CC, coefficient(t)))
end

function base_extend(p::P, ::Type{C}) where P<:Polynomial where C
    # Our implementation of promote_rule is not symmetric: it prefers extending
    # the basering of the LHS. For example:
    #     promote_rule(@ring(ℤ[x]), @ring(ℤ[y])) == @ring(ℤ[y][x])
    # see NamedPolynomials module. That's exactly the behaviour we want
    # for base_extend.
    PP = promote_rule(P, C)
    if PP == Bottom
        # if that yields no result, just apply a symmetric promote_type.
        PP = promote_type(P, C)
    end
    return PP(p)
end

base_extend(p::P)      where P <: Union{Term,Polynomial} = base_extend(p, fraction_field(basering(p)))
base_extend(::Type{P}) where P <: Union{Term,Polynomial} = base_extend(P, fraction_field(basering(P)))

base_extend(x, ::Type{C}) where C = convert(promote_type(typeof(x), C), x)

# -----------------------------------------------------------------------------
#
# Operations (potentially) needing base extension
#
# -----------------------------------------------------------------------------
/(a::T,b::Number)   where T <: Term = promote_type(T,    float(typeof(b)))(a.m, a.c/b)
//(a::T,b::Number)  where T <: Term = promote_type(T, fraction_field(typeof(b)))(a.m, a.c//b)

function /(a::P, b::Number) where P <: Polynomial
    P′ = promote_type(P, float(typeof(b)))
    T′ = termtype(P′)
    newterms = T′[t/b for t in terms(a)]
    P′(newterms)
end

function //(a::P, b::Number) where P <: Polynomial
    P′ = promote_type(P, fraction_field(typeof(b)))
    T′ = termtype(P′)
    newterms = T′[t//b for t in terms(a)]
    P′(newterms)
end

function convert(::Type{T1}, t::T2) where T1<:Term{M} where T2<:Term{M} where M
    T1(monomial(t), convert(basering(T1), coefficient(t)))
end

# short-circuit non-conversion case
convert(::Type{T}, t::T) where T <: Term{M} where M = t

# -----------------------------------------------------------------------------
#
# Promoting numbers to polynomials (possibly using base extension)
#
# -----------------------------------------------------------------------------
convert(::Type{P}, a::C) where P <: Polynomial where C<:Number = P(convert(basering(P), a))

# resolve ambiguity between C a coefficient and C a number
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


convert(::Type{T}, a::C) where T <: Term{M} where M where C<:Number = promote_type(T,C)(one(M), deepcopy(a))

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
        return unalias(C, coefficient(terms(a)[1]))
    else
        throw(InexactError(:convert, C, a))
    end
end

function convert(C::Type{<:Number}, a::Polynomial)
    if length(terms(a)) == 0
        return zero(C)
    elseif length(terms(a)) == 1 && total_degree(monomial(terms(a)[1])) == 0
        return unalias(C, coefficient(terms(a)[1]))
    else
        throw(InexactError(:convert, C, a))
    end
end

# fix abbiguity
function convert(::Type{C}, a::P) where P <: PolynomialOver{C} where C <: Number
    if length(terms(a)) == 0
        return zero(C)
    elseif length(terms(a)) == 1 && total_degree(monomial(terms(a)[1])) == 0
        return unalias(C, coefficient(terms(a)[1]))
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

# -----------------------------------------------------------------------------
#
# Promotions for more complicated functions
#
# -----------------------------------------------------------------------------
function promote_vector(a::S,b::AbstractVector{T}) where {S,T<:Polynomial}
    U = promote_type(S, T)
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
xdiv(a::Number, b::AbstractVector{<:Polynomial})    = xdiv(promote_vector(a, b)...)
xrem(a::Number, b::AbstractVector{<:Polynomial})    = xrem(promote_vector(a, b)...)
xdivrem(a::Number, b::AbstractVector{<:Polynomial}) = xdivrem(promote_vector(a, b)...)


# -----------------------------------------------------------------------------
#
# Avoid Matrix{Any} results arising from the use of promote_op in the
# Base implementation
#
# -----------------------------------------------------------------------------
promote_op(f, P::Type{<:Polynomial}, Q::Type{<:Polynomial}) = promote_type(P, Q)

# -----------------------------------------------------------------------------
#
# Support e.g. (x^2 + y^2)*I
#
# -----------------------------------------------------------------------------
"""
    _UniformScaling{T}

Fulfils the same role as LinearAlgebra.UniformScaling, but
without requiring that T <: Number.
"""
struct _UniformScaling{T}
    λ::T
end
*(x::AbstractVector, J::_UniformScaling) = x * J.λ
*(J::_UniformScaling, x::AbstractVector) = J.λ * x
*(x::AbstractMatrix, J::_UniformScaling) = x * J.λ
*(J::_UniformScaling, x::AbstractMatrix) = J.λ * x
for P in [Number, AbstractMonomial, Term, Polynomial] @eval begin
    *(x::$P, J::_UniformScaling) = _UniformScaling(x*J.λ)
    *(J::_UniformScaling, x::$P) = _UniformScaling(J.λ*x)
end end
*(J::_UniformScaling, I::UniformScaling)  = _UniformScaling(J.λ * I.λ)
*(I::UniformScaling, J::_UniformScaling)  = _UniformScaling(I.λ * J.λ)

for P in [AbstractMonomial, Term, Polynomial] @eval begin
    *(x::$P, J::UniformScaling) = _UniformScaling(x*J.λ)
    *(J::UniformScaling, x::$P) = _UniformScaling(J.λ*x)
end end

promote(x::AbstractMatrix, J::_UniformScaling) = (x, J.λ*one(x))
promote(J::_UniformScaling, x::AbstractMatrix) = (J.λ*one(x), x)

+(J::_UniformScaling, x) = +(promote(J, x)...)
-(J::_UniformScaling, x) = -(promote(J, x)...)
==(J::_UniformScaling, x) = ==(promote(J, x)...)
+(x, J::_UniformScaling) = +(promote(x, J)...)
-(x, J::_UniformScaling) = -(promote(x, J)...)
==(x, J::_UniformScaling) = ==(promote(x, J)...)

+(I::_UniformScaling, J::_UniformScaling) = _UniformScaling(I.λ + J.λ)
-(I::_UniformScaling, J::_UniformScaling) = _UniformScaling(I.λ - J.λ)
*(I::_UniformScaling, J::_UniformScaling) = _UniformScaling(I.λ * J.λ)
==(I::_UniformScaling, J::_UniformScaling) = I.λ == J.λ

end
