"""
Singleton types for Zero, One and MinusOne. Used for base cases of
recursions, e.g. in expansion().
"""
module Constants

using PolynomialRings.Monomials: AbstractMonomial
using PolynomialRings.Terms: Term
using PolynomialRings.Polynomials: Polynomial

abstract type Constant <: Number end

struct One <: Constant end
struct Zero <: Constant end
struct MinusOne <: Constant end

_N = Union{Number,AbstractMonomial,Term,Polynomial}

import Base: promote_rule, convert, +, *, -, zero, one

promote_rule(::Type{N}, ::Type{C}) where N <: _N where C <: Constant = N

convert(::Type{N}, ::One) where N <: _N = one(N)
convert(::Type{N}, ::Zero) where N <: _N = zero(N)
convert(::Type{N}, ::MinusOne) where N <: _N = -one(N)

*(x, ::One) = x
*(::One, x) = x
*(x::_N, ::One) = x
*(::One, x::_N) = x

*(x, ::MinusOne) = -x
*(::MinusOne, x) = -x
*(x::_N, ::MinusOne) = -x
*(::MinusOne, x::_N) = -x

+(x, ::Zero) = x
-(x, ::Zero) = x
*(x, ::Zero) = zero(x)
+(x::_N, ::Zero) = x
-(x::_N, ::Zero) = x
*(x::_N, ::Zero) = zero(x)
+(::Zero, x) = x
-(::Zero, x) = x
*(::Zero, x) = zero(x)
+(::Zero, x::_N) = x
-(::Zero, x::_N) = x
*(::Zero, x::_N) = zero(x)

zero(::Type{C}) where C <: Constant = Zero()
one(::Type{C})  where C <: Constant = One()

# fix one particular ambiguity

promote_rule(::Type{P}, ::Type{C}) where {P<:Polynomial,C<:Constant} = P


end
