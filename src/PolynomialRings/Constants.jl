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

import Base: promote_rule, convert, +, *, -, zero, one

*(x, ::One) = deepcopy(x)
*(::One, x) = deepcopy(x)

+(x, ::Zero) = deepcopy(x)
-(x, ::Zero) = deepcopy(x)
*(x, ::Zero) = zero(x)

*(x, ::MinusOne) = -x
*(::MinusOne, x) = -x

+(::Zero, x) = deepcopy(x)
-(::Zero, x) = -x
*(::Zero, x) = zero(x)

zero(::Type{C}) where C <: Constant = Zero()
one(::Type{C})  where C <: Constant = One()

for N = [Number, AbstractMonomial, Term, Polynomial]
    @eval begin
        promote_rule(::Type{T}, ::Type{C}) where {T<:$N, C <: Constant} = T

        convert(::Type{T}, ::One)      where T<:$N = one(T)
        convert(::Type{T}, ::Zero)     where T<:$N = zero(T)
        convert(::Type{T}, ::MinusOne) where T<:$N = -one(T)

        # fix method ambiguities
        *(x::$N, ::One) = deepcopy(x)
        *(::One, x::$N) = deepcopy(x)
        *(x::$N, ::MinusOne) = -x
        *(::MinusOne, x::$N) = -x

        +(x::$N, ::Zero) = deepcopy(x)
        -(x::$N, ::Zero) = deepcopy(x)
        *(x::$N, ::Zero) = zero(x)
        +(::Zero, x::$N) = deepcopy(x)
        -(::Zero, x::$N) = -x
        *(::Zero, x::$N) = zero(x)
    end
end

end
