"""
Singleton types for Zero, One and MinusOne. Used for base cases of
recursions, e.g. in expansion().
"""
module Constants

import Base: promote_rule, convert, +, *, -, zero, one
import Base: to_power_type
import Base: iszero, isone

import InPlace: inplace!

import ..Monomials: AbstractMonomial
import ..Polynomials: Polynomial
import ..Terms: Term

abstract type Constant <: Number end

struct One <: Constant end
struct Zero <: Constant end
struct MinusOne <: Constant end

+(::One) = One()
+(::Zero) = Zero()
+(::MinusOne) = MinusOne()
-(::One) = MinusOne()
-(::Zero) = Zero()
-(::MinusOne) = One()

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

*(::One, ::One) = One()
*(::Zero, ::Zero) = Zero()
*(::Zero, ::One) = Zero()
*(::One, ::Zero) = Zero()

+(::Zero, ::Zero) = Zero()
+(::Zero, ::One) = One()
+(::One, ::Zero) = One()

-(::Zero, ::Zero) = Zero()
-(::Zero, ::One) = MinusOne()
-(::One, ::Zero) = One()

zero(::Type{C}) where C <: Constant = Zero()
one(::Type{C})  where C <: Constant = One()

iszero(::Constant) = false
isone(::Constant) = false
iszero(::Zero) = true
isone(::One) = true

to_power_type(::Zero) = Zero()
to_power_type(::One) = One()

for N = [Number, AbstractMonomial, Term, Polynomial]
    @eval begin
        promote_rule(::Type{T}, ::Type{C}) where {T<:$N, C <: Constant} = T

        convert(::Type{T}, ::One)      where T<:$N = one(T)
        convert(::Type{T}, ::Zero)     where T<:$N = zero(T)
        convert(::Type{T}, ::MinusOne) where T<:$N = -one(T)

        convert(::Type{Union{T, One}}, ::One)           where T<:$N = One()
        convert(::Type{Union{T, Zero}}, ::Zero)         where T<:$N = Zero()
        convert(::Type{Union{T, MinusOne}}, ::MinusOne) where T<:$N = MinusOne()

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

for C in [One, Zero, MinusOne]
    @eval begin
        convert(::Type{$C}, ::$C) = $C()
    end
end

inplace!(::typeof(+), a::BigInt, b::BigInt, c::Zero) = (Base.GMP.MPZ.set!(a,b); a)
inplace!(::typeof(+), a::BigInt, b::Zero, c::BigInt) = (Base.GMP.MPZ.set!(a,c); a)
inplace!(::typeof(-), a::BigInt, b::BigInt, c::Zero) = (Base.GMP.MPZ.set!(a,b); a)
inplace!(::typeof(-), a::BigInt, b::Zero, c::BigInt) = (Base.GMP.MPZ.neg!(a,c); a)

end
