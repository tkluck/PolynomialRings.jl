"""
Singleton types for Zero, One and MinusOne. Used for base cases of
recursions, e.g. in expansion().
"""
module Constants

import Base: iszero, isone
import Base: promote_rule, convert, +, *, -, zero, one
import Base: to_power_type

import InPlace: inplace!

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
*(::MinusOne, ::MinusOne) = One()
*(::Zero, ::One) = Zero()
*(::Zero, ::MinusOne) = Zero()
*(::One, ::Zero) = Zero()
*(::MinusOne, ::Zero) = Zero()

+(::Zero, ::Zero) = Zero()
+(::Zero, ::One) = One()
+(::One, ::Zero) = One()
+(::One, ::MinusOne) = Zero()
+(::MinusOne, ::One) = Zero()

-(::Zero, ::Zero) = Zero()
-(::Zero, ::One) = MinusOne()
-(::One, ::Zero) = One()
-(::One, ::One) = Zero()
-(::MinusOne, ::MinusOne) = Zero()

zero(::Type{C}) where C <: Constant = Zero()
one(::Type{C})  where C <: Constant = One()

iszero(::Constant) = false
isone(::Constant) = false
iszero(::Zero) = true
isone(::One) = true

to_power_type(::Zero) = Zero()
to_power_type(::One) = One()

inplace!(::typeof(+), a::BigInt, b::BigInt, c::Zero) = (Base.GMP.MPZ.set!(a,b); a)
inplace!(::typeof(+), a::BigInt, b::Zero, c::BigInt) = (Base.GMP.MPZ.set!(a,c); a)
inplace!(::typeof(-), a::BigInt, b::BigInt, c::Zero) = (Base.GMP.MPZ.set!(a,b); a)
inplace!(::typeof(-), a::BigInt, b::Zero, c::BigInt) = (Base.GMP.MPZ.neg!(a,c); a)

end
