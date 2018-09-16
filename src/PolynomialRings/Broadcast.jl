"""
Broadcasting for polynomials
----------------------------
This module uses Julia's advanced broadcasting support to implement:

1. Term-wise operations, i.e. for polynomials `f` and `g`,

         @. 3f + 4g

   is evaluated term-by-term without allocating intermediate `Polynomial`s for
   `3f` and `4g`.

2. In-place operations for `BigInt` coefficients, i.e. for `f ∈ @ring ℤ[x]`,

        f .*= 3

   is evaluated by multiplying `f`'s coefficients in-place. More generally, we
   can re-use the allocated `BigInt` objects in `f` even if the right-hand side
   operation is more complicated.

The most important combination of these operations is

    @. f = m1*f - m2*t*g

because this is the inner loop of reduction operations (and therefore of Gröbner basis
computations).

Implementation
--------------

### Julia broadcasting

Since julia 1.0, broadcasting is implemented by lowering e.g.

    f .= g .* h .+ j

to

    materialize!(f, broadcasted(+, broadcasted(*, g, h)))

In order to define our own behaviour, we override `broadcasted` and `materialize!`.

The function `broadcasted` decides on a `BroadcastStyle` based on its arguments.
This is typically used to decide the shape of the output, but we re-use this feature
to:
- use the `Termwise` style if all arguments are Polynomials or scalars;
- use the default behaviour otherwise.
In particular, this means that e.g. `f .* [1,2]` works exactly as you'd
expect by distributing over the vector elements.
This is achieved by overriding `BroadcastStyle(...)`.

### Eager evaluation

Some (many) operations do not actually benefit from term-wise operations:
e.g. we may as well evaluate

     g .* h

as `g * h` if `g` and `h` are polynomials. In this case, the allocation is probably
negligible compared to the time spent multiplying.

To achieve this, we override the function `broadcasted` with an eager implementation.
Only those operations that we _know_ to work term-wise efficiently get a more
specific override.

### Lazy evaluation

For the operations that _do_ work well term-wise, we implement a function
`iterterms` that takes a `Broadcasted` object or a scalar, and returns
an object that supports the `iterate` protocol.

The function `iterterms` is paired with a helper function `termsbound` that
tells the function `materialize!` how many terms to allocate. It is an upper
bound for how many terms the `iterterms` object may return.

### In-place evaluation

(write something about all the difficulties with potentially aliased coefficients
between different polynomials and between different terms of the same polynomial(!).
What's the wisest way to deal with this?)
"""
module Broadcast

using Base: RefValue
using Base.Broadcast: Style, AbstractArrayStyle, BroadcastStyle, Broadcasted, broadcasted
using PolynomialRings: monomialorder
using PolynomialRings.Constants: Zero, One
using PolynomialRings.Util: ParallelIter, Start
using PolynomialRings.MonomialOrderings: MonomialOrder
using PolynomialRings.Monomials: AbstractMonomial
using PolynomialRings.Terms: Term, monomial, coefficient
using PolynomialRings.Polynomials: Polynomial, PolynomialOver, PolynomialBy, terms, termtype

import Base.Broadcast: broadcastable, broadcasted, materialize, materialize!

broadcastable(p::AbstractMonomial) = Ref(p)
broadcastable(p::Term) = Ref(p)
broadcastable(p::Polynomial) = Ref(p)

struct Termwise{Order, P, inplace} <: BroadcastStyle end

BroadcastStyle(::Type{<:RefValue{P}}) where P<:Polynomial = Termwise{typeof(monomialorder(P)), P, false}()
BroadcastStyle(s::T, t::T) where T<:Termwise = s
BroadcastStyle(s::Termwise, t::AbstractArrayStyle{0}) = s
BroadcastStyle(s::Termwise, t::BroadcastStyle) = t

const BrTermwise{Order,P,inplace} = Broadcasted{Termwise{Order,P,inplace}}
const PlusMinus = Union{typeof(+), typeof(-)}

struct InPlace{P}
    x::P
end
Base.getindex(x::InPlace) = x.x

# Eagerly evaluate all expressions involving polynomials, except for the
# ones we explicitly know how to do. This ensures that e.g. operations
# with different variables/orders get eagerly evaluated.
# Note that by the time this function gets called, all the BroadcastStyles
# have already been bubbled up, so if we still have Termwise as the
# first argument, we are sure we only have polynomials and scalars.
broadcasted(::Termwise, op, a, b) = op(a[],b[])

struct TermsMap{Order,Inplace,Terms,Op}
    terms::Terms
    op::Op
end
Base.getindex(t::TermsMap) = t

TermsMap(op::Op, o::Order, terms::Terms, inplace=false) where {Op, Order,Terms} = TermsMap{Order,inplace,Terms,Op}(terms, op)
@inline function Base.iterate(t::TermsMap)
    it = iterate(t.terms)
    while it !== nothing
        s = t.op(it[1])
        if s !== nothing
            return s, it[2]
        end
        it = iterate(t.terms, it[2])
    end
    return nothing
end
@inline function Base.iterate(t::TermsMap, state)
    it = iterate(t.terms, state)
    while it !== nothing
        s = t.op(it[1])
        if s !== nothing
            return s, it[2]
        end
        it = iterate(t.terms, it[2])
    end
    return nothing
end
@inline Base.iterate(t::TermsMap, state::Start) = iterate(t)

termsbound(a::RefValue{<:Polynomial}) = length(terms(a[]))
iterterms(a::RefValue{<:Polynomial}) = terms(a[])
termsbound(a::InPlace{<:Polynomial}) = length(terms(a[]))
iterterms(a::InPlace{<:Polynomial}) = terms(a[])
termsbound(a::RefValue) = 1
termsbound(a::Number) = 1
termsbound(bc::Broadcasted{<:Termwise, Nothing, <:PlusMinus}) = sum(termsbound, bc.args)
termsbound(bc::Broadcasted{<:Termwise, Nothing, typeof(*)}) = prod(termsbound, bc.args)

const AbstractInPlace{Order,C} = Union{
    BrTermwise{Order,<:PolynomialBy{Order,C},true},
    InPlace{<:PolynomialBy{Order,C}},
}
const TermsBy{Order} = Union{
    BrTermwise{Order},
    RefValue{<:PolynomialBy{Order}},
    AbstractInPlace{Order},
}
# We know how to lazily do +/- if the orders are the same
broadcasted(st::Termwise{Order}, op::PlusMinus, a::TermsBy{Order}, b::TermsBy{Order}) where Order = Broadcasted{typeof(st)}(op, (a,b))

# we also know how to lazily do * when scaling by a Number or base ring element
broadcasted(st::Termwise{Order}, op::typeof(*), a::RefValue{<:PolynomialOver{C,Order}}, b::RefValue{C}) where {Order,C} = Broadcasted{typeof(st)}(op, (a, b))
broadcasted(st::Termwise{Order}, op::typeof(*), a::RefValue{<:PolynomialBy{Order}}, b::Number) where Order = Broadcasted{typeof(st)}(op, (a,b))
broadcasted(st::Termwise{Order}, op::typeof(*), a::RefValue{C}, b::RefValue{<:PolynomialOver{C,Order}}) where {Order,C} = Broadcasted{typeof(st)}(op, (a,b))
broadcasted(st::Termwise{Order}, op::typeof(*), a::Number, b::RefValue{<:PolynomialBy{Order}}) where Order = Broadcasted{typeof(st)}(op, (a,b))

iterterms(bc::Broadcasted{<:Termwise}) = iterterms(bc.f, bc.args...)

function iterterms(op::PlusMinus, a::TermsBy{Order}, b::TermsBy{Order}) where Order
    ≺(a,b) = Base.Order.lt(Order(), a, b)

    summands = ParallelIter(
        monomial, coefficient, ≺,
        Zero(), Zero(),
        iterterms(a), iterterms(b),
    )
    TermsMap(Order(), summands) do (m, cleft, cright)
        coeff = op(cleft, cright)
        iszero(coeff) ? nothing : Term(m, coeff)
    end
end

for T = [Number, RefValue{<:AbstractMonomial}, RefValue{<:Term}]
    @eval function iterterms(op::typeof(*), a::TermsBy{Order}, b::$T) where Order
        TermsMap(Order(), iterterms(a)) do t
            iszero(b) ? nothing : t*b
        end
    end

    @eval function iterterms(op::typeof(*), a::$T, b::TermsBy{Order}) where Order
        TermsMap(Order(), iterterms(b)) do t
            iszero(a) ? nothing : a*t
        end
    end
end

const PossiblyBigInt = Union{Int, BigInt}
mul!(a::BigInt, b::BigInt, c::BigInt) = Base.GMP.MPZ.mul!(a, b, c)
mul!(a::BigInt, b::BigInt, c::Int) = Base.GMP.MPZ.mul_si!(a, b, c)
mul!(a::BigInt, b::Int, c::BigInt) = Base.GMP.MPZ.mul_si!(a, c, b)
function iterterms(op::typeof(*), a::PossiblyBigInt, b::AbstractInPlace{Order,BigInt}) where Order
    TermsMap(Order(), iterterms(b), true) do t
        if iszero(a)
            return nothing
        else
            # TODO: need to ensure that several terms don't share the
            # same BigInt *in the same polynomial*!!!
            mul!(t.c, a, t.c)
            return t
        end
    end
end
function iterterms(op::typeof(*), a::AbstractInPlace{Order,BigInt}, b::PossiblyBigInt) where Order
    TermsMap(Order(), iterterms(a), true) do t
        if iszero(b)
            return nothing
        else
            # TODO: need to ensure that several terms don't share the
            # same BigInt *in the same polynomial*!!!
            mul!(t.c, t.c, b)
            return t
        end
    end
end

function materialize(bc::BrTermwise{Order,P}) where {Order,P}
    x = deepcopy(zero(P))
    _materialize!(x, bc)
end

isinplace(::Broadcasted{<:Termwise{<:Any,<:Any,true}}) = true
isinplace(::Broadcasted{<:Termwise{<:Any,<:Any,false}}) = false
isinplace(::InPlace) = true
isinplace(::Any) = false

mark_inplace(y, x) = y
mark_inplace(bc::RefValue, x) = bc[] === x ? InPlace(bc[]) : bc
mark_inplace(::Type{<:Termwise{Order,P}}) where {Order,P} = Termwise{Order,P,true}
"""
Mark at most occurrence of x as in-place in a Broadcasted tree.
We iterate over the arguments last-to-first and depth-first, so
we find the _last_ one that will be evaluated _first_. That is
the place in the optree that we can consider in-place.
"""
function mark_inplace(bc::Broadcasted{St}, x) where St <: Termwise
    st = St
    args = []
    n = length(bc.args)
    while n >= 1
        a = mark_inplace(bc.args[n], x)
        pushfirst!(args, a)
        if isinplace(a)
            st = mark_inplace(st)
            break
        end
        n -= 1
    end
    while n >= 1
        pushfirst!(args, bc.args[n])
        n -= 1
    end
    Broadcasted{st}(bc.f, tuple(args...))
end

function materialize!(x::Polynomial, bc::BrTermwise{Order,P}) where {Order,P}
    _materialize!(x, mark_inplace(bc, x))
end

function _materialize!(x::Polynomial, bc::BrTermwise{Order,P}) where {Order,P}
    resize!(x.terms, termsbound(bc))
    n = 0
    for t in iterterms(bc)
        @inbounds x.terms[n+=1] = t
    end
    resize!(x.terms, n)
    x
end

end
