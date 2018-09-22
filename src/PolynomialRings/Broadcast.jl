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

This is achieved by overriding `BroadcastStyle(...)`.

In particular, this means that e.g. `f .* [1,2]` works exactly as you'd
expect by distributing over the vector elements.

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

For coefficients of type `BigInt`, it can be advantageous to do operations
in-place, mainly because that saves on allocations.

We can do in-place evaluation in two cases:

 - If one of the source polynomials is also the target, e.g.

       f .= 5 .* g  .- 4 .* f

   (If the target polynomial appears several times, then the _last_ operation to
   be evaluated can be done in-place.)

 - If we compute an intermediate polynomial, e.g.

       f .* g .+ h

   In this example case, `f .* g` has no term-wise implementation, so we evaluate it
   eagerly as `f * g`. The resulting polynomial is transient, so we may apply the
   `... .+ h)` operation in-place.

We represent both cases by wrapping these elements in an `InPlace` struct.
These structs result in a `TermsMap` with `Inplace=true`, and this property
bubbles up through the optree.
"""
module Broadcast

using Base: RefValue
using Base.Broadcast: Style, AbstractArrayStyle, BroadcastStyle, Broadcasted, broadcasted
using PolynomialRings: monomialorder
using PolynomialRings.Constants: Zero, One
using PolynomialRings.Util: ParallelIter
using PolynomialRings.MonomialOrderings: MonomialOrder
using PolynomialRings.Monomials: AbstractMonomial
using PolynomialRings.Terms: Term, monomial, coefficient
using PolynomialRings.Polynomials: Polynomial, TermOver, PolynomialOver, PolynomialBy, terms, termtype

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base.Broadcast: broadcastable, broadcasted, materialize, materialize!

broadcastable(p::AbstractMonomial) = Ref(p)
broadcastable(p::Term) = Ref(p)
broadcastable(p::Polynomial) = Ref(p)

# -----------------------------------------------------------------------------
#
# Defining the broadcast style
#
# -----------------------------------------------------------------------------
struct Termwise{Order, P} <: BroadcastStyle end

BroadcastStyle(::Type{<:RefValue{P}}) where P<:Polynomial = Termwise{typeof(monomialorder(P)), P}()
BroadcastStyle(s::Termwise{Order, P}, t::Termwise{Order, Q}) where {Order,P,Q} = Termwise{Order, promote_type(P, Q)}()
BroadcastStyle(s::Termwise, t::AbstractArrayStyle{0}) = s
BroadcastStyle(s::Termwise, t::BroadcastStyle) = t

# -----------------------------------------------------------------------------
#
# Handling polynomials that may be edited in-place
#
# -----------------------------------------------------------------------------
const BrTermwise{Order,P} = Broadcasted{Termwise{Order,P}}
const PlusMinus = Union{typeof(+), typeof(-)}

struct InPlace{P}
    x::P
end
Base.getindex(x::InPlace) = x.x

broadcastable(x::InPlace) = x
BroadcastStyle(::Type{<:InPlace{P}}) where P<:Polynomial = Termwise{typeof(monomialorder(P)), P}()

# Eagerly evaluate all expressions involving polynomials, except for the
# ones we explicitly know how to do. This ensures that e.g. operations
# with different variables/orders get eagerly evaluated.
eager(a) = a
eager(a::InPlace) = a[]
eager(a::RefValue) = a[]
eager(a::Broadcasted) = materialize(a)
# Note that by the time this function gets called, all the BroadcastStyles
# have already been bubbled up, so if we still have Termwise as the
# first argument, we are sure we only have polynomials and scalars.
# Note that if we've evaluated eagerly, then we own the resulting Polynomial,
# so we may apply in-place operations to it.
broadcasted(::Termwise, op, a, b) = InPlace(op(eager(a), eager(b)))

"""
    TermsMap{Order,Inplace,Terms,Op}

Represents a lazily evaluated generator of terms. `Inplace` is either
true or false, and represents whether the consumer is allowed to modify the
coefficients in-place. This is e.g. true if we are iterating over an
`InPlace{<:Polynomial}` or if the generator has allocated its own
`Term`.
"""
struct TermsMap{Order,Inplace,Terms,Op}
    terms::Terms
    op::Op
end
Base.getindex(t::TermsMap) = t
is_inplace(::TermsMap{Order,Inplace}) where {Order,Inplace} = Inplace

TermsMap(op::Op, o::Order, terms::Terms, inplace=false) where {Op, Order,Terms} = TermsMap{Order,inplace,Terms,Op}(terms, op)

# keeping the method with and without state separate instead of unifying
# through e.g. iterate(t, state...) because that seems to have a moderate
# performance benefit.
# Other than that, the method bodies are identical.
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

# -----------------------------------------------------------------------------
#
#  Leaf cases for `iterterms`
#
# -----------------------------------------------------------------------------
iterterms(a::RefValue{<:Polynomial}) = TermsMap(identity, monomialorder(a[]), terms(a[]), false)
iterterms(a::InPlace{<:Polynomial}) = TermsMap(identity, monomialorder(a[]), terms(a[]), true)

# -----------------------------------------------------------------------------
#
#  termsbound base case and recursion
#
# -----------------------------------------------------------------------------
termsbound(a::RefValue{<:Polynomial}) = length(terms(a[]))
termsbound(a::InPlace{<:Polynomial}) = length(terms(a[]))
termsbound(a::RefValue) = 1
termsbound(a::Number) = 1
termsbound(bc::Broadcasted{<:Termwise, Nothing, <:PlusMinus}) = sum(termsbound, bc.args)
termsbound(bc::Broadcasted{<:Termwise, Nothing, typeof(*)}) = prod(termsbound, bc.args)

# -----------------------------------------------------------------------------
#
#  Decide which broadcasts can be done lazily
#
# -----------------------------------------------------------------------------
const TermsBy{Order} = Union{
    BrTermwise{Order},
    RefValue{<:PolynomialBy{Order}},
    InPlace{<:PolynomialBy{Order}},
}
# We know how to lazily do +/- if the orders are the same
broadcasted(st::Termwise{Order}, op::PlusMinus, a::TermsBy{Order}, b::TermsBy{Order}) where Order = Broadcasted{typeof(st)}(op, (a,b))

# we also know how to lazily do * when scaling by a Number or base ring element
broadcasted(st::Termwise{Order}, op::typeof(*), a::RefValue{<:PolynomialOver{C,Order}}, b::RefValue{C}) where {Order,C} = Broadcasted{typeof(st)}(op, (a, b))
broadcasted(st::Termwise{Order}, op::typeof(*), a::TermsBy{Order}, b::Number) where Order = Broadcasted{typeof(st)}(op, (a,b))
broadcasted(st::Termwise{Order}, op::typeof(*), a::RefValue{C}, b::RefValue{<:PolynomialOver{C,Order}}) where {Order,C} = Broadcasted{typeof(st)}(op, (a,b))
broadcasted(st::Termwise{Order}, op::typeof(*), a::Number, b::TermsBy{Order}) where Order = Broadcasted{typeof(st)}(op, (a,b))

# also when scaling by a monomial
broadcasted(st::Termwise{Order}, op::typeof(*), a::RefValue{<:AbstractMonomial}, b::RefValue{<:PolynomialBy{Order}}) where Order = Broadcasted{typeof(st)}(op, (a,b))

# -----------------------------------------------------------------------------
#
#  Lazy implementations of these broadcasts
#
# -----------------------------------------------------------------------------
iterterms(x) = x
iterterms(bc::Broadcasted{<:Termwise}) = iterterms(bc.f, map(iterterms, bc.args)...)

# -----------------------------------------------------------------------------
#
#  Lazy implementations of scalar multiplication
#
# -----------------------------------------------------------------------------
function iterterms(op::typeof(*), a::TermsMap{Order}, b::Number) where Order
    b′ = deepcopy(b)
    TermsMap(Order(), a) do t
        iszero(b) ? nothing : Term(monomial(t), coefficient(t)*b′)
    end
end

function iterterms(op::typeof(*), a::Number, b::TermsMap{Order}) where Order
    a′ = deepcopy(a)
    TermsMap(Order(), b) do t
        iszero(a) ? nothing : Term(monomial(t), a′*coefficient(t))
    end
end

const PossiblyBigInt = Union{Int, BigInt}
mul!(a::Term, b::Integer) = a*b
mul!(a::TermOver{BigInt}, b::Int) = (Base.GMP.MPZ.mul_si!(a.c, b); a)
mul!(a::TermOver{BigInt}, b::BigInt) = (Base.GMP.MPZ.mul!(a.c, b); a)
function iterterms(op::typeof(*), a::PossiblyBigInt, b::TermsMap{Order,true}) where Order
    a′ = deepcopy(a)
    TermsMap(Order(), b, true) do t
        if iszero(a)
            return nothing
        else
            t = mul!(t, a′)
            return t
        end
    end
end
function iterterms(op::typeof(*), a::TermsMap{Order,true}, b::PossiblyBigInt) where Order
    b′ = deepcopy(b)
    TermsMap(Order(), a, true) do t
        if iszero(b)
            return nothing
        else
            t = mul!(t, b′)
            return t
        end
    end
end

function iterterms(op::typeof(*), a::RefValue{<:AbstractMonomial}, b::TermsMap{Order}) where Order
    TermsMap(Order(), b, is_inplace(b)) do t
        # NOTE: we are not deepcopying the coefficient, but materialize!() will
        # take care of that if the end result is not transient
        return typeof(t)(a[]*monomial(t), coefficient(t))
    end
end

function iterterms(op::typeof(*), a::TermsMap{Order}, b::RefValue{<:AbstractMonomial}) where Order
    TermsMap(Order(), a, is_inplace(a)) do t
        # NOTE: we are not deepcopying the coefficient, but materialize!() will
        # take care of that if the end result is not transient
        return typeof(t)(monomial(t)*b[], coefficient(t))
    end
end

# -----------------------------------------------------------------------------
#
#  Lazy implementations of addition/substraction
#
# -----------------------------------------------------------------------------
inplace!(op, a, b, c) = (a = op(b,c); a)
inplace!(::typeof(+), a::BigInt, b::BigInt, c::BigInt) = (Base.GMP.MPZ.add!(a,b,c); a)
inplace!(::typeof(+), a::BigInt, b::BigInt, c::Zero) = (Base.GMP.MPZ.set!(a,b); a)
inplace!(::typeof(+), a::BigInt, b::Zero, c::BigInt) = (Base.GMP.MPZ.set!(a,c); a)
inplace!(::typeof(-), a::BigInt, b::BigInt, c::BigInt) = (Base.GMP.MPZ.sub!(a,b,c); a)
inplace!(::typeof(-), a::BigInt, b::BigInt, c::Zero) = (Base.GMP.MPZ.set!(a,b); a)
inplace!(::typeof(-), a::BigInt, b::Zero, c::BigInt) = (Base.GMP.MPZ.neg!(a,c); a)
function iterterms(op::PlusMinus, a::TermsMap{Order,true}, b::TermsMap{Order,true}) where Order
    invoke(iterterms, Tuple{PlusMinus, TermsMap{Order,true}, TermsMap{Order}}, op, a, b)
end
function iterterms(op::PlusMinus, a::TermsMap{Order,true}, b::TermsMap{Order}) where Order
    ≺(a,b) = Base.Order.lt(Order(), a, b)

    summands = ParallelIter(
        monomial, coefficient, ≺,
        Zero(), Zero(),
        a, b,
    )
    TermsMap(Order(), summands, true) do (m, cleft, cright)
        cleft = inplace!(op, cleft, cleft, cright)
        iszero(cleft) ? nothing : Term(m, cleft)
    end
end
function iterterms(op::PlusMinus, a::TermsMap{Order}, b::TermsMap{Order,true}) where Order
    ≺(a,b) = Base.Order.lt(Order(), a, b)

    summands = ParallelIter(
        monomial, coefficient, ≺,
        Zero(), Zero(),
        a, b,
    )
    TermsMap(Order(), summands, true) do (m, cleft, cright)
        cright = inplace!(op, cright, cleft, cright)
        iszero(cright) ? nothing : Term(m, cright)
    end
end
function iterterms(op::PlusMinus, a::TermsMap{Order}, b::TermsMap{Order}) where Order
    ≺(a,b) = Base.Order.lt(Order(), a, b)

    summands = ParallelIter(
        monomial, coefficient, ≺,
        Zero(), Zero(),
        a, b,
    )
    TermsMap(Order(), summands, true) do (m, cleft, cright)
        coeff = op(cleft, cright)
        iszero(coeff) ? nothing : Term(m, coeff)
    end
end

# -----------------------------------------------------------------------------
#
#  Materializing the lazily computed results
#
# -----------------------------------------------------------------------------

materialize(bc::InPlace) = bc[]

function materialize(bc::BrTermwise{Order,P}) where {Order,P}
    x = deepcopy(zero(P))
    _materialize!(x, bc)
end

mark_inplace(y, x) = (y, :notfound)
mark_inplace(bc::RefValue, x) = bc[] === x ? (InPlace(bc[]), :found) : (bc, :notfound)
"""
Mark at most a single occurrence of x as in-place in a Broadcasted tree. We
iterate over the arguments last-to-first and depth-first, so we find the _last_
one that will be evaluated _first_. That is the place in the optree that we can
consider in-place.
"""
function mark_inplace(bc::Broadcasted{St}, x) where St <: Termwise
    args = []
    found = :notfound
    for n = length(bc.args):-1:1
        if found == :notfound
            (a, found) = mark_inplace(bc.args[n], x)
            pushfirst!(args, a)
        else
            pushfirst!(args, bc.args[n])
        end
    end
    return (Broadcasted{St}(bc.f, tuple(args...)), found)
end

function materialize!(x::Polynomial, bc::BrTermwise{Order,P}) where {Order,P}
    (bc′, found) = mark_inplace(bc, x)
    if found == :found
        tgt = deepcopy(zero(x))
        _materialize!(tgt, bc′)
        resize!(x.terms, length(tgt.terms))
        copyto!(x.terms, tgt.terms)
    elseif found == :notfound
        _materialize!(x, bc′)
    else
        @assert false "unreachable"
    end
    x
end

function _materialize!(x::Polynomial, bc::BrTermwise{Order,P}) where {Order,P}
    resize!(x.terms, termsbound(bc))
    n = 0
    it = iterterms(bc)
    if is_inplace(it)
        for t in it
            @inbounds x.terms[n+=1] = t
        end
    else
        for t in it
            @inbounds x.terms[n+=1] = deepcopy(t)
        end
    end
    resize!(x.terms, n)
    x
end

end
