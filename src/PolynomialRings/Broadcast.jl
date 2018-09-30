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

To achieve this, the default implementation for `iterterms` eagerly evaluates
the broadcast operation. Only those operations that we _know_ to work term-wise
efficiently get a more specific override.

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
using PolynomialRings.Util: ParallelIter, inplace!
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
    bound::Int
end
Base.getindex(t::TermsMap) = t
is_inplace(::TermsMap{Order,Inplace}) where {Order,Inplace} = Inplace

TermsMap(op::Op, o::Order, terms::Terms, bound::Int, inplace=false) where {Op, Order,Terms} = TermsMap{Order,inplace,Terms,Op}(terms, op, bound)

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
Base.IteratorSize(::TermsMap) = Base.SizeUnknown()
Base.eltype(t::TermsMap) = Base._return_type(t.op, Tuple{eltype(t.terms)})

# -----------------------------------------------------------------------------
#
#  Leaf cases for `iterterms`
#
# -----------------------------------------------------------------------------
iterterms(a::RefValue{<:PolynomialBy{Order}}) where Order = TermsMap(identity, Order(), terms(a[]), length(terms(a[])), false)
iterterms(a::InPlace{<:PolynomialBy{Order}}) where Order = TermsMap(identity, Order(), terms(a[]), length(terms(a[])), true)

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
#  Recurse into the broadcasting operation tree
#
# -----------------------------------------------------------------------------
iterterms(x) = x
iterterms(bc::Broadcasted{<:Termwise{Order}}) where Order = iterterms(Order(), bc.f, map(iterterms, bc.args)...)

# -----------------------------------------------------------------------------
#
#  Default implementation for these broadcasts is eager evaluation
#
# -----------------------------------------------------------------------------
eager(a) = a
eager(a::InPlace) = a[]
eager(a::RefValue) = a[]
eager(a::Broadcasted) = materialize(a)
function eager(a::TermsMap)
    T = eltype(a)
    P = Polynomial{T}
    terms = Vector{T}(undef, a.bound)
    n = 0
    for t in a
        terms[n+=1] = t
    end
    resize!(terms, n)
    P(terms)
end
# XXX ensure right order
iterterms(order, op, a, b) = iterterms(InPlace(op(eager(a), eager(b))))

# -----------------------------------------------------------------------------
#
#  Lazy implementations of scalar multiplication
#
# -----------------------------------------------------------------------------
function iterterms(::Order, op::typeof(*), a::TermsMap{Order}, b::Number) where Order
    b′ = deepcopy(b)
    b_vanishes = iszero(b)
    TermsMap(Order(), a, a.bound) do t
        b_vanishes ? nothing : Term(monomial(t), coefficient(t)*b′)
    end
end

function iterterms(::Order, op::typeof(*), a::Number, b::TermsMap{Order}) where Order
    a′ = deepcopy(a)
    a_vanishes = iszero(a)
    TermsMap(Order(), b, b.bound) do t
        a_vanishes ? nothing : Term(monomial(t), a′*coefficient(t))
    end
end

const PossiblyBigInt = Union{Int, BigInt}
mul!(a::Term, b::Integer) = a*b
mul!(a::TermOver{BigInt}, b::Int) = (Base.GMP.MPZ.mul_si!(a.c, b); a)
mul!(a::TermOver{BigInt}, b::BigInt) = (Base.GMP.MPZ.mul!(a.c, b); a)
function iterterms(::Order, op::typeof(*), a::PossiblyBigInt, b::TermsMap{Order,true}) where Order
    a′ = deepcopy(a)
    a_vanishes = iszero(a)
    TermsMap(Order(), b, b.bound, true) do t
        if a_vanishes
            return nothing
        else
            t = mul!(t, a′)
            return t
        end
    end
end
function iterterms(::Order, op::typeof(*), a::TermsMap{Order,true}, b::PossiblyBigInt) where Order
    b′ = deepcopy(b)
    b_vanishes = iszero(b)
    TermsMap(Order(), a, a.bound, true) do t
        if b_vanishes
            return nothing
        else
            t = mul!(t, b′)
            return t
        end
    end
end

function iterterms(::Order, op::typeof(*), a::RefValue{<:AbstractMonomial}, b::TermsMap{Order}) where Order
    TermsMap(Order(), b, b.bound, is_inplace(b)) do t
        # NOTE: we are not deepcopying the coefficient, but materialize!() will
        # take care of that if the end result is not transient
        return typeof(t)(a[]*monomial(t), coefficient(t))
    end
end

function iterterms(::Order, op::typeof(*), a::TermsMap{Order}, b::RefValue{<:AbstractMonomial}) where Order
    TermsMap(Order(), a, a.bound, is_inplace(a)) do t
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
function iterterms(::Order, op::PlusMinus, a::TermsMap{Order,true}, b::TermsMap{Order,true}) where Order
    invoke(iterterms, Tuple{Order, PlusMinus, TermsMap{Order,true}, TermsMap{Order}}, Order(), op, a, b)
end
function iterterms(::Order, op::PlusMinus, a::TermsMap{Order,true}, b::TermsMap{Order}) where Order
    ≺(a,b) = Base.Order.lt(Order(), a, b)

    summands = ParallelIter(
        monomial, coefficient, ≺,
        Zero(), Zero(),
        a, b,
    )
    TermsMap(Order(), summands, a.bound + b.bound, true) do (m, cleft, cright)
        cleft = inplace!(op, cleft, cleft, cright)
        iszero(cleft) ? nothing : Term(m, cleft)
    end
end
function iterterms(::Order, op::PlusMinus, a::TermsMap{Order}, b::TermsMap{Order,true}) where Order
    ≺(a,b) = Base.Order.lt(Order(), a, b)

    summands = ParallelIter(
        monomial, coefficient, ≺,
        Zero(), Zero(),
        a, b,
    )
    TermsMap(Order(), summands, a.bound + b.bound, true) do (m, cleft, cright)
        cright = inplace!(op, cright, cleft, cright)
        iszero(cright) ? nothing : Term(m, cright)
    end
end
function iterterms(::Order, op::PlusMinus, a::TermsMap{Order}, b::TermsMap{Order}) where Order
    ≺(a,b) = Base.Order.lt(Order(), a, b)

    summands = ParallelIter(
        monomial, coefficient, ≺,
        Zero(), Zero(),
        a, b,
    )
    TermsMap(Order(), summands, a.bound + b.bound, true) do (m, cleft, cright)
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

# this is the inner loop for many reduction operations:
#    @. f = m1*f - m2*t*g
const HandOptimizedBroadcast = Broadcasted{
    Termwise{Order,P},
    Nothing,
    typeof(-),
    Tuple{
        Broadcasted{
            Termwise{Order,P},
            Nothing,
            typeof(*),
            Tuple{
                BigInt,
                InPlace{P},
            },
        },
        Broadcasted{
            Termwise{Order,P},
            Nothing,
            typeof(*),
            Tuple{
                BigInt,
                Broadcasted{
                    Termwise{Order,P},
                    Nothing,
                    typeof(*),
                    Tuple{
                        RefValue{M},
                        RefValue{P},
                    },
                },
            },
        },
    },
} where P<:Polynomial{<:Term{M,BigInt}} where M<:AbstractMonomial{Order} where Order

function _materialize!(x::Polynomial, bc::HandOptimizedBroadcast)
    ≺(a,b) = Base.Order.lt(monomialorder(x), a, b)

    m1 = bc.args[1].args[1]
    v1 = bc.args[1].args[2][]
    m2 = bc.args[2].args[1]
    t  = bc.args[2].args[2].args[1][]
    v2 = bc.args[2].args[2].args[2][]

    tgt = x.terms
    src1 = v1.terms
    src2 = map(s->t*s, v2.terms)

    # I could dispatch to a much simpler version in case these
    # scalar vanish, but that gives relatively little gain.
    m1_vanishes = iszero(m1)
    m2_vanishes = iszero(m2)

    resize!(tgt, length(src1) + length(src2))
    n = 0

    ix1 = 1; ix2 = 1
    while ix1 <= length(src1) && ix2 <= length(src2)
        if src2[ix2] ≺ src1[ix1]
            if !m2_vanishes
                tgt[n+=1] = -m2*src2[ix2]
            end
            ix2 += 1
        elseif src1[ix1] ≺ src2[ix2]
            if !m1_vanishes
                Base.GMP.MPZ.mul!(src1[ix1].c, m1, src1[ix1].c)
                tgt[n+=1] = src1[ix1]
            end
            ix1 += 1
        else
            Base.GMP.MPZ.sub!(src1[ix1].c, m1*src1[ix1].c, m2*src2[ix2].c)
            if !iszero(src1[ix1])
                tgt[n+=1] = src1[ix1]
            end
            ix1 += 1
            ix2 += 1
        end
    end
    while ix1 <= length(src1)
        if !m1_vanishes
            Base.GMP.MPZ.mul!(src1[ix1].c, m1, src1[ix1].c)
            tgt[n+=1] = src1[ix1]
        end
        ix1 += 1
    end
    while ix2 <= length(src2)
        if !m2_vanishes
            tgt[n+=1] = -m2*src2[ix2]
        end
        ix2 += 1
    end

    resize!(tgt, n)
end

end
