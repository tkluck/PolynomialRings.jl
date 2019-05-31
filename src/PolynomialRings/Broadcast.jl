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

In turn, `materialize` calls `copyto!` In order to define our own behaviour, we
override `broadcasted` and `copyto!`.

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

We represent both cases by passing a value for `owned` alongside them in the
TermsBy struct. This property bubbles up through the optree.
"""
module Broadcast

import Base.Broadcast: Style, AbstractArrayStyle, BroadcastStyle, Broadcasted, broadcasted
import Base.Broadcast: copyto!, copy
import Base.Broadcast: broadcastable, broadcasted, materialize!
import Base: RefValue, similar

import InPlace: @inplace, inplace!, inclusiveinplace!
import Transducers: Transducer, eduction, Map, Filter

import ..MonomialIterators: MonomialIter
import ..MonomialOrderings: MonomialOrder
import ..Monomials: AbstractMonomial
import ..Polynomials: Polynomial, PolynomialBy, nzterms, nztermscount, TermBy, MonomialBy
import ..Terms: Term, monomial, coefficient
import ..Util: MergingTransducer, _Map
import PolynomialRings: monomialorder

broadcastable(p::AbstractMonomial) = p
broadcastable(p::Term) = p
broadcastable(p::Polynomial) = p

# -----------------------------------------------------------------------------
#
# Defining the broadcast style
#
# -----------------------------------------------------------------------------
struct Termwise{Order, P} <: BroadcastStyle end

BroadcastStyle(::Type{<:P}) where P<:Polynomial = Termwise{typeof(monomialorder(P)), P}()
BroadcastStyle(s::Termwise{Order, P}, t::Termwise{Order, Q}) where {Order,P,Q} = Termwise{Order, promote_type(P, Q)}()
BroadcastStyle(s::Termwise, t::AbstractArrayStyle{0}) = s
BroadcastStyle(s::Termwise, t::BroadcastStyle) = t

# -----------------------------------------------------------------------------
#
# A light-weight wrapper around an iterator that yields terms
#
# -----------------------------------------------------------------------------
struct TermsBy{Order, Iter}
    order :: Order
    iter  :: Iter
    owned :: Bool
end

isowned(t::TermsBy) = t.owned

iterterms(dest, x) = x
# TODO: only the last one is really owned
iterterms(dest, a::Polynomial) = TermsBy(monomialorder(a), nzterms(a), a === dest)

iterterms(order::MonomialOrder, owned, transducer, coll) = TermsBy(order, eduction(transducer |> Filter(!iszero), coll), owned)

iterterms(dest, bc::Broadcasted{<:Termwise}) = iterterms(bc.f, map(arg -> iterterms(dest, arg), bc.args)...)
iterterms(f::Function, args...) = iterterms(f(args...))

coeffwise(op) = (a, b) -> (@assert monomial(a) == monomial(b); res = Term(monomial(a), op(coefficient(a), coefficient(b))); res)

function iterterms(op::typeof(+), a::TermsBy{Order}, b::TermsBy{Order}) where Order <: MonomialOrder
    if isowned(a) && isowned(b)
        iterterms(Order(), true,
            MergingTransducer(a.iter, Order(), identity, identity, coeffwise((a_i, b_i) -> inclusiveinplace!(+, a_i, b_i)), monomial, identity), b.iter)
    elseif isowned(a)
        iterterms(Order(), true,
            MergingTransducer(a.iter, Order(), identity, +, coeffwise((a_i, b_i) -> inclusiveinplace!(+, a_i, b_i)), monomial, identity), b.iter)
    elseif isowned(b)
        iterterms(Order(), true,
            MergingTransducer(a.iter, Order(), +, identity, coeffwise((a_i, b_i) -> inplace!(+, b_i, a_i, b_i)), monomial, identity), b.iter)
    else
        iterterms(Order(), true, MergingTransducer(a.iter, Order(), +, +, coeffwise(+), monomial, identity), b.iter)
    end
end

function iterterms(op::typeof(-), a::TermsBy{Order}, b::TermsBy{Order}) where Order <: MonomialOrder
    if isowned(a) && isowned(b)
        iterterms(Order(), true,
            MergingTransducer(a.iter, Order(), identity, b_i -> inclusiveinplace!(-, b_i), coeffwise((a_i, b_i) -> inclusiveinplace!(-, a_i, b_i)), monomial, identity), b.iter)
    elseif isowned(a)
        iterterms(Order(), true,
            MergingTransducer(a.iter, Order(), identity, -, coeffwise((a_i, b_i) -> inclusiveinplace!(-, a_i, b_i)), monomial, identity), b.iter)
    elseif isowned(b)
        iterterms(Order(), true,
            MergingTransducer(a.iter, Order(), +, b_i -> inclusiveinplace!(-, b_i), coeffwise((a_i, b_i) -> inplace!(-, b_i, a_i, b_i)), monomial, identity), b.iter)
    else
        iterterms(Order(), true, MergingTransducer(a.iter, Order(), +, -, coeffwise(-), monomial, identity), b.iter)
    end
end

function iterterms(op::typeof(*), a::TermsBy{Order}, b::Union{TermBy{Order}, MonomialBy{Order}, Number}) where Order <: MonomialOrder
    if isowned(a)
        iterterms(Order(), true, _Map(a_i -> inclusiveinplace!(*, a_i, b)), a.iter)
    else
        iterterms(Order(), true, _Map(a_i -> a_i * b),                      a.iter)
    end
end

function iterterms(op::typeof(*), a::Union{TermBy{Order}, MonomialBy{Order}, Number}, b::TermsBy{Order}) where Order <: MonomialOrder
    if isowned(b)
        iterterms(Order(), true, _Map(b_i -> inplace!(*, b_i, a, b_i)), b.iter)
    else
        iterterms(Order(), true, _Map(b_i -> a * b_i),                  b.iter)
    end
end

similar(bc::Broadcasted{<:Termwise{Order}}, ::Type{P}) where P <: PolynomialBy{Order} where Order = zero(P)

function copy(bc::Broadcasted{Termwise{Order, P}}) where P <: PolynomialBy{Order} where Order
    result = zero(P)
    copyto!(result, bc)
end

function copyto!(dest::P, bc::Broadcasted{Termwise{Order, P}}) where P <: PolynomialBy{Order} where Order
    d = zero(dest)
    ed = iterterms(dest, bc).iter
    sizehint!(d, termsbound(bc))
    copy!(Transducer(ed), d, ed.coll)
    copy!(dest.coeffs, d.coeffs)
    copy!(dest.monomials, d.monomials)
    dest
end

# -----------------------------------------------------------------------------
#
#  termsbound base case and recursion
#
# -----------------------------------------------------------------------------
const PlusMinus = Union{typeof(+), typeof(-)}
termsbound(a::Polynomial) = nztermscount(a)
termsbound(a::RefValue) = 1
termsbound(a::AbstractMonomial) = 1
termsbound(a::Term) = 1
termsbound(a::Number) = 1
termsbound(bc::Broadcasted{<:Termwise, A, <:PlusMinus}) where A = sum(termsbound, bc.args)
termsbound(bc::Broadcasted{<:Termwise, A, typeof(*)}) where A = prod(termsbound, bc.args)

# -----------------------------------------------------------------------------
#
#  Special-case optimizations
#
# -----------------------------------------------------------------------------
# this is the inner loop for m4gb
#    @. g -= c * h
const M4GBBroadcast = Broadcasted{
    Termwise{Order, P},
    Nothing,
    typeof(-),
    Tuple{
        P,
        Broadcasted{
            Termwise{Order, P},
            Nothing,
            typeof(*),
            Tuple{
                C,
                P,
            },
        },
    },
} where P <: Polynomial{M, C, MI} where M <: AbstractMonomial{Order} where MI <: MonomialIter where {C, Order}

function materialize!(g::Polynomial, bc::M4GBBroadcast)
    @assert g === bc.args[1]
    c = bc.args[2].args[1]
    h = bc.args[2].args[2]

    n = length(g.coeffs)
    m = something(findlast(!iszero, h.coeffs), 0)
    if n < m
        resize!(g.coeffs, m)
        for i in n + 1 : m
            g.coeffs[i] = zero(eltype(g.coeffs))
        end
    end

    @. g.coeffs[1:m] -= c * @view h.coeffs[1:m]

    m = something(findlast(!iszero, g.coeffs), 0)
    resize!(g.coeffs, m)

    return g
end

end
