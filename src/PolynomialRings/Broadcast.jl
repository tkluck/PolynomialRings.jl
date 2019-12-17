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

import Base: +, -, *
import Base.Broadcast: Style, AbstractArrayStyle, BroadcastStyle, Broadcasted, broadcasted
import Base.Broadcast: copyto!, copy, flatten
import Base.Broadcast: broadcastable, broadcasted, DefaultArrayStyle
import Base: RefValue, similar

import InPlace: @inplace, inplace!, inclusiveinplace!
import Transducers: Transducer, eduction, Filter, Map

import ..MonomialIterators: MonomialIter
import ..MonomialOrderings: MonomialOrder
import ..Monomials: AbstractMonomial
import ..Polynomials: Polynomial, PolynomialBy, nzterms, nztermscount, TermBy, MonomialBy
import ..Terms: Term, monomial, coefficient
import ..Util: MergingTransducer, @assertvalid
import PolynomialRings: monomialorder, basering

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
struct TermsBy{Order, Iter, Owned}
    order :: Order
    iter  :: Iter
    owned :: Owned
end

isowned(::Val{owned}) where owned = owned
isowned(x::Bool) = x
_ownedop(op, owned, x) = isowned(owned) ? inplace!(op, x, x) : op(x)
_ownedop(op, ownedx, x, ownedy, y) = isowned(ownedx) ?
                                     inplace!(op, x, x, y) :
                                     isowned(ownedy) ?
                                     inplace!(op, y, x, y) :
                                     op(x, y)
_unalias(owned, x) = isowned(owned) ? x : deepcopy(x)
_unalias(x) = x
_unalias(x::TermsBy) = iterterms(x.order, Map(_unalias), x.iter)

_constructterm(m, c) = Term(m, c)

function merge(a::TermsBy{Order}, b::TermsBy{Order}, leftop, rightop, mergeop, key, value, constructor) where Order <: MonomialOrder
    leftop′(x) = _ownedop(leftop, a.owned, x)
    rightop′(x) = _ownedop(rightop, a.owned, x)
    mergeop′(x, y) = _ownedop(mergeop, a.owned, x, b.owned, y)
    iterterms(
        Order(),
        MergingTransducer(a.iter, Order(), leftop′, rightop′, mergeop′, monomial, coefficient, _constructterm),
        b.iter,
    )
end

iterterms(destix, myix, x) = x

function iterterms(destix, myix, a::Polynomial)
    owned = isbitstype(basering(a)) ? Val(true) : destix == myix
    TermsBy(monomialorder(a), nzterms(a), owned)
end

iterterms(order::MonomialOrder, transducer, coll) = TermsBy(order, eduction(transducer |> Filter(!iszero), coll), Val(true))

# the simple solution with map(...) leads to code that the compiler doesn't inline,
# and then this part becomes a major bottleneck. By having the generated function
# spell out the map, we fix that.
@generated function iterterms(destix, myix, bc::Broadcasted{<:Termwise, Axes, Op, Args}) where {Axes, Op, Args}
    call = :( iterterms(bc.f) )
    for ix = 1:length(Args.types)
        push!(call.args, :( iterterms(destix, myix + $(ix - 1), bc.args[$ix])))
    end
    return call
end

iterterms(destix::Nothing, myix, bc::Broadcasted{<:Termwise}) = iterterms(bc.f, map(arg -> iterterms(destix, 1, arg), bc.args)...)
iterterms(f::Function, args...) = iterterms(f(args...))


function iterterms(op::typeof(+), a::TermsBy{Order}, b::TermsBy{Order}) where Order <: MonomialOrder
    return merge(a, b, +, +, +, monomial, coefficient, Term)
end

function iterterms(op::typeof(-), a::TermsBy{Order}, b::TermsBy{Order}) where Order <: MonomialOrder
    return merge(a, b, +, -, -, monomial, coefficient, Term)
end

function iterterms(op::typeof(*), a::TermsBy{Order}, b::Union{TermBy{Order}, MonomialBy{Order}, Number}) where Order <: MonomialOrder
    iterterms(Order(), Map(a_i -> a_i * b), a.iter)
end

function iterterms(op::typeof(*), a::Union{TermBy{Order}, MonomialBy{Order}, Number}, b::TermsBy{Order}) where Order <: MonomialOrder
    iterterms(Order(), Map(b_i -> a * b_i), b.iter)
end

similar(bc::Broadcasted{<:Termwise{Order}}, ::Type{P}) where P <: PolynomialBy{Order} where Order = zero(P)

function copy(bc::Broadcasted{Termwise{Order, P}}) where P <: PolynomialBy{Order} where Order
    result = zero(P)
    sizehint!(result, termsbound(bc))
    terms = _unalias(iterterms(nothing, nothing, bc)).iter
    copy!(Transducer(terms), result, terms.coll)
    @assertvalid result
end

copyto!(dest::P, bc::Broadcasted{Termwise{Order, P}}) where P <: PolynomialBy{Order} where Order = _copyto!(dest, bc)

# This is just the intended body of copyto! above, but I need to call it from
# the handcrafted version as well. My solution with `invoke` gives a segfault
# in Julia's code generator (Julia bug) so I'll just manually disentangle them.
function _copyto!(dest, bc)
    destix = findlast(a -> dest === a, flatten(bc).args)
    terms = _unalias(iterterms(destix, 1, bc)).iter
    if !isnothing(destix)
        d = zero(dest)
        sizehint!(d, termsbound(bc))
        copy!(Transducer(terms), d, terms.coll)
        copy!(dest, d)
    else
        sizehint!(dest, termsbound(bc))
        copy!(Transducer(terms), dest, terms.coll)
    end
    @assertvalid dest
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
# this is the inner loop for many reduction operations:
#    @. f = m1*f - m2*t*g
const HandOptimizedBroadcast = Broadcasted{
    Termwise{Order,P},
    <:Union{Tuple{}, Nothing},
    typeof(-),
    Tuple{
        Broadcasted{
            Termwise{Order,P},
            Nothing,
            typeof(*),
            Tuple{
                C,
                P,
            },
        },
        Broadcasted{
            Termwise{Order,P},
            Nothing,
            typeof(*),
            Tuple{
                C,
                Broadcasted{
                    Termwise{Order,P},
                    Nothing,
                    typeof(*),
                    Tuple{
                        M,
                        P,
                    },
                },
            },
        },
    },
} where P<:Polynomial where M<:AbstractMonomial{Order} where C where Order

function copyto!(dest::P, bc::HandOptimizedBroadcast{Order, C, M, P}) where {Order, C, M, P <: PolynomialBy{Order, C}}
    ≺(a,b) = Base.Order.lt(monomialorder(dest), a, b)

    m1 = bc.args[1].args[1]
    v1 = bc.args[1].args[2][]
    m2 = bc.args[2].args[1]
    t  = bc.args[2].args[2].args[1]
    v2 = bc.args[2].args[2].args[2]

    applicable = dest === v1 && dest !== v2
    # The solution with `invoke` segfaults on Julia Version 1.3.0-DEV.377 (2019-06-09)
    # Commit 5d02c59185
    !applicable && return _copyto!(dest, bc) #invoke(copyto!, Tuple{P, Broadcasted{Termwise{Order, P}}} where P <: PolynomialBy{Order} where Order <: MonomialOrder, dest, bc)

    d = zero(dest)

    monomials = d.monomials
    coeffs = d.coeffs
    monomials1 = v1.monomials
    coeffs1 = v1.coeffs
    monomials2 = v2.monomials
    coeffs2 = v2.coeffs

    # I could dispatch to a much simpler version in case these
    # scalar vanish, but that gives relatively little gain.
    m1_vanishes = iszero(m1)
    m2_vanishes = iszero(m2)

    resize!(monomials, length(monomials1) + length(monomials2))
    resize!(coeffs,    length(coeffs1)    + length(coeffs2))
    n = 0

    temp = zero(BigInt)

    ix1 = 1; ix2 = 1
    while ix1 <= length(monomials1) && ix2 <= length(monomials2)
        m′ = t * monomials2[ix2]
        if m′ ≺ monomials1[ix1]
            if !m2_vanishes
                n += 1
                monomials[n] = m′
                coeffs[n] = -m2*coeffs2[ix2]
            end
            ix2 += 1
        elseif monomials1[ix1] ≺ m′
            if !m1_vanishes
                @inplace coeffs1[ix1] *= m1
                n += 1
                monomials[n] = monomials1[ix1]
                coeffs[n] = coeffs1[ix1]
            end
            ix1 += 1
        else
            @inplace coeffs1[ix1] *= m1
            @inplace temp = m2 * coeffs2[ix2]
            @inplace coeffs1[ix1] -= temp
            if !iszero(coeffs1[ix1])
                n += 1
                monomials[n] = m′
                coeffs[n] = coeffs1[ix1]
            end
            ix1 += 1
            ix2 += 1
        end
    end
    while ix1 <= length(monomials1)
        if !m1_vanishes
            @inplace coeffs1[ix1] *= m1
            n += 1
            monomials[n] = monomials1[ix1]
            coeffs[n] = coeffs1[ix1]
        end
        ix1 += 1
    end
    while ix2 <= length(monomials2)
        if !m2_vanishes
            n += 1
            monomials[n] = t * monomials2[ix2]
            coeffs[n] = -m2*coeffs2[ix2]
        end
        ix2 += 1
    end

    # copy!(..., @view ...) is slow because it needs to allocate the view.
    empty!(dest.monomials); for ix = 1:n; push!(dest.monomials, monomials[ix]); end
    empty!(dest.coeffs);    for ix = 1:n; push!(dest.coeffs,    coeffs[ix]);    end
    @assertvalid dest
end

# this is the inner loop for m4gb
#    @. g -= c * h
const M4GBBroadcast = Broadcasted{
    Termwise{Order, P},
    <:Union{Tuple{}, Nothing},
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

function copyto!(g::P, bc::M4GBBroadcast{C, Order, MI, M, P}) where {C, Order, MI, M, P <: PolynomialBy{Order, C}}
    applicable = g === bc.args[1]
    !applicable && return _copyto!(g, bc)

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

    return @assertvalid g
end

end
