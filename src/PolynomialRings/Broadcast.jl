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

In order to define our own behaviour, we override `materialize!` (and `copy` for
the variant that allocates its result).

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

To achieve this, the default implementation for `maybe_instantiate` eagerly
evaluates the broadcast operation. Only those operations that we _know_ to work
term-wise efficiently get a more specific override.

### Lazy evaluation

For the operations that _do_ work well term-wise, we implement a function
`maybe_instantiate` that takes a `Broadcasted` object or a scalar, and returns
either an `Owned{<:Polynomial}` or a `TermsBy` object. These can be composed
to form the full operation.

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

We represent both cases by keeping a `owned` value with the scalar or the
`TermsBy` object.
"""
module Broadcast

import Base.Broadcast: AbstractArrayStyle, BroadcastStyle, Broadcasted
import Base.Broadcast: materialize!, copyto!, copy, flatten, dotview
import Base.Broadcast: broadcastable, broadcasted
import Base: RefValue

import Combinatorics: combinations
import InPlace: @inplace, inplace!
import Transducers: eduction, Map, Filter, Eduction, Transducer, transduce

import ..MonomialIterators: MonomialIter
import ..MonomialOrderings: MonomialOrder
import ..Monomials: AbstractMonomial
import ..Polynomials: Polynomial, DensePolynomial, PolynomialBy, SparsePolynomialBy, DensePolynomialBy, nzterms, nztermscount, TermBy, MonomialBy, coefficients
import ..Terms: Term, monomial, coefficient, basering
import ..Util: MergingTransducer, @assertvalid
import PolynomialRings: monomialorder

const PlusMinus = Union{typeof(+), typeof(-)}

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
# Return values for the `instantiate` function
#
# -----------------------------------------------------------------------------
struct TermsBy{Order, P, Iter, Owned}
    order :: Order
    P     :: Type{P}
    iter  :: Iter
    owned :: Owned
    bound :: Int
end

struct CoeffsBy{Order, P, Coeffs, Owned}
    order  :: Order
    P      :: Type{P}
    coeffs :: Coeffs
    owned  :: Owned
end

struct Owned{Value, IsOwned}
    value :: Value
    owned :: IsOwned
end

const TermsIterable{Order} = Union{Owned{<:SparsePolynomialBy{Order}}, TermsBy{Order}}
const CoeffsIterable{Order} = Union{Owned{<:DensePolynomialBy{Order}}, CoeffsBy{Order}}

function Owned(f::Function, args::Owned...)
    Owned(f(map(a -> a.value, args)...), Val(false))
end

const MathOperator = Union{typeof(+), typeof(-), typeof(*), typeof(/), typeof(//)}
function Owned(f::MathOperator, args::Owned...)
    Owned(f(map(a -> a.value, args)...), Val(true))
end

copy(x::TermsBy) = copyto_unaliased!(zero(x.P), x)
copy(x::CoeffsBy) = x.P(copy(x.coeffs)) # TODO: no need to copy if it's already an array and we own it
copy(x::Owned) = isowned(x) ? x.value : deepcopy(x.value)
nzterms(x::TermsBy) = x.iter
nzterms(x::CoeffsBy) = nzterms(x.P(x.coeffs))
nzterms(x::Owned{<:Polynomial}) = nzterms(x.value)
coefficients(x::CoeffsBy) = x.coeffs
coefficients(x::Owned{<:Polynomial}) = coefficients(x.value)
termsbound(x::TermsBy) = x.bound
termsbound(x::CoeffsBy) = count(!iszero, x.coeffs)
termsbound(x::Owned{<:Polynomial}) = nztermscount(x.value)
polynomialtype(x::TermsBy) = x.P
polynomialtype(x::CoeffsBy) = x.P
polynomialtype(x::Owned{<:Polynomial}) = typeof(x.value)

isowned(::Val{owned}) where owned = owned
isowned(x::Bool) = x
isowned(x::TermsBy) = isowned(x.owned)
isowned(x::CoeffsBy) = isowned(x.owned)
isowned(x::Owned) = isowned(x.owned)

_ownedop(op, owned, x) = isowned(owned) ? inplace!(op, x, x) : op(x)
_ownedop(op, ownedx, x, ownedy, y) = isowned(ownedx) ?
                                     inplace!(op, x, x, y) :
                                     isowned(ownedy) ?
                                     inplace!(op, y, x, y) :
                                     op(x, y)

_constructterm(m, c) = Term(m, c)

withownership(x::Owned, args...) = error("Can't apply withownership twice!")
withownership(x, destix) = withownership(x, destix, 1)
withownership(x, destix, myix) = Owned(x, isbitstype(typeof(x)) ? Val(true) : destix == myix)
@generated function withownership(bc::BC, destix, myix) where BC <: Broadcasted{Tw, Axes, F, Args} where {Tw <: Termwise, Axes, F, Args}
    argtuple = :( tuple() )
    expr = :( Broadcasted{Tw}(bc.f, $argtuple) )
    for ix = 1:length(Args.types)
        push!(argtuple.args, :( withownership(bc.args[$ix], destix, myix + $(ix - 1)) ))
    end
    return expr
end

maybe_collect(x::Owned) = x
maybe_collect(x::TermsBy) = Owned(copy(x), Val(true))
maybe_collect(x::CoeffsBy) = Owned(copy(x), Val(true))

maybe_instantiate_default(f, args...) = Owned(f, map(maybe_collect, args)...)

maybe_instantiate(x) = error("Please apply withownership before instantiating")
maybe_instantiate(x::Owned) = x
maybe_instantiate(op::Function, args...) = maybe_instantiate_default(op, args...)

function maybe_instantiate(bc::Broadcasted{<:Termwise})
    if maybe_instantiate_coeffwise(typeof(bc))
        return maybe_instantiate_coeffs(bc)
    else
        return maybe_instantiate(bc.f, map(maybe_instantiate, bc.args)...)
    end
end

instantiate(bc::Broadcasted{<:Termwise}) = maybe_instantiate(bc)

# -----------------------------------------------------------------------------
#
# Optimized versions for term-by-term instantiating.
#
# -----------------------------------------------------------------------------
function merge(a::TermsIterable{Order}, b::TermsIterable{Order}, leftop, rightop, mergeop) where Order <: MonomialOrder
    leftop′(x) = _ownedop(leftop, isowned(a), x)
    rightop′(x) = _ownedop(rightop, isowned(b), x)
    mergeop′(x, y) = _ownedop(mergeop, isowned(a), x, isowned(b), y)
    return TermsBy(
        Order(),
        promote_type(polynomialtype(a), polynomialtype(b)),
        eduction(
            MergingTransducer(nzterms(a), Order(), leftop′, rightop′, mergeop′, monomial, coefficient, _constructterm) |> Filter(!iszero),
            nzterms(b),
        ),
        Val(true),
        termsbound(a) + termsbound(b),
    )
end

maybe_instantiate(op::typeof(+), a::TermsIterable, b::TermsIterable) = merge(a, b, +, +, +)
maybe_instantiate(op::typeof(-), a::TermsIterable, b::TermsIterable) = merge(a, b, +, -, -)

function maybe_instantiate(op::typeof(*), a::TermsIterable{Order}, b::Owned{<:Union{TermBy{Order}, MonomialBy{Order}, Number}}) where Order
    return TermsBy(
        Order(),
        promote_type(polynomialtype(a), typeof(b.value)),
        eduction(
            Map(a_i -> _ownedop(*, isowned(a), a_i, Val(false), b.value)) |> Filter(!iszero),
            nzterms(a),
        ),
        Val(true),
        termsbound(a),
    )
end

function maybe_instantiate(op::typeof(*), a::Owned{<:Union{TermBy{Order}, MonomialBy{Order}, Number}}, b::TermsIterable{Order}) where Order
    return TermsBy(
        Order(),
        promote_type(typeof(a.value), polynomialtype(b)),
        eduction(
            Map(b_i -> _ownedop(*, Val(false), a.value, isowned(b), b_i)) |> Filter(!iszero),
            nzterms(b),
        ),
        Val(true),
        termsbound(b),
    )
end
# -----------------------------------------------------------------------------
#
# Optimized versions for coefficient-wise instantiating
#
# -----------------------------------------------------------------------------
maybe_instantiate_coeffwise(::Type) = false
maybe_instantiate_coeffwise(::Type{<:Owned{<:DensePolynomialBy}}) = true
maybe_instantiate_coeffwise(::Type{<:Owned{<:Number}}) = true
@generated function maybe_instantiate_coeffwise(::Type{Broadcasted{Style, Nothing, F, Args}}) where {Style, F, Args}
    return all(maybe_instantiate_coeffwise, Args.types)
end

function maybe_instantiate_coeffs(bc::Broadcasted{Termwise{Order, P}}) where {Order, P}
    bcf = flatten(bc)
    return maybe_instantiate_coeffs_generated(bcf)
end

@generated function maybe_instantiate_coeffs_generated(bcf::B) where
            B <: Broadcasted{Termwise{Order, P}, Nothing, Op, Args} where
            {Order, P, Op, Args}

    indices = 1:length(Args.types)
    poly_indices = filter(indices) do ix
        Args.types[ix] <: Owned{<:DensePolynomialBy}
    end
    args_expr = [:(bcf.args[$ix].value) for ix in indices]
    lengths_expr = [:(length($a.coeffs)) for a in args_expr]
    zero_expr = [:(zero(basering($a))) for a in args_expr]
    poly_args_expr = args_expr[poly_indices]
    poly_lengths_expr = lengths_expr[poly_indices]

    code = quote
        N = max($(poly_lengths_expr...))
        # TODO: use in-place if we own any of the source polynomials
        coeffs = Vector{basering(P)}(undef, N)
    end
    for selection in combinations(poly_indices)
        complement = setdiff(poly_indices, selection)
        selected_poly_lengths_expr   = lengths_expr[selection]
        unselected_poly_lengths_expr = lengths_expr[complement]

        args_expr = map(1:length(Args.types)) do ix
            if ix in poly_indices
                if ix in selection
                    :(view(bcf.args[$ix].value.coeffs, lo:hi))
                else
                    zero_expr[ix]
                end
            else
                args_expr[ix]
            end
        end
        push!(code.args, :(let
            lo = max(0, $(unselected_poly_lengths_expr...)) + 1
            hi = min($(selected_poly_lengths_expr...))
            if lo <= hi
                broadcast!(bcf.f, dotview(coeffs, lo:hi), $(args_expr...))
            end
        end))
    end

    push!(code.args, quote
        N = findlast(!iszero, coeffs)
        resize!(coeffs, something(N, 0))
        P(coeffs)
    end)

    return code
end

# -----------------------------------------------------------------------------
#
# Copy methods
#
# -----------------------------------------------------------------------------
function copy(bc::Broadcasted{Termwise{Order, P}}) where P <: PolynomialBy{Order} where Order
    @assertvalid copy(instantiate(withownership(bc, nothing)))
end

# This is just the intended body of copyto! below, but I need to call it from
# the handcrafted version as well. My solution with `invoke` gives a segfault
# in Julia's code generator (Julia bug) so I'll just manually disentangle them.
function _copyto!(dest, bc)
    destix = findlast(a -> dest === a, flatten(bc).args)
    bc = withownership(bc, destix)
    if !isnothing(destix)
        d = copy(instantiate(bc))
        copy!(dest, d)
    else
        copyto_unaliased!(dest, instantiate(bc))
    end
    @assertvalid dest
end

function copyto_unaliased!(dest, x::TermsIterable)
    sizehint!(dest, termsbound(x))
    copy!(dest, nzterms(x))
end

function copyto_unaliased!(dest::PolynomialBy{Order}, src::TermsBy{Order, P, <:Eduction}) where {Order, P}
    xf, coll = Transducer(src.iter), src.iter.coll

    resize!(dest.coeffs, termsbound(src))
    resize!(dest.monomials, termsbound(src))

    function step(state, term)
        state += 1
        @inbounds dest.coeffs[state] = coefficient(term)
        @inbounds dest.monomials[state] = monomial(term)
        state
    end
    function step(state)
        resize!(dest.coeffs, state)
        resize!(dest.monomials, state)
    end
    transduce(xf, step, 0, coll)

    return dest
end

materialize!(dest::P, bc::Broadcasted{Termwise{Order, P}}) where P <: PolynomialBy{Order} where Order = _copyto!(dest, bc)

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

function materialize!(dest::P, bc::HandOptimizedBroadcast{Order, C, M, P}) where {Order, C, M, P <: PolynomialBy{Order, C}}
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

    resize!(dest.monomials, n); for ix in 1:n; dest.monomials[ix] = monomials[ix]; end
    resize!(dest.coeffs, n);    for ix in 1:n; dest.coeffs[ix]    = coeffs[ix];    end
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
} where P <: DensePolynomial{M, C} where M <: AbstractMonomial{Order} where {C, Order}

function materialize!(g::P, bc::M4GBBroadcast{C, Order, M, P}) where {C, Order, M, P <: PolynomialBy{Order, C}}
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
