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

To achieve this, the default implementation for `termwise` eagerly
evaluates the broadcast operation. Only those operations that we _know_ to work
term-wise efficiently get a more specific override.

### Lazy evaluation

For the operations that _do_ work well term-wise, we implement a function
`termwise` that takes a `Broadcasted` object or a scalar, and returns
either an `Owned{<:Polynomial}` or a `SparseTermsBy` object. These can be composed
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
`SparseTermsBy` object.
"""
module Broadcast

import Base.Broadcast: AbstractArrayStyle, BroadcastStyle, Broadcasted
import Base.Broadcast: broadcastable, broadcasted, Unknown
import Base.Broadcast: materialize!, materialize, copyto!, copy, flatten, dotview

import Combinatorics: combinations
import InPlace: @inplace, inplace!
import Transducers: eduction, Map, Filter, Eduction, Transducer, transduce

import ..AbstractMonomials: AbstractMonomial
import ..MonomialOrderings: MonomialOrder
import ..Polynomials: Polynomial, DensePolynomial, PolynomialBy, SparsePolynomialBy, DensePolynomialBy, nzterms, nztermscount, TermBy, MonomialBy
import ..Terms: Term, monomial, coefficient, basering
import ..Util: MergingTransducer, @assertvalid
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
BroadcastStyle(s::Termwise, t::AbstractArrayStyle) = t
BroadcastStyle(s::Termwise, t::BroadcastStyle) = Unknown()

# -----------------------------------------------------------------------------
#
# Override `materialize(!)` so we can mark the destination as `owned` and
# operate in-place.
#
# -----------------------------------------------------------------------------
function materialize(bc::Broadcasted{<:Termwise{P}}) where P
    if can_termwise_vectorbroadcast(typeof(bc))
        return termwise_vectorbroadcast(flatten(bc))
    end
    bc_withownership = withownership(bc)
    copy(termwise(bc_withownership))
end

function materialize!(dest::PolynomialBy{Order}, bc::Broadcasted{<:Termwise{Order}}) where Order
    if can_termwise_vectorbroadcast(typeof(bc))
        return termwise_vectorbroadcast(flatten(bc), dest)
    end
    destix = findlast(a -> dest === a, flatten(bc).args)
    bc_withownership = withownership(bc, destix)
    if !isnothing(destix)
        d = copy(termwise(bc_withownership))
        copy!(dest, d)
    else
        copyto!(dest, termwise(bc_withownership))
    end
end

# -----------------------------------------------------------------------------
#
# A type for marking ownership either at runtime (when `dest` is also an
# operand) or at compile time (intermediate results).
#
# -----------------------------------------------------------------------------
struct Owned{Value, IsOwned}
    value :: Value
    owned :: IsOwned
end

ownership(x::Owned) = x.owned

isowned(::Val{owned}) where owned = owned
isowned(x::Bool) = x
isowned(x) = isowned(ownership(x))
value(x::Owned) = x.value

function Owned(f::Function, args::Owned...)
    # we can't be sure the return value is owned if
    # we don't know anything about `f`; the result
    # will usually be owned but e.g. not in the case
    # `f == identity`. So take Val(false) here.
    Owned(f(map(a -> a.value, args)...), Val(false))
end

const MathOperator = Union{typeof(+), typeof(-), typeof(*), typeof(/), typeof(//)}
function Owned(f::MathOperator, x::Owned, y::Owned)
    res = isowned(x) ?
              inplace!(f, value(x), value(x), value(y)) :
          isowned(y) ?
              inplace!(f, value(y), value(x), value(y)) :
              f(value(x), value(y))
    Owned(res, Val(true))
end

ownedop(f, owned...) = (args...) -> value(Owned(f, map(Owned, args, owned)...))

withownership(x::Owned, args...) = error("Can't apply withownership twice!")
withownership(x, destix=nothing) = withownership(x, destix, 1)
function withownership(x, destix, myix)
    owned = isbitstype(typeof(x)) ?
                Val(true) :
            isnothing(destix) ?
                Val(false) :
                destix == myix
    Owned(x, owned)
end
"""
    withownership(bc::Broadcasted, destix)

Wrap the leaf arguments of a (possibly) nested broadcast structure in
`Owned` objects, with `isowned(...) = true` if and only if its flat
index is equal to `destix`. Suggested use:

    destix = findlast(a -> dest === a, flatten(bc).args)
    bc_withownership = withownership(bc, destix)
"""
@generated function withownership(bc::BC, destix, myix) where BC <: Broadcasted{Tw, Axes, F, Args} where {Tw <: Termwise, Axes, F, Args}
    argtuple = :( tuple() )
    expr = :( Broadcasted{Tw}(bc.f, $argtuple) )
    for ix = 1:length(Args.types)
        push!(argtuple.args, :( withownership(bc.args[$ix], destix, myix + $(ix - 1)) ))
    end
    return expr
end

# -----------------------------------------------------------------------------
#
# Lazy return values for the `termwise` function
#
# -----------------------------------------------------------------------------
struct SparseTermsBy{Order, P, Iter, Owned}
    order :: Order
    P     :: Type{P}
    iter  :: Iter
    owned :: Owned
    bound :: Int
end

struct DenseTermsBy{Order, P, Coeffs, Owned}
    order  :: Order
    P      :: Type{P}
    coeffs :: Coeffs
    owned  :: Owned
end

const TermsIterable{Order} = Union{Owned{<:PolynomialBy{Order}}, SparseTermsBy{Order}, DenseTermsBy{Order}}

ownership(x::SparseTermsBy) = x.owned
ownership(x::DenseTermsBy) = x.owned

nzterms(x::Owned{<:Polynomial}) = nzterms(x.value)
nzterms(x::SparseTermsBy) = x.iter
nzterms(x::DenseTermsBy) = nzterms(x.P(x.coeffs))

termsbound(x::SparseTermsBy) = x.bound
termsbound(x::DenseTermsBy) = count(!iszero, x.coeffs)
termsbound(x::Owned{<:Polynomial}) = nztermscount(x.value)

polynomialtype(x::SparseTermsBy) = x.P
polynomialtype(x::DenseTermsBy) = x.P
polynomialtype(x::Owned{<:Polynomial}) = typeof(x.value)

# -----------------------------------------------------------------------------
#
# Implement the `copy` methods for everything that we can get from `termwise`
#
# -----------------------------------------------------------------------------
copy(x::Owned) = isowned(x) ? x.value : deepcopy(x.value)
copy(x::SparseTermsBy) = copyto!(zero(x.P), x)
copy(x::DenseTermsBy) = if isowned(x) && x.coeffs isa Vector
    x.P(x.coeffs)
else
    x.P(copy(x.coeffs))
end

owned(x::Owned) = x
owned(x::SparseTermsBy) = Owned(copy(x), Val(true))
owned(x::DenseTermsBy) = Owned(copy(x), Val(true))

# TODO: do we own it?
copyto!(dest::Polynomial, x::Owned) = copy!(dest, nzterms(x))
copyto!(dest::Polynomial, x::SparseTermsBy) = copy!(dest, nzterms(x))
copyto!(dest::Polynomial, x::DenseTermsBy) = copy(dest, nzterms(x))

# -----------------------------------------------------------------------------
#
# compute how to handle a broadcast operation term-wise
#
# -----------------------------------------------------------------------------
function termwise(bc::Broadcasted{<:Termwise})
    if can_termwise_vectorbroadcast(typeof(bc))
        return termwise_vectorbroadcast(flatten(bc))
    else
        return termwise(bc.f, map(termwise, bc.args)...)
    end
end

termwise(x) = error("Please apply withownership before instantiating")
termwise(x::Owned) = x
# fallback implementation: apply `f` to the materialized arguments
termwise(f, args...) = Owned(f, map(owned, args)...)

# -----------------------------------------------------------------------------
#
# Implement the vector-broadcasted operation
#
# -----------------------------------------------------------------------------
can_termwise_vectorbroadcast(::Type) = false
can_termwise_vectorbroadcast(::Type{<:Owned{<:DensePolynomialBy}}) = true
can_termwise_vectorbroadcast(::Type{<:Owned{<:Number}}) = true
@generated function can_termwise_vectorbroadcast(::Type{Broadcasted{Style, Nothing, F, Args}}) where {Style, F, Args}
    # TODO: should also check the operation (F)
    return all(can_termwise_vectorbroadcast, Args.types)
end

@generated function termwise_vectorbroadcast(bcf::B, dest=zero(P)) where
            B <: Broadcasted{Termwise{Order, P}, Nothing, Op, Args} where
            {Order, P, Op, Args}
    #=
    In general, the coefficient vectors have different lengths, and
    we need to broadcast them by extending with zeros. For example,
    in the case of two arguments, we want to do

        f = bcf.f; a, b = bcf.args
        N = min(length(a), length(b))
        res[1 : hi] .= @views f.(a[1 : hi], b[1 : hi])
        res[hi + 1 : length(a)] .= @views f.(a[hi + 1 : length(a)], zero(eltype(b)))
        res[hi + 1 : length(b)] .= @views f.(zero(eltype(a)), b[hi + 1 : length(b)])

    When there's more than two arguments, we need to have one such line for
    every possible combination of arguments that are shorter than a given
    length. This is what we are generating below.
    =#
    indices = 1:length(Args.types)
    poly_indices = filter(indices) do ix
        Args.types[ix] <: Owned{<:DensePolynomialBy}
    end
    args_expr = [:(bcf.args[$ix].value) for ix in indices]
    lengths_names = [Symbol(:length, ix) for ix in indices]
    lengths_expr = [:(length($a.coeffs)) for a in args_expr]
    zero_expr = [:(zero(basering($a))) for a in args_expr]
    poly_args_expr = args_expr[poly_indices]
    poly_lengths_names = lengths_names[poly_indices]
    poly_lengths_expr = lengths_expr[poly_indices]
    poly_lengths_assgn = [:( $name = $expr ) for (name, expr) in zip(poly_lengths_names, poly_lengths_expr)]

    code = quote
        $(poly_lengths_assgn...)
        N = max($(poly_lengths_names...))
        coeffs = dest.coeffs
        resize!(coeffs, N)
    end
    for selection in combinations(poly_indices)
        complement = setdiff(poly_indices, selection)
        selected_poly_lengths_expr   = lengths_names[selection]
        unselected_poly_lengths_expr = lengths_names[complement]

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
        Owned(P(coeffs), Val(true))
    end)

    return code
end

# -----------------------------------------------------------------------------
#
# Optimized versions for term-by-term instantiating.
#
# -----------------------------------------------------------------------------
function merge(a::TermsIterable{Order}, b::TermsIterable{Order}, leftop, rightop, mergeop) where Order <: MonomialOrder
    leftop′ = ownedop(leftop, ownership(a))
    rightop′ = ownedop(rightop, ownership(b))
    mergeop′ = ownedop(mergeop, ownership(a), ownership(b))
    constructterm(m, c) = Term(m, c)

    return SparseTermsBy(
        Order(),
        promote_type(polynomialtype(a), polynomialtype(b)),
        eduction(
            MergingTransducer(nzterms(a), Order(), leftop′, rightop′, mergeop′, monomial, coefficient, constructterm) |> Filter(!iszero),
            nzterms(b),
        ),
        Val(true),
        termsbound(a) + termsbound(b),
    )
end

termwise(op::typeof(+), a::TermsIterable, b::TermsIterable) = merge(a, b, +, +, +)
termwise(op::typeof(-), a::TermsIterable, b::TermsIterable) = merge(a, b, +, -, -)

function termwise(op::typeof(*), a::TermsIterable{Order}, b::Owned{<:Union{TermBy{Order}, MonomialBy{Order}, Number}}) where Order
    return SparseTermsBy(
        Order(),
        promote_type(polynomialtype(a), typeof(b.value)),
        eduction(
            Map(a_i -> value(Owned(*, Owned(a_i, Val(false)), b))) |> Filter(!iszero),
            nzterms(a),
        ),
        Val(true),
        termsbound(a),
    )
end

function termwise(op::typeof(*), a::Owned{<:Union{TermBy{Order}, MonomialBy{Order}, Number}}, b::TermsIterable{Order}) where Order
    return SparseTermsBy(
        Order(),
        promote_type(typeof(a.value), polynomialtype(b)),
        eduction(
            Map(b_i -> value(Owned(*, a, Owned(b_i, Val(false))))) |> Filter(!iszero),
            nzterms(b),
        ),
        Val(true),
        termsbound(b),
    )
end

# -----------------------------------------------------------------------------
#
# Copy method
#
# -----------------------------------------------------------------------------
function copyto!(dest::SparsePolynomialBy{Order}, src::SparseTermsBy{Order, P, <:Eduction}) where {Order, P}
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
} where P<:SparsePolynomialBy{Order} where M<:AbstractMonomial{Order} where C where Order

function materialize!(dest::P, bc::HandOptimizedBroadcast{Order, C, M, P}) where {Order, C, M, P <: SparsePolynomialBy{Order, C}}
    ≺(a,b) = Base.Order.lt(monomialorder(dest), a, b)

    m1 = bc.args[1].args[1]
    v1 = bc.args[1].args[2][]
    m2 = bc.args[2].args[1]
    t  = bc.args[2].args[2].args[1]
    v2 = bc.args[2].args[2].args[2]

    applicable = dest === v1 && dest !== v2
    if !applicable
        destix = findlast(a -> dest === a, flatten(bc).args)
        bc_withownership = withownership(bc, destix)
        return copyto!(dest, termwise(bc_withownership))
    end

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

function materialize!(g::P, bc::M4GBBroadcast{C, Order, M, P}) where {C, Order, M, P <: DensePolynomialBy{Order, C}}
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
