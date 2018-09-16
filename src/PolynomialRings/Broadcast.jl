module Broadcast

using Base: RefValue
using Base.Broadcast: Style, AbstractArrayStyle, BroadcastStyle, Broadcasted
using PolynomialRings: monomialorder
using PolynomialRings.Constants: Zero, One
using PolynomialRings.Util: ParallelIter, ConstantIter, Start
using PolynomialRings.MonomialOrderings: MonomialOrder
using PolynomialRings.Monomials: AbstractMonomial
using PolynomialRings.Terms: Term, monomial, coefficient
using PolynomialRings.Polynomials: Polynomial, PolynomialOver, PolynomialBy, terms, termtype

Base.Broadcast.broadcastable(p::AbstractMonomial) = Ref(p)
Base.Broadcast.broadcastable(p::Term) = Ref(p)
Base.Broadcast.broadcastable(p::Polynomial) = Ref(p)

struct Termwise{Order} <: BroadcastStyle end

BroadcastStyle(::Type{<:RefValue{P}}) where P<:Polynomial = Termwise{typeof(monomialorder(P))}()
BroadcastStyle(s::Termwise, t::Termwise) = s
BroadcastStyle(s::Termwise, t::AbstractArrayStyle{0}) = s
BroadcastStyle(s::Termwise, t::BroadcastStyle) = t

const BrStPoly{Order} = Broadcasted{Termwise{Order}}

Base.Broadcast.instantiate(bc::BrStPoly) = bc

function Base.copy(bc::BrStPoly)
    P = Base.Broadcast._broadcast_getindex_eltype(bc)
    x = deepcopy(zero(P))
    Base.Broadcast.materialize!(x, bc)
end

const PlusMinus = Union{typeof(+), typeof(-)}
# Eagerly evaluate all expressions involving polynomials, except for the
# ones we explicitly know how to do. This ensures that e.g. operations
# with different variables/orders get eagerly evaluated.
Base.Broadcast.broadcasted(::Termwise, op, a, b) = op(a[],b[])

const TermsBy{Order} = Union{BrStPoly{Order}, RefValue{<:PolynomialBy{Order}}}
# We know how to lazily do +/- if the orders are the same
Base.Broadcast.broadcasted(st::Termwise{Order}, op::PlusMinus, a::TermsBy{Order}, b::TermsBy{Order}) where Order = Base.Broadcast.Broadcasted{typeof(st)}(op, (a, b))

# we also know how to lazily do * when scaling by a Number or base ring element
Base.Broadcast.broadcasted(st::Termwise{Order}, op::typeof(*), a::RefValue{<:PolynomialOver{C,Order}}, b::RefValue{C}) where {Order,C} = Base.Broadcast.Broadcasted{typeof(st)}(op, (a, b))
Base.Broadcast.broadcasted(st::Termwise{Order}, op::typeof(*), a::RefValue{<:PolynomialBy{Order}}, b::Number) where Order = Base.Broadcast.Broadcasted{typeof(st)}(op, (a, b))
Base.Broadcast.broadcasted(st::Termwise{Order}, op::typeof(*), a::RefValue{C}, b::RefValue{<:PolynomialOver{C,Order}}) where {Order,C} = Base.Broadcast.Broadcasted{typeof(st)}(op, (a, b))
Base.Broadcast.broadcasted(st::Termwise{Order}, op::typeof(*), a::Number, b::RefValue{<:PolynomialBy{Order}}) where Order = Base.Broadcast.Broadcasted{typeof(st)}(op, (a, b))

struct TermsMap{Order,Terms,Op}
    terms::Terms
    op::Op
    bound::Int
end
TermsMap(op::Op, o::Order, terms::Terms, bound=length(terms)) where {Op, Order,Terms} = TermsMap{Order,Terms,Op}(terms, op, bound)
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

termsbound(p::TermsMap) = p.bound
iterterms(p::TermsMap) = p

termsbound(a::Polynomial) = length(terms(a))
iterterms(a::Polynomial) = terms(a)

prepare(x::RefValue) = x[]
prepare(bc::BrStPoly) = bc.f(map(prepare, bc.args)...)
prepare(x) = x
function prepare(bc::Broadcasted{<:Termwise, Nothing, Op, <:Tuple{A, B}}) where {Op, A, B}
    a = prepare(bc.args[1])
    b = prepare(bc.args[2])
    prepare(bc.f, a, b)
end

function prepare(op::PlusMinus, a::TermsBy{Order}, b::TermsBy{Order}) where Order
    ≺(a,b) = Base.Order.lt(Order(), a, b)

    summands = ParallelIter(
        monomial, coefficient, ≺,
        Zero(), Zero(),
        iterterms(a), iterterms(b),
    )
    bound = termsbound(a) + termsbound(b)
    TermsMap(Order(), summands, bound) do (m, cleft, cright)
        coeff = op(cleft, cright)
        iszero(coeff) ? nothing : Term(m, coeff)
    end
end

for T = [Number, AbstractMonomial, Term]
    @eval function prepare(op::typeof(*), a::TermsBy{Order}, b::$T) where Order
        bound = termsbound(a)
        TermsMap(Order(), iterterms(a), bound) do t
            iszero(b) ? nothing : t*b
        end
    end

    @eval function prepare(op::typeof(*), a::$T, b::TermsBy{Order}) where Order
        bound = termsbound(b)
        TermsMap(Order(), iterterms(b), bound) do t
            iszero(a) ? nothing : a*t
        end
    end
end

prepare(op, a, b) = op(a, b)

function Base.Broadcast.materialize!(x::Polynomial, bc::Broadcasted{Style{Polynomial}})
    bc′ = prepare(bc)
    resize!(x.terms, termsbound(bc′))
    n = 0
    for t in iterterms(bc′)
        @inbounds x.terms[n+=1] = t
    end
    resize!(x.terms, n)
    x
end

end
