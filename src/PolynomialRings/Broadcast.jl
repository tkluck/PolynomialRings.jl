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

struct Termwise{Order, P} <: BroadcastStyle end

BroadcastStyle(::Type{<:RefValue{P}}) where P<:Polynomial = Termwise{typeof(monomialorder(P)), P}()
BroadcastStyle(s::T, t::T) where T<:Termwise = s
BroadcastStyle(s::Termwise, t::AbstractArrayStyle{0}) = s
BroadcastStyle(s::Termwise, t::BroadcastStyle) = t

const BrTermwise{Order,P} = Broadcasted{Termwise{Order,P}}
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

const TermsBy{Order} = Union{
    BrTermwise{Order},
    RefValue{<:PolynomialBy{Order}},
    InPlace{<:PolynomialBy{Order}},
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
function iterterms(op::typeof(*), a::PossiblyBigInt, b::InPlace{<:PolynomialBy{Order,BigInt}}) where Order
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
function iterterms(op::typeof(*), a::InPlace{<:PolynomialBy{Order,BigInt}}, b::PossiblyBigInt) where Order
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

mark_inplace(y, x) = y
mark_inplace(bc::RefValue, x) = bc[] === x ? InPlace(bc[]) : bc
mark_inplace(bc::Broadcasted{St}, x) where St <: Termwise = Broadcasted{St}(bc.f, map(y->mark_inplace(y, x), bc.args))

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
