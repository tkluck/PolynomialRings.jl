module Broadcast

using Base: RefValue
using Base.Broadcast: Style, AbstractArrayStyle, BroadcastStyle, Broadcasted
using PolynomialRings.Constants: Zero, One
using PolynomialRings.Util: ParallelIter, Start
using PolynomialRings.Monomials: AbstractMonomial
using PolynomialRings.Terms: Term, monomial, coefficient
using PolynomialRings.Polynomials: Polynomial, PolynomialOver, PolynomialBy, terms, termtype

Base.Broadcast.broadcastable(p::AbstractMonomial) = Ref(p)
Base.Broadcast.broadcastable(p::Term) = Ref(p)
Base.Broadcast.broadcastable(p::Polynomial) = Ref(p)

Base.BroadcastStyle(::Type{<:RefValue{<:Polynomial}}) = Style{Polynomial}()
Base.BroadcastStyle(s::Style{Polynomial}, t::Style{Polynomial}) = s
Base.BroadcastStyle(s::Style{Polynomial}, t::AbstractArrayStyle{0}) = s
Base.BroadcastStyle(s::Style{Polynomial}, t::BroadcastStyle) = t

Base.Broadcast.instantiate(bc::Broadcasted{Style{Polynomial}}) = bc

function Base.copy(bc::Broadcasted{Style{Polynomial}})
    P = Base.Broadcast._broadcast_getindex_eltype(bc)
    x = deepcopy(zero(P))
    Base.Broadcast.materialize!(x, bc)
end

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
prepare(bc::Broadcasted{Style{Polynomial}}) = bc.f(map(prepare, bc.args)...)
prepare(x) = x
function prepare(bc::Broadcasted{Style{Polynomial}, Nothing, Op, <:Tuple{A, B}}) where {Op, A, B}
    a = prepare(bc.args[1])
    b = prepare(bc.args[2])
    prepare(bc.f, a, b)
end

const PlusMinus = Union{typeof(+), typeof(-)}
const TermsBy{Order} = Union{TermsMap{Order}, PolynomialBy{Order}}
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
