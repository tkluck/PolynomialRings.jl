module Modules

import Base: *, +, -, ÷
import Base: iszero, zero, div, rem, divrem, *, ==
import Base: keytype, hash, lcm
import LinearAlgebra: mul!
import SparseArrays: AbstractSparseArray, SparseVector, sparsevec, spzeros, nonzeros

import ..MonomialOrderings: MonomialOrder, @withmonomialorder
import ..Monomials: AbstractMonomial
import ..Monomials: total_degree
import ..Operators: RedType, Lead, Full, Tail
import ..Operators: one_step_div!, one_step_xdiv!, content, integral_fraction
import ..Polynomials: Polynomial, monomialorder, basering, tail
import ..Polynomials: nzterms, nzrevterms, nztailterms
import ..Terms: Term
import ..Terms: coefficient, monomial
import PolynomialRings: leaddiv, leadrem, leaddivrem
import PolynomialRings: leading_row, leading_term, leading_monomial, leading_coefficient, base_extend
import PolynomialRings: maybe_div, divides, lcm_degree, lcm_multipliers
import PolynomialRings: termtype, monomialtype

# This should probably be in Base; see
# https://github.com/JuliaLang/julia/pull/27749
if VERSION < v"1.2-"
    keytype(a::AbstractArray) = keytype(typeof(a))
    keytype(T::Type{<:AbstractArray}) = CartesianIndex{ndims(T)}
    keytype(::Type{<:AbstractVector}) = Int
end

iszero(x::SparseVector{<:Polynomial}) = all(iszero, nonzeros(x))

# see https://github.com/JuliaLang/julia/issues/31835
zero(a::AbstractArray{<:Polynomial}) = map(_ -> zero(eltype(a)), a)
zero(a::AbstractSparseArray{<:Polynomial}) = spzeros(eltype(a), size(a)...)

base_extend(x::AbstractArray{P}, ::Type{C}) where P<:Polynomial where C = map(p->base_extend(p,C), x)
base_extend(x::AbstractArray{P})            where P<:Polynomial         = map(base_extend, x)

content(x::AbstractArray{P}) where P<:Polynomial = gcd(map(content, x))

# -----------------------------------------------------------------------------
#
# The signature of a module element is just its leading monomial. We represent
# it by an index and the leading monomial at that index.
# an array.
#
# -----------------------------------------------------------------------------
struct Signature{M,I}
    i::I
    m::M
end

termtype(p::AbstractArray{<:Polynomial}) = Signature{termtype(eltype(p)), keytype(p)}
termtype(P::Type{<:AbstractArray{<:Polynomial}}) = Signature{termtype(eltype(P)), keytype(P)}
monomialtype(p::AbstractArray{<:Polynomial}) = Signature{monomialtype(eltype(p)), keytype(p)}
monomialtype(p::Type{<:AbstractArray{<:Polynomial}}) = Signature{monomialtype(eltype(p)), keytype(p)}

*(s::Signature,m::Union{AbstractMonomial,Term,Number})  = Signature(s.i, s.m * m)
*(m::Union{AbstractMonomial,Term,Number}, s::Signature) = Signature(s.i, s.m * m)
maybe_div(s::Signature, t::Signature)            = s.i == t.i ? maybe_div(s.m, t.m) : nothing
divides(s::Signature, t::Signature)              = s.i == t.i && divides(s.m, t.m)
lcm_degree(s::Signature, t::Signature)           = s.i == t.i ? lcm_degree(s.m, t.m) : nothing
lcm_multipliers(s::Signature, t::Signature)      = s.i == t.i ? lcm_multipliers(s.m, t.m) : nothing
lcm(s::Signature, t::Signature)                  = s.i == t.i ? Signature(s.i, lcm(s.m, t.m)) : nothing
total_degree(s::Signature)                       = total_degree(s.m)
Base.Order.lt(o::MonomialOrder, s::Signature, t::Signature) = s.i > t.i || (s.i == t.i && Base.Order.lt(o, s.m, t.m))
==(s::S, t::S) where S <: Signature = s.i == t.i && s.m == t.m
iszero(s::Signature{<:Term}) = iszero(s.m)

coefficient(s::Signature{<:Term}) = coefficient(s.m)
monomial(s::Signature{<:Term}) = Signature(s.i, monomial(s.m))

hash(s::Signature, h::UInt) = hash(s.i, hash(s.m))

leading_row(x::AbstractArray{<:Polynomial}) = findfirst(!iszero, x)

function leading_row(x::SparseVector{<:Polynomial})
    n = findfirst(!iszero, x.nzval)
    return x.nzind[n]
end

function leading_term(x::AbstractArray{P}; order::MonomialOrder=monomialorder(x)) where P<:Polynomial
    ix = leading_row(x)
    return Signature(ix, leading_term(x[ix], order=order))
end

function leading_monomial(x::AbstractArray{P}; order::MonomialOrder=monomialorder(x)) where P<:Polynomial
    ix = leading_row(x)
    return Signature(ix, leading_monomial(x[ix], order=order))
end

leading_coefficient(x::AbstractArray{P}; order::MonomialOrder=monomialorder(x)) where P<:Polynomial = leading_coefficient(x[leading_row(x)], order=order)

function Base.Order.lt(order::MonomialOrder, s::A, t::A) where A<:AbstractArray{P} where P<:Polynomial
    iszero(t) && return false
    iszero(s) && return true
    Base.Order.lt(order, leading_monomial(s, order=order), leading_monomial(t, order=order))
end

Base.getindex(a::AbstractArray{<:Polynomial}, s::Signature{<:AbstractMonomial}) = a[s.i][s.m]
function Base.getindex(a::SparseVector{<:Polynomial}, s::Signature{<:AbstractMonomial})
    ixrange = searchsorted(a.nzind, s.i)
    if isempty(ixrange)
        return zero(modulebasering(a))
    else
        return a.nzval[ixrange[1]][s.m]
    end
end

function one_step_div!(a::A, b::A; order::MonomialOrder, redtype::RedType) where A<:AbstractArray{<:Polynomial}
    @withmonomialorder order
    @assert size(a) == size(b)
    i = findfirst(!iszero, b)
    if i !== nothing && !iszero(a[i])
        lt_a = leading_term(a[i])
        lt_b = leading_term(b[i])
        factor = maybe_div(lt_a, lt_b)
        if factor !== nothing
            for i in eachindex(a)
                if iszero(a[i]) # possibly a sparse zero, so don't try in-place
                    a[i] -= factor * b[i]
                else
                    @. a[i] -= factor * b[i]
                end
            end
        end
        return factor
    else
        return nothing
    end
end

function one_step_xdiv!(a::A, b::A; order::MonomialOrder, redtype::RedType) where A<:AbstractArray{<:Polynomial}
    @withmonomialorder order
    @assert size(a) == size(b)
    i = findfirst(!iszero, b)
    if i !== nothing && !iszero(a[i])
        lt_a = leading_monomial(a[i])
        lt_b = leading_monomial(b[i])
        factor = maybe_div(lt_a, lt_b)
        if factor !== nothing
            c1 = leading_coefficient(a[i])
            c2 = leading_coefficient(b[i])
            m1, m2 = lcm_multipliers(c1, c2)
            for j in eachindex(a)
                if iszero(a[i]) # possibly a sparse zero, so don't try in-place
                    a[j] = m1 * a[j] - m2 * (factor * b[j])
                else
                    @. a[j] = m1 * a[j] - m2 * (factor * b[j])
                end
            end
            return m1, m2 * factor
        else
            return nothing
        end
    else
        return nothing
    end
end

leaddivrem(f::A,g::AbstractVector{A}) where A<:AbstractArray{P} where P<:Polynomial = divrem(f, g, order=monomialorder(P), redtype=Lead())
divrem(f::A,g::AbstractVector{A})     where A<:AbstractArray{P} where P<:Polynomial = divrem(f, g, order=monomialorder(P), redtype=Full())
leadrem(f::A,g::AbstractVector{A})    where A<:AbstractArray{P} where P<:Polynomial = rem(f, g, order=monomialorder(P), redtype=Lead())
rem(f::A,g::AbstractVector{A})        where A<:AbstractArray{P} where P<:Polynomial = rem(f, g, order=monomialorder(P), redtype=Full())
leaddiv(f::A,g::AbstractVector{A})    where A<:AbstractArray{P} where P<:Polynomial = div(f, g, order=monomialorder(P), redtype=Lead())
div(f::A,g::AbstractVector{A})        where A<:AbstractArray{P} where P<:Polynomial = div(f, g, order=monomialorder(P), redtype=Full())


# compatibility: a ring is just a rank-one module over itself, so the 'leading'
# row is just the first one.
leading_row(x::Polynomial) = 1

# Work around sparse-dense multiplication in Base only working for eltype() <: Number
mul!(A, B, C, α::Polynomial, β::Polynomial) = mul!(A, B, C, convert(basering(α),α), convert(basering(β), β))

nzterms(x::AbstractArray{<:Polynomial}; order) = (
    Signature(ix, t)
    for (ix, x_i) in Iterators.reverse(enumerate(x))
    for t in nzterms(x_i, order=order)
)

nzrevterms(x::AbstractArray{<:Polynomial}; order) = (
    Signature(ix, t)
    for (ix, x_i) in enumerate(x)
    for t in nzrevterms(x_i, order=order)
)

nzterms(x::SparseVector{<:Polynomial}; order) = (
    Signature(ix, t)
    for (ix, x_i) in Iterators.reverse(zip(x.nzind, x.nzval))
    for t in nzterms(x_i, order=order)
)

nzrevterms(x::SparseVector{<:Polynomial}; order) = (
    Signature(ix, t)
    for (ix, x_i) in zip(x.nzind, x.nzval)
    for t in nzrevterms(x_i, order=order)
)

function tail(x::AbstractVector{<:Polynomial}; order)
    res = deepcopy(x)
    ix = leading_row(x)
    res[ix] = tail(res[ix]; order=order)
    return res
end

"""

    TransformedModuleElement

A combination of a module element and a transformation that yielded
it through linear operations. This is a utility type for keeping track
of all transformations happening during e.g. a Gröbner basis transformation.

The invariant is that

    n*p = tr*inputs

where `inputs` is the array that was passed to `withtransformations()`.

The role of the integer `n` is to avoid needing rationals in `tr`.

"""
mutable struct TransformedModuleElement{P,M,I}
    p::M
    tr::SparseVector{P, Int}
    n::I
end
# gathering leading terms etc
leading_monomial(m::TransformedModuleElement; order) = leading_monomial(m.p, order=order)
leading_coefficient(m::TransformedModuleElement; order) = leading_coefficient(m.p, order=order)
leading_term(m::TransformedModuleElement; order) = leading_term(m.p, order=order)
content(m::TransformedModuleElement) = content(m.p)
Base.Order.lt(o::MonomialOrder, a::T, b::T) where T<:TransformedModuleElement = Base.Order.lt(o, a.p, b.p)
# linear operations
*(f, g::TransformedModuleElement) = TransformedModuleElement(f*g.p, f*g.tr, g.n)
*(f::TransformedModuleElement, g) = TransformedModuleElement(f.p*g, f.tr*g, f.n)
# TODO: reduce the tr/n fraction
÷(f::TransformedModuleElement, g) = TransformedModuleElement(f.p÷g, f.tr, f.n*g)
function +(f::T, g::T) where T<:TransformedModuleElement
    m1, m2 = lcm_multipliers(f.n, g.n)
    N = m1*f.n
    TransformedModuleElement(f.p + g.p, m1*f.tr + m2*g.tr, N)
end
function -(f::T, g::T) where T<:TransformedModuleElement
    m1, m2 = lcm_multipliers(f.n, g.n)
    N = m1*f.n
    TransformedModuleElement(f.p - g.p, m1*f.tr - m2*g.tr, N)
end
+(f::T) where T<:TransformedModuleElement = TransformedModuleElement(+f.p, +f.tr, +f.n)
-(f::T) where T<:TransformedModuleElement = TransformedModuleElement(-f.p, -f.tr, +f.n)
Base.iszero(f::TransformedModuleElement) = iszero(f.p)
# broadcasting: just evaluate it all eagerly
struct TransformedStyle <: Base.Broadcast.BroadcastStyle end
Base.Broadcast.broadcastable(f::TransformedModuleElement) = f
Base.Broadcast.BroadcastStyle(::Type{<:TransformedModuleElement}) = TransformedStyle()
Base.Broadcast.BroadcastStyle(::TransformedStyle, ::Base.Broadcast.BroadcastStyle) = TransformedStyle()
eager(x) = x
eager(x::Base.RefValue) = x[]
Base.Broadcast.broadcasted(::TransformedStyle, op, args...) = op(map(eager, args)...)
function Base.Broadcast.materialize!(tgt::TransformedModuleElement, src::TransformedModuleElement)
    tgt.p = src.p
    tgt.tr = src.tr
    tgt.n = src.n
end

function one_step_xdiv!(a::A, b::A; order::MonomialOrder, redtype::RedType) where A<:TransformedModuleElement
    res = one_step_xdiv!(a.p, b.p, order=order, redtype=redtype)
    if res !== nothing
        m, factor = res
        a.tr = m * b.n * a.tr - factor * a.n * b.tr
        a.n *= b.n
    end
    return res
end

function withtransformations(x::AbstractVector{M}) where M
    P = modulebasering(M)
    m = length(x)
    map(enumerate(x)) do (i, x_i)
        x_i, n = basering(P) <: Rational ? integral_fraction(x_i) : (x_i, one(P))
        tr = sparsevec(Dict(i=>P(n)), m)
        TransformedModuleElement(x_i, tr, one(basering(P)))
    end
end

function separatetransformation(x::AbstractVector{<:TransformedModuleElement{P}}) where P
    result         = map(a->a.p,       x)
    transformation = map(a->a.tr//a.n, x)

    columns = isempty(transformation) ? 0 : length(transformation[1])

    flat_tr = spzeros(base_extend(P), length(result), columns)
    for (i,t) in enumerate(transformation)
        flat_tr[i,:] = t
    end
    return result, flat_tr
end

# -----------------------------------------------------------------------------
#
# An abstract module element is either a ring element (module over itself) or
# an array. It may also include the transformation that yielded it, so
# TransformedModuleElement is also an option.
#
# -----------------------------------------------------------------------------
AbstractModuleElement{P<:Polynomial} = Union{P, AbstractArray{P}, TransformedModuleElement{P}}
modulebasering(::Type{A}) where A <: AbstractModuleElement{P} where P<:Polynomial = P
modulebasering(::A)       where A <: AbstractModuleElement{P} where P<:Polynomial = modulebasering(A)

end
