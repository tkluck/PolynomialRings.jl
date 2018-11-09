module Modules

import Base.Order: lt
import Base: *, +, -, ÷
import Base: iszero, div, rem, divrem, *, ==
import Base: keytype
import LinearAlgebra: mul!
import SparseArrays: SparseVector, sparsevec, spzeros

import ..MonomialOrderings: MonomialOrder
import ..Monomials: AbstractMonomial
import ..Monomials: total_degree
import ..Operators: RedType, Lead, Full, Tail
import ..Operators: one_step_div!, one_step_xdiv!, content
import ..Polynomials: Polynomial, monomialorder, basering
import ..Terms: Term
import ..Terms: coefficient, monomial
import PolynomialRings: leaddiv, leadrem, leaddivrem
import PolynomialRings: leading_row, leading_term, leading_monomial, leading_coefficient, base_extend
import PolynomialRings: maybe_div, lcm_degree, lcm_multipliers
import PolynomialRings: termtype, monomialtype

# This should probably be in Base; see
# https://github.com/JuliaLang/julia/pull/27749
keytype(a::AbstractArray) = CartesianIndex{ndims(a)}
keytype(a::AbstractVector) = Int

iszero(x::AbstractArray{P}) where P<:Polynomial = all(iszero, x)

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
lcm_degree(s::Signature, t::Signature)           = s.i == t.i ? lcm_degree(s.m, t.m) : nothing
lcm_multipliers(s::Signature, t::Signature)      = s.i == t.i ? lcm_multipliers(s.m, t.m) : nothing
total_degree(s::Signature)                       = total_degree(s.m)
Base.Order.lt(o::MonomialOrder, s::Signature, t::Signature) = s.i > t.i || (s.i == t.i && lt(o, s.m, t.m))
==(s::S, t::S) where S <: Signature = s.i == t.i && s.m == t.m
iszero(s::Signature{<:Term}) = iszero(s.m)

coefficient(s::Signature{<:Term}) = coefficient(s.m)
monomial(s::Signature{<:Term}) = Signature(s.i, monomial(s.m))


leading_row(x::AbstractArray{<:Polynomial}) = findfirst(!iszero, x)
leading_term(x::AbstractArray{P}) where P<:Polynomial = leading_term(monomialorder(P), x)
leading_term(o::MonomialOrder, x::AbstractArray{P}) where P<:Polynomial = Signature(leading_row(x), leading_term(o, x[leading_row(x)]))
leading_monomial(x::AbstractArray{P}) where P<:Polynomial = leading_monomial(monomialorder(P), x)
leading_monomial(o::MonomialOrder, x::AbstractArray{P}) where P<:Polynomial = Signature(leading_row(x), leading_monomial(o, x[leading_row(x)]))
leading_coefficient(x::AbstractArray{P}) where P<:Polynomial = leading_coefficient(monomialorder(P), x)
leading_coefficient(o::MonomialOrder, x::AbstractArray{P}) where P<:Polynomial = leading_coefficient(o, x[leading_row(x)])

function Base.Order.lt(o::MonomialOrder, s::A, t::A) where A<:AbstractArray{P} where P<:Polynomial
    iszero(t) && return false
    iszero(s) && return true
    Base.Order.lt(o, leading_monomial(o, s), leading_monomial(o, t))
end

function one_step_div!(a::A, b::A; order::MonomialOrder, redtype::RedType) where A<:AbstractArray{<:Polynomial}
    i = findfirst(!iszero, b)
    if i !== nothing && !iszero(a[i])
        lt_a = leading_term(order, a[i])
        lt_b = leading_term(order, b[i])
        factor = maybe_div(lt_a, lt_b)
        if factor !== nothing
            for i in eachindex(a)
                a[i] -= factor * b[i]
                #if iszero(a[i]) # possibly a sparse zero, so don't try in-place
                #    a[i] -= factor * b[i]
                #else
                #    @. a[i] -= factor * b[i]
                #end
            end
        end
        return factor
    else
        return nothing
    end
end

function one_step_xdiv!(a::A, b::A; order::MonomialOrder, redtype::RedType) where A<:AbstractArray{<:Polynomial}
    i = findfirst(!iszero, b)
    if i !== nothing && !iszero(a[i])
        lt_a = leading_monomial(order, a[i])
        lt_b = leading_monomial(order, b[i])
        factor = maybe_div(lt_a, lt_b)
        if factor !== nothing
            c1 = leading_coefficient(order, a[i])
            c2 = leading_coefficient(order, b[i])
            m1, m2 = lcm_multipliers(c1, c2)
            for i in eachindex(a)
                a[i] = m1 * a[i] - m2 * (factor * b[i])
                #if iszero(a[i]) # possibly a sparse zero, so don't try in-place
                #    a[i] -= factor * b[i]
                #else
                #    @. a[i] -= factor * b[i]
                #end
            end
            return m1, factor
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
leading_monomial(o, m::TransformedModuleElement) = leading_monomial(o, m.p)
leading_coefficient(o, m::TransformedModuleElement) = leading_coefficient(o, m.p)
leading_term(o, m::TransformedModuleElement) = leading_term(o, m.p)
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
        a.tr = m * b.n * a.tr - factor * b.tr
        a.n *= b.n
    end
    return res
end

function withtransformations(x::AbstractVector{M}) where M
    P = modulebasering(M)
    n = length(x)
    map(enumerate(x)) do (i,x_i)
        tr = sparsevec(Dict(i=>one(P)), n)
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
