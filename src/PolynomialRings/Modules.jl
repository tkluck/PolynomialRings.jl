module Modules

import Base: *, +, -, ÷
import Base: iszero, zero, div, rem, divrem, *, ==
import Base: keytype, hash, lcm
import LinearAlgebra: mul!
import SparseArrays: AbstractSparseArray, SparseVector, sparsevec, spzeros, nonzeros

import InPlace: @inplace, inclusiveinplace!

import ..AbstractMonomials: AbstractMonomial
import ..Constants: One
import ..Expansions: atomicorder
import ..MonomialOrderings: MonomialOrder, @withmonomialorder
import ..MonomialOrderings: monomialorderkey, monomialorderkeypair
import ..Operators: RedType, Lead, Full, Tail
import ..Operators: one_step_div!, one_step_xdiv!, content, integral_fraction
import ..Polynomials: Polynomial, PolynomialBy, monomialorder, basering, tail
import ..Signatures: Sig
import ..StandardMonomialOrderings: LexCombinationOrder, KeyOrder
import ..Terms: Term
import ..Terms: coefficient, monomial
import ..Util: nzpairs
import PolynomialRings: leaddiv, leadrem, leaddivrem
import PolynomialRings: leading_row, leading_term, leading_monomial, leading_coefficient, base_extend
import PolynomialRings: maybe_div, divides, lcm_degree, lcm_multipliers, mutuallyprime
import PolynomialRings: termtype, monomialtype, base_restrict, deg

iszero(x::SparseVector{<:Polynomial}) = all(iszero, nonzeros(x))
"""
    iszero(x::AbstractArray{<:Polynomial}, ix)

Return true if iszero(x[ix]). In the case of sparse arrays, this
is faster than iszero(x[xi]) because a new zero(eltype(x)) does
not need to be allocated.
"""
iszero(x::AbstractArray{<:Polynomial}, ix) = iszero(x[ix])
function iszero(x::SparseVector{<:Polynomial}, ix::Integer)
    r = searchsorted(x.nzind, ix)
    return isempty(r) || iszero(x.nzval[first(r)])
end

# un-alias the polynomials
zero(a::AbstractArray{<:Polynomial}) = map(_ -> zero(eltype(a)), a)

# see https://github.com/JuliaLang/julia/issues/31835
if VERSION < v"1.4-"
    zero(a::AbstractSparseArray{<:Polynomial}) = spzeros(eltype(a), size(a)...)
end

base_extend(x::AbstractArray{P}, ::Type{C}) where P<:Polynomial where C = map(p->base_extend(p,C), x)
base_extend(x::AbstractArray{P})            where P<:Polynomial         = map(base_extend, x)

content(x::AbstractArray{P}) where P<:Polynomial = gcd(map(content, x))
content(x::AbstractSparseArray{P}) where P<:Polynomial = gcd(map(content, nonzeros(x)))

termtype(p::AbstractArray{<:Polynomial}) = Sig{keytype(p), termtype(eltype(p))}
termtype(P::Type{<:AbstractArray{<:Polynomial}}) = Sig{keytype(P), termtype(eltype(P))}
monomialtype(p::AbstractArray{<:Polynomial}) = Sig{keytype(p), monomialtype(eltype(p))}
monomialtype(p::Type{<:AbstractArray{<:Polynomial}}) = Sig{keytype(p), monomialtype(eltype(p))}
monomialorder(p::Type{<:AbstractArray{<:Polynomial}}) = LexCombinationOrder(KeyOrder(), monomialorder(eltype(p)))
monomialorder(p::AbstractArray{<:Polynomial}) = monomialorder(typeof(p))

leading_row(x::AbstractArray{<:Polynomial}) = findfirst(!iszero, x)

function leading_row(x::SparseVector{<:Polynomial})
    n = findfirst(!iszero, x.nzval)
    return x.nzind[n]
end

function leading_term(x::AbstractArray{P}; order::MonomialOrder=monomialorder(x)) where P<:Polynomial
    ix = leading_row(x)
    return Sig(ix, leading_term(x[ix], order=order))
end

function leading_monomial(x::AbstractArray{P}; order::MonomialOrder=monomialorder(x)) where P<:Polynomial
    ix = leading_row(x)
    return Sig(ix, leading_monomial(x[ix], order=order))
end

function monomialorderkey(order, a::AbstractArray{<:Polynomial})
    maximum(order, (monomialorderkey(order, x) for x in a if !iszero(x)))
end

function monomialorderkey(order, a::SparseVector{<:Polynomial})
    maximum(order, (monomialorderkey(order, x) for x in a.nzval))
end

leading_coefficient(x::AbstractArray{P}; order::MonomialOrder=monomialorder(x)) where P<:Polynomial = leading_coefficient(x[leading_row(x)], order=order)


function one_step_div!(a::A, b::A; order::MonomialOrder, redtype::RedType) where A<:AbstractArray{<:Polynomial}
    @withmonomialorder order
    @assert size(a) == size(b)
    i = findfirst(!iszero, b)
    if i !== nothing && !iszero(a[i])
        lt_a = leading_term(a[i])
        lt_b = leading_term(b[i])
        factor = maybe_div(lt_a, lt_b)
        if factor !== nothing
            for (j, b_j) in nzpairs(b)
                a_j = a[j]
                if iszero(a_j) # possibly a sparse zero, so don't try in-place
                    a[j] = -factor * b_j
                else
                    @. a_j -= factor * b_j
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
            for (j, b_j) in nzpairs(b)
                a_j = a[j]
                if iszero(a_j) # possibly a sparse zero, so be sure to assign back
                    # TODO: if just - m2 * (factor * b_j) is faster, use that
                    @. a_j = m1 * a_j - m2 * (factor * b_j)
                    a[j] = a_j
                else
                    @. a_j = m1 * a_j - m2 * (factor * b_j)
                end
            end
            for (j, a_j) in nzpairs(a)
                if iszero(b, j)
                    @inplace a[j] *= m1
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
leading_row(x::AbstractMonomial) = 1
leading_row(x::Term) = 1

# Work around sparse-dense multiplication in Base only working for eltype() <: Number
mul!(A, B, C, α::Polynomial, β::Polynomial) = mul!(A, B, C, convert(basering(α),α), convert(basering(β), β))

function tail(x::AbstractArray{<:Polynomial}; order)
    res = deepcopy(x)
    ix = leading_row(x)
    res[ix] = tail(res[ix]; order=atomicorder(order))
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
# type information
monomialtype(::Type{TransformedModuleElement{P,M,I}}) where {P,M,I} = monomialtype(M)
keytype(::Type{TransformedModuleElement{P,M,I}}) where {P,M,I} = keytype(M)

monomialorder(::Type{TransformedModuleElement{P,M,I}}) where {P,M,I} = monomialorder(P)
# gathering leading terms etc
leading_monomial(m::TransformedModuleElement; order) = leading_monomial(m.p, order=order)
leading_coefficient(m::TransformedModuleElement; order) = leading_coefficient(m.p, order=order)
leading_term(m::TransformedModuleElement; order) = leading_term(m.p, order=order)
leading_row(m::TransformedModuleElement) = leading_row(m.p)
content(m::TransformedModuleElement) = content(m.p)

monomialorderkey(order, a::TransformedModuleElement) = monomialorderkey(order, a.p)
monomialorderkeypair(order, a::TransformedModuleElement) = monomialorderkeypair(order, a.p)
# resolve ambiguity
monomialorderkeypair(order::typeof(KeyOrder()), a::TransformedModuleElement) = monomialorderkeypair(order, a.p)

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
==(f::T, g::T) where T<:TransformedModuleElement = f.p == g.p && f.tr == g.tr && f.n == g.n
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
        op!(a_tr, b_tr) = a_tr .= (m * b.n) .* a_tr .- (factor * a.n) .* b_tr
        @. a.tr = op!(a.tr, b.tr)
        a.n *= b.n
    end
    return res
end

function withtransformations(x::AbstractVector{M}) where M
    P = modulebasering(M)
    PP = basering(P) <: Rational ? base_restrict(P) : P
    m = length(x)
    map(enumerate(x)) do (i, x_i)
        x_i, n = basering(P) <: Rational ? integral_fraction(x_i) : (x_i, one(P))
        tr = sparsevec(Dict(i=>PP(n)), m)
        TransformedModuleElement(x_i, tr, one(basering(PP)))
    end
end

function separatetransformation(x::AbstractVector{<:TransformedModuleElement{P}}) where P
    result         = map(a->a.p,             x)
    transformation = map(a->(1//a.n) * a.tr, x)

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
