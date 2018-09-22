module Modules

import PolynomialRings.Polynomials: Polynomial, monomialorder, basering
import PolynomialRings.MonomialOrderings: MonomialOrder
import PolynomialRings.Monomials: AbstractMonomial
import PolynomialRings.Terms: Term
import PolynomialRings.Operators: RedType, Lead, Full, Tail

import Base: keytype
keytype(a::AbstractArray) = CartesianIndex{ndims(a)}
keytype(a::AbstractVector) = Int

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: iszero, div, rem, divrem, *, ==
import Base.Order: lt
import PolynomialRings: leading_row, leading_term, leading_monomial, leading_coefficient, base_extend
import PolynomialRings: termtype, monomialtype
import PolynomialRings: maybe_div, lcm_degree, lcm_multipliers
import PolynomialRings: leaddiv, leadrem, leaddivrem
import PolynomialRings.Operators: one_step_div!
import PolynomialRings.Terms: coefficient, monomial
import PolynomialRings.Monomials: total_degree

# -----------------------------------------------------------------------------
#
# An abstract module element is either a ring element (module over itself) or
# an array.
#
# -----------------------------------------------------------------------------
AbstractModuleElement{P<:Polynomial} = Union{P, AbstractArray{P}}
modulebasering(::Type{A}) where A <: AbstractModuleElement{P} where P<:Polynomial = P
modulebasering(::A)       where A <: AbstractModuleElement{P} where P<:Polynomial = modulebasering(A)

iszero(x::AbstractArray{P}) where P<:Polynomial = all(iszero, x)

base_extend(x::AbstractArray{P}, ::Type{C}) where P<:Polynomial where C = map(p->base_extend(p,C), x)
base_extend(x::AbstractArray{P})            where P<:Polynomial         = map(base_extend, x)

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
lt(o::MonomialOrder, s::Signature, t::Signature) = s.i > t.i || (s.i == t.i && lt(o, s.m, t.m))
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

function one_step_div!(redtype::RedType, o::MonomialOrder, a::A, b::A) where A<:AbstractArray{<:Polynomial}
    i = findfirst(!iszero, b)
    if i !== nothing && !iszero(a[i])
        lt_a = leading_term(o, a[i])
        lt_b = leading_term(o, b[i])
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

leaddivrem(f::A,g::AbstractVector{A}) where A<:AbstractArray{P} where P<:Polynomial = divrem(Lead(), monomialorder(P), f, g)
divrem(f::A,g::AbstractVector{A})     where A<:AbstractArray{P} where P<:Polynomial = divrem(Full(), monomialorder(P), f, g)
leadrem(f::A,g::AbstractVector{A})    where A<:AbstractArray{P} where P<:Polynomial = rem(Lead(), monomialorder(P), f, g)
rem(f::A,g::AbstractVector{A})        where A<:AbstractArray{P} where P<:Polynomial = rem(Full(), monomialorder(P), f, g)
leaddiv(f::A,g::AbstractVector{A})    where A<:AbstractArray{P} where P<:Polynomial = div(Lead(), monomialorder(P), f, g)
div(f::A,g::AbstractVector{A})        where A<:AbstractArray{P} where P<:Polynomial = div(Full(), monomialorder(P), f, g)


# compatibility: a ring is just a rank-one module over itself, so the 'leading'
# row is just the first one.
leading_row(x::Polynomial) = 1

# Work around sparse-dense multiplication in Base only working for eltype() <: Number
import LinearAlgebra: mul!
mul!(A, B, C, α::Polynomial, β::Polynomial) = mul!(A, B, C, convert(basering(α),α), convert(basering(β), β))

end
