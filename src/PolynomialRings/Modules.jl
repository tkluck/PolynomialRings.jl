module Modules

using Nulls

import PolynomialRings.Polynomials: Polynomial, monomialorder
import PolynomialRings.MonomialOrderings: MonomialOrder
import PolynomialRings.Monomials: AbstractMonomial
import PolynomialRings.Terms: Term
import PolynomialRings.Operators: RedType, Lead, Full, Tail

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
import PolynomialRings.Operators: one_step_div, one_step_rem, one_step_divrem
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

iszero(x::AbstractArray{P}) where P<:Polynomial = (i = findfirst(x); i>0 ? iszero(x[i]) : true)

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

termtype(p::AbstractArray{<:Polynomial}) = Signature{termtype(eltype(p)), Int}
termtype(P::Type{<:AbstractArray{<:Polynomial}}) = Signature{termtype(eltype(P)), Int}
monomialtype(p::AbstractArray{<:Polynomial}) = Signature{monomialtype(eltype(p)), Int}
monomialtype(p::Type{<:AbstractArray{<:Polynomial}}) = Signature{monomialtype(eltype(p)), Int}

*(s::Signature,m::Union{AbstractMonomial,Term,Number})  = Signature(s.i, s.m * m)
*(m::Union{AbstractMonomial,Term,Number}, s::Signature) = Signature(s.i, s.m * m)
maybe_div(s::Signature, t::Signature)            = s.i == t.i ? maybe_div(s.m, t.m) : null
lcm_degree(s::Signature, t::Signature)           = s.i == t.i ? lcm_degree(s.m, t.m) : null
lcm_multipliers(s::Signature, t::Signature)      = s.i == t.i ? lcm_multipliers(s.m, t.m) : null
total_degree(s::Signature)                       = total_degree(s.m)
lt(o::MonomialOrder, s::Signature, t::Signature) = s.i > t.i || (s.i == t.i && lt(o, s.m, t.m))
==(s::S, t::S) where S <: Signature = s.i == t.i && s.m == t.m
iszero(s::Signature{<:Term}) = iszero(s.m)

coefficient(s::Signature{<:Term}) = coefficient(s.m)
monomial(s::Signature{<:Term}) = Signature(s.i, monomial(s.m))


leading_row(x::AbstractArray{<:Polynomial}) = findfirst(x)
leading_term(x::AbstractArray{P}) where P<:Polynomial = leading_term(monomialorder(P), x)
leading_term(o::MonomialOrder, x::AbstractArray{P}) where P<:Polynomial = Signature(leading_row(x), leading_term(o, x[leading_row(x)]))
leading_monomial(x::AbstractArray{P}) where P<:Polynomial = leading_monomial(monomialorder(P), x)
leading_monomial(o::MonomialOrder, x::AbstractArray{P}) where P<:Polynomial = Signature(leading_row(x), leading_monomial(o, x[leading_row(x)]))
leading_coefficient(x::AbstractArray{P}) where P<:Polynomial = leading_coefficient(monomialorder(P), x)
leading_coefficient(o::MonomialOrder, x::AbstractArray{P}) where P<:Polynomial = leading_coefficient(o, x[leading_row(x)])

function one_step_divrem(redtype::RedType, o::MonomialOrder, a::A, b::A) where A<:AbstractArray{<:Polynomial}
    i = findfirst(b)
    if i>0
        (q,r) = divrem(redtype, o, a[i], b[i])
        if iszero(q)
            # make sure to maintain object identity for a
            return q, a
        else
            return q, a - q*b
        end
    else
        return zero(P), a
    end
end

one_step_div(redtype::RedType, o::MonomialOrder, a::A, b::A) where A<:AbstractArray{<:Polynomial} = one_step_divrem(redtype, o, a, b)[1]
one_step_rem(redtype::RedType, o::MonomialOrder, a::A, b::A) where A<:AbstractArray{<:Polynomial} = one_step_divrem(redtype, o, a, b)[2]

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
# The following code is copied from base/sparse/linalg.jl
# (https://github.com/JuliaLang/julia/blob/93168a68268a2023c0da5f14e75ccb807cc4fc35/base/sparse/linalg.jl#L50)
# except ::Number has been replaced by ::Polynomial
import Base: A_mul_B!, Ac_mul_B!, At_mul_B!
for (f, op, transp) in ((:A_mul_B, :identity, false),
                        (:Ac_mul_B, :ctranspose, true),
                        (:At_mul_B, :transpose, true))
    @eval begin
        function $(Symbol(f,:!))(α::Polynomial, A::SparseMatrixCSC, B::StridedVecOrMat, β::Polynomial, C::StridedVecOrMat)
            if $transp
                A.n == size(C, 1) || throw(DimensionMismatch())
                A.m == size(B, 1) || throw(DimensionMismatch())
            else
                A.n == size(B, 1) || throw(DimensionMismatch())
                A.m == size(C, 1) || throw(DimensionMismatch())
            end
            size(B, 2) == size(C, 2) || throw(DimensionMismatch())
            nzv = A.nzval
            rv = A.rowval
            if β != 1
                β != 0 ? scale!(C, β) : fill!(C, zero(eltype(C)))
            end
            for k = 1:size(C, 2)
                for col = 1:A.n
                    if $transp
                        tmp = zero(eltype(C))
                        @inbounds for j = A.colptr[col]:(A.colptr[col + 1] - 1)
                            tmp += $(op)(nzv[j])*B[rv[j],k]
                        end
                        C[col,k] += α*tmp
                    else
                        αxj = α*B[col,k]
                        @inbounds for j = A.colptr[col]:(A.colptr[col + 1] - 1)
                            C[rv[j], k] += nzv[j]*αxj
                        end
                    end
                end
            end
            C
        end
    end
end

end
