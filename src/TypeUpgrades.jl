module TypeUpgrades

import Base: @pure
import SparseArrays: SparseVector

import ..AbstractMonomials: AbstractMonomial
import ..Constants: One, Zero, MinusOne, Constant
import ..MonomialOrderings: MonomialOrder
import ..Monomials.TupleMonomials: TupleMonomial
import ..Monomials.VectorMonomials: VectorMonomial
import ..NamingSchemes: NamingScheme, NamedVariable
import ..Polynomials: SparsePolynomial, Polynomial
import ..StandardMonomialOrderings: MonomialOrdering
import ..Terms: Term
import PolynomialRings: namingscheme, monomialorder, monomialtype, termtype, polynomialtype, basering
import PolynomialRings: num_variables

monomialorder(; rule=:degrevlex) = monomialorder(namingscheme(), rule)
monomialorder(names::Symbol...; rule=:degrevlex) = monomialorder(namingscheme(names...), rule)
monomialorder(name::Symbol, n::Number, rule=:degrevlex) = monomialorder(namingscheme(name, n), rule)

monomialorder(var::NamedVariable...; rule=:degrevlex) = monomialorder(namingscheme(var...), rule)

monomialorder(scheme::NamingScheme, rule=:degrevlex) = MonomialOrdering{rule, typeof(scheme)}()

monomialtype(scheme::NamingScheme, exptype=Int16) = monomialtype(monomialorder(scheme), exptype)
monomialtype(var::NamedVariable, exptype=Int16) = monomialtype(monomialorder(var), exptype)

function monomialtype(order::MonomialOrder, exptype=Int16)
    N = num_variables(namingscheme(order))
    if exptype == Union{}
        exptype = Int16
    end
    if iszero(N)
        return One
    elseif N < Inf
        return TupleMonomial{N, exptype, typeof(order)}
    else
        return VectorMonomial{SparseVector{exptype, Int}, exptype, typeof(order)}
    end
end

function monomialtype(names::Symbol...; order=:degrevlex, exptype::Type{<:Integer}=Int16)
    order = monomialorder(names...; rule=order)
    return monomialtype(order, exptype)
end

function monomialtype(name::Symbol, n::Number; order=:degrevlex, exptype::Type{<:Integer}=Int16)
    @assert n isa Integer || n == Inf
    order = monomialorder(name, n, order)
    return monomialtype(order, exptype)
end

termtype(scheme::NamingScheme, basering=Int, exptype=Int16) = termtype(monomialtype(scheme, exptype), basering)
termtype(order::MonomialOrder,  basering=Int, exptype=Int16) = termtype(monomialtype(order, exptype), basering)
termtype(M::Type{<:AbstractMonomial}, basering=Int) = Term{M, basering}

@pure function polynomialtype(scheme::NamingScheme, basering=Int; exptype=Int16, sparse=true)
    return polynomialtype(monomialtype(scheme, exptype), basering, sparse=sparse)
end

@pure function polynomialtype(order::MonomialOrder, basering=Int; exptype=Int16, sparse=true)
    return polynomialtype(monomialtype(order, exptype), basering, sparse=sparse)
end

@pure function polynomialtype(M::Type{<:AbstractMonomial}, basering=Int, sparse=true)
    return sparse ? SparsePolynomial{M, basering} : DensePolynomial{M, basering}
end

@pure function polynomialtype(T::Type{<:Term}; sparse=true)
    return polynomialtype(monomialtype(T), basering(T); sparse=sparse)
end

@pure function polynomialtype(scheme::NamingScheme, basering, exptype, sparse)
    return polynomialtype(monomialtype(scheme, exptype), basering, sparse)
end

@pure function polynomialtype(order::MonomialOrder, basering, exptype, sparse)
    return polynomialtype(monomialtype(order, exptype), basering, sparse)
end

@pure function polynomialtype(T::Type{<:Term}, sparse)
    return polynomialtype(monomialtype(T), basering(T), sparse)
end

for N = [Number, AbstractMonomial, Term, Polynomial]
    @eval begin
        Base.promote_rule(::Type{T}, ::Type{C}) where {T<:$N, C <: Constant} = T

        Base.convert(::Type{T}, ::One)      where T<:$N = one(T)
        Base.convert(::Type{T}, ::Zero)     where T<:$N = zero(T)
        Base.convert(::Type{T}, ::MinusOne) where T<:$N = -one(T)

        Base.convert(::Type{Union{T, One}}, ::One)           where T<:$N = One()
        Base.convert(::Type{Union{T, Zero}}, ::Zero)         where T<:$N = Zero()
        Base.convert(::Type{Union{T, MinusOne}}, ::MinusOne) where T<:$N = MinusOne()

        # fix method ambiguities
        Base.:*(x::$N, ::One) = deepcopy(x)
        Base.:*(::One, x::$N) = deepcopy(x)
        Base.:*(x::$N, ::MinusOne) = -x
        Base.:*(::MinusOne, x::$N) = -x

        Base.:+(x::$N, ::Zero) = deepcopy(x)
        Base.:-(x::$N, ::Zero) = deepcopy(x)
        Base.:*(x::$N, ::Zero) = zero(x)
        Base.:+(::Zero, x::$N) = deepcopy(x)
        Base.:-(::Zero, x::$N) = -x
        Base.:*(::Zero, x::$N) = zero(x)
    end
end

for C in [One, Zero, MinusOne]
    @eval begin
        Base.convert(::Type{$C}, ::$C) = $C()
    end
end


end # module
