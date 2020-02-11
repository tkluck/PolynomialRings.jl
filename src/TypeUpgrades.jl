module TypeUpgrades

import Base: @pure
import SparseArrays: SparseVector

import ..AbstractMonomials: AbstractMonomial
import ..Constants: One
import ..MonomialOrderings: MonomialOrder
import ..Monomials.TupleMonomials: TupleMonomial
import ..Monomials.VectorMonomials: VectorMonomial
import ..NamingSchemes: NamingScheme
import ..Polynomials: SparsePolynomial
import ..StandardMonomialOrderings: MonomialOrdering
import ..Terms: Term
import PolynomialRings: namingscheme, monomialorder, monomialtype, termtype, polynomialtype, basering
import PolynomialRings: num_variables

monomialorder(names::Symbol...; rule=:degrevlex) = monomialorder(namingscheme(names...), rule)
monomialorder(name::Symbol, n::Number, rule=:degrevlex) = monomialorder(namingscheme(name, n), rule)

monomialorder(scheme::NamingScheme, rule=:degrevlex) = MonomialOrdering{rule, typeof(scheme)}()

monomialtype(scheme::NamingScheme, exptype=Int16) = monomialtype(monomialorder(scheme), exptype)

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

end # module
