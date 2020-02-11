module Monomials

import SparseArrays: SparseVector, sparsevec

import ..AbstractMonomials: AbstractMonomial
import ..MonomialOrderings: MonomialOrder
import PolynomialRings: monomialtype

include("Monomials/TupleMonomials.jl")
include("Monomials/VectorMonomials.jl")
include("Monomials/IndexedMonomials.jl")

import .TupleMonomials: TupleMonomial
import .VectorMonomials: VectorMonomial

# -----------------------------------------------------------------------------
#
# Conversion from Vector to tuple (sparse to dense)
#
# -----------------------------------------------------------------------------

promote_rule(::Type{<:TupleMonomial{N,I,Order}}, ::Type{<:VectorMonomial{V,J,Order}}) where {N,V,I,J,Order} = TupleMonomial{N,promote_type(I,J),Order}

# -----------------------------------------------------------------------------
#
# Constructing a monomial from an expression
#
# -----------------------------------------------------------------------------
recurse_monomial_from_expr(x) = x
recurse_monomial_from_expr(x::Symbol) = :(exp(monomialtype($(QuoteNode(x))), (1,)))

function recurse_monomial_from_expr(expr::Expr)
    if expr.head == :ref
        x, i = expr.args
        return :(exp(monomialtype($(QuoteNode(x)), Inf), sparsevec([$i], [1])))
    elseif expr.head == :call
        args = map(recurse_monomial_from_expr, expr.args[2:end])
        return Expr(expr.head, esc(expr.args[1]), args...)
    else
        return Expr(expr.head, map(recurse_monomial_from_expr, expr.args)...)
    end
end

macro monomial(expr)
    return Expr(:(::), recurse_monomial_from_expr(expr), :AbstractMonomial)
end

end
