module NamedPolynomials

import PolynomialRings: termtype, terms, namestype, variablesymbols, exptype, monomialtype, allvariablesymbols
import PolynomialRings.Polynomials: Polynomial, monomialorder
import PolynomialRings.Terms: Term, basering, monomial, coefficient
import PolynomialRings.Monomials: TupleMonomial, AbstractMonomial, _construct
import PolynomialRings.VariableNames: Named, Numbered

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: promote_rule, convert

# -----------------------------------------------------------------------------
#
# Type definitions
#
# -----------------------------------------------------------------------------
const NamedMonomial                 = AbstractMonomial{<:Named}
const NumberedMonomial              = AbstractMonomial{<:Numbered}
const PolynomialOver{C,Names,Order} = Polynomial{<:AbstractVector{<:Term{<:AbstractMonomial{Names}, C}},Order}
const NamedPolynomial{C,Order}      = PolynomialOver{C,<:Named,Order}
const NumberedPolynomial{C,Order}   = PolynomialOver{C,<:Numbered,Order}

# -----------------------------------------------------------------------------
#
# Generating symbols that do not conflict with existing ones
#
# -----------------------------------------------------------------------------
function unused_variable(P, a)
    E = exptype(P)
    N = max_variable_index(a)
    P(_construct(monomialtype(P), i->i==(N+1)?one(E):zero(E), N+1:N+1))
end
unused_variable(p::Polynomial)                  = unused_variable(typeof(p), p)
unused_variable(a::AbstractArray{<:Polynomial}) = unused_variable(eltype(a), a)

# -----------------------------------------------------------------------------
#
# Coefficient promotions when variable names are the same
#
# -----------------------------------------------------------------------------
function promote_rule(P1::Type{<:PolynomialOver{C,N}}, P2::Type{<:PolynomialOver{D,N}}) where {C,D,N}
    return base_extend(P1, D)
end

# separate versions for N<:Named and N<:Numbered to resolve method ambiguity
# with the version for which P and p do not have the same names.
function convert(P::Type{<:PolynomialOver{C,N}}, p::PolynomialOver{D,N}) where {C,D,N<:Named}
    return base_extend(p, C)
end
function convert(P::Type{<:PolynomialOver{C,N}}, p::PolynomialOver{D,N}) where {C,D,N<:Numbered}
    return base_extend(p, C)
end
# and short-circuit the non-conversions
convert(P::Type{<:PolynomialOver{C,N}}, p::PolynomialOver{C,N}) where {C,N<:Named} = p
convert(P::Type{<:PolynomialOver{C,N}}, p::PolynomialOver{C,N}) where {C,N<:Numbered} = p
# -----------------------------------------------------------------------------
#
# Promotions for different variable name sets
#
# -----------------------------------------------------------------------------

convert(::Type{M}, monomial::M) where M<:NamedMonomial = monomial

@generated function convert(::Type{M}, monomial::AbstractMonomial) where M<:NamedMonomial
    src = variablesymbols(monomial)
    dest = variablesymbols(M)
    for s in src
        if !(s in dest)
            throw(ArgumentError("Cannot convert variables $src to variables $dest"))
        end
    end
    :( _lossy_convert_monomial(M, monomial) )
end

@generated function _lossy_convert_monomial(::Type{M}, monomial::AbstractMonomial) where M
    src = variablesymbols(monomial)
    dest = variablesymbols(M)
    # create an expression that calls the tuple constructor. No arguments -- so far
    converter = :( tuple() )
    degree = :( +(0) )
    for d in dest
        # for every result field, add the constant 0 as an argument
        push!(converter.args, :( zero(exptype(monomial)) ))
        for (j,s) in enumerate(src)
            if d == s
                # HOWEVER, if it actually also exists in src, then replace the 0
                # by reading from exponent_tuple
                converter.args[end]= :( monomial[$j] )
                push!(degree.args,:( monomial[$j] ))
                break
            end
        end
    end
    return :( M($converter, $degree ) )
end

_allpolynomialvars(x::Type) = Set()
_allpolynomialvars(x::Type{P}) where P<:NamedPolynomial = union(variablesymbols(P), _allpolynomialvars(basering(P)))
_allothervars(x::Type) = setdiff(allvariablesymbols(x), _allpolynomialvars(x))
_coeff(x::Type) = x
_coeff(::Type{P}) where P<:NamedPolynomial = _coeff(basering(P))
_exptype(x::Type) = Union{}
_exptype(::Type{P}) where P<:NamedPolynomial = promote_type(exptype(P), _exptype(basering(P)))

function promote_rule(::Type{P1}, ::Type{P2}) where P1 <: Polynomial where P2 <: Polynomial
    if namestype(P1) <: Named && namestype(P2) <: Named
        AllNames = Set()
        free_variables = union(
                               setdiff(_allpolynomialvars(P1), _allothervars(P2)),
                               setdiff(_allpolynomialvars(P2), _allothervars(P1)),
                              )
        Symbols = sort(collect(free_variables))
        Names = tuple(Symbols...)
        N = length(Symbols)
        C = promote_type(_coeff(P1), _coeff(P2))
        I = promote_type(_exptype(P1), _exptype(P2))

        return Polynomial{Vector{Term{TupleMonomial{N, I, Named{Names}}, C}}, :degrevlex}
    else
        return Union{}
    end
end

function promote_rule(::Type{P1}, ::Type{P2}) where P1 <: NamedPolynomial where P2 <: NumberedPolynomial
    return P2 ⊗ P1
end

using PolynomialRings

function convert(::Type{P1}, a::P2) where P1 <: NamedPolynomial where P2 <: Polynomial
    T = termtype(P1)
    # Without the leading T[ ... ], type inference makes this an Array{Any}, so
    # it can't be omitted.
    converted_terms = T[ T(m,c) for (m,c) in PolynomialRings.Expansions._expansion(a, namestype(P1)) ]
    # zero may happen if conversion to the basering is lossy; e.g. mapping ℚ[α]
    # to the number field ℚ[α]/Ideal(α^2-2)
    # TODO: needs testing as soon as number fields are part of this package.
    filter!(!iszero, converted_terms)
    sort!(converted_terms, order=monomialorder(P1))
    P1(converted_terms)
end

convert(::Type{P}, a::P) where P <: NamedPolynomial = a
end
