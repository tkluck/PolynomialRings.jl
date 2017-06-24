module NamedPolynomials

import PolynomialRings: generators, ⊗
import PolynomialRings.Polynomials: Polynomial
import PolynomialRings.Constructors: free_generators
import PolynomialRings.Polynomials: Polynomial, terms, termtype
import PolynomialRings.Terms: Term, basering, monomial, coefficient
import PolynomialRings.Monomials: TupleMonomial, VectorMonomial, AbstractMonomial
import PolynomialRings.Util: lazymap

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: promote_rule, convert
import Base: +,*,-,==,zero,one
import PolynomialRings: iszero


"""
    NamedPolynomial{P<:Polynomial, Names}

A type representing variable names + a storage format.
"""
struct NamedPolynomial{P<:Polynomial, Names}
    p::P
end

polynomialtype(::Type{NamedPolynomial{P,Names}}) where P <: Polynomial where Names = P


# -----------------------------------------------------------------------------
#
# Promoting scalars to polynomials
#
# -----------------------------------------------------------------------------

promote_rule(::Type{NP}, ::Type{C}) where NP <: NamedPolynomial{P, Names} where P <: Polynomial where {C,Names} = NamedPolynomial{promote_type(P, C), Names}

convert(::Type{NP}, a::C) where NP <: NamedPolynomial{P, Names} where P <: Polynomial where {C,Names} = NP(convert(promote_type(P,C), a))

# -----------------------------------------------------------------------------
#
# Pass-through operations
#
# -----------------------------------------------------------------------------
+(a::NP,b::NP) where NP <: NamedPolynomial = NP(a.p+b.p)
-(a::NP,b::NP) where NP <: NamedPolynomial = NP(a.p-b.p)
*(a::NP,b::NP) where NP <: NamedPolynomial = NP(a.p*b.p)

==(a::NP,b::NP) where NP <: NamedPolynomial = a.p==b.p
iszero(a::NamedPolynomial) = iszero(a.p)
zero(::Type{NP}) where NP <: NamedPolynomial = NP(zero(polynomialtype(NP)))
one(::Type{NP})  where NP <: NamedPolynomial = NP( one(polynomialtype(NP)))

# -----------------------------------------------------------------------------
#
# Constructing polynomial_rings
#
# -----------------------------------------------------------------------------
function polynomial_ring(basering::Type, symbols::Symbol...)
    Names = Tuple{symbols...}
    gens = free_generators(length(symbols))
    NP = NamedPolynomial{eltype(gens), Names}

    return NP, map(g->NP(g), gens)
end

function generic_coefficients(::Type{NP}, name::Symbol) where NP <: NamedPolynomial
    P = polynomialtype(NP)
    C = Polynomial{Vector{Term{VectorMonomial{SparseVector{Int,Int}}, Int}}, :deglex}
    NP2 = NamedPolynomial{C, name}

    return lazymap(g->NP2(g)⊗one(P), generators(C))
end

# -----------------------------------------------------------------------------
#
# Promotions for different variable name sets
#
# -----------------------------------------------------------------------------
_fieldtypes{T <: Tuple}(t::Type{T}) = Symbol[fieldtype(T, i) for i in 1:nfields(T)]

@generated function _convert_monomial(::Type{T}, ::Type{U}, monomial::AbstractMonomial) where T <: Tuple where U <: Tuple
    for j in 1:nfields(U)
        if !any(fieldtype(T,i) == fieldtype(U,j) for i in 1:nfields(T))
            throw(ArgumentError("Cannot convert variables $U to variables $T"))
        end
    end
    :( _lossy_convert_monomial(T, U, monomial) )
end

@generated function _lossy_convert_monomial(::Type{T}, ::Type{U}, monomial::AbstractMonomial) where T <: Tuple where U <: Tuple
    # create an expression that calls the tuple constructor. No arguments -- so far
    converter = :( tuple() )
    for i in 1:nfields(T)
        # for every result field, add the constant 0 as an argument
        push!(converter.args, 0)
        for j in 1:nfields(U)
            if fieldtype(T, i) == fieldtype(U,j)
                # HOWEVER, if it actually also exists in U, then replace the 0
                # by reading from exponent_tuple
                converter.args[end]= :( monomial[$j] )
                break
            end
        end
    end
    return :( TupleMonomial( $converter ) )
end

function promote_rule(::Type{NP1}, ::Type{NP2}) where NP1 <: NamedPolynomial{P1, Names1} where NP2 <: NamedPolynomial{P2, Names2} where {P1<:Polynomial,P2<:Polynomial,Names1<:Tuple,Names2<:Tuple}
    AllNames = Set()
    union!(AllNames, _fieldtypes(Names1))
    union!(AllNames, _fieldtypes(Names2))
    Symbols = sort(collect(AllNames))
    Names = Tuple{Symbols...}
    N = length(Symbols)
    C = promote_type(basering(P1), basering(P2))
    return NamedPolynomial{Polynomial{Vector{Term{TupleMonomial{N,Int},C}}, :degrevlex}, Names}
end

function convert(::Type{NP1}, a::NP2) where NP1 <: NamedPolynomial{P1, Names1} where NP2 <: NamedPolynomial{P2, Names2} where {P1<:Polynomial,P2<:Polynomial,Names1<:Tuple,Names2<:Tuple}
    f = t->termtype(P1)( _convert_monomial(Names1, Names2, monomial(t)), coefficient(t) )
    NP1(P1(map(f, terms(a.p))))
end

end
