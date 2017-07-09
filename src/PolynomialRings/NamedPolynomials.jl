module NamedPolynomials

import PolynomialRings: generators, ⊗, base_extend, termtype, terms
import PolynomialRings.Polynomials: Polynomial, monomialorder
import PolynomialRings.Constructors: free_generators
import PolynomialRings.Polynomials: Polynomial
import PolynomialRings.Terms: Term, basering, monomial, coefficient
import PolynomialRings.Monomials: TupleMonomial, VectorMonomial, AbstractMonomial
import PolynomialRings.Util: lazymap

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import Base: promote_rule, convert, promote_type
import Base: +,*,-,==,zero,one,divrem,iszero,copy
import PolynomialRings: to_dense_monomials, max_variable_index, leading_term, lcm_multipliers, deg, exptype


_P = Union{Polynomial,Term,AbstractMonomial}
"""
    NamedPolynomial{P<:Polynomial, Names}

A type representing variable names + a storage format.
"""
struct NamedPolynomial{P<:_P, Names}
    p::P
end

polynomialtype(::Type{NamedPolynomial{P,Names}}) where {P,Names} = P
names(::Type{NamedPolynomial{P,Names}}) where {P,Names} = Names


# -----------------------------------------------------------------------------
#
# Promotions
#
# -----------------------------------------------------------------------------

function promote_rule(::Type{NP}, ::Type{C}) where NP <: NamedPolynomial{P, Names} where P <: Polynomial where {C,Names}
    rule_for_P = typejoin( promote_rule(P,C), promote_rule(C,P) )
    if rule_for_P === Union{}
        return rule_for_P
    else
        return NamedPolynomial{rule_for_P, Names}
    end
end

(::Type{NP})(a::NP) where NP <: NamedPolynomial = a

# -----------------------------------------------------------------------------
#
# Pass-through operations
#
# -----------------------------------------------------------------------------
+(a::NP,b::NP)      where NP <: NamedPolynomial = NP(a.p+b.p)
+(a::NP)            where NP <: NamedPolynomial = NP(+a.p)
-(a::NP,b::NP)      where NP <: NamedPolynomial = NP(a.p-b.p)
-(a::NP)            where NP <: NamedPolynomial = NP(-a.p)
*(a::NP,b::NP)      where NP <: NamedPolynomial = NP(a.p*b.p)
divrem(a::NP,b::NP) where NP <: NamedPolynomial = ((q,r) = divrem(a.p, b.p); (NP(q), NP(r)))

==(a::NP,b::NP) where NP <: NamedPolynomial = a.p==b.p
iszero(a::NamedPolynomial) = iszero(a.p)
zero(::Type{NP}) where NP <: NamedPolynomial = NP(zero(polynomialtype(NP)))
zero(a::NamedPolynomial) = zero(typeof(a))
one(::Type{NP})  where NP <: NamedPolynomial = NP( one(polynomialtype(NP)))
one(a::NamedPolynomial) = one(typeof(a))

basering(::Type{NP}) where NP <: NamedPolynomial = basering(polynomialtype(NP))
termtype(::Type{NP}) where NP <: NamedPolynomial{P} where P <: Polynomial = NamedPolynomial{termtype(P), names(NP)}
exptype(::Type{NP}) where NP <: NamedPolynomial = exptype(polynomialtype(NP))

function to_dense_monomials(n,a::NamedPolynomial)
    p = to_dense_monomials(n, a.p)
    s = names(typeof(a))::Symbol
    new_names = [Symbol("$s$i") for i=1:n]
    NamedPolynomial{typeof(p),Tuple{new_names...}}(p)
end

max_variable_index(a::NamedPolynomial) = max_variable_index(a.p)

leading_term(a::NamedPolynomial) = termtype(a)(leading_term(a.p))

lcm_multipliers(a::NP, b::NP) where NP <: NamedPolynomial = ((m_a,m_b) = lcm_multipliers(a.p, b.p); (NP(m_a), NP(m_b)))

deg(a::NP) where NP <: NamedPolynomial = deg(a.p)

copy(a::NP) where NP <: NamedPolynomial = NP(copy(a.p))

# -----------------------------------------------------------------------------
#
# Constructing polynomial_rings
#
# -----------------------------------------------------------------------------
"""
    polynomial_ring(basering::Type, symbols::Symbol...)

Create a type for the polynomial ring over `basering` in variables with names
specified by `symbols`, and return the type and a tuple of these variables.

# Examples
```jldoctest
julia> R,(x,y,z) = polynomial_ring(Int, :x, :y, :z)
julia> x*y + z
1 z + 1 x y
```
"""
function polynomial_ring(basering::Type, symbols::Symbol...)
    length(symbols)>0 || throw(ArgumentError("Need at least one variable name"))

    Names = Tuple{symbols...}
    P = Polynomial{Vector{Term{TupleMonomial{length(symbols),Int16}, basering}}, :degrevlex}
    gens = generators(P)
    NP = NamedPolynomial{P, Names}

    return NP, map(g->NP(g), gens)
end

"""
    formal_coefficients(R, name::Symbol)

Return a `Channel` with formal coefficients for the polynomial ring `R`.

Formal coefficients means that these are generators for a polynomial ring
`C` with an unbounded number of variables, and this polynomial ring is used
(through base extension) as the coefficients for `R`.

In other words, the channel yields `c_i⊗ 1` for generators `c_i ∈ C` and `1 ∈ R`.

# Examples
```jldoctest
julia> R,(x,) = polynomial_ring(Int, :x);
julia> coeffs = formal_coefficients(R, :c);
julia> c() = take!(coeffs);
julia> [c()*x^2 + c()*x + c() , c()*x^2 + c()*x + c()]
2-element Array{(Polynomial over (Polynomial over Int64 in c0) in x),1}:
 1 c3 + 1 c2 x + 1 c1 x^2
 1 c6 + 1 c5 x + 1 c4 x^2
```
"""
function formal_coefficients(::Type{NP}, name::Symbol) where NP <: NamedPolynomial
    _C = Polynomial{Vector{Term{VectorMonomial{SparseVector{Int16,Int}}, Int}}, :deglex}
    CC = NamedPolynomial{_C, name}

    PP = base_extend(NP, CC)
    C = basering(PP)
    P = polynomialtype(C)

    return lazymap(g->PP(C(g)), generators(P))
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
        push!(converter.args, :( zero(exptype(monomial)) ))
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
    I = promote_type(exptype(NP1), exptype(NP2))
    return NamedPolynomial{Polynomial{Vector{Term{TupleMonomial{N,I},C}}, :degrevlex}, Names}
end

function convert(::Type{NP1}, a::NP2) where NP1 <: NamedPolynomial{P1, Names1} where NP2 <: NamedPolynomial{P2, Names2} where {P1<:Polynomial,P2<:Polynomial,Names1<:Tuple,Names2<:Tuple}
    f = t->termtype(P1)( _convert_monomial(Names1, Names2, monomial(t)), coefficient(t) )
    # there used to be map(f, terms(a.p)) here, but type inference makes that an
    # Array{Any}. That's why we explicitly write termtype(P1)[ .... ] .
    converted_terms = termtype(P1)[f(t) for t in terms(a.p)]
    sort!(converted_terms, lt=(a,b)->isless(monomial(a),monomial(b),Val{monomialorder(P1)}))
    NP1(P1(converted_terms))
end


# -----------------------------------------------------------------------------
#
# Use Term as a polynomial
#
# -----------------------------------------------------------------------------
*(a::NamedPolynomial{T,Names}, b::NamedPolynomial{Polynomial{V, Order},Names}) where V <: AbstractVector{T} where T <: Term where {Names,Order} = typeof(b)( a.p * b.p )
*(a::NamedPolynomial{Polynomial{V, Order},Names}, b::NamedPolynomial{T,Names}) where V <: AbstractVector{T} where T <: Term where {Names,Order} = typeof(a)( a.p * b.p )

+(a::NamedPolynomial{T,Names}, b::NamedPolynomial{Polynomial{V, Order},Names}) where V <: AbstractVector{T} where T <: Term where {Names,Order} = typeof(b)( a.p + b.p )
+(a::NamedPolynomial{Polynomial{V, Order},Names}, b::NamedPolynomial{T,Names}) where V <: AbstractVector{T} where T <: Term where {Names,Order} = typeof(a)( a.p + b.p )

-(a::NamedPolynomial{T,Names}, b::NamedPolynomial{Polynomial{V, Order},Names}) where V <: AbstractVector{T} where T <: Term where {Names,Order} = typeof(b)( a.p - b.p )
-(a::NamedPolynomial{Polynomial{V, Order},Names}, b::NamedPolynomial{T,Names}) where V <: AbstractVector{T} where T <: Term where {Names,Order} = typeof(a)( a.p - b.p )

end
