module NamedPolynomials

import Base: promote_rule, convert, Bottom
import SparseArrays: SparseVector

import ..Constants: One
import ..MonomialOrderings: MonomialOrder, rulesymbol
import ..Monomials: TupleMonomial, VectorMonomial, AbstractMonomial, _construct, exptype, num_variables, nzindices
import ..NamingSchemes: Named, Numbered, NamingScheme, numberedvariablename, remove_variables, isdisjoint, boundnames, ≺
import ..Operators: _filterzeros!, _collectsummands!
import ..Polynomials:  NamedMonomial, NumberedMonomial, NamedTerm, NumberedTerm, TermOver, monomialorder, NamedOrder, NumberedOrder, polynomial_ring
import ..Polynomials: Polynomial, PolynomialOver, NamedPolynomial, NumberedPolynomial, PolynomialBy, PolynomialIn, nzterms
import ..Terms: Term, basering, monomial, coefficient
import PolynomialRings: termtype, namingscheme, variablesymbols, exptype, monomialtype, allvariablesymbols, iscanonical, canonicaltype, fullnamingscheme, fullboundnames, max_variable_index, polynomialtype

# -----------------------------------------------------------------------------
#
# Generating symbols that do not conflict with existing ones
#
# -----------------------------------------------------------------------------
function unused_variable(P, a)
    E = exptype(P)
    N = max_variable_index(a)
    P(_construct(monomialtype(P), i->i==(N+1) ? one(E) : zero(E), N+1:N+1))
end
unused_variable(p::Polynomial)                  = unused_variable(typeof(p), p)
unused_variable(a::AbstractArray{<:Polynomial}) = unused_variable(eltype(a), a)

# separate versions for N<:Named and N<:Numbered to resolve method ambiguity
# with the version for which P and p do not have the same names.
function convert(P::Type{<:PolynomialOver{C,O}}, p::PolynomialOver{D,O}) where {C,D,O<:NamedOrder}
    res = Polynomial(p.monomials, convert.(C, p.coeffs))
    _filterzeros!(res)
end
function convert(P::Type{<:PolynomialOver{C,O}}, p::PolynomialOver{D,O}) where {C,D,O<:NumberedOrder}
    res = Polynomial(p.monomials, convert.(C, p.coeffs))
    _filterzeros!(res)
end
# and short-circuit the non-conversions
convert(::Type{P}, p::P) where P <: PolynomialOver{C,O} where {C,O<:NamedOrder} = p
convert(::Type{P}, p::P) where P <: PolynomialOver{C,O} where {C,O<:NumberedOrder} = p
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

_lossy_convert_monomial(::Type{M}, ::One) where M<:AbstractMonomial = one(M)
_lossy_convert_monomial(::Type{M}, ::NumberedMonomial) where M<:NamedMonomial = one(M)
_lossy_convert_monomial(::Type{M}, ::NamedMonomial) where M<:NumberedMonomial = one(M)
_lossy_convert_monomial(::Type{One}, ::AbstractMonomial) = One()

@generated function _lossy_convert_monomial(::Type{M}, monomial::NamedMonomial) where M <: NamedMonomial
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

# workaround for the @generated body needing to be pure (no closures)
_indexer(monomial) = i ->
                     i <= num_variables(typeof(monomial)) ?
                     monomial[i] :
                     zero(exptype(monomial))

@generated function _lossy_convert_monomial(::Type{M1}, monomial::M2) where {M1 <: NumberedMonomial, M2 <: NumberedMonomial}
    if numberedvariablename(M1) != numberedvariablename(M2)
        return :( One() )
    end
    @assert num_variables(M1) >= num_variables(M2)
    return quote
        $_construct(M1, $_indexer(monomial), $nzindices(monomial))
    end
end

# fix method ambiguity
promote_rule(::Type{P}, ::Type{C}) where P<:PolynomialOver{C} where C <: Polynomial = P

function remove_variables(O::MonomialOrder, vars)
    O′ = remove_variables(namingscheme(O), vars)
    O′ == nothing && return nothing
    return MonomialOrder{rulesymbol(O), typeof(O′)}()
end

function remove_variables(::Type{M}, vars) where M <: AbstractMonomial
    O = remove_variables(monomialorder(M), vars)
    O == nothing && return One
    return monomialtype(O, exptype(M))
 end

function remove_variables(::Type{T}, vars) where T <: Term
    M = remove_variables(monomialtype(T), vars)
    C = remove_variables(basering(T), vars)
    M == One && return C
    return Term{M, C}
end
function remove_variables(::Type{P}, vars) where P <: Polynomial
    M = remove_variables(monomialtype(P), vars)
    C = remove_variables(basering(P), vars)
    M == One && return C
    return polynomialtype(M, C)
end
remove_variables(T::Type, vars) = T

fullnamingscheme(T::Type{<:Term}) = fullnamingscheme(basering(T)) * namingscheme(T)
fullnamingscheme(T::Type{<:Polynomial}) = fullnamingscheme(basering(T)) * namingscheme(T)
fullboundnames(T::Type{<:Term}) = fullboundnames(basering(T))
fullboundnames(T::Type{<:Polynomial}) = fullboundnames(basering(T))

_promote_rule(T1::Type{<:Polynomial}, T2::Type) = promote_rule(T1, T2)
_promote_rule(T1::Type,               T2::Type) = (res = promote_type(T1, T2); res === Any ? Bottom : res)

function promote_rule(T1::Type{<:Polynomial}, T2::Type)
    if !isdisjoint(namingscheme(T1), fullboundnames(T2))
        # FIXME(tkluck): this loses information on the exptype associated to
        # the namingscheme of T1.
        T1′ = remove_variables(T1, fullboundnames(T2))
        return _promote_rule(T1′, T2)
    elseif fullnamingscheme(T1) ⊆ fullnamingscheme(T2)
        # FIXME(tkluck): this loses information on the exptype associated to
        # the namingscheme of T1.
        return _promote_rule(basering(T1), T2)
    elseif isdisjoint(namingscheme(T1), fullnamingscheme(T2))
        if (C = _promote_rule(basering(T1), T2)) !== Bottom
            return polynomialtype(monomialtype(T1), C)
        end
    end
    return Bottom
end

function promote_rule(T1::Type{<:Term}, T2::Type)
    if !isdisjoint(namingscheme(T1), fullboundnames(T2))
        T1′ = remove_variables(T1, fullboundnames(T2))
        return _promote_rule(T1′, T2)
    elseif fullnamingscheme(T1) ⊆ fullnamingscheme(T2)
        return _promote_rule(basering(T1), T2)
    elseif isdisjoint(namingscheme(T1), fullnamingscheme(T2))
        if (C = _promote_rule(basering(T1), T2)) !== Bottom
            return Term{monomialtype(T1), C}
        end
    end
    return Bottom
end


# -----------------------------------------------------------------------------
#
# Canonical types
#
# -----------------------------------------------------------------------------

promote_canonical_type(T1::Type, T2::Type) = promote_type(T1, T2)

function promote_canonical_type(T1::Type{<:Polynomial}, T2::Type)
    if !isdisjoint(namingscheme(T1), fullboundnames(T2))
        T1′ = remove_variables(T1, fullboundnames(T2))
        return promote_canonical_type(T1′, T2)
    else
        M = monomialtype(T1)
        C = promote_canonical_type(basering(T1), T2)
        return polynomialtype(M, C)
    end
end

promote_canonical_type(T1::Type, T2::Type{<:Polynomial}) = promote_canonical_type(T2, T1)

function promote_canonical_type(T1::Type{<:Polynomial}, T2::Type{<:Polynomial})
    @assert iscanonical(T1) && iscanonical(T2)

    if !isdisjoint(namingscheme(T1), fullboundnames(T2))
        T1′ = remove_variables(T1, fullboundnames(T2))
        return promote_canonical_type(T1′, T2)
    elseif !isdisjoint(namingscheme(T2), fullboundnames(T1))
        T2′ = remove_variables(T2, fullboundnames(T1))
        return promote_canonical_type(T1, T2′)
    elseif namingscheme(T1) ≺ namingscheme(T2)
        M = monomialtype(T2)
        C = promote_canonical_type(T1, basering(T2))
        return polynomialtype(M, C)
    elseif namingscheme(T2) ≺ namingscheme(T1)
        M = monomialtype(T1)
        C = promote_canonical_type(basering(T1), T2)
        return polynomialtype(M, C)
    else
        M = promote_type(monomialtype(T1), monomialtype(T2))
        C = promote_type(basering(T1), basering(T2))
        return polynomialtype(M, C)
    end
end

function promote_rule(::Type{M1}, ::Type{M2}) where M1 <: AbstractMonomial where M2 <: AbstractMonomial
    O = promote_rule(typeof(monomialorder(M1)), typeof(monomialorder(M2)))
    if O <: MonomialOrder
        N = length(variablesymbols(O))
        I = promote_type(exptype(M1), exptype(M2))
        return TupleMonomial{N, I, O}
    else
        return Union{}
    end
end

using PolynomialRings

function convert(::Type{P1}, a::P2) where P1 <: Polynomial where P2 <: Polynomial
    M = monomialtype(P1)
    C = basering(P1)
    monomials = M[]
    coeffs = C[]
    for (c, (m,)) in PolynomialRings.Expansions._expansion2(a, monomialorder(P1))
        push!(monomials, m)
        push!(coeffs, c)
    end
    _collectsummands!(P1(monomials, coeffs))
end

convert(::Type{P}, a::P) where P <: NamedPolynomial = a

polynomialtype(T::Type{<:Term}) = polynomialtype(monomialtype(T), basering(T))

function canonicaltype(P::Type{<:PolynomialOver{<:Polynomial}})
    C = canonicaltype(basering(P))
    M1 = monomialtype(C)
    M2 = canonicaltype(monomialtype(P))
    if namingscheme(M1) ≺ namingscheme(M2)
        P′ = polynomialtype(M2, C)
    elseif namingscheme(M2) ≺ namingscheme(M1)
        C1 = basering(C)
        P′ = polynomialtype(M1, polynomialtype(M2, C1))
    else
        M = promote_type(M1, M2)
        C1 = basering(C)
        P′ = polynomialtype(M, C1)
    end
    if P′ == P
        return P
    else
        # recursive sort
        return canonicaltype(P′)
    end
end
function canonicaltype(P::Type{<:Polynomial})
    C = canonicaltype(basering(P))
    M = canonicaltype(monomialtype(P))
    return polynomialtype(M, C)
end
@generated function canonicaltype(::Type{M}) where M <: NamedMonomial
    N = num_variables(M)
    I = exptype(M)
    names = tuple(sort(collect(variablesymbols(M)))...)
    res = TupleMonomial{N, I, MonomialOrder{:degrevlex, Named{names}}}
    return :($res)
end
function canonicaltype(M::Type{<:NumberedMonomial})
    I = exptype(M)
    name = numberedvariablename(M)
    VectorMonomial{SparseVector{I,Int}, I, MonomialOrder{:degrevlex, Numbered{name, Inf}}}
end
canonicaltype(T::Type{<:Term}) = termtype(canonicaltype(polynomialtype(T)))
canonicaltype(T::Type) = T

iscanonical(::Type) = true
iscanonical(M::Type{<:AbstractMonomial}) = iscanonical(namingscheme(M)) && rulesymbol(monomialorder(M)) == :degrevlex

iscanonical(T::Type{<:Term})       = iscanonical(fullnamingscheme(T))
iscanonical(P::Type{<:Polynomial}) = iscanonical(fullnamingscheme(P))

function _promote_result(T, S, LTR, RTL)
    if LTR == Bottom && RTL != Bottom
        return RTL
    elseif RTL == Bottom && LTR != Bottom
        return LTR
    elseif LTR == RTL && LTR != Bottom
        return LTR
    else
        if namingscheme(T) == namingscheme(S)
            M = promote_type(monomialtype(T), monomialtype(S))
            C = promote_type(basering(T), basering(S))
            return polynomialtype(M, C)
        else
            return promote_canonical_type(canonicaltype(T), canonicaltype(S))
        end
    end
end

_promote_type(T, S) = _promote_result(T, S, promote_rule(T, S), promote_rule(S, T))

for T in [Term, Polynomial]
    @eval begin
        Base.promote_type(T::Type{<:$T}, S::Type)         = _promote_type(T, S)
        Base.promote_type(T::Type,       S::Type{<:$T})   = _promote_type(T, S)
        Base.promote_type(T::Type{<:$T}, S::Type{<:$T})   = _promote_type(T, S)

        Base.promote_type(T::Type{<:$T}, S::Type{Bottom}) = T
        Base.promote_type(T::Type{Bottom}, S::Type{<:$T}) = S
    end
end
for (T1, T2) in [(Term, Polynomial), (Polynomial, Term)]
    @eval begin
        Base.promote_type(T::Type{<:$T1}, S::Type{<:$T2}) = _promote_type(T, S)
    end
end

"""
    R = minring(f)

The smallest ring that faithfully contains `f`, i.e. the
intersection of all rings `R` that faithfully contain `f`.
"""
function minring end

minring(x::Integer) = typemin(Int) <= x <= typemax(Int) ? Int : BigInt
minring(x::Rational) = denominator(x) == 1 ? minring(numerator(x)) : typeof(x)
minring(x::Real) = round(x) ≈ x ? minring(Integer(x)) : typeof(x)
minring(x::Complex) = real(x) ≈ x ? minring(real(x)) : typeof(x)
minring(x) = typeof(x)

function minring(f::NamedPolynomial)
    base = minring([coefficient(t) for t in nzterms(f)]...)

    m = prod(monomial(t) for t in nzterms(f))
    nz = findall(!iszero, m.e)
    syms = variablesymbols(namingscheme(f))
    isempty(nz) ? base : polynomial_ring(syms[nz]..., basering=base)[1]
end

function minring(f::NumberedPolynomial)
    base = minring([coefficient(t) for t in nzterms(f)]...)

    m = prod(monomial(t) for t in nzterms(f))
    isone(m) ? base : polynomial_ring(namingscheme(f), basering=base)
end

"""
    R = minring(fs...)

The smallest ring that faithfully contains all `f ∈ fs`
"""
minring(fs...) = promote_type(minring.(fs)...)


"""
    g = ofminring(f)

Shorthand for `convert(minring(f), f)`
"""
ofminring(f) = convert(minring(f), f)

end
