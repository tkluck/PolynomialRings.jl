"""
    DensePolynomial{M, C} where M <: AbstractMonomial where C

This type represents a polynomial as a vector of coefficients, ordered by
increasing monomial order. (see `PolynomialRings.MonomialOrderings`).
"""
struct DensePolynomial{M <: AbstractMonomial, C}
    coeffs :: Vector{C}
end

const DensePolynomialOver{C,Order} = DensePolynomial{<:AbstractMonomial{Order}, C}
const DensePolynomialBy{Order,C}   = DensePolynomialOver{C,Order}

isstrictlysparse(P::Type{<:DensePolynomial}) = false
issparse(P::Type{<:DensePolynomial}) = false

monomials(f::DensePolynomial) = monomialiter(typeof(f), length(f.coeffs))
# TODO: rename because of naming clash with the Expansions. version
coefficients(f::DensePolynomial) = f.coeffs

# -----------------------------------------------------------------------------
#
# Methods for collection-of-terms
#
# -----------------------------------------------------------------------------
function Base.empty!(p::DensePolynomial)
    empty!(p.coeffs)
    p
end

function Base.push!(p::DensePolynomial{M}, t::Term{M}) where M <: AbstractMonomial
    @inplace p += t
    p
end

Base.sizehint!(p::DensePolynomial, n) = sizehint!(p.coeffs, n)
Base.copy!(dst::DensePolynomial, src::DensePolynomial) = copy!(dst.coeffs, src.coeffs)

hash(p::DensePolynomial, h::UInt) = hash(hash(p.coeffs, h), hash(monomialtype(p)))

function _ensurecoeffs!(coeffs, n)
    if (m = length(coeffs)) < n
        resize!(coeffs, n)
        for i in m + 1 : n
            coeffs[i] = zero(eltype(coeffs))
        end
    end
    coeffs
end

# -----------------------------------------------------------------------------
#
# zero, one, etc
#
# -----------------------------------------------------------------------------
zero(::Type{P}) where P <: DensePolynomial = @assertvalid P(basering(P)[])
one(::Type{P})  where P <: DensePolynomial = @assertvalid P([one(basering(P))])
iszero(a::P)    where P <: DensePolynomial = iszero(a.coeffs)

function ==(a::P, b::P)  where P <: DensePolynomial
    # TODO
    error("Not implemented")
end

+(a::P)         where P <: DensePolynomial = @assertvalid P(copy(a.coeffs))
-(a::P)         where P <: DensePolynomial = @assertvalid P(map(-, a.coeffs))



#function todense(f::Polynomial)
#    M = IndexedMonomial{typeof(monomialorder(f)), Int}
#    C = basering(f)
#
#    # TODO: need to assert degrevlex
#    N = degrevlex_index(leading_monomial(f).e)
#    monomials = MonomialIter{M, M}()
#    coeffs = zeros(C, N)
#
#    for (m, c) in expansion(f, monomialorder(f))
#        coeffs[degrevlex_index(m.e)] = c
#    end
#
#    Polynomial(monomials, coeffs)
#end
#
#function tosparse(f::DensePolynomial)
#    M = monomialtype(monomialorder(f))
#    C = basering(f)
#
#    N = nztermscount(f)
#    monomials = Vector{M}(undef, N)
#    coeffs = Vector{C}(undef, N)
#    n = 0
#
#    for (m, c) in expansion(f, monomialorder(f))
#        if !iszero(c)
#            n += 1
#            monomials[n] = m
#            coeffs[n] = c
#        end
#    end
#
#    Polynomial(monomials, coeffs)
#end

function map_coefficients(f, a::DensePolynomial)
    @assertvalid typeof(a)(map(f, coefficients(a)))
end

function convert(P::Type{<:DensePolynomialOver{C,O}}, p::DensePolynomialOver{D,O}) where {C,D,O <: MonomialOrder}
    return P(convert.(C, p.coeffs))
end
