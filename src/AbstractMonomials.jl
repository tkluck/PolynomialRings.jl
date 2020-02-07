module AbstractMonomials

import Base: exponent, gcd, lcm, one, *, ^, ==, diff, isless, iszero, exp
import Base: hash
import Base: iterate
import Base: last, findlast, length
import Base: promote_rule
import SparseArrays: SparseVector, sparsevec
import SparseArrays: nonzeroinds

import ..NamingSchemes: Named, Numbered, NamingScheme, isdisjoint
import ..MonomialOrderings: MonomialOrderIn
import PolynomialRings: generators, to_dense_monomials, max_variable_index, monomialtype, num_variables, divides, mutuallyprime
import PolynomialRings: maybe_div, lcm_multipliers, exptype, lcm_degree, namingscheme, monomialorder, deg
import PolynomialRings: leading_monomial

"""
    AbstractMonomial{Order}

The abstract base type for multi-variate monomials.

Specifying a monomial is equivalent to specifying the exponents for all variables.
The concrete type decides whether this happens as a tuple or as a (sparse or dense)
array.

The type also encodes the monomial order, and as part of that, the names
of the variables.

Each concrete implementation `M` should implement for elements `m`:

    exponent(m, i)
    nzindices(m)
    _construct(M, i -> exponent, nonzero_indices, [total_degree])
    exptype(M)

In addition, one may choose to add specific optimizations by overloading
other functions, as well.
"""
abstract type AbstractMonomial{Order} end

const MonomialIn{Names} = AbstractMonomial{<:MonomialOrderIn{Names}}

# -----------------------------------------------------------------------------
#
# Abstract fallbacks
#
# -----------------------------------------------------------------------------
@inline _construct(::Type{M}, f, nzindices, deg) where M <: AbstractMonomial = _construct(M, f, nzindices)
@inline _construct(::Type{M}, f, nzindices) where M <: AbstractMonomial = _construct(M, f, nzindices, exptype(M)(mapreduce(f, +, nzindices, init=zero(exptype(M)))))

exp(::Type{M}, exps, deg=sum(exps)) where M <: AbstractMonomial = _construct(M, i -> exps[i], 1:length(exps), deg)
exp(::Type{M}, exps::Pair...) where M <: AbstractMonomial = (exps = Dict(exps...); _construct(M, i -> exps[i], keys(exps), deg))

one(::Type{M}) where M <: AbstractMonomial = _construct(M, i->0, 1:0)
one(::M) where M <: AbstractMonomial = one(M)

function *(a::AbstractMonomial, b::AbstractMonomial)
    N = promote_type(namingscheme(a), namingscheme(b))
    N isa NamingScheme || error("Cannot multiply $(typeof(a)) and $(typeof(b)); convert to polynomials first")
    T = monomialtype(N) # FIXME: get exptype from a and b
    exp(T, exponents(a, N) .+ exponents(b, N))
end

^(a::AbstractMonomial, n::Integer) = exp(typeof(a), n .* exponents(a, namingscheme(a)))

total_degree(a::A) where A <: AbstractMonomial = mapreduce(i->exponent(a, i), +, nzindices(a), init=zero(exptype(a)))

leading_monomial(a::AbstractMonomial; order) = a # note that we don't need order congruence

lcm(a::AbstractMonomial{Order}, b::AbstractMonomial{Order}) where Order = _construct(promote_type(typeof(a), typeof(b)),i -> max(exponent(a, i), exponent(b, i)), index_union(a,b))
gcd(a::AbstractMonomial{Order}, b::AbstractMonomial{Order}) where Order = _construct(promote_type(typeof(a), typeof(b)),i -> min(exponent(a, i), exponent(b, i)), index_union(a,b))

monomialorder(::Type{M}) where M <: AbstractMonomial{Order} where Order = Order()
monomialtype(::Type{M}) where M <: AbstractMonomial = M
namingscheme(::Type{M}) where M <: AbstractMonomial = namingscheme(monomialorder(M))
isless(a::M, b::M) where M <: AbstractMonomial = Base.Order.lt(monomialorder(M), a, b)
iszero(a::AbstractMonomial) = false

function exptype(::Type{M}, scheme::NamingScheme) where M <: AbstractMonomial
    return isdisjoint(namingscheme(M), scheme) ? Int16 : exptype(M)
end

num_variables(::Type{M}) where M <: AbstractMonomial = num_variables(namingscheme(M))

"""
    enumeratenz(monomial)

Enumerate (i.e. return an iterator) for `(variable index, exponent)` tuples for `monomial`,
where `exponent` is a structural nonzero (hence `nz`).

This means that, depending on implementation details, the variable indices with
zero exponent *may* be skipped, but this is not guaranteed. In practice, this
only happens if the storage format is sparse.
"""
enumeratenz(a::M) where M <: AbstractMonomial = EnumerateNZ(a)

exptype(a::AbstractMonomial) = exptype(typeof(a))

"""
    hash(monomial)

This hash function is carefully designed to give the same answer
for sparse and dense representations. This is necessary for a
typical `any_divisor` use-case: `any_divisor` loops over the
possible divisors in-place in an array, but its function `f` might
operate on tuple monomials. They should compare equal and hash
equal.

TODO: add test cases for that!
"""
function hash(a::AbstractMonomial, h::UInt)
    for (i,e) in enumeratenz(a)
        if !iszero(e)
            h = hash((i,e), h)
        end
    end
    h
end

==(a::AbstractMonomial{Order}, b::AbstractMonomial{Order}) where Order = all(i->exponent(a, i) == exponent(b, i), index_union(a,b))

function maybe_div(a::AbstractMonomial{Order}, b::AbstractMonomial{Order}) where Order
    M = promote_type(typeof(a), typeof(b))
    if all(i -> exponent(a, i) >= exponent(b, i), index_union(a,b))
        return _construct(M,i -> exponent(a, i) - exponent(b, i), index_union(a,b))
    else
        return nothing
    end
end

function divides(a::AbstractMonomial{Order}, b::AbstractMonomial{Order}) where Order
    return all(i -> exponent(a, i) <= exponent(b, i), index_union(a,b))
end

function lcm_multipliers(a::AbstractMonomial{Order}, b::AbstractMonomial{Order}) where Order
    M = promote_type(typeof(a), typeof(b))
    return (
        _construct(M, i -> max(exponent(a, i), exponent(b, i)) - exponent(a, i), index_union(a,b)),
        _construct(M, i -> max(exponent(a, i), exponent(b, i)) - exponent(b, i), index_union(a,b)),
    )
end

function diff(a::M, i::Integer) where M <: AbstractMonomial
    n = exponent(a, i)
    if iszero(n)
        return (n, one(M))
    else
        return (n, _construct(M, j -> (j==i ? exponent(a, j) - one(exptype(M)) : exponent(a, j)), nzindices(a)))
    end
end

function lcm_degree(a::AbstractMonomial{Order}, b::AbstractMonomial{Order}) where Order
    # avoid summing empty iterator
    iszero(total_degree(a)) && iszero(total_degree(b)) && return zero(exptype(M))
    return sum(max(exponent(a, i), exponent(b, i)) for i in index_union(a,b))
end

function mutuallyprime(a::AbstractMonomial{Order}, b::AbstractMonomial{Order}) where Order
    return all(iszero(min(exponent(a, i), exponent(b, i))) for i in index_union(a, b))
end



function any_divisor(f::Function, a::M) where M <: AbstractMonomial
    if isempty(nzindices(a))
        return f(a)
    end


    n = last(nzindices(a))
    nzinds = collect(nzindices(a))
    nonzeros_a = map(i -> exponent(a, i), nzinds)
    nonzeros = copy(nonzeros_a)
    e = SparseVector{exptype(M), Int}(n, nzinds, nonzeros)

    N = VectorMonomial{typeof(e), exptype(M), typeof(monomialorder(M))}

    while true
        m = N(e, sum(e))
        if f(m)
            return true
        end
        carry = 1
        for j = 1:length(nonzeros)
            if iszero(nonzeros[j]) && !iszero(carry)
                nonzeros[j] = nonzeros_a[j]
                carry = 1
            else
                nonzeros[j] -= carry
                carry = 0
            end
        end
        if !iszero(carry)
            return false
        end
    end
end

exponents(m::MonomialIn{Scheme}, scheme::Scheme) where Scheme <: NamingScheme = m.e
deg(m::MonomialIn{Scheme}, scheme::Scheme) where Scheme <: NamingScheme = m.deg

@generated function exponents(m::MonomialIn{Named{SourceNames}}, scheme::Named{TargetNames}) where {SourceNames, TargetNames}
    # create an expression that calls the tuple constructor. No arguments -- so far
    exps = :( tuple() )
    for d in TargetNames
        # for every result field, add the constant 0 as an argument
        push!(exps.args, :( zero(exptype(m)) ))
        for (j,s) in enumerate(SourceNames)
            if d == s
                # HOWEVER, if it actually also exists in src, then replace the 0
                # by reading from exponent_tuple
                exps.args[end]= :( m.e[$j] )
                break
            end
        end
    end
    return exps
end

deg(m::AbstractMonomial, scheme::NamingScheme) = sum(exponents(m, scheme))

function exponentsnz(scheme::NamingScheme, ms::AbstractMonomial...)
    exps(m) = exponents(m, scheme)
    return enumerate(zip(map(exps, ms)...))
end

revexponentsnz(scheme::NamingScheme, ms::AbstractMonomial...) = Iterators.reverse(exponentsnz(scheme, ms...))

end # module
