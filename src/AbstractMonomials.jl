module AbstractMonomials

import Base: exponent, gcd, lcm, one, *, ^, ==, diff, isless, iszero, exp
import Base: hash
import Base: iterate
import Base: last, findlast, length
import Base: promote_rule, convert
import SparseArrays: SparseVector, sparsevec
import SparseArrays: nonzeroinds

#import ..Constants: One
# FIXME: reference cycle
struct One end

import ..NamingSchemes: Named, Numbered, NamingScheme, isdisjoint, variablesymbols
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

    exp(M, exponents, deg=sum(exponents))
    exponents(scheme::NamingScheme, m::M)
    exptype(M)

In addition, one may choose to add specific optimizations by overloading
other functions, as well.
"""
abstract type AbstractMonomial{Order} end

const MonomialIn{Names} = AbstractMonomial{<:MonomialOrderIn{Names}}
const NamedMonomial = MonomialIn{<:Named}
const NumberedMonomial = MonomialIn{<:Numbered}

# -----------------------------------------------------------------------------
#
# Abstract fallbacks
#
# -----------------------------------------------------------------------------

one(::Type{M}) where M <: AbstractMonomial = convert(M, One())
one(::M) where M <: AbstractMonomial = one(M)

function exponentwise(op, ms::AbstractMonomial...)
    M = promote_type(map(typeof, ms)...)
    N = namingscheme(M)
    exp(M, broadcast(op, exponents(N, ms...)...))
end

*(a::AbstractMonomial, b::AbstractMonomial) = exponentwise(+, a, b)
lcm(a::AbstractMonomial, b::AbstractMonomial) = exponentwise(max, a, b)
gcd(a::AbstractMonomial, b::AbstractMonomial) = exponentwise(min, a, b)

^(a::AbstractMonomial, n::Integer) = exp(typeof(a), n .* exponents(a, namingscheme(a)))

function ==(a::AbstractMonomial, b::AbstractMonomial)
    N = promote_type(namingscheme(a), namingscheme(b))
    N isa NamingScheme || return false
    return all(((_, (a,b)),) -> a == b, exponentsnz(N, a, b))
end

leading_monomial(a::AbstractMonomial; order) = a # note that we don't need order congruence

monomialorder(::Type{M}) where M <: AbstractMonomial{Order} where Order = Order()
monomialtype(::Type{M}) where M <: AbstractMonomial = M
namingscheme(::Type{M}) where M <: AbstractMonomial = namingscheme(monomialorder(M))
isless(a::M, b::M) where M <: AbstractMonomial = Base.Order.lt(monomialorder(M), a, b)
iszero(a::AbstractMonomial) = false

function exptype(::Type{M}, scheme::NamingScheme) where M <: AbstractMonomial
    return isdisjoint(namingscheme(M), scheme) ? Int16 : exptype(M)
end

exptype(a::AbstractMonomial) = exptype(typeof(a))

num_variables(::Type{M}) where M <: AbstractMonomial = num_variables(namingscheme(M))


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
    for (i, (e,)) in exponentsnz(namingscheme(a), a)
        if !iszero(e)
            h = hash((i, e), h)
        end
    end
    h
end

function divides(a::AbstractMonomial, b::AbstractMonomial)
    N = promote_type(namingscheme(a), namingscheme(b))
    return all(d ≤ e for (_, (d, e)) in exponentsnz(N, a, b))
end

function maybe_div(a::AbstractMonomial, b::AbstractMonomial)
    if divides(b, a)
        M = typeof(a)
        ea, eb = exponents(namingscheme(M), a, b)
        return exp(M, ea .- eb)
    else
        return nothing
    end
end

function lcm_multipliers(a::AbstractMonomial, b::AbstractMonomial)
    M = promote_type(typeof(a), typeof(b))
    ea, eb = exponents(namingscheme(M), a, b)
    return (
        exp(M, max.(ea, eb) .- ea),
        exp(M, max.(ea, eb) .- eb),
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

function lcm_degree(a::AbstractMonomial, b::AbstractMonomial)
    M = promote_type(typeof(a), typeof(b))
    # avoid summing empty iterator
    isone(a) && isone(b) && return zero(exptype(M))
    return sum(max(d, e) for (_, (d, e)) in exponentsnz(namingscheme(M), a, b))
end

function mutuallyprime(a::AbstractMonomial, b::AbstractMonomial)
    N = promote_type(namingscheme(a), namingscheme(b))
    return all(iszero(min(d, e)) for (_, (d, e)) in exponentsnz(N, a, b))
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


function exponents(scheme::NamingScheme, ms::AbstractMonomial...)
    exps(m) = exponents(m, scheme)
    map(exps, ms)
end

const InfiniteScheme{Name} = Numbered{Name, Inf}

function exponents(scheme::InfiniteScheme, ms::AbstractMonomial...;
                   max_variable_index = maximum(max_variable_index(scheme, m) for m in ms))
    exps(m) = exponents(m, scheme, max_variable_index=max_variable_index)
    map(exps, ms)
end

function exponents(m::MonomialIn{<:Numbered{Name}}, scheme::Numbered{Name, N}) where {Name, N}
    infscheme = Numbered{Name, Inf}()
    max_variable_index(infscheme, m) <= N || error("Retrieving too few exponents")
    return exponents(m, infscheme, max_variable_index=N)
end

@generated function exponents(m::One, scheme::Named{TargetNames}) where TargetNames
    ntuple(_ -> zero(Int16), length(TargetNames))
end

function exponents(m::One, scheme::Numbered)
    Int16[]
end

deg(m::AbstractMonomial, scheme::NamingScheme) = sum(exponents(scheme, m))

function exponentsnz(scheme::NamingScheme, ms::AbstractMonomial...)
    return enumerate(zip(exponents(scheme, ms...)...))
end

revexponentsnz(scheme::NamingScheme, ms::AbstractMonomial...) = Iterators.reverse(exponentsnz(scheme, ms...))

# -----------------------------------------------------------------------------
#
# Conversions
#
# -----------------------------------------------------------------------------
function convert(::Type{M}, m::AbstractMonomial) where M <: AbstractMonomial
    N = diff(namingscheme(m), namingscheme(M))
    isnothing(N) || all(iszero, exponents(m, N)) || throw(InexactError(:convert, M, m))
    exp(M, exponents(m, namingscheme(M)))
end

convert(::Type{M}, m::One) where M <: AbstractMonomial = exp(M, exponents(m, namingscheme(M)))
convert(::Type{M}, m::M) where M <: AbstractMonomial = m

function convert(::Type{M}, m::Symbol) where M <: NamedMonomial
    ix = indexin(m, namingscheme(M))
    exp(M, sparsevec([ix], [1]))
end

generators(::Type{M}) where M <: NamedMonomial = (convert(M, s) for s in variablesymbols(M))

end # module
