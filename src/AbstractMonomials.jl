module AbstractMonomials

import Base: exponent, gcd, lcm, one, *, ^, ==, diff, isless, iszero, exp
import Base: hash
import Base: iterate
import Base: last, findlast, length
import Base: promote_rule, convert

import SparseArrays: sparsevec, sparse, spzeros
import SparseArrays: nonzeroinds

import ..MonomialOrderings: MonomialOrder
import ..NamingSchemes: Variable, Named, Numbered, InfiniteScheme, NamingScheme
import ..NamingSchemes: numberedvariablename, variablesymbols
import ..Util: isdisjoint, eachstoredindex
import PolynomialRings: to_dense_monomials, max_variable_index, num_variables, monomialtype
import PolynomialRings: leading_monomial
import PolynomialRings: maybe_div, lcm_multipliers, exptype, lcm_degree, namingscheme
import PolynomialRings: monomialorder, deg, divides, mutuallyprime

#import ..Constants: One
# FIXME: reference cycle
struct One end

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

const MonomialIn{Scheme} = AbstractMonomial{<:MonomialOrder{Scheme}}
const NamedMonomial{Names} = MonomialIn{<:Named{Names}}
const NumberedMonomial{Name} = MonomialIn{<:Numbered{Name}}

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
    ea, eb = exponents(N, a, b)
    return @inbounds all(ea[i] == eb[i] for i in eachstoredindex(ea, eb))
end

monomialorder(::Type{M}) where M <: AbstractMonomial{Order} where Order = Order.instance
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
    for (i, e) in enumerate(exponents(a, namingscheme(a)))
        if !iszero(e)
            h = hash((i, e), h)
        end
    end
    h
end

function divides(a::AbstractMonomial, b::AbstractMonomial)
    N = promote_type(namingscheme(a), namingscheme(b))
    ea, eb = exponents(N, a, b)
    return @inbounds all(ea[i] ≤ eb[i] for i in eachstoredindex(ea, eb))
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

function exponent(a::AbstractMonomial, x::Variable)
    if (ix = indexin(x, namingscheme(a))) |> !isnothing
        if ix <= length(a.e)
            return a.e[ix]
        end
    end
    return zero(exptype(a))
end

function diff(a::M, x::Variable) where M <: AbstractMonomial
    n = exponent(a, x)
    if iszero(n)
        return (n, one(M))
    else
        i = indexin(x, namingscheme(a))
        exps = exponents(a, namingscheme(a))
        newexps = map(((j, e),) -> j == i ? e - one(e) : e, enumerate(exps))
        return (n, exp(M, newexps))
    end
end

function lcm_degree(a::AbstractMonomial, b::AbstractMonomial)
    M = promote_type(typeof(a), typeof(b))
    # avoid summing empty iterator
    isone(a) && isone(b) && return zero(exptype(M))
    ea, eb = exponents(namingscheme(M), a, b)
    return @inbounds sum(max(ea[i], eb[i]) for i in eachstoredindex(ea, eb))
end

function mutuallyprime(a::AbstractMonomial, b::AbstractMonomial)
    N = promote_type(namingscheme(a), namingscheme(b))
    return all(iszero(min(d, e)) for (_, (d, e)) in exponentsnz(N, a, b))
end


function any_divisor(f::Function, a::M, scheme::NamingScheme) where M <: AbstractMonomial
    isone(a) && return f(a)

    nonzeros_a = sparse(collect(exponents(a, scheme)))
    e = copy(nonzeros_a)
    nzinds = e.nzind
    nonzeros = e.nzval

    while true
        m = exp(M, e)
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

@generated function exponents(m::NamedMonomial{SourceNames}, scheme::Named{TargetNames}) where {SourceNames, TargetNames}
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

function exponents(m::NumberedMonomial{Name}, scheme::Numbered{Name, N}) where {Name, N}
    namingscheme(m) == scheme && return m.e

    infscheme = Numbered{Name, Inf}()
    max_variable_index(infscheme, m) <= N || error("Retrieving too few exponents")
    return exponents(m, infscheme, max_variable_index=N)
end

exponents(m::NumberedMonomial, scheme::Named) = ntuple(_ -> zero(Int16), num_variables(scheme))
exponents(m::NamedMonomial, scheme::Numbered) = spzeros(Int16, 0)
exponents(m::One, scheme::Named)              = ntuple(_ -> zero(Int16), num_variables(scheme))
exponents(m::One, scheme::Numbered)           = spzeros(Int16, 0)

function exponents(scheme::NamingScheme, ms::AbstractMonomial...)
    exps(m) = exponents(m, scheme)
    map(exps, ms)
end

function exponents(scheme::InfiniteScheme, ms::AbstractMonomial...;
                   max_variable_index = maximum(max_variable_index(scheme, m) for m in ms))
    exps(m) = exponents(m, scheme, max_variable_index=max_variable_index)
    map(exps, ms)
end


deg(m::AbstractMonomial, scheme::NamingScheme) = sum(exponents(m, scheme))

exponentsnz(scheme::NamingScheme, ms::AbstractMonomial...) = (
    (i, exps)
    for (i, exps) in enumerate(zip(exponents(scheme, ms...)...))
    if any(!iszero, exps)
)

revexponentsnz(scheme::NamingScheme, ms::AbstractMonomial...) = Iterators.reverse(exponentsnz(scheme, ms...))

# -----------------------------------------------------------------------------
#
# Conversions
#
# -----------------------------------------------------------------------------
function convert(::Type{M}, m::AbstractMonomial) where M <: AbstractMonomial
    if namingscheme(m) isa Numbered && namingscheme(M) isa Numbered &&
            numberedvariablename(typeof(m)) == numberedvariablename(M)
        sym = numberedvariablename(M)
        n = max_variable_index(namingscheme(sym, Inf), m)
        n ≤ num_variables(M) || throw(InexactError(:convert, M, m))
        return exp(M, @view exponents(m, namingscheme(m))[1:min(end, n)])
    else
        N = diff(namingscheme(m), namingscheme(M))
        isempty(N) || all(iszero, exponents(m, N)) || throw(InexactError(:convert, M, m))
        return exp(M, exponents(m, namingscheme(M)))
    end
end

convert(::Type{M}, m::One) where M <: AbstractMonomial = exp(M, exponents(m, namingscheme(M)))
convert(::Type{M}, m::M) where M <: AbstractMonomial = m

function convert(::Type{M}, m::Symbol) where M <: NamedMonomial
    ix = indexin(m, namingscheme(M))
    exp(M, sparsevec([ix], [1]))
end

function promote_rule(::Type{M1}, ::Type{M2}) where M1 <: AbstractMonomial where M2 <: AbstractMonomial
    order = promote_type(monomialorder(M1), monomialorder(M2))
    if order isa MonomialOrder
        I = promote_type(exptype(M1), exptype(M2))
        return monomialtype(order, I)
    else
        return Union{}
    end
end

# -----------------------------------------------------------------------------
#
# Conversion from c[] to c[1:N]
#
# -----------------------------------------------------------------------------

function to_dense_monomials(scheme::InfiniteScheme, M::Type{<:AbstractMonomial}, max_variable_index)
    isconcretetype(M) || error("Cannot compute to_dense_monomials for non-concrete $M")
    order = to_dense_monomials(scheme, monomialorder(M), max_variable_index)
    return monomialtype(order, exptype(M))
end

function to_dense_monomials(scheme::InfiniteScheme, m::AbstractMonomial, max_variable_index)
    M = to_dense_monomials(scheme, typeof(m), max_variable_index)
    return convert(M, m)
end

end # module
