module Signatures

import Base: *, lcm, gcd, show, ==
import Base: indexed_iterate

import SparseArrays: SparseVector

import InPlace: inclusiveinplace!

import ..Constants: One
import ..Terms: monomial, coefficient, basering
import PolynomialRings: mutuallyprime, divides, maybe_div, lcm_multipliers, deg

"""
    struct Sig{K, V}

Represents a monomial or a term of an element of a module; for example,
a term in a `Vector{@ring(Int[x])}`. Is is a combination of an index
and a term or a monomial appearing at that index.

A `Sig` is functionally very similar to a `Pair` except that it also supports
some arithmetic operations such as `lcm` and scalar multiplications. Nested
`Pair`s and nested `Sig`s are (recursively!) converted into each other
by calling their respective constructors.
"""
struct Sig{K, V}
    first  :: K
    second :: V
end

Sig(p::Pair) = Sig(p.first, p.second)
Sig(p::Pair{<:Any, <:Pair}) = Sig(p.first, Sig(p.second))
Pair(sig::Sig) = sig.first => sig.second
Pair(sig::Sig{<:Any, <:Sig}) = sig.first => Pair(sig.second)

indexed_iterate(sig::Sig, i, state=1) = (getfield(sig, i), i + 1)

showpair(io::IO, sig::Sig) = show(io, Pair(sig))
show(io::IO, sig::Sig) = (print(io, "Sig("); showpair(io, sig); print(io, ")"))


*(x, sig::Sig) = Sig(sig.first, x * sig.second)
*(sig::Sig, x) = Sig(sig.first, sig.second * x)

*(sig::Sig, ::One) = sig # TODO: copy
*(::One, sig::Sig) = sig # TODO: copy

lcm(a::Sig, b::Sig) = a.first == b.first ? Sig(a.first, lcm(a.second, b.second)) : nothing
gcd(a::Sig, b::Sig) = a.first == b.first ? Sig(a.first, gcd(a.second, b.second)) : nothing
mutuallyprime(a::Sig, b::Sig) = a.first == b.first ? mutuallyprime(a.second, b.second) : nothing
lcm_multipliers(a::Sig, b::Sig) = a.first == b.first ? lcm_multipliers(a.second, b.second) : nothing

divides(a::Sig, b::Sig) = a.first == b.first && divides(a.second, b.second)
maybe_div(a::Sig, b::Sig) = a.first == b.first ? maybe_div(a.second, b.second) : nothing

deg(a::Sig, spec...) = deg(a.second, spec...)

monomial(sig::Sig) = Sig(sig.first, monomial(sig.second))
coefficient(sig::Sig) = coefficient(sig.second)
basering(sig::Sig) = basering(sig.second)
basering(::Type{Sig{K, V}}) where {K, V} = basering(V)

==(a::Sig, b::Sig)  = a.first == b.first && a.second == b.second
==(a::Sig, b::Pair) = a.first == b.first && a.second == b.second
==(a::Pair, b::Sig) = a.first == b.first && a.second == b.second

Base.get(a::AbstractArray, s::Sig, default) = get(a[s.first], s.second, default)
Base.get(a::SparseVector, s::Sig, default) = begin
    ixrange = searchsorted(a.nzind, s.first)
    if isempty(ixrange)
        return default
    else
        return get(a.nzval[ixrange[1]], s.second, default)
    end
end

# TODO: also add the 'normal', non-InPlace operations
inclusiveinplace!(op::Union{typeof(+), typeof(-)}, a::AbstractArray, b::Sig) = (a[b.first] = inclusiveinplace!(op, a[b.first], b.second); a)


# TODO: remove; replace the testing by =>
==(a::Tuple, b::Sig) = a[1] == b.first && a[2] == b.second
==(b::Sig, a::Tuple) = a[1] == b.first && a[2] == b.second

end # module
