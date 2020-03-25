module NamedConversions

import Base: convert
import InPlace: @inplace

import ..AbstractMonomials: exponents
import ..Expansions: expansion
import ..Generators: NumberedVariableGenerator
import ..Polynomials: Polynomial, NamedPolynomial, NumberedPolynomial
import ..Polynomials: generators, basering
import PolynomialRings: boundnames, boundvalues, nestednamingscheme

boundnames(T) = ()
boundvalues(T) = ()

convert(::Type{P1}, a::P2) where P1 <: Polynomial where P2 = convert_through_expansion(P1, a)

markednames(T) = boundnames(T)
markednames(P::Type{<:Polynomial}) = nestednamingscheme(P)
markedvalues(T) = boundvalues(T)
markedvalues(P::Type{<:NamedPolynomial}) = begin
    v = markedvalues(basering(P))
    g = map(x -> 1x, generators(P))
    return (v..., generators(P))
end
markedvalues(P::Type{<:NumberedPolynomial}) = begin
    v = markedvalues(basering(P))
    g = NumberedVariableGenerator(P)
    return (v..., g)
end
markedcoeff(T, x) = convert(Number, x)
markedcoeff(P::Type{<:Polynomial}, x) = convert(basering(P), x)

convert_through_expansion(T, x) = begin
    isempty(markednames(T)) && return convert(T, x)
    res = zero(T)

    for (c, ms) in _multiexpansion(x, markednames(T)...)
        # special cases to avoid relying on implementations of :* and :^ when possible
        if isone(c) && all(isone, ms)
            @inplace res += one(T)
        elseif isone(c)
            @inplace res += _subs(one(T), ms .=> markednames(T) .=> markedvalues(T))
        elseif all(isone, ms)
            cc = markedcoeff(T, c)
            @inplace res += cc
        else
            cc = markedcoeff(T, c)
            @inplace res +=  _subs(cc, ms .=> markednames(T) .=> markedvalues(T))
        end
    end

    return res
end

_multiexpansion(x) = ((x,()),)
_multiexpansion(x, scheme, schemes...) = (
    (c, (m, ms...))
    for (m, cc) in expansion(x, scheme)
    for (c, ms) in _multiexpansion(cc, schemes...)
)

const TupleOf{T, N} = NTuple{N, T}

_subs(c, pairs::TupleOf{Pair}) = _subs(c, pairs...)
_subs(c) = c
_subs(c, pairs::Pair...) = begin
    m, (scheme, val) = first(pairs)
    if isone(m)
        return _subs(c, Base.tail(pairs)...)
    else
        a = _subs(val, exponents(m, scheme))
        b = _subs(c, Base.tail(pairs)...)
        return a * b
    end
end

_subs(val, exps) = prod(
    isone(e) ? v : v^e
    for (v, e) in zip(val, exps)
    if !iszero(e)
)

_subs(val::NumberedVariableGenerator, exps) = prod(
    val[i]^e
    for (i, e) in enumerate(exps)
)


end # module
