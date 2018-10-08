module Display

import Base: show


import ..MonomialOrderings: MonomialOrder
import ..Monomials: AbstractMonomial, enumeratenz
import ..Polynomials: Polynomial, terms, basering
import ..Terms: Term, coefficient, monomial
import ..VariableNames: Named, Numbered
import PolynomialRings: namestype


# -----------------------------------------------------------------------------
#
# Display of polynomials
#
# -----------------------------------------------------------------------------

_variable(::Type{Named{Names}}, ix)   where Names = String(Names[ix])
_variable(::Type{Numbered{Name}}, ix) where Name  = "$Name[$ix]"

function show(io::IO, m::AbstractMonomial)
    if m == one(m)
        print(io, "1")
        return
    end
    factors = String[]
    for (ix, i) in enumeratenz(m)
        symbol = _variable(namestype(m), ix)
        if i == 1
            push!(factors, "$symbol")
        elseif i > 1
            push!(factors, "$symbol^$i")
        end
    end
    join(io, factors, "*")
end

function show(io::IO, t::Term)
    coeff = coefficient(t)
    monom = monomial(t)
    sign = ""
    factors = String[]
    if monom != one(monom) && coeff == -one(coeff) && coeff != one(coeff) # 1 == -1 in ℤ/2ℤ
        sign = "-"
    elseif monom == one(monom) || coeff != one(coeff)
        coeff_repr = "$(coefficient(t))"
        if (occursin(" + ", coeff_repr) || occursin(" - ", coeff_repr)) && monomial(t) != one(monomial(t))
            push!(factors, "($coeff_repr)")
        else
            push!(factors, coeff_repr)
        end
    end
    if monom != one(monom)
        push!(factors, "$monom")
    end
    print(io, sign)
    join(io, factors, "*")
end

function show(io::IO, p::Polynomial)
    if length(terms(p)) == 0
        print(io, "0")
    end
    print(io, join((repr(t) for t in reverse(terms(p))), " + "))
end

# -----------------------------------------------------------------------------
#
# Display of types
#
# -----------------------------------------------------------------------------

function defaultshow(io, t)
    if t isa DataType
        invoke(show, Tuple{IO, DataType}, io, t)
    elseif t isa UnionAll
        invoke(show, Tuple{IO, UnionAll}, io, t)
    else
        print(io, "<undisplayable>")
    end
end

function show(io::IO, t::MO) where MO <: MonomialOrder{Name} where Name
    if isconcretetype(t)
        print(io, Name)
    else
        defaultshow(io, t)
    end
end

function show(io::IO, t::Type{Named{Names}}) where Names
    if isconcretetype(t)
        join(io, Names, ",")
    else
        defaultshow(io, t)
    end
end

function show(io::IO, t::Type{Numbered{Name}}) where Name
    if isconcretetype(t)
        print(io, "$(Name)[]")
    else
        defaultshow(io, t)
    end
end

# keep in sync with Constructors.jl
_repr(::Type{BigInt}) = :ℤ
_repr(::Type{Rational{BigInt}}) = :ℚ
_repr(::Type{BigFloat}) = :ℝ
_repr(::Type{Complex{BigFloat}}) = :ℂ
_repr(x) = x

function show(io::IO, t::Type{P}) where P<:Polynomial
    if isconcretetype(t)
        print(io, "$(_repr(basering(P)))[$(namestype(P))]")
    else
        defaultshow(io, t)
    end
end

function show(io::IO, t::Type{Term{M,C}}) where {M,C}
    if isconcretetype(t)
        print(io, "(Term over $C in $(namestype(M)))")
    else
        defaultshow(io, t)
    end
end


end
