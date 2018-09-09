module Display

import PolynomialRings: namestype
import PolynomialRings.Polynomials: Polynomial, terms, basering
import PolynomialRings.Terms: Term, coefficient, monomial
import PolynomialRings.Monomials: AbstractMonomial, enumeratenz
import PolynomialRings.VariableNames: Named, Numbered
import PolynomialRings.MonomialOrderings: MonomialOrder

import Base: show

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

function show(io::IO, ::MO) where MO <: MonomialOrder{Name} where Name
    print(io, Name)
end

function show(io::IO, ::Type{Named{Names}}) where Names
    join(io, Names, ",")
end

function show(io::IO, ::Type{Numbered{Name}}) where Name
    print(io, "$(Name)[]")
end

# keep in sync with Constructors.jl
_repr(::Type{BigInt}) = :ℤ
_repr(::Type{Rational{BigInt}}) = :ℚ
_repr(::Type{BigFloat}) = :ℝ
_repr(::Type{Complex{BigFloat}}) = :ℂ
_repr(x) = x

function show(io::IO, ::Type{Polynomial{T}}) where T
    print(io, "$(_repr(basering(T)))[$(namestype(T))]")
end

function show(io::IO, ::Type{Term{M,C}}) where {M,C}
    print(io, "(Term over $C in $(namestype(M)))")
end


end
