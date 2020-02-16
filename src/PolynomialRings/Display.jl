module Display

import Base: show

import ..AbstractMonomials: AbstractMonomial, exponentsnz
import ..NamingSchemes: Named, Numbered, showvars
import ..Polynomials: Polynomial, nzrevterms, basering
import ..Terms: Term, coefficient, monomial
import PolynomialRings: namingscheme, monomialorder

# -----------------------------------------------------------------------------
#
# Display of polynomials
#
# -----------------------------------------------------------------------------

_variable(::Named{Names}, ix)   where Names = String(Names[ix])
_variable(::Numbered{Name}, ix) where Name  = "$Name[$ix]"

function show(io::IO, m::AbstractMonomial)
    if m == one(m)
        print(io, "1")
        return
    end
    factors = String[]
    for (ix, (i,)) in exponentsnz(namingscheme(m), m)
        symbol = _variable(namingscheme(m), ix)
        if i == 1
            push!(factors, "$symbol")
        elseif i > 1
            push!(factors, "$symbol^$i")
        end
    end
    join(io, factors, "*")
end

# call isone on matrices/arrays
isone_safe(x) = try isone(x); catch; false; end

function show(io::IO, t::Term)
    coeff = coefficient(t)
    monom = monomial(t)
    sign = ""
    factors = String[]
    if !isone(monom) && isone_safe(-coeff) && !isone_safe(coeff) # 1 == -1 in ℤ/2ℤ
        sign = "-"
    elseif isone(monom) || !isone_safe(coeff)
        coeff_repr = "$(coefficient(t))"
        if (occursin(" + ", coeff_repr) || occursin(" - ", coeff_repr)) && monomial(t) != one(monomial(t))
            push!(factors, "($coeff_repr)")
        else
            push!(factors, coeff_repr)
        end
    end
    if !isone(monom)
        push!(factors, "$monom")
    end
    print(io, sign)
    join(io, factors, "*")
end

function show(io::IO, p::Polynomial)
    if iszero(p)
        print(io, "0")
    end
    print(io, join((repr(t) for t in nzrevterms(p)), " + "))
end

# -----------------------------------------------------------------------------
#
# Display of types
#
# -----------------------------------------------------------------------------

function defaultshow(io, T)
    invoke(show, Tuple{IO, Type}, io, T)
end

# keep in sync with Constructors.jl
_repr(x) = x
_repr(::Type{BigInt}) = :ℤ
_repr(::Type{Rational{BigInt}}) = :ℚ
_repr(::Type{BigFloat}) = :ℝ
_repr(::Type{Complex{BigFloat}}) = :ℂ
_repr(P::Type{<:Polynomial}) = begin
    if isconcretetype(P)
        "$(_repr(basering(P)))[$(showvars(P))]"
    else
        defaultshow(io, P)
    end
end

function show(io::IO, t::Type{P}) where P<:Polynomial
    if isconcretetype(t)
        print(io, "@ring(", _repr(t), ")")
    else
        defaultshow(io, t)
    end
end

function show(io::IO, t::Type{Term{M,C}}) where {M,C}
    if isconcretetype(t)
        print(io, "(Term over $C in $(monomialorder(t)))")
    else
        defaultshow(io, t)
    end
end


end
