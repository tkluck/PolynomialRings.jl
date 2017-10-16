module Display

import PolynomialRings: namestype
import PolynomialRings.Polynomials: Polynomial, terms, basering
import PolynomialRings.Terms: Term, coefficient, monomial
import PolynomialRings.Monomials: AbstractMonomial
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
    for (ix, i) in enumerate(m)
        symbol = _variable(namestype(m), ix)
        if i == 1
            print(io, " $symbol")
        elseif i > 1
            print(io, " $symbol^$i")
        end
    end
end

function show(io::IO, t::Term)
    print(io, coefficient(t))
    print(io, monomial(t))
end

function show(io::IO, p::Polynomial)
    if length(terms(p)) == 0
        print(io, zero(basering(p)))
    end
    print(io, join((repr(t) for t in terms(p)), " + "))
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
    print(io, join(Names, ",", " and "))
end

function show(io::IO, ::Type{Numbered{Name}}) where Name
    print(io, "$(Name)[]")
end

function show(io::IO, ::Type{Polynomial{A,Order}}) where {A,Order}
    T = eltype(A)
    print(io, "(Polynomial over $(basering(T)) in $(namestype(T)) ($Order))")
end

function show(io::IO, ::Type{Term{M,C}}) where {M,C}
    print(io, "(Term over $C in $(namestype(M)))")
end


end
