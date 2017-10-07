module Display

import PolynomialRings: namestype, variablesymbols
import PolynomialRings.Polynomials: Polynomial, terms, basering
import PolynomialRings.Terms: Term, coefficient, monomial
import PolynomialRings.VariableNames: Named, Numbered
import PolynomialRings.MonomialOrderings: MonomialOrder

import Base: show

# -----------------------------------------------------------------------------
#
# Display of polynomials
#
# -----------------------------------------------------------------------------

function show(io::IO, p::Polynomial)
    frst = true
    if length(terms(p)) == 0
        print(io, zero(basering(p)))
    end
    for t in terms(p)
        if !frst
            print(io, " + ")
        else
            frst = false
        end
        print(io, coefficient(t))
        for ((ix, i), symbol) in zip( enumerate(monomial(t)), variablesymbols(typeof(p)) )
            if i == 1
                print(io, " $symbol")
            elseif i > 1
                print(io, " $symbol^$i")
            end
        end
    end
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
    print(io, "$(Name)_i")
end

function show(io::IO, ::Type{Polynomial{A,Order}}) where {A,Order}
    T = eltype(A)
    print(io, "(Polynomial over $(basering(T)) in $(namestype(T)) ($Order))")
end

function show(io::IO, ::Type{Term{M,C}}) where {M,C}
    print(io, "(Term over $C in $(namestype(M)))")
end


end
