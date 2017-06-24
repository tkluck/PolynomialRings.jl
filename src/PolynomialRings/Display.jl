module Display

import PolynomialRings.Polynomials: Polynomial, terms, basering
import PolynomialRings.NamedPolynomials: NamedPolynomial
import PolynomialRings.Terms: coefficient, monomial

import Base: show

function show(io::IO, p::P) where P <: Polynomial
    DummyNames = :x
    show(io, NamedPolynomial{P, DummyNames}(p))
end

_varname(::Type{Names}, ix::Integer) where Names <: Tuple = repr(fieldtype(Names, ix))[2:end]
_varname(s::Symbol, ix::Integer) = (var = repr(s)[2:end]; "$var$ix")

function show(io::IO, np::NP) where NP <: NamedPolynomial{P, Names} where {P, Names}
    p = np.p
    frst = true
    if length(terms(p)) == 0
        print(io, zero(basering(P)))
    end
    for t in terms(p)
        if !frst
            print(io, " + ")
        else
            frst = false
        end
        print(io, coefficient(t))
        for (ix, i) in enumerate(monomial(t))
            varname = _varname(Names, ix)
            if i == 1
                print(io, " $varname")
            elseif i > 1
                print(io, " $varname^$i")
            end
        end
    end
end

end
