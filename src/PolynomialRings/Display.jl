module Display

import PolynomialRings.Polynomials: Polynomial, terms
import PolynomialRings.Terms: coefficient, monomial

import Base: show

function show(io::IO, p::P) where P <: Polynomial
    frst = true
    if length(terms(p)) == 0
        print(io, zero(R))
    end
    for t in terms(p)
        if !frst
            print(io, " + ")
        else
            frst = false
        end
        print(io, coefficient(t))
        for (ix, i) in enumerate(monomial(t))
            varname = "x$ix"
            if i == 1
                print(io, " $varname")
            elseif i > 1
                print(io, " $varname^$i")
            end
        end
    end
end

end
