module Display

import PolynomialRings.Polynomials: Polynomial, terms, basering
import PolynomialRings.NamedPolynomials: NamedPolynomial, names
import PolynomialRings.Terms: Term, coefficient, monomial
import PolynomialRings.Monomials: AbstractMonomial, num_variables
import PolynomialRings: monomialtype, monomialorder

import Base: show

# -----------------------------------------------------------------------------
#
# Display of polynomials
#
# -----------------------------------------------------------------------------

function show(io::IO, p::P) where P <: Polynomial
    DummyNames = :x
    show(io, NamedPolynomial{P, DummyNames}(p))
end

_varname(::Type{Names}, ix::Integer) where Names <: Tuple = repr(fieldtype(Names, ix))[2:end]
_varname(s::Symbol, ix::Integer) = (var = repr(s)[2:end]; "$var$ix")

function show(io::IO, np::NP) where NP <: NamedPolynomial{P, Names} where P<:Polynomial where Names
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

# -----------------------------------------------------------------------------
#
# Display of types
#
# -----------------------------------------------------------------------------

function show(io::IO, ::Type{NP}) where NP <: NamedPolynomial{P} where P <: Polynomial
    show_names = names(NP) isa Symbol ? "$(names(NP))_i" : join([_varname(names(NP), i) for i in 1:nfields(names(NP))], ",", " and ")
    print(io, "(Polynomial over $(basering(NP)) in $show_names)")
end

function show(io::IO, ::Type{NP}) where NP <: NamedPolynomial{P} where P <: Term
    show_names = names(NP) isa Symbol ? "$(names(NP))_i" : join([_varname(names(NP), i) for i in 1:nfields(names(NP))], ",", " and ")
    print(io, "(Term over $(basering(NP)) in $show_names)")
end

function show(io::IO, ::Type{NP}) where NP <: NamedPolynomial{P} where P <: AbstractMonomial
    show_names = names(NP) isa Symbol ? "$(names(NP))_i" : join([_varname(names(NP), i) for i in 1:nfields(names(NP))], ",", " and ")
    print(io, "(Monomial in $show_names)")
end

function show(io::IO, ::Type{P}) where P <: Polynomial
    n = try
        num_variables(monomialtype(P))
    catch
        "∞"
    end
    print(io, "(Polynomial over $(basering(P)) in $n variables ($(monomialorder(P))))")
end

end
