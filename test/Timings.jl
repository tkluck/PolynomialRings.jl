using Combinatorics
using PolynomialRings

import PolynomialRings.Library: cyclic_ideal, katsura_ideal

PolynomialRings.Backends.Gröbner.set_default(PolynomialRings.GröbnerGWV.GWV())

macro showtime(expr)
    rep = sprint(print, expr)
    quote
        info("Timing: $( $rep )")
        @time $expr
    end
end

@ring! ℤ[c[]]
gröbner_basis(cyclic_ideal(c[1:3]...)) # compile
@showtime gröbner_basis(cyclic_ideal(c[1:6]...))
@showtime gröbner_basis(katsura_ideal(c[1:6]...))

R, c = polynomial_ring(:c1, :c2, :c3, :c4, :c5, :c6, :c7, :c8, :c9, monomialorder=:degrevlex)
gröbner_basis(cyclic_ideal(c[1:3]...)) # compile
@showtime gröbner_basis(cyclic_ideal(c[1:6]...))
@showtime gröbner_basis(katsura_ideal(c[1:6]...))

R, c = polynomial_ring(:c1, :c2, :c3, :c4, :c5, :c6, :c7, :c8, :c9, monomialorder=:lex)
gröbner_basis(cyclic_ideal(c[1:3]...)) # compile
@showtime gröbner_basis(cyclic_ideal(c[1:4]...))
@showtime gröbner_basis(katsura_ideal(c[1:4]...))
