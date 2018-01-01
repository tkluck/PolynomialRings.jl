using Combinatorics
using PolynomialRings

macro showtime(expr)
    rep = sprint(print, expr)
    quote
        info("Timing: $( $rep )")
        @time $expr
    end
end

cyclic(vars...) = (vars=collect(vars); [prod(vars) - 1; [sum(i->prod(circshift(vars, i)[1:n]), 1:length(vars)) for n=1:(length(vars)-1)]])

@ring! ℤ[c[]]
groebner_basis(cyclic(c[1:3]...)) # compile
@showtime groebner_basis(cyclic(c[1:5]...))

R, c = polynomial_ring(:c1, :c2, :c3, :c4, :c5, :c6, :c7, :c8, :c9, monomialorder=:degrevlex)
groebner_basis(cyclic(c[1:3]...)) # compile
@showtime groebner_basis(cyclic(c[1:5]...))

R, c = polynomial_ring(:c1, :c2, :c3, :c4, :c5, :c6, :c7, :c8, :c9, monomialorder=:lex)
groebner_basis(cyclic(c[1:3]...)) # compile
@showtime groebner_basis(cyclic(c[1:4]...))
