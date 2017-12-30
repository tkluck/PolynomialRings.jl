using Combinatorics
using PolynomialRings

macro showtime(expr)
    rep = sprint(print, expr)
    quote
        info("Timing: $( $rep )")
        @time $expr
    end
end

cyclic(vars...) = [prod(vars) - 1; [sum(prod, combinations(vars, n)) for n=1:(length(vars)-1)]]

@ring! ℤ[c[]]
groebner_basis(cyclic(c[1:3]...)) # compile
@showtime groebner_basis(cyclic(c[1:9]...))
