using Base.Test
using PolynomialRings: polynomial_ring
using PolynomialRings.Groebner: red, groebner_basis

@testset "Groebner" begin

    R,(x,y) = polynomial_ring(Rational{Int}, :x, :y)
    S,(z,) = polynomial_ring(Int, :z)

    @test red(x^2, [x]) == (0, [x]')

    @test red(x + y, [x]) == (y, [1]')

    f, G = (x^23 + y -x*43, [x^3*y^4, x^7])
    f_red, factors = red(f,G)
    @test f == f_red + (factors * G)

    G = [x^5, x^2 + y, x*y + y^2]
    GG = groebner_basis(G)
    @test length(GG) == 3

end
