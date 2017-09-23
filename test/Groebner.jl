using Base.Test
using PolynomialRings
using PolynomialRings.Groebner: red, groebner_basis, syzygies

@testset "Groebner" begin

    R = @ring ℤ[x,y]

    @test red(x^2, [x]) == (0, [x]')

    @test red(x + y, [x]) == (y, [1]')

    @test red(1, [x]) == (1, [0]')

    f, G = (x^23 + y -x*43, [x^3*y^4, x^7])
    f_red, factors = red(f,G)
    @test f == f_red + (factors * G)

    G = [x^5, x^2 + y, x*y + y^2]
    GG, tr = groebner_basis(G)
    @test length(GG) == 5
    @test [a for a in tr]*G == GG

    G = [[x^5-y,x^4],[x^3+y,y^3]]
    GG, tr= groebner_basis(G)
    @test length(GG) == 6
    @test [a for a in tr]*G == GG

    GG= groebner_basis(G, Val{false})
    @test length(GG) == 6
end

@testset "Syzygy" begin

    R = @ring ℚ[x,y]

    G = [x^5, x^2 + y, x*y + y^2]
    GG, tr = groebner_basis(G)

    K = syzygies(GG)

    @test iszero(K * GG)

    G = [[x^5-y,x^4],[x^3+y,y^3]]
    GG, tr= groebner_basis(G)

    K = syzygies(GG)

    @test iszero(K * GG)

end
