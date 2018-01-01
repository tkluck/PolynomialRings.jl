using Base.Test
using PolynomialRings

@testset "Reductions" begin
    R = @ring! ℤ[x,y]

    @test divrem(x^2, [x]) == ([x]', 0)
    @test divrem(x + y, [x]) == ([1]', y)
    @test divrem(1, [x]) == ([0]', 1)
    @test divrem(x^2, [x,0]) == ([x,0]', 0)

    @test div(x^2, [x]) == [x]'
    @test div(x + y, [x]) == [1]'
    @test div(1, [x]) == [0]'

    @test rem(x^2, [x]) == 0
    @test rem(x + y, [x]) == y
    @test rem(1, [x]) == 1

    f, G = (x^23 + y -x*43, [x^3*y^4, x^7])
    factors, f_red = divrem(f,G)
    @test f == f_red + (factors * G)
end

@testset "Gröbner" begin
    for backend in [PolynomialRings.Backends.Gröbner.Buchberger(), PolynomialRings.GröbnerGWV.GWV()]
        PolynomialRings.Backends.Gröbner.set_default(backend)

        R = @ring! ℤ[x,y]

        G = [x^5, x^2 + y, x*y + y^2]
        GG, tr = gröbner_transformation(G)
        @test rem(y^2, GG) == 0
        @test [a for a in tr]*G == GG
        @test rem(y^2, gröbner_basis(G)) == 0

        G = [[x^5-y,x^4],[x^3+y,y^3]]
        GG, tr= gröbner_transformation(G)
        @test [a for a in tr]*G == GG

        GG= gröbner_basis(G)

        @test gröbner_basis(R[]) == R[]
    end
end

@testset "Syzygy" begin

    R = @ring! ℚ[x,y]

    G = [x^5, x^2 + y, x*y + y^2]
    GG, tr = gröbner_transformation(G)

    K = syzygies(GG)

    @test iszero(K * GG)

    G = [[x^5-y,x^4],[x^3+y,y^3]]
    GG, tr= gröbner_transformation(G)

    K = syzygies(GG)

    @test iszero(K * GG)

end
