using Base.Test
using PolynomialRings

@testset "PolynomialRings" begin

    import PolynomialRings: polynomial_ring

    R,(x,y) = polynomial_ring(Rational{Int}, :x, :y)
    S,(z,) = polynomial_ring(Int, :z)

    @test x != 0
    @test 0*x == 0
    @test 1*x != 0
    @test 1*x == x
    @test 2*x == x+x
    @test 2*x*y == y*x*2
    @test x*y*x == x^2*y
    @test x-x == 0

    @test x*z == z*x
    @test x*y*z == x*z*y

    @test (x+z)*(x-z) == x^2 - z^2

    @test (x^2+y^2)(x=1,y=2) == 5
    @test (x^2+y^2)(x=1) == 1+y^2
    @test [1+x; 1+y](x=1) == [2; 1+y]
    @test [1+x; 1+y](x=1, y=2) == [2; 3]

    @test findfirst([x-x, x, x-x, 0, x]) == 2
    @test findfirst([0, x, x-x, 0, x]) == 2
    @test findfirst([0*x, x-x, 0, x]) == 4
end

@testset "Expansions" begin

    import PolynomialRings: expansion

    @test expansion(x*y*z + x*z + z^2, :z) == [(z, x*y + x), (z^2, 1)]

    @test expansion([x*z 1; z+1 x], :z) == [(1, [0 1; 1 x]), (z, [x 0; 1 0])]

end
