using Base.Test
using PolynomialRings

@testset "PolynomialRings" begin

    using PolynomialRings: basering

    R,(x,y) = polynomial_ring(Rational{Int}, :x, :y)
    S,(z,) = polynomial_ring(Int, :z)
    S,(a,b) = polynomial_ring(BigInt, :a, :b)

    # arithmetic
    @test x != 0
    @test 0*x == 0
    @test 1*x != 0
    @test 1*x == x
    @test 2*x == x+x
    @test 2*x*y == y*x*2
    @test x*y*x == x^2*y
    @test x-x == 0
    @test -x == 0-x
    @test +x == x

    # Extension of scalars
    @test 1//2*z == z//2
    @test 2*z//2 == z
    @test 0.5*z == z/2
    @test 2(z+0.5) == 2*z + 1
    @test 2(z+1//2) == 2*z + 1
    @test basering(z+1//2) == Rational{Int}
    @test basering(z+0.5) == float(Int)

    # conversions between rings
    @test x*z == z*x
    @test x*y*z == x*z*y
    @test (x+z)*(x-z) == x^2 - z^2

    # substitution
    @test (x^2+y^2)(x=1,y=2) == 5
    @test (x^2+y^2)(x=1) == 1+y^2
    @test [1+x; 1+y](x=1) == [2; 1+y]
    @test [1+x; 1+y](x=1, y=2) == [2; 3]

    # zero comparison in Base
    @test findfirst([x-x, x, x-x, 0, x]) == 2
    @test findfirst([0, x, x-x, 0, x]) == 2
    @test findfirst([0*x, x-x, 0, x]) == 4

    # degrees
    @test deg((a^2+9)^39) == 2*39
    @test deg((a*b+9)^39) == 2*39
    @test deg((a*b*z+9)^39) == 3*39
end

@testset "Expansions" begin

    using PolynomialRings: expansion
    R,(x,y,z) = polynomial_ring(Int, :x, :y, :z)

    @test collect(expansion(x*y*z + x*z + z^2, :z)) == [(z, x*y + x), (z^2, 1)]
    @test collect(expansion(x*y - x, :x, :y, :z)) == [(x,-1), (x*y, 1)]
    @test collect(expansion([x*z 1; z+1 x], :z)) == [(1, [0 1; 1 x]), (z, [x 0; 1 0])]

end
