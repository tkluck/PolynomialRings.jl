using Base.Test
using PolynomialRings

@testset "PolynomialRings" begin

    using PolynomialRings: basering

    R,(x,y) = polynomial_ring(Rational{Int}, :x, :y)
    S,(z,) = polynomial_ring(Int, :z)
    T,(a,b) = polynomial_ring(BigInt, :a, :b)

    @testset "Arithmetic" begin
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
        @test x^1 == x
        @test (x+y)^9 == (x+y)^6 * (x+y)^3
        @test prod(x+y for _=1:20) == (x+y)^20
        @test prod(x*y+y for _=1:20) == (x*y+y)^20
    end

    @testset "Extension of scalars" begin
        @test 1//2*z == z//2
        @test 2*z//2 == z
        @test 0.5*z == z/2
        @test 2(z+0.5) == 2*z + 1
        @test 2(z+1//2) == 2*z + 1
        @test basering(z+1//2) == Rational{Int}
        @test basering(z+0.5) == float(Int)
        @test (x+im*y)*(x-im*y) == x^2 + y^2
    end

    @testset "conversions between rings" begin
        @test x*z == z*x
        @test x*y*z == x*z*y
        @test (x+z)*(x-z) == x^2 - z^2

        @test convert(R,:x) == x
        @test convert(S,:z) == z
    end

    @testset "substitution" begin
        @test (x^2+y^2)(x=1,y=2) == 5
        @test (x^2+y^2)(x=1) == 1+y^2
        @test [1+x; 1+y](x=1) == [2; 1+y]
        @test [1+x; 1+y](x=1, y=2) == [2; 3]
    end

    @testset "zero comparison in Base" begin
        @test findfirst([x-x, x, x-x, 0, x]) == 2
        @test findfirst([0, x, x-x, 0, x]) == 2
        @test findfirst([0*x, x-x, 0, x]) == 4
    end

    @testset "degrees" begin
        @test deg((a^2+9)^39) == 2*39
        @test deg((a*b+9)^39) == 2*39
        @test deg((a*b*z+9)^39) == 3*39
    end

    dx(f) = diff(f, :x)
    dy(f) = diff(f, :y)
    euler(f) = x*dx(f) + y*dy(f)

    @testset "differentiation" begin
        @test dx(x^2) == 2x
        @test dy(x^2) == 0
        dz(f) = diff(f, :z)
        @test dz(z^2) == 2z
        @test dz(S(1)) == 0
    end

    @testset "formal coefficients" begin
        ch = formal_coefficients(R, :c)
        c() = take!(ch)
        h5() = c()*x^5 + c()*x^4*y + c()*x^3*y^2 + c()*x^2*y^3 + c()*x*y^4 + c()*y^5
        f = h5()
        @test euler(f) == 5*f

        @test diff(f^2, :x) == diff(f, :x) * 2*f

        g = [h5(); h5()]
        @test euler(g) == 5*g

    end



end

@testset "Expansions" begin

    using PolynomialRings: expansion, @expansion, coefficient, @coefficient
    R,(x,y,z) = polynomial_ring(Int, :x, :y, :z)

    @testset "expansion()" begin
        @test collect(expansion(x*y*z + x*z + z^2, :z)) == [((1,), x*y + x), ((2,), 1)]
        @test collect(expansion(x*y - x, :x, :y, :z)) == [((1,0,0),-1), ((1,1,0), 1)]
        @test collect(expansion(x*y - x, :z, :x, :y)) == [((0,1,0),-1), ((0,1,1), 1)]
        @test collect(expansion([x*z 1; z+1 x], :z)) == [((0,), [0 1; 1 x]), ((1,), [x 0; 1 0])]

        # work-around for nested macros
        lhs = collect(@expansion(x*y*z + x*z + z^2, z))
        @test lhs == [(z, x*y + x), (z^2, 1)]

        lhs = collect(@expansion(x*y - x, z, x, y))
        @test lhs == [(x,-1), (x*y, 1)]
    end

    @testset "coefficient()" begin
        @test coefficient(x^3 + x^2*y + y, (1,), :y) == x^2 + 1
        @test coefficient(x^3 + x^2*y + y, (0,1), :x, :y) == 1
        @test coefficient(x^3 + x^2*y + y, (1,0), :y, :x) == 1

        @test coefficient(x^3 + x^2*y + y, y, :y) == x^2 + 1
        @test coefficient(x^3 + x^2*y + y, y, :x, :y) == 1

        @test 1 == @coefficient(x^3 + x^2*y + y, x^0 * y)
        @test x^2+1 == @coefficient(x^3 + x^2*y + y, y)

        @test 0 == @coefficient(x^3 + x^2*y + y, y^2)

        @test 1 + y == constant_coefficient(x^3*y + x + y + 1, :x)
        @test 1     == constant_coefficient(x^3*y + x + y + 1, :x, :y)
        @test 1 + y == @constant_coefficient(x^3*y + x + y + 1, x)
        @test 1     == @constant_coefficient(x^3*y + x + y + 1, x, y)
    end

end
