using Test

import PolynomialRings.Expansions: expansionorder, constant_coefficient, deg
import PolynomialRings.Generators: Generator
import PolynomialRings: @degrevlex, @variable, @ring, @ring!
import PolynomialRings: polynomial_ring, monomialorder

@testset "Generators" begin
    @testset "Named generators" begin
        R, (x, y) = polynomial_ring(:x, :y, basering=Int)
        X, Y = 1x, 1y
        @test X isa R
        @test Y isa R

        @test x == X
        @test y == Y

        @test 1x isa R
        @test x + 0 isa R
        @test convert(@ring(Int[x,y,z]), x) isa @ring(Int[x,y,z])

        @test expansionorder(x) == @degrevlex(x)
        @test expansionorder(x, y) == @degrevlex(x > y)
        @test expansionorder(y, x) == @degrevlex(y > x)

        @test 6x^2 * diff(x, x) ==3x * diff(x^2, x) == 2diff(x^3, x) == 6x^2

        @test constant_coefficient(x, x) == 0
        @test deg(x, x) == 1
        @test constant_coefficient(x, y) == x
        @test deg(x, y) == 0
        @test constant_coefficient(x, x, y) == 0
        @test deg(x, x, y) == 1
    end

    @testset "Numbered generators" begin
        R = @ring! Int[c[]]

        @test c[1] isa R
        c1, c2 = c[]
        @test c1 isa R && c2 isa R
        c3, c4 = c(), c()
        @test c3 isa R && c4 isa R
        reset(c)
        c5, c6 = c(), c()
        @test (c3, c4) == (c5, c6)

        R = @ring! Int[c[1:4]]

        @test c[1] isa R
        c1, c2 = c[]
        @test c1 isa R && c2 isa R
        c3, c4 = c(), c()
        @test c3 isa R && c4 isa R
        reset(c)
        c5, c6 = c(), c()
        @test (c3, c4) == (c5, c6)

        c(); c()
        @test_throws BoundsError c()
    end
end
