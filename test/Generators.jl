using Test

import PolynomialRings.Expansions: expansionorder
import PolynomialRings.Generators: Generator
import PolynomialRings: @degrevlex, @variable, @ring
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
    end
end
