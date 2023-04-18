using Test
using PolynomialRings
using LinearAlgebra


@testset "LinearAlgebra" begin
    R, (x, y) = polynomial_ring(:x, :y, basering=Int)

    @test [x,y]' * [-y,x] == transpose([x,y]) * [-y,x] == dot([x,y], [-y,x]) == 0
end