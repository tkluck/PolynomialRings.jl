using Test
using PolynomialRings
using LinearAlgebra


@testset "LinearAlgebra" begin
    R, (x, y) = polynomial_ring(:x, :y, basering=Int)

    @test [x,y]' * [-y,x] == transpose([x,y]) * [-y,x] == dot([x,y], [-y,x]) == 0
    @test rem.([x y; -y x] * [x,y], 1-x^2-y^2) == [1,0]
end