using Test

import PolynomialRings.Constants: One, Zero, MinusOne

@testset "Constants" begin
    @testset "Compile-time operations" begin
        @test one(One) === one(Zero) === +One() === -MinusOne() === One() + Zero() ===
                    Zero() + One() === One() * One() == MinusOne() * MinusOne()
        @test zero(Zero) === zero(One) === +Zero() === -Zero() === One() + MinusOne() ===
                    Zero() * One() === Zero() * MinusOne() === One() - One() === MinusOne() - MinusOne()
        @test iszero(Zero())
        @test !iszero(One())
        @test isone(One())
        @test !iszero(MinusOne()) && !isone(MinusOne())
    end
end
