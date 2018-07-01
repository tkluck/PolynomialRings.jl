if VERSION < v"0.7-"
    using Base.Test
else
    using Test
end
using PolynomialRings


@testset "CommutativeAlgebras" begin
    @testset "Ideals" begin
        R = @ring! Int[x,y]
        I = Ideal(x^2)
        @test !(1 in I)
        @test !(x in I)
        @test x^2 in I
        @test x^3 in I
        @test !(y in I)
        @test !(x*y in I)
        @test x^2*y in I
        @test x^3*y in I
        @test !(x^2*y + 1 in I)

        J = Ideal(x^2, y^2)
        @test I ⊆ J
        @test !(J ⊆ I)

        @test I + J == J
        @test !(y^2 in I*J)
        @test I^5 ⊆ J^5
    end

    @testset "Construction and conversion" begin
        R = @ring! ℚ[α]

        S = R/Ideal(α^2 - 2)

        @test S(α)^2 - 2 == 0

        Q = NumberField(S)
        @test Q(α)^2 - 2 == 0

        @test Q(1+α) // Q(1+α) == 1
        @test Q(1+α)*Q(1-α) == -1
        @test -1 // Q(1+α) == Q(1-α)

        A = @ring! Q[x]
        @test (α*x)^2 == 2x^2

        # duplicate variable name
        @test_throws ArgumentError @ring Q[α]

        # memoization
        @test S === R/Ideal(α^2 - 2)

        #@numberfield! Q[γ]/(γ^2 - α)

        #@test γ^2 == α
        #@test γ^3 == α*γ
        #@test γ^4 == 2

        #B = @ring! ℚ[α, x]
        #@test (α*x)^2 != 2x^2
        #@test A(α*x)^2 == A(2x^2)

        #S = @numberfield! ℚ[α,β]/(α^2 - 2, β^3 - 2)
        #@test α^2 == β^3 == 2

        #QQ = @numberfield Q[β]/(β^3 - 2)
        #@test QQ(β + α) == QQ(β) + Q(α)
    end
end
