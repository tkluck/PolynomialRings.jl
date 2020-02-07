using Test
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

        B = @ring! ℚ[α, x]
        @test (α*x)^2 != 2x^2
        @test A(α*x)^2 == A(2x^2)

        C = @ring! ℚ[c[1:2]]
        D = C / Ideal(c[1]^2 - 2, c[2]^3 - 3)
        E = @ring! C[x]
        @test base_extend(c[1]^2*x - 2x, D) == 0
        @test base_extend(c[2]^3*x - 2x, D) == x

        S = @numberfield! ℚ[α,β]/(α^2 - 2, β^3 - 2)
        @test α^2 == β^3 == 2

        #QQ = @numberfield Q[β]/(β^3 - 2)
        #@test QQ(β + α) == QQ(β) + Q(α)
    end

    @testset "Interplay with conversions" begin
        import PolynomialRings: iscanonical, canonicaltype

        Q = @ring ℤ[a]/(a^2 - 2)
        R = @ring ℤ[b]/(b^2 - 3)
        S = @ring ℤ[b]/(b^2 - 5)
        @test iscanonical(@ring Q[c,d])
        @test canonicaltype(@ring Q[c][d]) == @ring Q[c,d]
        @test promote_type(Q, @ring ℤ[a]) == Q
        @test promote_type(Q, @ring ℤ[a,b]) == @ring Q[b]
        @test promote_type(Q, @ring ℤ[c]) == @ring Q[c]
        @test promote_type(@ring(Q[c]), @ring(ℤ[a])) == @ring Q[c]
        @test promote_type(@ring(Q[c]), @ring(ℤ[a,d])) == @ring Q[c,d]
        #@test promote_type(@ring(Q[b]), @ring(R[a])) == (Q⊗R)
        #@test promote_type(Q[b,c], @ring R[a,d]) == @ring (Q⊗R)[c,d]
        @test_throws ArgumentError promote_type(@ring(R[b]), @ring(S[a]))

        T = @ring! ℤ[a]/(a^2 - 2)
        @test (im*a)^2 == -2
        @test a * (a*im) == 2*im

        @ring! T[y][z]
        @test (a*z)^2 == 2z^2
    end

    @testset "Bound names" begin
        import PolynomialRings: boundnames, nestednamingscheme

        @test boundnames(@ring ℤ[x][y]/(x^2 - y^3)) == nestednamingscheme(@ring ℤ[x][y])
    end
end
