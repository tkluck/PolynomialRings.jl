using Base.Test
using PolynomialRings

@testset "Display" begin

    using PolynomialRings
    using PolynomialRings: basering, termtype

    R = @ring ℚ[x,y]
    q, = formal_coefficients(R, :q)
    S = typeof(q)
    T = @ring ℤ[a,b,c]
    r, = formal_coefficients(T, :r)
    U = @ring Int64[ε]

    @testset "Types" begin
        @test repr(R) == "ℚ[x,y]"
        @test repr(S) == "ℚ[q[]][x,y]"
        @test repr(T) == "ℤ[a,b,c]"
        @test repr(U) == "Int64[ε]"

        @test repr(termtype(R)) == "(Term over Rational{BigInt} in x,y)"

        # test that this does not throw an error
        @test repr(methods(^)) isa String
    end

    @testset "Polynomials" begin
        @test repr(a) == "a"
        @test repr(r) == "r[1]"
        @test repr(a+b) == "b + a"
        @test repr(2a) == "2 a"
        @test repr(r*a) == "r[1] a"
        @test repr(r*a + a) == "(1 + r[1]) a"
        @test repr(2r*a + a) == "(1 + 2 r[1]) a"

        e1,e2,e3 = formal_coefficients(R, :e)
        @test repr(e1) == "e[1]"
        @test repr(e2) == "e[2]"
        @test repr(e3) == "e[3]"
        @test repr(2*e3) == "2//1 e[3]"

    end

end

