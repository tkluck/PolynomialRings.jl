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

    @testset "Types" begin
        @test repr(R) == "(Polynomial over Rational{BigInt} in x and y (degrevlex))"
        @test repr(S) == "(Polynomial over (Polynomial over Rational{BigInt} in q[] (degrevlex)) in x and y (degrevlex))"
        @test repr(T) == "(Polynomial over BigInt in a,b and c (degrevlex))"

        @test repr(termtype(R)) == "(Term over Rational{BigInt} in x and y)"

        # test that this does not throw an error
        @test repr(methods(^)) isa String
    end

    @testset "Polynomials" begin
        @test repr(a) == "1 a"
        @test repr(a+b) == "1 b + 1 a"
        @test repr(2a) == "2 a"
        @test repr(r*a) == "1 r[1] a"
        @test repr(r*a + a) == "1 + 1 r[1] a" # not a very pretty representation (for now)

        e1,e2,e3 = formal_coefficients(R, :e)
        @test repr(e1) == "1//1 e[1]"
        @test repr(e2) == "1//1 e[2]"
        @test repr(e3) == "1//1 e[3]"

    end

end

