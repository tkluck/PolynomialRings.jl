using Base.Test
using PolynomialRings

@testset "Display" begin

    using PolynomialRings
    using PolynomialRings: basering, polynomialtype, termtype


    R,(x,y) = polynomial_ring(Rational{Int64}, :x, :y)
    q, = formal_coefficients(R, :q)
    S = typeof(q)
    T,(a,b,c) = polynomial_ring(BigInt, :a, :b, :c)
    r, = formal_coefficients(T, :r)

    @testset "Types" begin
        @test repr(R) == "(Polynomial over Rational{Int64} in x and y)"
        @test repr(S) == "(Polynomial over (Polynomial over Rational{Int64} in q_i) in x and y)"
        @test repr(T) == "(Polynomial over BigInt in a,b and c)"

        @test repr(polynomialtype(R)) == "(Polynomial over Rational{Int64} in 2 variables (degrevlex))"
        @test repr(polynomialtype(S)) == "(Polynomial over (Polynomial over Rational{Int64} in q_i) in 2 variables (degrevlex))"
        @test repr(polynomialtype(basering(S))) == "(Polynomial over Rational{Int64} in ∞ variables (degrevlex))"
        @test repr(polynomialtype(T)) == "(Polynomial over BigInt in 3 variables (degrevlex))"

        @test repr(termtype(R)) == "(Term over Rational{Int64} in x and y)"
    end

    @testset "Polynomials" begin
        @test repr(a) == "1 a"
        @test repr(a+b) == "1 b + 1 a"
        @test repr(2a) == "2 a"
        @test repr(r*a) == "1 r1 a"
        @test repr(r*a + a) == "1 + 1 r1 a" # not a very pretty representation (for now)
    end

end

