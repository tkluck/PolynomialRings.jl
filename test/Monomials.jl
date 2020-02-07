using Test

import PolynomialRings.NamingSchemes: @namingscheme
import PolynomialRings.MonomialOrderings: @lex
import PolynomialRings.AbstractMonomials: exponents, exponentsnz
import PolynomialRings.Monomials: @monomial
import PolynomialRings: monomialtype
import PolynomialRings: maybe_div, lcm, gcd, divides, lcm_multipliers, deg

@testset "Monomials" begin
    @testset "Constructors" begin
        @test @monomial(x*y) == @monomial(y*x)
        @test @monomial(x[1]*x[2]) == @monomial(x[2]*x[1])

        M1 = monomialtype(:x, :y)
        @test exp(M1, (2, 0)) == @monomial(x^2)
        M2 = monomialtype(@namingscheme(c[]))
        @test exp(M2, [0,0,1,0,2]) == @monomial(c[3]*c[5]^2)
        M3 = monomialtype(@lex(x > y))
        @test exp(M3, [1, 2]) == @monomial(x*y^2)
    end

    @testset "Exponents" begin
        @test exponents(@monomial(x*y^2), @namingscheme((x,y))) == (1, 2)
        @test exponents(@monomial(y^2), @namingscheme((x,y))) == (0, 2)
        @test exponents(@monomial(c[2]^2*c[3]), @namingscheme(c[])) == [0, 2, 1]
        @test exponents(@monomial(c[2]^2*c[3]), @namingscheme(c[1:5])) == [0, 2, 1, 0, 0]

        @test collect(exponentsnz(@namingscheme(x[]), @monomial(x[2]*x[4]^2), @monomial(x[3]))) == [
            (2, (1, 0)),
            (3, (0, 1)),
            (4, (2, 0)),
        ]

        @test deg(@monomial(x*y^2), @namingscheme(x)) == 1
        @test deg(@monomial(x*y^2), @namingscheme(y)) == 2
        @test deg(@monomial(x*y^2), @namingscheme((x,y))) == 3
    end

    sometypes = [
        monomialtype(:x, :y),
        monomialtype(@namingscheme(c[])),
        monomialtype(@lex(x > y)),
    ]

    @testset "Arithmetic in $M" for M in sometypes
        x = rand(M, 100)
        y = rand(M, 100)
        @test x .* one(M) == x
        @test one(M) .* y == y

        @test x .^ 2 == x .* x
        @test x .^ 5 == x .* x .* x .* x .* x

        z = x .* y
        @test maybe_div.(z, x) == y

        ab = lcm_multipliers.(x, y)
        @test getindex.(ab, 1) .* x == getindex.(ab, 2) .* y == lcm.(x, y)

        @test maybe_div.(x .* y, gcd.(x, y)) == lcm.(x, y)

        # TODO: more arithmetic
    end

    @testset "Conversions" begin
        M1 = monomialtype(@namingscheme((x,y,z)))
        M2 = monomialtype(@namingscheme((y,z,w)))

        @test convert(M1, @monomial(y)) isa M1
        @test convert(M2, @monomial(y)) isa M2
        @test convert(M1, @monomial(y*z)) == convert(M2, @monomial(y*z))

        @test_throws InexactError convert(M1, @monomial(w))
        @test_throws InexactError convert(M1, convert(M2, @monomial(w)))

        @test convert(M1, @monomial(x)) * convert(M2, @monomial(w)) isa monomialtype(@namingscheme((w,x,y,z)))

        M3 = monomialtype(@namingscheme(c[]))
        M4 = monomialtype(@namingscheme(c[1:20]))

        @test convert(M3, @monomial(c[1])) isa M3
        @test convert(M4, @monomial(c[1])) isa M4
        @test convert(M3, @monomial(c[21])) isa M3
        @test_throws InexactError convert(M4, @monomial(c[21]))

        @test convert(M3, @monomial(c[1]*c[2])) == convert(M4, @monomial(c[1]*c[2]))
        @test convert(M3, @monomial(c[1])) * convert(M4, @monomial(c[1])) isa monomialtype(@namingscheme(c[]))
    end

    @testset "Overflow behaviour" begin
        M1 = monomialtype(@namingscheme(x), Int8)
        @test exp(M1, (64,)) * exp(M1, (64,)) == exp(M1, (typemin(Int8),))

        M2 = monomialtype(@namingscheme(x[]), Int8)
        @test exp(M2, (64,)) * exp(M2, (64,)) == exp(M2, (typemin(Int8),))
    end
end
