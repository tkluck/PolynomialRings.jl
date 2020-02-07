using Test

import SparseArrays: sparse

import PolynomialRings.NamingSchemes: @namingscheme
import PolynomialRings.MonomialOrderings: @lex
import PolynomialRings.AbstractMonomials: exponents, exponentsnz
import PolynomialRings.Monomials: @monomial
import PolynomialRings: monomialtype
import PolynomialRings: maybe_div, lcm, gcd, divides, lcm_multipliers

@testset "Monomials" begin
    @testset "Constructors" begin
        @test @monomial(x*y) == @monomial(y*x)
        @test @monomial(x[1]*x[2]) == @monomial(x[2]*x[1])

        M1 = monomialtype(:x, :y)
        @test exp(M1, (2, 0)) == @monomial(x^2)
        M2 = monomialtype(@namingscheme(c[]))
        @test exp(M2, sparse([0,0,1,0,2])) == @monomial(c[3]*c[5]^2)
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
end
