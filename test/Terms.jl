using Test

using PolynomialRings.Monomials: @monomial
using PolynomialRings.Polynomials: TermOver, Polynomial
using PolynomialRings.Terms: Term

@testset "Terms" begin
    @testset "Construction" begin
        @test Term(@monomial(x*y), 3) == 3 * @monomial(x*y)
        @test Term(@monomial(x[1]), 3) == 3 * @monomial(x[1])
        @test_throws MethodError Term(1, 1)

        (m, c) = Term(@monomial(x*y), 3)
        @test (m, c) == (@monomial(x*y), 3)
        @test_throws BoundsError (m, c, toolong) = Term(@monomial(x), 3)

        #= TODO
        @test Term(@monomial(x), @monomial(y)) isa TermOver{<:Polynomial}
        =#
    end

    @testset "Arithmetic" begin
        @test Term(@monomial(x), 3) * Term(@monomial(y), 4) == Term(@monomial(x*y), 12)
    end
end
