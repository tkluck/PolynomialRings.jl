using Test

using PolynomialRings: @namingscheme, @monomial
using PolynomialRings: monomialtype, termtype, polynomialtype

@testset "exp-style construction" begin
    @test exp(monomialtype(@namingscheme((x,y))), (1, 2)) == @monomial(x*y^2)
    @test exp(termtype(@namingscheme((x,y))), (1, 2)) == 1*@monomial(x*y^2)
    @test exp(polynomialtype(@namingscheme((x,y))), (1, 2)) == 1*@monomial(x*y^2)

    @test exp(monomialtype(@namingscheme(c[])), [1,0,3]) == @monomial(c[1]*c[3]^3)
    @test exp(termtype(@namingscheme(c[])), [1,0,3]) == 1*@monomial(c[1]*c[3]^3)
    @test exp(polynomialtype(@namingscheme(c[])), [1,0,3]) == 1*@monomial(c[1]*c[3]^3)
end
