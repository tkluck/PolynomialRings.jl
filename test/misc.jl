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

@testset "Conversion method ambiguity" begin
    R = @ring! Int[x]
    @test convert(Int, R(1)) === 1
    @test convert(Rational{Int}, R(1)) === 1//1

    R = @ring! Int[x][y]
    @test convert(@ring(Int[x]), x) isa @ring(Int[x])
    @test convert(@ring(Rational{Int}[x]), x) isa @ring(Rational{Int}[x])
    @test convert(Int, R(2)) === 2
    @test convert(Rational{Int}, R(2)) === 2//1

    R = @ring! Int[a[1:8]][y]
    @test convert(@ring(Int[a[1:8]]), a[7]) isa @ring(Int[a[1:8]])
    @test convert(@ring(Rational{Int}[a[1:8]]), a[7]) isa @ring(Rational{Int}[a[1:8]])
    @test convert(Int, R(2)) === 2
    @test convert(Rational{Int}, R(2)) === 2//1
end
