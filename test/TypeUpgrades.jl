using Test

using PolynomialRings.Monomials: @monomial
using PolynomialRings.NamingSchemes: @namingscheme
using PolynomialRings.StandardMonomialOrderings: @degrevlex, @deglex
using PolynomialRings: namingscheme, monomialorder, monomialtype, termtype, polynomialtype, @ring

@testset "Type upgrades" begin
    N1 = namingscheme(:x, :y)
    @test @inferred(monomialorder(N1)) == @degrevlex(x > y)
    @test @inferred(monomialtype(N1)) == typeof(@monomial(x*y))
    @test @inferred(termtype(N1)) == termtype(@ring(Int[x,y]))
    @test @inferred(termtype(N1, Float64)) == termtype(@ring(Float64[x,y]))
    @test @inferred(polynomialtype(N1)) == @ring(Int[x,y])
    @test @inferred(polynomialtype(N1, Float64)) == @ring(Float64[x,y])

    N2 = namingscheme(:c, Inf)
    #@test @inferred(monomialorder(N2)) == @degrevlex(c[])
    @test @inferred(monomialtype(N2)) == typeof(@monomial(c[1]))
    @test @inferred(termtype(N2)) == termtype(@ring(Int[c[]]))
    @test @inferred(termtype(N2, Float64)) == termtype(@ring(Float64[c[]]))
    @test @inferred(polynomialtype(N2)) == @ring(Int[c[]])
    @test @inferred(polynomialtype(N2, Float64)) == @ring(Float64[c[]])
end
