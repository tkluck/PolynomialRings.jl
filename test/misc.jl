using Test

using PolynomialRings: @namingscheme, @monomial, @ring!, @ring
using PolynomialRings: monomialtype, termtype, polynomialtype, namingscheme
using PolynomialRings.NamedPromotions: canonicaltype

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

@testset "to_dense_monomials inferrability" begin
    R = @ring! Int[c[]]

    @test namingscheme(eltype(to_dense_monomials(@namingscheme(c[]), [c[1], c[2]]))) == @namingscheme(c[1:2])
    @test namingscheme(eltype(to_dense_monomials(@namingscheme(c[]), [0, c[2]]))) == @namingscheme(c[1:2])
end

@testset "canonical types" begin
    R = @ring! Int[a[1:2]]
    S = @ring! Int[a[1:5]]
    T = @ring! Int[a[]]
    U = @ring! Int[x,y]
    @test canonicaltype(R) == R
    @test canonicaltype(S) == S
    @test canonicaltype(T) == T
    @test canonicaltype(U) == U

    @test promote_type(R, U) == @ring! Int[a[1:2]][x,y]
    @test promote_type(S, U) == @ring! Int[a[1:5]][x,y]
    @test promote_type(T, U) == @ring! Int[a[]][x,y]

    @test promote_type(R, S) == S
    @test promote_type(R, S, T) == T
    @test promote_type(S, T) == T

    @test promote_type(R, S, T, U) == @ring! Int[a[]][x,y]
end

@testset "Arithmetic" begin
    R = @ring! Int[x]
    a = x^2 + x

    @test x == +x == -(-x) == *(x)
    @test a == +a == -(-a) == *(a)
end
