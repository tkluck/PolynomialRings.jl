using Test

using LinearAlgebra: I
using SparseArrays: sparse


using PolynomialRings.Expansions: expansiontype
using PolynomialRings.Monomials: @monomial
using PolynomialRings.NamingSchemes: @namingscheme
using PolynomialRings.Signatures: Sig
using PolynomialRings.StandardMonomialOrderings: @degrevlex, @lex, KeyOrder
using PolynomialRings.Terms: Term
using PolynomialRings: @ring!, @ring, polynomial_ring
using PolynomialRings: @expand, expand
using PolynomialRings: @expansion, expansion
using PolynomialRings: @coefficient, coefficient
using PolynomialRings: @expandcoefficients, expandcoefficients
using PolynomialRings: @linear_coefficients, linear_coefficients
using PolynomialRings: @flat_coefficients, flat_coefficients
using PolynomialRings: @constant_coefficient, constant_coefficient
using PolynomialRings: @expansion_terms, expansion_terms
using PolynomialRings: common_denominator, integral_fraction
using PolynomialRings: monomialtype, termtype, substitute

@testset "Expansions" begin

    @testset "types" begin
        @test @inferred(expansiontype(Float64, @namingscheme(x))) ==
                termtype(@namingscheme(x), Float64)

        R = @ring Int[z,x,y,w]

        @test @inferred(expansiontype(R, @namingscheme(x))) ==
                termtype(@namingscheme(x), @ring(Int[z,y,w]))
        @test @inferred(expansiontype(R, @namingscheme(y))) ==
                termtype(@namingscheme(y), @ring(Int[z,x,w]))
        @test @inferred(expansiontype(R, @namingscheme((y,z)))) ==
                termtype(@namingscheme((y,z)), @ring(Int[x,w]))
        @test @inferred(expansiontype(R, @namingscheme((x,q)))) ==
                termtype(@namingscheme((x,q)), @ring(Int[z,y,w]))

        S = @ring Int[c[]][y,x]
        @test @inferred(expansiontype(S, @namingscheme(x))) ==
                termtype(@namingscheme(x), @ring(Int[c[]][y]))
        @test @inferred(expansiontype(S, @namingscheme((x,y)))) ==
                termtype(@namingscheme((x,y)), @ring(Int[c[]]))
        @test @inferred(expansiontype(S, @namingscheme(c[]))) ==
                termtype(@namingscheme(c[]), @ring(Int[y,x]))

        T = @ring Int[y,x][c[]]
        @test @inferred(expansiontype(T, @namingscheme(x))) ==
                termtype(@namingscheme(x), @ring(Int[y][c[]]))
        @test @inferred(expansiontype(T, @namingscheme((x,y)))) ==
                termtype(@namingscheme((x,y)), @ring(Int[c[]]))
        @test @inferred(expansiontype(T, @namingscheme(c[]))) ==
                termtype(@namingscheme(c[]), @ring(Int[y,x]))

        A = Vector{@ring(Int[x,y])}
        @test @inferred(expansiontype(A, @namingscheme(x))) ==
                termtype(@namingscheme(x), Vector{@ring(Int[y])})
        @test @inferred(expansiontype(A, @lex(@keyorder() > x))) ==
                Sig{Int, termtype(@degrevlex(x), @ring(Int[y]))}
        @test @inferred(expansiontype(A, KeyOrder())) ==
                Sig{Int, @ring(Int[x,y])}

        B = Vector{Vector{@ring(Int[x,y])}}
        @test @inferred(expansiontype(B, @namingscheme(x))) ==
                termtype(@namingscheme(x), Vector{Vector{@ring(Int[y])}})
        @test @inferred(expansiontype(B, @lex(@keyorder() > x))) ==
                Sig{Int, termtype(@degrevlex(x), Vector{@ring(Int[y])})}
        @test @inferred(expansiontype(B, @lex(@keyorder() > x > @keyorder()))) ==
                Sig{Int, Sig{Int, termtype(@degrevlex(x), @ring(Int[y]))}}
    end

    R,(x,y,z) = polynomial_ring(:x, :y, :z, basering=Int64)
    @ring! ℚ[ε]

    @testset "expansion()" begin
        @test collect(expand(zero(z), :z)) == []

        @test collect(expand(x*y*z + x*z + z^2, :z)) == [((1,), x*y + x), ((2,), 1)]
        @test collect(expand(x*y - x, :x, :y, :z)) == [((1,0,0),-1), ((1,1,0), 1)]
        @test collect(expand(x*y - x, :z, :x, :y)) == [((0,1,0),-1), ((0,1,1), 1)]
        @test collect(expand(x*y - x, :z, :x)) == [((0,1), y - 1)]
        @test collect(expand([x*z 1; z+1 x], :z)) == [((0,), [0 1; 1 x]), ((1,), [x 0; 1 0])]
        @test collect(expand(sparse([x*z 1; z+1 x]), :z)) == [((0,), [0 1; 1 x]), ((1,), [x 0; 1 0])]

        @test collect(expansion_terms([x*z 1; z+1 x], :z)) == [[0 1; 1 x], [x*z 0; z 0]]

        @test collect(expandcoefficients(x*y*z + x*z + z^2, :z)) == [x*y + x, 1]
        @test collect(expandcoefficients(x*y - x, :x, :y, :z)) == [-1, 1]
        @test collect(expandcoefficients(x*y - x, :z, :x, :y)) == [-1, 1]
        @test collect(expandcoefficients(x*y - x, :z, :x)) == [y - 1]
        @test collect(expandcoefficients([x*z 1; z+1 x], :z)) == [[0 1; 1 x], [x 0; 1 0]]

        @test collect(flat_coefficients([x*z 1; z+1 x], :z)) == [x, 1, 1, 1, x]

        # work-around for nested macros
        lhs = collect(@expansion(x*y*z + x*z + z^2, z))
        @test lhs == [Term(@monomial(z), @ring(Int[x,y])(x*y + x)), Term(@monomial(z^2), 1)]

        lhs = collect(@expansion(x*y - x, z, x, y))
        @test lhs == [Term(@monomial(x),-1), Term(@monomial(x*y), 1)]
    end

    T = @ring! R[c[]]
    c1,c2,c3 = c[]
    @testset "numbered variables" begin
        @test [1] == @expandcoefficients c1*c2*c3 c[]
        @test [1,-1] == @expandcoefficients c1-c1*c2*c3 c[]

        @test [0,1,-1] == @linear_coefficients c2-c3 c[]
        @test [] == @linear_coefficients c2^2-c3^2 c[]
        @test [] == @linear_coefficients zero(c2) c[]

        @test (c1*c2*c3 + 3*c3)(c = i->i) == 15

        @test (c1+c2+c3)(c=i->2i) == 12
        @test zero(T)(c=i->1) == 0
        @test one(T)(c=i->1) == 1
    end

    @testset "coefficient()" begin
        @test coefficient(x^3 + x^2*y + y, (1,), :y) == x^2 + 1
        @test coefficient(x^3 + x^2*y + y, (0,1), :x, :y) == 1
        @test coefficient(x^3 + x^2*y + y, (1,0), :y, :x) == 1

        @test coefficient(x^3 + x^2*y + y, y, :y) == x^2 + 1
        @test coefficient(x^3 + x^2*y + y, y, :x, :y) == 1

        @test 1 == @coefficient(x^3 + x^2*y + y, x^0 * y)
        @test x^2+1 == @coefficient(x^3 + x^2*y + y, y)

        @test 0 == @coefficient(x^3 + x^2*y + y, y^2)

        @test 1 + y == constant_coefficient(x^3*y + x + y + 1, :x)
        @test 1     == constant_coefficient(x^3*y + x + y + 1, :x, :y)
        @test 1 + y == @constant_coefficient(x^3*y + x + y + 1, x)
        @test 1     == @constant_coefficient(x^3*y + x + y + 1, x, y)

        @test linear_coefficients(x+y+1, :x, :y) == [1,1]
        @test linear_coefficients(x^2+y^2+x-y+1, :x, :y) == [1,-1]
        @test linear_coefficients(x^2+y^2+x-y+1, :y, :x) == [-1,1]
        @test linear_coefficients(x^2+y^2+x-y+1, :y, :z, :x) == [-1,0,1]
        @test @linear_coefficients(x+y+1, x, y) == [1,1]
        @test @linear_coefficients(x^2+y^2+x-y+1, x, y) == [1,-1]
        @test @linear_coefficients(x^2+y^2+x-y+1, y, x) == [-1,1]
        @test @linear_coefficients(x^2+y^2+x-y+1, y, z, x) == [-1,0,1]

        @test [0] == @linear_coefficients(ε^2, ε)

        @test [0,1] == @linear_coefficients(y + y^2, x, y)
        @test eltype(@linear_coefficients(y + y^2, x, y, z)) == Int64
        @test eltype(@linear_coefficients(y + y^2, x, y)) == @ring(Int64[z])
        @test eltype(@linear_coefficients(y + y^2, x)) == @ring(Int64[y,z])
        @test eltype(@linear_coefficients(y + y^2, y)) == @ring(Int64[x,z])

        # TODO: test non-Union{Polynomial, Number} coeficients, e.g. QuotientRing
    end

    @testset "Substitution" begin
        @ring! Int[x,y,z]

        @test @inferred((x^2 + y)(x = 3)) == @inferred(substitute(x^2 + y, x => 3)) == 9 + y
        @test (x^2 + y)(x = 3) isa @ring(Int[y,z])
        @test @inferred((x^2 + y)(x = 3, y = 1)) == @inferred(substitute(x^2 + y, x => 3, y => 1)) == 10
        @test (x^2 + y)(x = 3, y = 1) isa @ring(Int[z])

        @test (x + y)(x = y, y = x) == x + y # non-recursive!
        @test (x + y)() == substitute(x + y) == x + y

        @ring! Int[c[]]

        @test @inferred((c[1]^2 + c[2]^2)(c=i -> i+1)) ==
                @inferred(substitute(c[1]^2 + c[2]^2, c[] => i -> i+1)) == 13
        @test (c[1]^2 + c[2]^2)(c=i -> i+1) isa Int

        @test (c[1] + c[2])() == substitute(c[1] + c[2]) == c[1] + c[2]
    end

    @testset "KeyOrder" begin
        @ring! Int[x]

        O1 = KeyOrder()
        O2 = @degrevlex(x)
        O3 = @lex(@keyorder() > x)
        O4 = @lex(x > @keyorder())

        @test expansion([2x^2 + x, 3x^3 + 2x^2], O1) == [
            2 => 3x^3 + 2x^2,
            1 => 2x^2 + x,
        ]

        @test expansion([2x^2 + x, 3x^3 + 2x^2], O2) == [
            Term(@monomial(x), [1, 0]),
            Term(@monomial(x^2), [2, 2]),
            Term(@monomial(x^3), [0, 3]),
        ]

        @test expansion([2x^2 + x, 3x^3 + 2x^2], O3) == [
            2 => Term(@monomial(x^2), 2),
            2 => Term(@monomial(x^3), 3),
            1 => Term(@monomial(x), 1),
            1 => Term(@monomial(x^2), 2),
        ]

        @test expansion([2x^2 + x, 3x^3 + 2x^2], O4) == [
            1 => Term(@monomial(x), 1),
            2 => Term(@monomial(x^2), 2),
            1 => Term(@monomial(x^2), 2),
            2 => Term(@monomial(x^3), 3),
        ]

        O5 = @lex(@keyorder() > x > @keyorder())
        O6 = @lex(@keyorder() > @keyorder() > x)

        @test expansion([[2x^2 + x, x], [3x^3 + x, 2x^2]], O5) == [
            2 => 1 => Term(@monomial(x), 1),
            2 => 2 => Term(@monomial(x^2), 2),
            2 => 1 => Term(@monomial(x^3), 3),
            1 => 2 => Term(@monomial(x), 1),
            1 => 1 => Term(@monomial(x), 1),
            1 => 1 => Term(@monomial(x^2), 2),
        ]

        @test expansion([[2x^2 + x, x], [3x^3 + x, 2x^2]], O6) == [
            2 => 2 => Term(@monomial(x^2), 2),
            2 => 1 => Term(@monomial(x), 1),
            2 => 1 => Term(@monomial(x^3), 3),
            1 => 2 => Term(@monomial(x), 1),
            1 => 1 => Term(@monomial(x), 1),
            1 => 1 => Term(@monomial(x^2), 2),
        ]

        @ring! Int[x,y]
        O7 = @lex(@keyorder() > @degrevlex(x > y) > @keyorder())
        O8 = @lex(@keyorder() > x > @keyorder() > y)

        @test expansion([[2x^2 + x*y, x], [2x^2 + x, 2x^2*y]], O7) == [
            2 => 1 => Term(@monomial(x), 1),
            2 => 1 => Term(@monomial(x^2), 2),
            2 => 2 => Term(@monomial(x^2*y), 2),
            1 => 2 => Term(@monomial(x), 1),
            1 => 1 => Term(@monomial(x*y), 1),
            1 => 1 => Term(@monomial(x^2), 2),
        ]

        @test expansion([[2x^2 + x*y, x], [2x^2 + x, 2x^2*y]], O8) == [
            2 => 1 => Term(@monomial(x), 1),
            2 => 2 => Term(@monomial(x^2*y), 2),
            2 => 1 => Term(@monomial(x^2), 2),
            1 => 2 => Term(@monomial(x), 1),
            1 => 1 => Term(@monomial(x*y), 1),
            1 => 1 => Term(@monomial(x^2), 2),
        ]

        O9 = @lex(@keyorder() > @degrevlex(x > y))
        O10 = @lex(y > @keyorder() > x)

        @test expansion([[2x^2 + x*y, x], [2x^2 + x, 2x^2*y]], O9) == [
            2 => Term(@monomial(x), [1, 0]),
            2 => Term(@monomial(x^2), [2, 0]),
            2 => Term(@monomial(x^2*y), [0, 2]),
            1 => Term(@monomial(x), [0, 1]),
            1 => Term(@monomial(x*y), [1, 0]),
            1 => Term(@monomial(x^2), [2, 0]),
        ]

        @test expansion([[2x^2 + x*y, x], [2x^2 + x, 2x^2*y]], O10) == [
            2 => Term(@monomial(x), [1, 0]),
            2 => Term(@monomial(x^2), [2, 0]),
            1 => Term(@monomial(x), [0, 1]),
            1 => Term(@monomial(x^2), [2, 0]),
            2 => Term(@monomial(x^2*y), [0, 2]),
            1 => Term(@monomial(x*y), [1, 0]),
        ]
    end

    @testset "Arrays" begin
        R = @ring! ℚ[x,y]
        @test [[0 1], [1 0]] == @expandcoefficients [x y] x y
        @test [1 2] == [x y](x=1,y=2)
        @test [1 1] == @coefficient [x^2+y^2 x^2+1] x^2
        @test [1 1] == @coefficient [x^2+y^2 x^2+1] x^2
        @test [0 1] == @constant_coefficient [x^2+y^2 x^2+1] x y
        @test [y^2 1] == @constant_coefficient [x^2+y^2 x^2+1] x
        @test [[1 0], [0 0]] == @linear_coefficients [x+y^2 x^2+1] x y
        @test [[0 0], [1 0]] == @linear_coefficients [x+y^2 x^2+1] y x
        @test [[0 0]] == @linear_coefficients [ε^2  ε^3] ε

        @test [x 0; 0 x] == sparse([x 0; 0 x])
        @test [x 0; 0 x] * sparse([x 0; 0 x]) == [x^2 0; 0 x^2]
        @test sparse([x 0; 0 x]) * [x 0; 0 x] == [x^2 0; 0 x^2]

        @test eltype(eltype(@linear_coefficients([x+y, -x-y], x, y))) == Rational{BigInt}
        @test eltype(eltype(@linear_coefficients([x+y, -x-y], x))) == @ring(ℚ[y])
        @test eltype(eltype(@linear_coefficients([x+y, -x-y], y))) == @ring(ℚ[x])

        @test common_denominator([(3//5)z^5, 6z + 3//2]) == 10
        @test integral_fraction([(3//5)z^5, 6z + 3//2]) == ([6z^5, 60z + 15], 10)

        @test I*x == [x 0; 0 x] == x*I
    end

    @testset "Generators + polynomials as expansion specs" begin
        @ring! Int[x,y,z]
        X, Y, Z = 1x, 1y, 1z # materialize Generator into Polynomial

        @test collect(expansion(x^2 + y^2, :x)) == collect(expansion(x^2 + y^2, x)) == collect(expansion(x^2 + y^2, X))
        @test diff(x^2 + y^2, :x) == diff(x^2 + y^2, x) == diff(x^2 + y^2, X)

    end

end
