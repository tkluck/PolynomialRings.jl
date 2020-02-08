using Test

using LinearAlgebra: I
using SparseArrays: sparse

using PolynomialRings.StandardMonomialOrderings: @degrevlex, @lex, KeyOrder
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

@testset "Expansions" begin

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
        @test lhs == [(z, x*y + x), (z^2, 1)]

        lhs = collect(@expansion(x*y - x, z, x, y))
        @test lhs == [(x,-1), (x*y, 1)]
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
    end

    @testset "KeyOrder" begin
        @ring! Int[x]

        O1 = KeyOrder()
        O2 = @degrevlex(x)
        O3 = @lex(@keyorder() > x)
        O4 = @lex(x > @keyorder())

        @test expansion([2x^2 + x, 3x^3 + 2x^2], O1) == [
            (2, 3x^3 + 2x^2),
            (1, 2x^2 + x),
        ]

        @test expansion([2x^2 + x, 3x^3 + 2x^2], O2) == [
            (x, [1, 0]),
            (x^2, [2, 2]),
            (x^3, [0, 3]),
        ]

        @test expansion([2x^2 + x, 3x^3 + 2x^2], O3) == [
            (2 => x^2, 2),
            (2 => x^3, 3),
            (1 => x, 1),
            (1 => x^2, 2),
        ]

        @test expansion([2x^2 + x, 3x^3 + 2x^2], O4) == [
            (1 => x, 1),
            (2 => x^2, 2),
            (1 => x^2, 2),
            (2 => x^3, 3),
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

end
