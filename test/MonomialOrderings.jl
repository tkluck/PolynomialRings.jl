using Test

import Base.Order: lt

import PolynomialRings.MonomialOrderings: MonomialOrder, degreecompatible
import PolynomialRings.Monomials: @monomial
import PolynomialRings.NamingSchemes: namingscheme, @namingscheme, EmptyNamingScheme
import PolynomialRings.StandardMonomialOrderings: @degrevlex, @deglex, @lex
import PolynomialRings.StandardMonomialOrderings: KeyOrder, LexCombinationOrder
import PolynomialRings: @ring!

@testset "MonomialOrderings" begin
    @testset "Constructors" begin
        @test @degrevlex(x) isa MonomialOrder
        @test @degrevlex(x > y) isa MonomialOrder
        @test @degrevlex(x > y > z) isa MonomialOrder
        @test @deglex(x > y > z) isa MonomialOrder
        @test @lex(x > y > z) isa MonomialOrder
        @test @lex(x > @degrevlex(y > z) > w) isa MonomialOrder
        @test @lex(@keyorder() > x > y) isa MonomialOrder

        @test namingscheme(@lex(x)) == @namingscheme(x)
        @test namingscheme(@lex(@keyorder() > x)) == @namingscheme(x)
        @test namingscheme(LexCombinationOrder()) == EmptyNamingScheme()
        @test namingscheme(KeyOrder()) == EmptyNamingScheme()
    end

    @testset "Comparisons" begin
        @ring! Int[x, y, z, w]

        O1 = @degrevlex(x > y > z)
        @test lt(O1, z, y)
        @test lt(O1, y, x)
        @test lt(O1, y^2, x^3)
        @test lt(O1, x*z, y^2)
        @test sort([x,y,z,y^2,x^3,x*z], order=O1) == [z,y,x,x*z,y^2,x^3]
        @test minimum(O1, [x,y,z,y^2,x^3,x*z]) == z
        @test maximum(O1, [x,y,z,y^2,x^3,x*z]) == x^3
        @test degreecompatible(O1)

        O2 = @deglex(x > y > z)
        @test lt(O2, z, y)
        @test lt(O2, y, x)
        @test lt(O2, y^2, x^3)
        @test lt(O2, y^2, x*z)
        @test sort([x,y,z,y^2,x^3,x*z], order=O2) == [z,y,x,y^2,x*z,x^3]
        @test minimum(O2, [x,y,z,y^2,x^3,x*z]) == z
        @test maximum(O2, [x,y,z,y^2,x^3,x*z]) == x^3
        @test degreecompatible(O2)

        O3 = @lex(x > y > z)
        @test lt(O3, z, y)
        @test lt(O3, y, x)
        @test lt(O3, y^5, x*y)
        @test lt(O3, z^5, y*z)
        @test sort([x,y,z,x*y,y^5,z^5,y*z], order=O3) == [z,z^5,y,y*z,y^5,x,x*y]
        @test !degreecompatible(O3)

        O4 = @lex(x > @degrevlex(y > z) > w)
        @test lt(O4, w, z)
        @test lt(O4, z, y)
        @test !lt(O4, z^2, y)
        @test lt(O4, y, x)
        @test lt(O4, y^5, x*y)
        @test !lt(O4, z^5, y*z)
        @test !degreecompatible(O4)
    end

    @testset "KeyOrder" begin
        @ring! Int[x, y, z, w]

        @test lt(KeyOrder(), [0, 1], [1, 0])
        @test !lt(KeyOrder(), [1, 0], [0, 1])
        @test !lt(KeyOrder(), [0, 0], [0, 0])

        O5 = @lex(@keyorder() > x > y)
        @test !degreecompatible(O5)
        @test lt(O5, [0, x], [x, 0])
        @test lt(O5, [y, x], [x, 0])
        @test lt(O5, [y^2, x], [x, 0])
        @test !lt(O5, [0, 0], [0, 0])
        @test lt(O5, 4 => x^2, 3 => x)
        @test !lt(O5, 4 => x^2, 4 => x)

        O6 = @lex(@degrevlex(x) > @keyorder())
        @test lt(O6, [x^3, 0], [0, x^4])
        @test !lt(O6, [x^4, 0], [0, x^4])
        @test !lt(O6, [0, 0], [0, 0])
        @test lt(O6, 3 => x, 4 => x^2)
        @test !lt(O6, 3 => x^2, 4 => x)
        @test lt(O6, 4 => x, 3 => x)

        O7 = @lex(@keyorder() > x > @keyorder() > y)
        @test lt(O7, 2 => 2 => x, 1 => 2 => x)
        @test lt(O7, 2 => 1 => y, 2 => 2 => x)
        @test lt(O7, 2 => 1 => y, 2 => 1 => x)
        @test lt(O7, 2 => 2 => y, 2 => 1 => y)
        @test lt(O7, 2 => 2 => y, 2 => 2 => y^2)

        O8 = @lex(@keyorder() > @degrevlex(x > y))
        @test lt(O8, 1 => 2 => y, 1 => 2 => x)
        @test lt(O8, 1 => 1 => y, 1 => 2 => x)

        O9 = @degrevlex(x > y)
        @test lt(O9, 1 => 1 => y, 1 => 1 => x)
        @test lt(O9, 1 => 1 => y, 2 => 2 => x)
    end

    @testset "Display" begin
        @test repr(@degrevlex(x > y)) == "@degrevlex(x > y)"
        @test repr(@deglex(x > y)) == "@deglex(x > y)"
        @test repr(@lex(x > y)) == "@lex(x > y)"
        @test repr(@lex(x > @keyorder() > y)) == "@lex(x > @keyorder() > y)"
        @test repr(KeyOrder()) == "KeyOrder()"
        @test repr(KeyOrder(Base.Order.Forward)) == "KeyOrder(Base.Order.Forward)"

        @test repr(typeof(@degrevlex(x))) == "typeof(@degrevlex(x))"
        @test repr(typeof(@lex(x > @keyorder()))) == "typeof(@lex(x > @keyorder()))"
    end
end
