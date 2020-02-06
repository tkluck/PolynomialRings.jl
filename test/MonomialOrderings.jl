using Test

import Base.Order: lt

import PolynomialRings.MonomialOrderings: @degrevlex, @deglex, @lex
import PolynomialRings.MonomialOrderings: MonomialOrder
import PolynomialRings: @ring!

@testset "MonomialOrderings" begin
    @testset "Constructors" begin
        @test @degrevlex(x) isa MonomialOrder
        @test @degrevlex(x > y) isa MonomialOrder
        @test @degrevlex(x > y > z) isa MonomialOrder
        @test @deglex(x > y > z) isa MonomialOrder
        @test @lex(x > y > z) isa MonomialOrder
        #@test @lex(x > @degrevlex(y > z) > w) isa MonomialOrder
    end

    @testset "Comparisons" begin
        @ring! Int[x, y, z, w]

        O1 = @degrevlex(x > y > z)
        @test lt(O1, z, y)
        @test lt(O1, y, x)
        @test lt(O1, y^2, x^3)
        @test lt(O1, x*z, y^2)
        @test sort([x,y,z,y^2,x^3,x*z], order=O1) == [z,y,x,y^2,x*z,x^3]
        @test minimum(O1, [x,y,z,y^2,x^3,x*z]) == z
        @test maximum(O1, [x,y,z,y^2,x^3,x*z]) == x^3
        @test degreecompatible(O1)

        O2 = @deglex(x > y > z)
        @test lt(O2, z, y)
        @test lt(O2, y, x)
        @test lt(O2, y^2, x^3)
        @test lt(O2, y^2, x*z)
        @test sort([x,y,z,y^2,x^3,x*z], order=O2) == [z,y,x,x*z,y^2,x^3]
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

        #=
        O4 = @lex(x > @degrevlex(y > z) > w)
        @test lt(O4, w, z)
        @test lt(O4, z, y)
        @test lt(O4, y, x)
        @test lt(O4, y^5, x*y)
        @test lt(O4, z^5, y*z)
        @test !degreecompatible(O4)
        =#
    end
end
