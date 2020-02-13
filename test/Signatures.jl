using Test

using PolynomialRings
using PolynomialRings.Signatures: Sig

@testset "Signatures" begin
    @testset "Constructors" begin
        @test Sig(1 => 2) == Sig(1, 2)
        @test Sig(1 => 2) isa Sig

        @test Sig(1 => 2 => 3) isa Sig{<:Any, <:Sig}
        @test Pair(Sig(1 => 2 => 3)) isa Pair{<:Any, <:Pair}

        @test repr(Sig(1 => 2 => 3)) == "Sig(1 => (2 => 3))"

        @test begin
            a, b = Sig(1 => 2)
            a == 1 && b == 2
        end

        @test (1 => 2) == Sig(1 => 2)
    end

    @testset "Arithmetic" begin
        @test Sig(1 => @monomial(x)) * @monomial(y) == Sig(1 => @monomial(x*y))
        @test Sig(1 => @monomial(x)) * 3 == Sig(1 => 3@monomial(x))
        # TODO: fix this multiplication...
        #@test Sig(1 => @monomial(x)) * 3@monomial(y) == Sig(1 => 3@monomial(x*y))

        @test Sig(1 => 2 => @monomial(x)) * @monomial(y) == Sig(1 => 2 => @monomial(x*y))

        @test lcm(Sig(1 => @monomial(x)), Sig(2 => @monomial(y))) == nothing
        @test lcm(Sig(2 => @monomial(x)), Sig(2 => @monomial(y))) == Sig(2 => @monomial(x*y))

        @test gcd(Sig(1 => @monomial(x)), Sig(2 => @monomial(y))) == nothing
        @test gcd(Sig(2 => @monomial(x*y^2)), Sig(2 => @monomial(y))) == Sig(2 => @monomial(y))
    end
end
