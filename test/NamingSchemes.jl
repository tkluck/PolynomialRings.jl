using Test

using PolynomialRings.NamingSchemes: @variable, @namingscheme, @nestednamingscheme
using PolynomialRings.NamingSchemes: iscanonical, canonicalscheme, namingscheme
using PolynomialRings.NamingSchemes: NamingSchemeError
using PolynomialRings: to_dense_monomials

@testset "NamingSchemes" begin
    @testset "Type properties" begin
        @test namingscheme(@namingscheme(x)) == @namingscheme(x)
        @test namingscheme(@namingscheme(x[])) == @namingscheme(x[])

        @test isempty(@namingscheme(()))
        @test !isempty(@namingscheme(x))
        @test !isempty(@namingscheme(x[]))
        @test isempty(@nestednamingscheme())
        @test !isempty(@nestednamingscheme(x,y))
    end

    @testset "Variables" begin
        @test @variable(x) == @variable(x)
        @test @variable(x) != @variable(y)
        @test @variable(x[1]) == @variable(x[1])
        @test @variable(x[1]) != @variable(x[2])
        @test @variable(x[1]) != @variable(x)

        @test indexin(@variable(x), @namingscheme(x)) == 1
        @test indexin(@variable(x), @namingscheme((x,y))) == 1
        @test indexin(@variable(y), @namingscheme((x,y))) == 2
        @test indexin(@variable(z), @namingscheme((x,y))) == nothing
    end

    @testset "Composition" begin
        @test @namingscheme(x) * @namingscheme(y) == @nestednamingscheme(x,y)
        @test @namingscheme(x) * @namingscheme(()) == @nestednamingscheme(x)
        @test @namingscheme(c[]) * @namingscheme(y) == @nestednamingscheme(c[],y)
        @test_throws NamingSchemeError @namingscheme(x) * @namingscheme(x)
        @test_throws NamingSchemeError @namingscheme(x[]) * @namingscheme(x[])
    end

    @testset "Inclusions" begin
        @test @namingscheme(x) ⊆ @namingscheme(x)
        @test @namingscheme(x) ⊆ @namingscheme((x,y))
        @test !(@namingscheme(x) ⊆ @namingscheme(y))
        @test @namingscheme((x,y)) ⊆ @namingscheme((x,y))
        @test !(@namingscheme((y,x)) ⊆ @namingscheme((x,y)))

        @test @namingscheme(x[]) ⊆ @namingscheme(x[])
        @test !(@namingscheme(x[]) ⊆ @namingscheme(y[]))
        @test !(@namingscheme(x[]) ⊆ @namingscheme(x))
        @test !(@namingscheme(x[]) ⊆ @namingscheme(y))

        @test @nestednamingscheme(x) ⊆ @namingscheme(x)
        @test @namingscheme(x) ⊆ @nestednamingscheme(x)
        @test @namingscheme(x) ⊆ @nestednamingscheme(x,c[])
        @test @namingscheme(x) ⊆ @nestednamingscheme(c[],x)
        @test !(@namingscheme(x) ⊆ @nestednamingscheme(c[]))
        @test !(@namingscheme(x) ⊆ @nestednamingscheme(c[],y))

        @test @nestednamingscheme(x,c[]) ⊆ @nestednamingscheme(x,c[])
        @test !(@nestednamingscheme(x,c[]) ⊆ @nestednamingscheme(c[],x))
    end

    @testset "Differences" begin
        @test diff(@namingscheme((x,y)), @namingscheme(y)) == @namingscheme(x)
        @test diff(@namingscheme((x,y)), @namingscheme(y[])) == @namingscheme((x,y))
        @test diff(@namingscheme((x,y)), @namingscheme((x,y))) == @namingscheme(())
        @test diff(@namingscheme(x[]), @namingscheme(x[])) == @namingscheme(())
    end

    @testset "Canonical (nested) naming schemes" begin
        @test iscanonical(@namingscheme(x))
        @test @inferred(canonicalscheme(@namingscheme(x))) == @nestednamingscheme(x)
        @test iscanonical(@namingscheme((x,y)))
        @test @inferred(canonicalscheme(@namingscheme((x,y)))) == @nestednamingscheme((x,y))
        @test iscanonical(@namingscheme(c[]))
        @test @inferred(canonicalscheme(@namingscheme(c[]))) == @nestednamingscheme(c[])
        @test iscanonical(@namingscheme(c[1:20]))
        @test @inferred(canonicalscheme(@namingscheme(c[1:20]))) == @nestednamingscheme(c[1:20])

        @test !iscanonical(@namingscheme((y,x)))
        @test @inferred(canonicalscheme(@namingscheme((y,x)))) == @nestednamingscheme((x,y))

        @test iscanonical(@nestednamingscheme(c[],x))
        @test @inferred(canonicalscheme(@nestednamingscheme(c[],x))) == @nestednamingscheme(c[],x)
        @test iscanonical(@nestednamingscheme(c[1:20],x))
        @test @inferred(canonicalscheme(@nestednamingscheme(c[1:20],x))) == @nestednamingscheme(c[1:20],x)
        @test !iscanonical(@nestednamingscheme(x,c[]))
        @test @inferred(canonicalscheme(@nestednamingscheme(x,c[]))) == @nestednamingscheme(c[],x)
        @test !iscanonical(@nestednamingscheme(x,c[1:20]))
        @test @inferred(canonicalscheme(@nestednamingscheme(x,c[1:20]))) == @nestednamingscheme(c[1:20],x)

        @test iscanonical(@nestednamingscheme(c[1:20],(x,y)))
        @test @inferred(canonicalscheme(@nestednamingscheme(c[1:20],(x,y)))) == @nestednamingscheme(c[1:20],(x,y))
        @test !iscanonical(@nestednamingscheme(c[1:20],x,y))
        @test @inferred(canonicalscheme(@nestednamingscheme(c[1:20],x,y))) == @nestednamingscheme(c[1:20],(x,y))
        @test !iscanonical(@nestednamingscheme(c[1:20],y,x))
        @test @inferred(canonicalscheme(@nestednamingscheme(c[1:20],y,x))) == @nestednamingscheme(c[1:20],(x,y))
    end

    @testset "Operations" begin
        @test to_dense_monomials(@namingscheme(c[]), @namingscheme(x), 20) == @namingscheme(x)
        @test to_dense_monomials(@namingscheme(c[]), @namingscheme(x[]), 20) == @namingscheme(x[])
        @test to_dense_monomials(@namingscheme(c[]), @namingscheme(c[]), 20) == @namingscheme(c[1:20])

        @test to_dense_monomials(@namingscheme(c[]), @nestednamingscheme(x, c[]), 20) == @nestednamingscheme(x, c[1:20])
    end

    @testset "Promotions" begin
        @test promote_type(@namingscheme(x), @namingscheme(x)) == @namingscheme(x)
        @test promote_type(@namingscheme(x), @namingscheme(y)) == @namingscheme((x,y))
        @test promote_type(@namingscheme(c[]), @namingscheme(c[])) == @namingscheme(c[])
        @test promote_type(@namingscheme(c[]), @namingscheme(c[1:20])) == @namingscheme(c[])
        @test promote_type(@namingscheme(c[1:20]), @namingscheme(c[1:20])) == @namingscheme(c[1:20])
        @test promote_type(@namingscheme(x), @namingscheme(x[])) == Any
        @test promote_type(@namingscheme(x), @namingscheme(c[])) == Any
    #=
        @test promote_type(@nestednamingscheme(x), @nestednamingscheme(x)) == @nestednamingscheme(x)
        @test promote_type(@nestednamingscheme(x), @nestednamingscheme(y)) == @nestednamingscheme((x,y))
        @test promote_type(@nestednamingscheme(x), @nestednamingscheme(x[])) == Any
        @test promote_type(@nestednamingscheme(x), @nestednamingscheme(c[])) == @nestednamingscheme(c[],x)

        @test promote_type(@nestednamingscheme(x), @nestednamingscheme((x,y))) == @nestednamingscheme((x,y))
        @test promote_type(@nestednamingscheme(x), @nestednamingscheme((y,x))) == @nestednamingscheme((y,x))
        @test promote_type(@nestednamingscheme(x), @nestednamingscheme(x,y)) == @nestednamingscheme(x,y)
        @test promote_type(@nestednamingscheme(y), @nestednamingscheme(x,y)) == @nestednamingscheme(x,y)

        @test promote_type(@nestednamingscheme((x,y)), @nestednamingscheme((y,x))) == @nestednamingscheme((x,y))
        @test promote_type(@nestednamingscheme(x,y), @nestednamingscheme(y,x)) == @nestednamingscheme((x,y))

        @test promote_type(@nestednamingscheme(c[],x), @nestednamingscheme(x,c[])) == @nestednamingscheme(c[],x)
        @test promote_type(@nestednamingscheme(c[]), @nestednamingscheme(d[],c[])) == @nestednamingscheme(d[],c[])
    =#
    end

    @testset "Display" begin
        @test repr(@variable(x)) == "@variable(x)"
        @test repr(@variable(c[3])) == "@variable(c[3])"

        @test repr(@namingscheme(x)) == "@namingscheme(x)"
        @test repr(@namingscheme(x[])) == "@namingscheme(x[])"
        @test repr(@namingscheme(x[1:20])) == "@namingscheme(x[1:20])"
        @test repr(@namingscheme((x,y))) == "@namingscheme((x,y))"

        @test repr(@nestednamingscheme(x,y)) == "@nestednamingscheme(x,y)"
        @test repr(@nestednamingscheme(x,y[])) == "@nestednamingscheme(x,y[])"
        @test repr(@nestednamingscheme(x,y[1:20])) == "@nestednamingscheme(x,y[1:20])"

        @test repr(typeof(@namingscheme(x))) == "typeof(@namingscheme(x))"
        @test repr(typeof(@nestednamingscheme(x))) == "typeof(@nestednamingscheme(x))"

        # these are technically <: NestedNamingScheme; don't modify the display value
        @test repr(tuple()) == "()"
        @test repr(Tuple{}) == "Tuple{}"
    end
end
