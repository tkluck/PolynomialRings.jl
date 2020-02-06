using Test

using PolynomialRings.NamingSchemes: @namingscheme, @nestednamingscheme
using PolynomialRings.NamingSchemes: iscanonical, canonicalscheme
using PolynomialRings.NamingSchemes: NamingSchemeError

@testset "NamingSchemes" begin
    @testset "Composition" begin
        @test @namingscheme(x) * @namingscheme(y) == @nestednamingscheme(x,y)
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

    @testset "Canonical (nested) naming schemes" begin
        @test iscanonical(@namingscheme(x))
        @test canonicalscheme(@namingscheme(x)) == @nestednamingscheme(x)
        @inferred canonicalscheme(@namingscheme(x))
        @test iscanonical(@namingscheme((x,y)))
        @test canonicalscheme(@namingscheme((x,y))) == @nestednamingscheme((x,y))
        @inferred canonicalscheme(@namingscheme((x,y)))
        @test iscanonical(@namingscheme(c[]))
        @test canonicalscheme(@namingscheme(c[])) == @nestednamingscheme(c[])
        @inferred canonicalscheme(@namingscheme(c[]))
        @test iscanonical(@namingscheme(c[1:20]))
        @test canonicalscheme(@namingscheme(c[1:20])) == @nestednamingscheme(c[1:20])
        @inferred canonicalscheme(@namingscheme(c[1:20]))

        @test !iscanonical(@namingscheme((y,x)))
        @test canonicalscheme(@namingscheme((y,x))) == @nestednamingscheme((x,y))
        @inferred canonicalscheme(@namingscheme((y,x)))

        @test iscanonical(@nestednamingscheme(c[],x))
        @test canonicalscheme(@nestednamingscheme(c[],x)) == @nestednamingscheme(c[],x)
        @inferred canonicalscheme(@nestednamingscheme(c[],x))
        @test iscanonical(@nestednamingscheme(c[1:20],x))
        @test canonicalscheme(@nestednamingscheme(c[1:20],x)) == @nestednamingscheme(c[1:20],x)
        @inferred canonicalscheme(@nestednamingscheme(c[1:20],x))
        @test !iscanonical(@nestednamingscheme(x,c[]))
        @test canonicalscheme(@nestednamingscheme(x,c[])) == @nestednamingscheme(c[],x)
        @inferred canonicalscheme(@nestednamingscheme(x,c[]))
        @test !iscanonical(@nestednamingscheme(x,c[1:20]))
        @test canonicalscheme(@nestednamingscheme(x,c[1:20])) == @nestednamingscheme(c[1:20],x)
        @inferred canonicalscheme(@nestednamingscheme(x,c[1:20]))

        @test iscanonical(@nestednamingscheme(c[1:20],(x,y)))
        @test canonicalscheme(@nestednamingscheme(c[1:20],(x,y))) == @nestednamingscheme(c[1:20],(x,y))
        @inferred canonicalscheme(@nestednamingscheme(c[1:20],(x,y)))
        @test !iscanonical(@nestednamingscheme(c[1:20],x,y))
        @test canonicalscheme(@nestednamingscheme(c[1:20],x,y)) == @nestednamingscheme(c[1:20],(x,y))
        @inferred canonicalscheme(@nestednamingscheme(c[1:20],x,y))
        @test !iscanonical(@nestednamingscheme(c[1:20],y,x))
        @test canonicalscheme(@nestednamingscheme(c[1:20],y,x)) == @nestednamingscheme(c[1:20],(x,y))
        @inferred canonicalscheme(@nestednamingscheme(c[1:20],y,x))
    end

    #=
    @testset "Promotions" begin
        @test promote_type(@namingscheme(x), @namingscheme(x)) == @namingscheme(x)
        @test promote_type(@namingscheme(x), @namingscheme(y)) == @namingscheme((x,y))
        @test promote_type(@namingscheme(x), @namingscheme(x[])) == Any
        @test promote_type(@namingscheme(x), @namingscheme(c[])) == Any

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
    end
    =#
end
