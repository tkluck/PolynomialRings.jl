using Test

using PolynomialRings

@testset "NamedPromotions" begin
    @testset "Polynomial promotions" begin
        @test @inferred(promote_type(@ring(ℤ[x]), @ring(ℚ[y]))) == @ring(ℚ[x,y])
        @test @inferred(promote_type(@ring(ℤ[a[]][x]), @ring(ℚ[y]))) == @ring(ℚ[a[]][x,y])
        @test @inferred(promote_type(@ring(ℤ[a[]][x]), @ring(ℚ[a[]][y]))) == @ring(ℚ[a[]][x,y])

        @test @inferred(promote_type(@ring(ℤ[y][x]), @ring(ℚ[y]))) == @ring(ℚ[y][x])
        @test @inferred(promote_type(@ring(ℤ[y][x]), @ring(ℚ[x]))) == @ring(ℚ[y][x])
        @test @inferred(promote_type(@ring(ℤ[y][x]), @ring(ℚ[x][y]))) == @ring(ℚ[x,y])

        @test @inferred(promote_type(@ring(ℤ[a][b[]][c][d[]]), @ring(ℚ[a][c]))) == @ring(ℚ[a][b[]][c][d[]])
        @test @inferred(promote_type(@ring(ℤ[a][b[]][c][d[]]), @ring(ℚ[b[]][c]))) == @ring(ℚ[a][b[]][c][d[]])
        @test @inferred(promote_type(@ring(ℤ[a][b[]][c][d[]]), @ring(ℚ[b[]][d[]]))) == @ring(ℚ[a][b[]][c][d[]])

        @test @inferred(promote_type(@ring(ℤ[x][y,z]), @ring(ℚ[x,y][z]))) == @ring(ℚ[x,y,z])
        @test @inferred(promote_type(@ring(ℤ[a,b][c,d]), @ring(ℚ[a,c][b,d]))) == @ring(ℚ[a,b,c,d])

        @test @inferred(promote_type(@ring(ℤ[a][b]), @ring(ℚ[c][b]))) == @ring(ℚ[a,c][b])
    end

    @testset "External type vs. polynomial promotions" begin
        @testset "External type without bound values" begin
            struct Bar; end
            Base.promote_rule(::Type{Int}, ::Type{Bar}) = Bar

            @test @inferred(base_extend(@ring(Int[x]), Bar)) == @ring(Bar[x])
            @test_throws ErrorException base_extend(Bar, @ring(Int[x]))

            @test @inferred(promote_type(Bar, @ring(Int[x,w]))) == @ring(Bar[x,w])
            @test @inferred(promote_type(Bar, @ring(Int[c[]]))) == @ring(Bar[c[]])
            @test @inferred(promote_type(Bar, @ring(Int[c[1:2]]))) == @ring(Bar[c[1:2]])
            @test @inferred(promote_type(Bar, @ring(Int[c[]][x,w]))) == @ring(Bar[c[]][x,w])

            @test @inferred(promote_type(Bar, @ring(Int[w,x,v]))) == @ring(Bar[w,x,v])
            @test @inferred(promote_type(Bar, @ring(Int[w][x][v]))) == @ring(Bar[w][x][v])
        end

        @testset "External type with bound values" begin
            struct Foo; val :: Symbol; end
            PolynomialRings.boundnames(::Type{Foo}) = @nestednamingscheme(c[], (x,y,z))
            PolynomialRings.boundvalues(::Type{Foo}) = (Foo(:c), (Foo(:x), Foo(:y), Foo(:z)))
            Base.promote_rule(::Type{Int}, ::Type{Foo}) = Foo

            @test @inferred(base_extend(@ring(Int[w]), Foo)) == @ring(Foo[w])
            @test @inferred(base_extend(@ring(Int[x]), Foo)) == Foo
            @test_throws ErrorException base_extend(Foo, @ring(Int[w]))
            @test_throws ErrorException base_extend(Foo, @ring(Int[x]))

            @test @inferred(promote_type(Foo, @ring(Int[x]))) == Foo
            @test @inferred(promote_type(Foo, @ring(Int[x,w]))) == @ring(Foo[w])
            @test @inferred(promote_type(Foo, @ring(Int[c[]]))) == Foo
            @test @inferred(promote_type(Foo, @ring(Int[c[1:2]]))) == Foo
            @test @inferred(promote_type(Foo, @ring(Int[c[]][x,w]))) == @ring(Foo[w])

            @test @inferred(promote_type(Foo, @ring(Int[w,x,v]))) == @ring(Foo[w,v])
            @test @inferred(promote_type(Foo, @ring(Int[w][x][v]))) == @ring(Foo[w][v])
        end
    end
end
