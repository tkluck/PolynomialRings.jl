using Test
import SparseArrays: sparse, spzeros
using PolynomialRings

@testset "Broadcasting" begin
    R = @ring! ℤ[x,y]     # basering = BigInt, so does support in-place ops
    S = @ring! Int[z,w]   # basering = Int, so doesn't support in-place ops

    g1 = sum(x^(i%13)*y^(i%127+5) for i=1:100)
    h1 = x*g1;
    t1 = g1.terms[1]

    g2 = sum(z^(i%13)*w^(i%127+5) for i=1:100)
    h2 = z*g2;
    t2 = g2.terms[1]

    @testset "BigInt" begin
        for (g,h,t) = [(g1,h1,t1), (g2,h2,t2)]
            @test g + h == @. g + h
            @test g - h == @. g - h
            @test g * h == @. g * h

            @test 3g + 4h == @. 3g + 4h
            @test 3g - 4h == @. 3g - 4h
            @test 3*(t*g) - 4h == @. 3*(t*g) - 4h

            g′ = deepcopy(g)
            @test g + h == (g′ .+= h)
            g′ = deepcopy(g)
            @test g - h == (g′ .-= h)
            g′ = deepcopy(g)
            @test g * h == (g′ .*= h)

            g′ = deepcopy(g)
            @test 3g + 4h == @. g′ = 3g′ + 4h
            g′ = deepcopy(g)
            @test 3g - 4h == @. g′ = 3g′ - 4h
            g′ = deepcopy(g)
            @test 3*(t*g) - 4h == @. g′ = 3*(t*g′) - 4h
        end
    end
end
