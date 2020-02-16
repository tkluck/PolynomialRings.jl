using Test
import SparseArrays: sparse, spzeros
using PolynomialRings
import PolynomialRings: expansion

@testset "Broadcasting" begin
    R = @ring! ℤ[x,y]     # basering = BigInt, so does support in-place ops
    S = @ring! Int[z,w]   # basering = Int, so doesn't support in-place ops

    g1 = sum(x^(i%13)*y^(i%127+5) for i=1:100)
    h1 = x*g1;
    t1 = first(expansion(g1))

    g2 = sum(z^(i%13)*w^(i%127+5) for i=1:100)
    h2 = z*g2;
    t2 = first(expansion(g2))

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

        # corner case of HandOptimizedBroadcast
        g1′ = deepcopy(g1)
        @test BigInt(0)*g1 - BigInt(4)*(t1.m*h1) == (g1′ .= BigInt(0).*g1′ .- BigInt(4).*(t1.m.*h1))
        g1′ = deepcopy(g1)
        @test BigInt(4)*g1 - BigInt(0)*(t1.m*h1) == (g1′ .= BigInt(4).*g1′ .- BigInt(0).*(t1.m.*h1))

    end
end
