using Base.Test
using PolynomialRings: polynomial_ring, expansion

@testset "Coefficients" begin
    S,(z,) = polynomial_ring(Int, :z)
    T,(w,) = polynomial_ring(eye(typeof(z),2), :w)

    @test [z 0; 0 z]*w == w*[z 0; 0 z]
    @test typeof([z 0; 0 z]*w) == typeof(w)
    @test z*[z 0; 0 z]*w == w*[z 0; 0 z]*z
    @test z*[z 0; 0 z]*w == [z^2 0; 0 z^2]*w

    m0 = [z 0; 0 2*z]
    m1 = typeof(z)[0 1; 1 0]
    @test (m0 + m1*w)^2 == m0^2 + (m1*m0 + m0*m1)*w + m1^2*w^2

    @test length(expansion(z*[z 0; 0 z]*w, :w)) == 1
    @test length(expansion(z*[z 0; 0 z]*w + one(w), :w)) == 2
    @test length(expansion(z*[z 0; 0 z]*w + one(w)*w, :w)) == 1
    @test length(expansion(z*[z 0; 0 z]*w - one(w)*w, :w)) == 1

end
