if VERSION < v"0.7-"
    using Base.Test
else
    using Test
end

@testset "PolynomialRings" begin
    include("PolynomialRings.jl")
    include("Display.jl")
    #include("Coefficients.jl")
    include("Groebner.jl")
    include("CommutativeAlgebras.jl")
end
