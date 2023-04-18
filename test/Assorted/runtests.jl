using Test

@testset "PolynomialRings" begin
    include("PolynomialRings.jl")
    include("Display.jl")
    #include("Broadcast.jl")
    #include("Coefficients.jl")
    include("Groebner.jl")
    include("CommutativeAlgebras.jl")
    include("LinearAlgebra.jl")
end
