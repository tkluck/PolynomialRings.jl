using Base.Test

@testset "PolynomialRings" begin
    include("PolynomialRings.jl")
    include("Display.jl")
    #include("Coefficients.jl")
    include("Groebner.jl")
    include("CommutativeAlgebras.jl")
end
