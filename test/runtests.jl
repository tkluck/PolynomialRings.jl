using Test

@testset "PolynomialRings.jl" begin
    include("NamingSchemes.jl")
    include("MonomialOrderings.jl")

    @testset "Assorted tests" begin
        include("Assorted/runtests.jl")
    end
end
