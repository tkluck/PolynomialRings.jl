using Test

@testset "PolynomialRings.jl" begin
    include("NamingSchemes.jl")
    include("MonomialOrderings.jl")
    include("Expansions.jl")
    include("TypeUpgrades.jl")

    @testset "Assorted tests" begin
        include("Assorted/runtests.jl")
    end
end
