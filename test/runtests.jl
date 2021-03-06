using Test

@testset "PolynomialRings.jl" begin
    include("Constants.jl")
    include("NamingSchemes.jl")
    include("MonomialOrderings.jl")
    include("Monomials.jl")
    include("Terms.jl")
    include("Expansions.jl")
    include("Generators.jl")
    include("TypeUpgrades.jl")
    include("misc.jl")

    @testset "Assorted tests" begin
        include("Assorted/runtests.jl")
    end
end
