using Test

include("NamingSchemes.jl")
include("MonomialOrderings.jl")

@testset "Assorted tests" begin
    include("Assorted/runtests.jl")
end
