using Documenter, PolynomialRings

makedocs(
    modules  = [PolynomialRings],
    repo     = "https://github.com/tkluck/PolynomialRings.jl.git",
    doctest  = false,
    format   = :html,
    sitename = "PolynomialRings.jl",
    authors  = "Timo Kluck",
    pages    = [
        "Home"                => "index.md",
        "Getting Started"     => "getting-started.md",
        "Design Goals"        => "design-goals.md",
        "Other packages"      => "other-packages.md",
        "Types and Functions" => "functions.md",
        "Reference Index"     => "reference.md",
    ],
)
deploydocs(
    repo   = "github.com/tkluck/PolynomialRings.jl.git",
    osname = "linux",
    target = "build",
    deps   = nothing,
    make   = nothing,
)
