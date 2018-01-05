using Documenter, PolynomialRings

makedocs(
    modules = [PolynomialRings],
    repo = "https://github.com/tkluck/PolynomialRings.jl.git",
    doctest = true,
    format = :html,
    sitename = "PolynomialRings.jl",
    authors = "Timo Kluck",
    pages = [
        "Home" => "index.md"
        "Getting Started" => "getting-started.md"
        "Reference Index" => "reference.md"
        "Types and Functions" => "functions.md"
    ],
)
