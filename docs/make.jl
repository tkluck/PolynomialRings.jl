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
    ],
)
