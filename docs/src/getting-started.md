# Getting Started With `PolynomialRings.jl`

## Installation

Refer to [the Julia website][1] for details on installing Julia. As soon as you have,
start it and run

    Pkg.add("https://github.com/tkluck/PolynomialRings.jl.git")

to install `PolynomialRings.jl` and its dependencies. To test whether it worked,
type

    using PolynomialRings
    @ring! ℤ[x,y]
    (x + y) * (x - y)

This should output

    -y^2 + x^2

If so, you are all set!

[1]: https://julialang.org/downloads/

## Overview

### Arithmetic

### Named and numbered variables

### Expansions, coefficients, collecting monomials

### Monomial orders

### Gröbner basis computations

### Using helper variables

### Free modules (arrays of polynomials)

### Base rings and base restriction / extension

## Frequently Asked Questions

### Be the first to ask a question
