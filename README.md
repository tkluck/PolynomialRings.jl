# PolynomialRings

[![](https://img.shields.io/badge/docs-stable-blue.svg)](https://tkluck.github.io/PolynomialRings.jl/stable)
[![](https://img.shields.io/badge/docs-latest-blue.svg)](https://tkluck.github.io/PolynomialRings.jl/latest)

[![Build Status](https://travis-ci.org/tkluck/PolynomialRings.jl.svg?branch=master)](https://travis-ci.org/tkluck/PolynomialRings.jl)

[![Coverage Status](https://coveralls.io/repos/tkluck/PolynomialRings.jl/badge.svg?branch=master&service=github)](https://coveralls.io/github/tkluck/PolynomialRings.jl?branch=master)

A library for arithmetic and algebra with multi-variable polynomials.

## Usage

```julia
using PolynomialRings
R = @ring! ℚ[x,y]

if (x+y)*(x-y) == x^2 - y^2
    println("Seems to work")
end
```

A few useful functions are `deg`, `expansion`, `groebner_basis`. Use `divrem`
and friends for doing reduction w.r.t. Gröbner bases.

Want to know more? Have a look [at the getting started guide][1].

[1]: https://tkluck.github.io/PolynomialRings.jl/latest/getting-started.html

## Maturity

Currently, this library should be considered alpha quality.
