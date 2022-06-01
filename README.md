# PolynomialRings

[![](https://img.shields.io/badge/docs-stable-blue.svg)](https://tkluck.github.io/PolynomialRings.jl/stable)
[![](https://img.shields.io/badge/docs-latest-blue.svg)](https://tkluck.github.io/PolynomialRings.jl/latest)


| **Build Status**        | **Test coverage**                              |
|:-----------------------:|:----------------------------------------------:|
| [![][c-i-img]][c-i-url] | [![Coverage Status][codecov-img]][codecov-url] |

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

[c-i-img]: https://github.com/tkluck/PolynomialRings.jl/workflows/CI/badge.svg
[c-i-url]: https://github.com/tkluck/PolynomialRings.jl/actions?query=workflow%3ACI

[codecov-img]: https://codecov.io/gh/tkluck/PolynomialRings.jl/branch/master/graph/badge.svg
[codecov-url]: https://codecov.io/gh/tkluck/PolynomialRings.jl
