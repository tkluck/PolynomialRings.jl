# PolynomialRings

[![](https://img.shields.io/badge/docs-stable-blue.svg)](https://tkluck.github.io/PolynomialRings.jl/stable)
[![](https://img.shields.io/badge/docs-latest-blue.svg)](https://tkluck.github.io/PolynomialRings.jl/latest)


| **Build Status**                                                | **Test coverage**                                       |
|:---------------------------------------------------------------:|:-------------------------------------------------------:|
| [![][travis-img]][travis-url] [![][appveyor-img]][appveyor-url] | [![Coverage Status][coveralls-img]][coveralls-url]      |

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

[travis-img]: https://travis-ci.org/tkluck/PolynomialRings.jl.svg?branch=master
[travis-url]: https://travis-ci.org/tkluck/PolynomialRings.jl

[appveyor-img]: https://ci.appveyor.com/api/projects/status/4g6ax1ni7ijx3rn4?svg=true
[appveyor-url]: https://ci.appveyor.com/project/tkluck/polynomialrings-jl

[coveralls-img]: https://coveralls.io/repos/github/tkluck/PolynomialRings.jl/badge.svg?branch=master
[coveralls-url]: https://coveralls.io/github/tkluck/PolynomialRings.jl?branch=master
