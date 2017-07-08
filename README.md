# PolynomialRings

[![Build Status](https://travis-ci.org/tkluck/PolynomialRings.jl.svg?branch=master)](https://travis-ci.org/tkluck/PolynomialRings.jl)

[![Coverage Status](https://coveralls.io/repos/tkluck/PolynomialRings.jl/badge.svg?branch=master&service=github)](https://coveralls.io/github/tkluck/PolynomialRings.jl?branch=master)

[![codecov.io](http://codecov.io/github/tkluck/PolynomialRings.jl/coverage.svg?branch=master)](http://codecov.io/github/tkluck/PolynomialRings.jl?branch=master)

A library for arithmetic and algebra with multi-variable polynomials.

## Usage

```julia
using PolynomialRings
R,(x,y) = polynomial_ring(Int, :x, :y)

if (x+y)*(x-y) == x^2 - y^2
    println("Seems to work")
end
```

A few useful functions are `deg`, `red`, `expansion`, `groebner_basis`.

## Relation to `MultiVariatePolynomials.jl`

Julia already has an excellent offering for multi-variate polynomials in the
form of MultiVariatePolynomials.jl. What place does PolynomialRings take?

The most important design difference is that in the latter, we choose to make
variable names (for example `x` and `y`) part of the type specification, as
opposed to part of the data structure.  We feel this is necessary for type
stability. For example, the expression `(x+y)*x` has exponents of type
`Tuple{Int,Int}`, whereas the expression `(x+y)*z` has exponents of type
`Tuple{Int,Int,Int}`. This is true even though *in both cases*, the arguments
to `*` have exponents of type `Tuple{Int,Int}` and `Tuple{Int}` respectively.
This means that the return type can only be inferred if the variable names are
part of the type.

In doing so, this is a nice exercise for Julia's type system. In practise, this
seems to add non-negligibly to compilation times, but not to run times.

## Relation to `Singular.jl`

Eventually, we hope to be an easy-to-deploy alternative to Singular.jl.

## Maturity

Currently, this library should be considered alpha quality.

## Design goals

### First-class support for different expansions of the same object

We hope to make it exceedingly easy to regard, for example, a matrix of
polynomials as a polynomial with matrix coefficients. Or to regard a
polynomial in five variables with coefficients in ℚ as a two-variable
polynomial with coefficients in the ring of three-variable polynomials
over ℚ.

We intend to make this possible by providing 'relative' versions of functions
such as `expansion()`, `leading_term()` and `deg()`.

### User-friendly support for pools of indeterminate variables

It should be easy to generate a vector such as "two instances of the most
general polynomial of degree two":

    [c1*x^2 + c2*x + c3, c4*x^2 + c5*x + c6 ]

We make this possible by supporting polynomial rings with an unbounded
number of variables and a sparse representation of the exponents.

### Speed

For elementary operations, we aim to get within the typical factor 2 for julia-vs-C
when compared to Singular. At this point, this library takes a middle ground between
MultivariatePolynomials and Singular on at least one simple benchmark:

    $ julia <<JULIA
    using PolynomialRings; using MultivariatePolynomials; using Singular
    @polyvar a b c
    R,(d,e,f) = polynomial_ring(Int, :d, :e, :f)
    S,g,h,i = Singular.SingularPolynomialRing(Singular.SingularZZ, ["g","h","i"])
    (a+b+c)^4; (d+e+f)^4; (g+h+i)^4 # compile all julia code
    @time (a+b+c)^200
    @time (d+e+f)^200
    @time (g+h+i)^200
    JULIA
     40.568423 seconds (83.07 M allocations: 5.159 GiB, 6.67% gc time)
      4.803838 seconds (302 allocations: 1.032 GiB, 5.65% gc time)
      0.879622 seconds (13.50 M allocations: 319.072 MiB, 2.00% gc time)

(Note: in this simple benchmark, both PolynomialRings and MultivariatePolynomials
have `Int` coefficients, which severely overflow in this computation.)

### Use elementary Julia types wherever possible

For example, for any function operating on free finitely generated modules, the
module elements should just be represented by `AbstractArray{<:Polynomial}` or
`Dict{K,<:Polynomial}`. Polynomial coefficients can be any `Number`, any
`Array` (for expansions in a module), or any `Matrix` (for a polynomial ring
with matrix coefficients).
