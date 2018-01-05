# Relation to other packages

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

In doing so, this is a nice exercise for Julia's type system. In practice, this
seems to add non-negligibly to compilation times, but not to run times.

## Relation to `Singular.jl`

Eventually, we hope to be an easy-to-deploy alternative to `Singular.jl`.

A pure Julia library will likely never match the brute computing power that
Singular brings to the table. However, a pure Julia implementation, thanks to
parametrized types, may apply the same algorithm with more ease for different
data types for exponents, base rings, etc, without needing a compilation step
from the user.

 In addition, Julia's high-level constructs may allow the user to make certain
 routine optimizations with more ease. As a speculative example, consider
 the following. In Julia, an invocation such as

```julia
@coefficient(f*g, x^10*y^10)
```

could conceivably notice that the first argument is a product. It could then
only compute the requested coefficient of the product, skipping the computation
whose result will be discarded.
