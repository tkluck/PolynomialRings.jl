# Getting Started With `PolynomialRings.jl`

## Installation

Refer to [the Julia website](https://julialang.org/downloads/) for details on
installing Julia. As soon as you have, start it and run
```julia-repl
julia> Pkg.add("PolynomialRings")
```

to install `PolynomialRings` and its dependencies. To test whether it worked,
type

```@repl getting-started
using PolynomialRings
@ring! Int[x,y]
(x + y) * (x - y)
```

If you see the same, you are all set!

## Overview

### Defining polynomial rings
The easiest way to define your polynomial rings is using the `@ring!` macro:

```@repl getting-started
R = @ring! Int[x,y]
```

This will create a type `R` for your polynomials, and it will assign the polynomial
`x` to the variable `x` and similarly for `y`.

For a mathematically more pleasing look, try

```@repl getting-started
R = @ring! ℤ[x,y]
```

For entering ℤ, type `\BbbZ<tab>` in the Julia command line.
([Juno](http://junolab.org/) and
[`julia-vim`](https://github.com/JuliaEditorSupport/julia-vim) support this as
well.) We support ℤ (arbitrary precision integers), ℚ (fractions of
arbitrary precision integers), ℝ (arbitrary precision floating point) and ℂ
(`a + im*b` with both coefficients in ℝ).

If your variables have numbers instead of distinct names, you can use `[]` to represent that:

```@repl getting-started
R = @ring! ℤ[c[]]
```

This will make available the object `c`, which you can use as follows:

```@repl getting-started
c1,c2,c3 = c[1], c[2], c[3]; c1,c2,c3  # or
c1,c2,c3 = c[1:3]; c1,c2,c3            # or
c1,c2,c3 = c[]; c1,c2,c3               # or
# note that the following keeps state:
c1 = c(); c2 = c(); c3 = c(); c1,c2,c3
c4 = c(); c5 = c(); c6 = c(); c4,c5,c6
```

Note that you cannot combine named and numbered variables in one ring definition.
However, you can let one kind of ring be the base ring for another:

```@repl getting-started
R = @ring! ℤ[c[]][x,y]
```

A quick way to define a polynomial without first defining the ring is

```@repl getting-started
# will implicitly create the ring Int[x,y]
@polynomial x^2 - y^2
```

### Arithmetic

The usual ring operations `+`,`-`,`*`,`^` work as you'd expect:

```@repl getting-started
@ring! ℤ[x,y]
(x + y) * (x - y) == x^2 - y^2
```

We also support reduction operations between polynomials; for that, you can use
the standard julia functions `div`, `rem` and `divrem`. For doing a single
reduction step, use `divrem(f, g)`. If you want to do a full reduction until no
further reductions are possible, use `divrem(f, [g])`. Using the latter semantics,
you can also reduce until no reductions are possible with a set of polynomials,
e.g. `divrem(f, [g1,g2])`.

For example, in the one-variable case, this is just the Euclidean algorithm:

```@repl getting-started
rem(x^2 - 1, [x - 1])
```

Don't forget to pass the second parameter as an array if you want to do as many
reduction operations as possible! For example,

```@repl getting-started
rem(x^2 - 1, x - 1)
```

only did the first reduction step `x^2 - 1 - x*(x-1)`.

### Variables in your ring vs. variables in your script

It is common to use names such as `f`,`g`,`h` for polynomials and names
such as $x,y,z$ for the variables in your ring. For example, you might
define
```@repl getting-started
R = @ring! ℤ[x,y,z]
f = x^2 - x*y
```
In this situation, `f` is a variable in your script, of type `R`.

You might also define
```@repl getting-started
g(x,y) = x^2 - x*y
```
but this means something different.  In this case, `x` and `y` are arguments
to the function, and in its body, they take whatever value you pass to `g`. For
example:

```@repl getting-started
g(x,y)
g(y,x)
g(y,y)
```
Maybe by now you wonder about `x` and `y`: are they Julia variables or just names?
The answer is easiest to understand if we look at the `@ring` macro. Note that
this one does not have the `!` in the end:

```@repl no-variable-injection
using PolynomialRings
S = @ring ℤ[x,y]
x
```
As you can see, we did define a type `S` that contains polynomials with names $x$
and $y$ for the variables. However, in our script, the variable `x` doesn't exist.
The way to get the variable with name $x$ is to start with the *symbol* `:x`, and
convert it to `S`. Here's how:
```@repl no-variable-injection
S(:x)
```
The result is an object of type `S`, much like how `f` was an object of type `R`.
It represents a polynomial with just one term: $1x$.

Wouldn't it be practical if we would do `x = S(:x)` and `y = S(:y)` now? That
way, we can use the Julia variable `x` to refer to the polynomial $x$. Indeed,
that's exactly what `@ring!` (with `!`) does!

In the next chapters, we will often pass variables as arguments. For example, we
pass the variable in which we are doing an expansion, or the variable with
respect to which we are taking a derivative. In those cases, we pass the
variable *as a symbol* (e.g. `:x`) to the function. For example, this works:

```@repl getting-started
diff(x^3, :x)
```
But this doesn't:
```@repl getting-started
diff(x^3, x)
```
In some cases, we offer a convenience macro. For example, the `@deg` macro:
```@repl getting-started
deg(x^3*y^4, :x)
deg(x^3*y^4, :y)
@deg x^3*y^4 y
```
### Expansions, coefficients, collecting monomials

The rings `ℤ[a,b][c]`, `ℤ[a,b,c]` and `ℤ[b][a,c]` are canonically isomorphic,
and we make it easy to switch perspective between them. For example, the different
polynomials compare equal (using `==`) and can be easily `convert`ed into each other.
Type promotions also happen as you'd expect.

```@repl getting-started
R = @ring ℤ[a,b][c]
T = @ring! ℤ[a,b,c]
U = @ring ℤ[b][a,c]
R(a*b + b*c + a*c)
T(a*b + b*c + a*c)
U(a*b + b*c + a*c)
```

Keep in mind that they don't have equal `hash()` values, so don't rely on this
for `Set{Any}` and `Dict{Any}`. `Set{R}` and `Dict{R}` should work, since type
conversion will happen before hashing.

For seeing the constituent parts of a polynomial, use the `@expand` macro. You
need to specify in which variables you are expanding. After all, $(a+1)bc = abc + bc$,
so the result from expanding in $a,b$ and $c$ is different from an expansion
in just $b$ and $c$.

```@repl getting-started
@ring! ℤ[a,b,c]
@expand (a*b*c + b*c) a b c
@expand (a*b*c + b*c) b c
```

For just obtaining a single coefficient, use `@coefficient`.

```@repl getting-started
@coefficient (a*b*c + b*c) a^0*b^1*c^1
@coefficient (a*b*c + b*c) b^1*c^1
```

There is also corresponding functions `expansion()` and `coefficient()`. For
those, you need to pass the variables as symbols. For example:

```@repl getting-started
coefficient(a*b*c + b*c, (0, 1, 1), :a, :b, :c)
coefficient(a*b*c + b*c, (1, 1), :b, :c)
```

### Monomial orders

Functions such as `leading_term` and `divrem` have an implicit understanding
of what the monomial order is. By default, if you create a ring, it will be
ordered by degree, then reversely lexicographically. This is often called 'degrevlex'.

If you want to use a different order, you can specify that by creating the ring
using the `polynomial_ring` function:

```@repl getting-started
R,(x,y) = polynomial_ring(:x, :y, monomialorder=:lex)
PolynomialRings.monomialorder(R)
```

Built-in are `:lex`, `:deglex` and `:degrevlex`. It is very easy to define your
own order, though, and thanks to Julia's design, this doesn't incur any performance
penalty. Read the documentation for
[`PolynomialRings.MonomialOrderings.MonomialOrder`](@ref) for details.

### Gröbner basis computations

For computing [a Gröbner basis](https://en.wikipedia.org/wiki/Groebner_basis)
for a set of polynomials, use the [`gröbner_basis`](@ref) function. (For easier
typing, `groebner_basis` is an alias.)

You typically use this to figure out whether a polynomial is contained in the ideal
generated by a set of other polynomials. For example, it is not obvious that $y^2$
is a member of the ideal $(x^5, x^2 + y, xy + y^2)$. Indeed, if one applies `rem`,
you will not find the expression of $y^2$ in terms of these polynomials:

```@repl getting-started
@ring! ℤ[x,y]
I = [x^5, x^2 + y, x*y + y^2]
rem(y^2, I)  # nonzero, even though y^2 ∈ (I)
```

However, if you compute a Gröbner basis first, you will:
```@repl getting-started
G = gröbner_basis(I)
rem(y^2, G) # now, it reduces to zero.
```

If you want to obtain the expression of $y^2$ in these elements, you can first use
`div` to obtain the (row) vector of factors expressing $y^2$ in G:
```@repl getting-started
div(y^2, G)
```
The [`gröbner_transformation`](@ref) function gives a matrix `tr` expressing `G` in
terms of `I`:
```@repl getting-started
G, tr = gröbner_transformation(I); tr
div(y^2, G) * tr * I   # gives back y^2
```

In other words, by looking at
```@repl getting-started
div(y^2, G) * tr
```
we see that
$y^2 = 1(x^5) + (y + xy - x^3)(x^2 + y) + -x(xy + y^2)$
which proves that $y^2 \in (I)$.

### Using helper variables

(Be sure you understand [Variables in your ring vs. variables in your script](@ref)
before reading this section.)

We now get to an important implementation detail. Imagine that you want to write
a function that computes a derivative in the following way:

```@repl getting-started
function myderivative(f::RR, varsymbol) where RR <: Polynomial
    varvalue = RR(varsymbol)
    @ring! Int[ε]
    return @coefficient f(; varsymbol => varvalue + ε) ε^1
end
myderivative(x^3 + x^2, :x)
```
(In fact, [`diff`](@ref) is already built-in and has a more efficient implementation,
but this example is for educational purposes.)

This works, but what about the following?

```@repl getting-started
@ring! ℚ[ε]
myderivative(ε^3 + ε^2, :ε)
```
This gives a wrong answer because of the naming clash inside `myderivative`. You
may be tempted to work around this as follows:

```@repl getting-started
function myderivative2(f::RR, varsymbol) where RR <: Polynomial
    varvalue = RR(varsymbol)
    ε = gensym()
    _,(ε_val,) = polynomial_ring(ε)
    return coefficient(f(;varsymbol => varvalue + ε_val), (1,), ε)
end
myderivative2(ε^3 + ε^2, :ε)
```
which gives the correct answer. Unfortunately, this is *very* inefficient:
```@repl getting-started
@time myderivative2(ε^3 + ε^2, :ε);
@time myderivative2(ε^3 + ε^2, :ε);
```
The reason is that variable names are part of the type definition, and Julia
specializes functions based on the type of its arguments. In this case, that
means that for evaluating the `@coefficient` call, and for the substitution
call, all the code needs to be compiled *every time you call `myderivative`*.

For this reason, we provide a function `formal_coefficient(R)` which yields
a variable that's guaranteed not to clash with the ring that you pass as an
argument:

```@repl getting-started
function myderivative3(f::RR, varsymbol) where RR <: Polynomial
    varvalue = RR(varsymbol)
    ε_sym, ε_val = formal_coefficient(typeof(f))
    return coefficient(f(;varsymbol => varvalue + ε_val), (1,), ε_sym)
end
@time myderivative3(ε^3 + ε^2, :ε);   # first time is still slow (compiling)
@time myderivative3(ε^3 + ε^2, :ε);   # but much faster the second time
@time myderivative3(ε^3 + ε^2, :ε);   # and the third
```

### Free modules (arrays of polynomials)

For practical purposes, a *free module* (of finite rank) over a ring $R$ is just
an array of polynomials in $R$. Many algorithms that work for polynomial rings
also work for modules. For example, the function `gröbner_basis` works just as
well if we pass a vector of vectors of polynomials instead of a vector of
polynomials:
```@repl getting-started
G = [[x^5-y,x^4],[x^3+y,y^3]];
GG = gröbner_basis(G)
```
One can then use the functions `rem` and `div` to express a given vector as an
$R$-linear combination of the others.

For these purposes, the leading term of a vector is defined to be the tuple $(i,t)$
where $i$ is the first nonzero index, and $t$ is the leading term of that nonzero
element.

### Base rings and base restriction / extension

Some operations need a field for a base ring. For example:
```@repl getting-started
R = @ring! ℤ[x]
rem(2x^2, 3x + 1)
```
gives an error because we have to substract $x^2 + \frac{2}{3}x$, which is
not representable in $R$. We offer a convenience function `base_extend` to
extend to ℚ:
```@repl getting-started
rem(base_extend(2x^2), base_extend(3x + 1))
```

If you want, you can also extend to bigger base rings than the quotient field by
passing that as an extra parameter. For example:
```@repl getting-started
f = base_extend(x^2 + 1, Complex{Rational{Int}})
div(f, [x - im])
```

### Implementation of named and numbered variables

The difference between `@ring Int[x1,x2,x3]` and `@ring Int[x[]]` is not just
the display name of the variables. In terms of implementation, the first version
uses a `Tuple` to represent the exponents, whereas the second version uses a
`SparseVector`. This means that for moderate number of variables, the former
is often more efficient than the latter as tuples can often remain on the stack,
saving allocation and garbage collection overhead. This stops being true when
your exponents are very sparse, when the overhead of dealing with all the zeros
in the tuple is worse than the overhead of garbage collection.

If you want to transform a set of polynomials from the latter representation to
the former, use `to_dense_monomials`. This is sometimes beneficial right before
doing a computationally expensive operation, e.g. a Gröbner basis computation.

## Frequently Asked Questions

Be the first to ask a question! Feel free to [open an issue for it](https://github.com/tkluck/PolynomialRings.jl/issues/new).
