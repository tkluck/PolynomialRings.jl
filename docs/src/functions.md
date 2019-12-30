# Types and Functions

## Entry points

```@docs
@ring!
@ring
@polyvar
@polynomial
polynomial_ring
formal_coefficients
```

## Arithmetic

```@docs
rem
divrem
PolynomialRings.Expansions.diff
div!
rem!
xrem
xdiv!
xrem!
map_coefficients
```

### Monomial orderings
```@docs
PolynomialRings.MonomialOrderings.MonomialOrder
```

### Expansions, coefficients, collecting monomials

```@docs
@expansion
expansion
@expand
@coefficient
coefficient
@expandcoefficients
expandcoefficients
@deg
deg
@linear_coefficients
linear_coefficients
@constant_coefficient
constant_coefficient
@flat_coefficients
flat_coefficients
```

### Gröbner basis computations

```@docs
gröbner_basis
gröbner_transformation
syzygies
lift
matrix_solve_affine
PolynomialRings.GröbnerGWV.gwv
```

### Internal types and functions
```@docs
PolynomialRings.Monomials.AbstractMonomial
PolynomialRings.Monomials.TupleMonomial
PolynomialRings.Monomials.VectorMonomial
PolynomialRings.Monomials.enumeratenz
PolynomialRings.Terms.Term
PolynomialRings.Polynomials.Polynomial
```
