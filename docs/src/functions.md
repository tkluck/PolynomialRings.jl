# Types and Functions

## Entry points

```@docs
@ring!
@ring
@polyvar
@polynomial
polynomial_ring
```

## Arithmetic

```@docs
rem
divrem
PolynomialRings.Expansions.diff
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
coefficients
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
```

### Internal types
```@docs
PolynomialRings.Monomials.AbstractMonomial
PolynomialRings.Monomials.TupleMonomial
PolynomialRings.Monomials.VectorMonomial
PolynomialRings.Terms.Term
PolynomialRings.Polynomials.Polynomial
```
