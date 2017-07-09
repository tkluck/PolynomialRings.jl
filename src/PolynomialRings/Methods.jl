generators(x)           = throw(AssertionError("Not implemented: generators(::$(typeof(x)))"))
⊗(x)                    = throw(AssertionError("Not implemented: ⊗(::$(typeof(x)))"))
to_dense_monomials(n,x) = throw(AssertionError("Not implemented: to_dense_monomials(::$(typeof(n)), ::$(typeof(x)))"))
max_variable_index(x)   = throw(AssertionError("Not implemented: max_variable_index(::$(typeof(x)))"))

base_extend(::Type{A}, ::Type{B}) where {A,B} = promote_type(A,B)

export generators, ⊗, to_dense_monomials, max_variable_index, base_extend

# -----------------------------------------------------------------------------
#
# Type information
#
# -----------------------------------------------------------------------------
basering(x::Type)      = throw(AssertionError("Not implemented: basering(::Type{$x})"))
monomialtype(x::Type)  = throw(AssertionError("Not implemented: monomialtype(::Type{$x})"))
monomialorder(x::Type) = throw(AssertionError("Not implemented: monomialorder(::Type{$x})"))
termtype(x::Type)      = throw(AssertionError("Not implemented: termtype(::Type{$x})"))
exptype(x::Type)       = throw(AssertionError("Not implemented: exptype(::Type{$x})"))

basering(x)      = basering(typeof(x))
monomialtype(x)  = monomialtype(typeof(x))
monomialorder(x) = monomialorder(typeof(x))
termtype(x)      = termtype(typeof(x))
exptype(x)       = termtype(typeof(x))

# -----------------------------------------------------------------------------
#
# Polynomial/term/monomial operations
#
# -----------------------------------------------------------------------------
deg(x)               = throw(AssertionError("Not implemented: deg(::$(typeof(x)))"))
terms(x)             = throw(AssertionError("Not implemented: terms(::$(typeof(x)))"))
leading_term(x)      = throw(AssertionError("Not implemented: leading_term(::$(typeof(x)))"))
maybe_div(a,b)       = throw(AssertionError("Not implemented: maybe_div(::$(typeof(a)), ::$(typeof(b)))"))
lcm_multipliers(a,b) = throw(AssertionError("Not implemented: lcm_multipliers(::$(typeof(a)), ::$(typeof(b)))"))

"""
    deg(f)

Return the total degree of f.

WARNING: currently, `deg` is oblivious to 'nested' polynomial rings. For example:

```jldoctest
julia> R, (x,) = polynomial_ring(Int,:x);
julia> c1,c2 = formal_coefficients(R, :c);
julia> deg(x^2)
2
julia> deg(c1*x^2)
2
julia> deg(@coefficient(c1*x^2, x^2))
1
```
"""
function deg end
