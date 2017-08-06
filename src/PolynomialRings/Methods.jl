function ⊗ end
function to_dense_monomials end
function max_variable_index end

# -----------------------------------------------------------------------------
#
# Type information
#
# -----------------------------------------------------------------------------
generators(x::Type)    = throw(AssertionError("Not implemented: generators(::Type{$x})"))
basering(x::Type)      = throw(AssertionError("Not implemented: basering(::Type{$x})"))
monomialtype(x::Type)  = throw(AssertionError("Not implemented: monomialtype(::Type{$x})"))
monomialorder(x::Type) = throw(AssertionError("Not implemented: monomialorder(::Type{$x})"))
termtype(x::Type)      = throw(AssertionError("Not implemented: termtype(::Type{$x})"))
exptype(x::Type)       = throw(AssertionError("Not implemented: exptype(::Type{$x})"))

generators(x)    = generators(typeof(x))
basering(x)      = basering(typeof(x))
monomialtype(x)  = monomialtype(typeof(x))
monomialorder(x) = monomialorder(typeof(x))
termtype(x)      = termtype(typeof(x))
exptype(x)       = exptype(typeof(x))

base_extend(::Type{A}, ::Type{B}) where {A,B} = promote_type(A,B)

# -----------------------------------------------------------------------------
#
# Polynomial/term/monomial operations
#
# -----------------------------------------------------------------------------
"""
    deg(f)

Return the total degree of f.

WARNING: currently, `deg` is oblivious to 'nested' polynomial rings. For example:

```jldoctest
julia> R = @ring ℤ[x];
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
function terms end
function leading_term end
function maybe_div end
function lcm_multipliers end
function lcm_degree end

export generators, ⊗, to_dense_monomials, max_variable_index, base_extend
