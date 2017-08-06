function ⊗ end
function to_dense_monomials end
function max_variable_index end

# -----------------------------------------------------------------------------
#
# Type information
#
# -----------------------------------------------------------------------------
function generators end
function basering end
function monomialtype end
function monomialorder end
function termtype end
function exptype end

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
