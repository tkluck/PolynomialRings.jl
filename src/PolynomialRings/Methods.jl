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
function namestype end
function variablesymbols end
function allvariablesymbols end

base_extend(::Type{A}, ::Type{B}) where {A,B} = promote_type(A,B)
base_restrict(::Type{A}, ::Type{B}) where {A,B} = B

fraction_field(::Type{I}) where I <: Integer = Rational{I}
fraction_field(::Type{R}) where R <: Rational = R
fraction_field(::Type{R}) where R <: Real = R
fraction_field(::Type{Complex{N}}) where N <: Number = Complex{fraction_field(N)}

integers(::Type{I}) where I <: Integer = I
integers(::Type{R}) where R <: Rational{I} where I = I

allvariablesymbols(::Type) = Set()

# -----------------------------------------------------------------------------
#
# Polynomial/term/monomial operations
#
# -----------------------------------------------------------------------------
function terms end
function leading_term end
function leading_monomial end
function leading_coefficient end
function leading_row end
function maybe_div end
function lcm_multipliers end
function lcm_degree end
function leaddiv end
function leadrem end
function leaddivrem end

# -----------------------------------------------------------------------------
#
# Gröbner basis operations
#
# -----------------------------------------------------------------------------
function gröbner_basis end
function gröbner_transformation end
function syzygies end
const groebner_basis = gröbner_basis
const groebner_transformation = gröbner_transformation


export generators, ⊗, to_dense_monomials, max_variable_index, base_extend
