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
function namingscheme end
function fullnamingscheme end
function boundnames end
function fullboundnames end
function num_variables end
function variablesymbols end
function allvariablesymbols end
function iscanonical end
function canonicaltype end

base_extend(A::Type, B::Type)   = promote_type(A, B)
base_restrict(A::Type, B::Type) = B

fraction_field(I::Type{<:Integer})  = Rational{I}
fraction_field(R::Type{<:Rational}) = R
fraction_field(R::Type{<:Real})     = R
fraction_field(::Type{Complex{N}}) where N <: Number = Complex{fraction_field(N)}

integers(I::Type{<:Integer}) = I
integers(R::Type{<:Rational{I}}) where I = I

# for Galois fields. This needs a more specific definition than <: Number
# but for now I'll leave it like this.
fraction_field(N::Type{<:Number}) = N
integers(N::Type{<:Number}) = N

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
function div! end
function rem! end
function xdiv! end
function xrem! end
function xdiv end
function xrem end
function xdivrem end
function tail end

lcm_multipliers(a, b) = deepcopy(b), deepcopy(a)
function lcm_multipliers(a::Integer, b::Integer)
    N = lcm(a, b)
    N÷a, N÷b
end

# -----------------------------------------------------------------------------
#
# Gröbner basis operations
#
# -----------------------------------------------------------------------------
function gröbner_basis end
function gröbner_transformation end
function lift end
function syzygies end
const groebner_basis = gröbner_basis
const groebner_transformation = gröbner_transformation


export generators, ⊗, to_dense_monomials, max_variable_index, base_extend
