module Solve

using Nulls

using PolynomialRings: lift

"""
    x = matrix_solve_affine(f, y, dims, Type=eltype(y))

Return the solution `x` to the equation

    ``f(x) = y``

where ``x`` is assumed to be a matrix of size `dims`, and `f` is assumed
to be a linear map over `Type`.

Note: I haven't really considered the proper semantics when type(x) is not
necessarily equal to type(y), and the behaviour of this function may (will)
change when I do.
"""
function matrix_solve_affine(f, y, dims, Type=eltype(y))
    z = sparse(zeros(Type, dims))
    basis = map(1:length(z)) do i
        b = copy(z)
        b[i] = one(Type)
        b
    end
    factors = lift(f.(basis), y)
    isnull(factors) && return null
    sparse_result = sum(prod, zip(factors, basis))
    return collect(sparse_result)
end


end
