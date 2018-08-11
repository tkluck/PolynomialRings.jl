module LinAlgUtil

if VERSION < v"0.7-"
    import Base: nullspace
else
    import LinearAlgebra: nullspace, I
end

abstract type AbstractExactNumber <: Number end

const ExactNumber = Union{Rational, AbstractExactNumber}

function echelon(M::Matrix{N}) where N <: ExactNumber
    # augment by an identity matrix
    cols = size(M, 2)
    eye = Matrix{N}(I, cols, cols)
    M_aug = vcat(M, eye)
    i,j = size(M)
    while i > 0 && j > 0
        # find a pivot in the i'th row left of the j'th column (inclusive)
        k = findprev(!iszero, M_aug[i,:], j)
        if VERSION >= v"0.7-" ? k === nothing : k == 0
            # move one row up if there's no pivots (i.e. everything is zero)
            i -= 1
            continue
        elseif k < j
            M_aug[:,[k,j]] = M_aug[:,[j,k]]
        end

        # assert that we found it
        @assert !iszero(M_aug[i,j])

        for k=(j-1):-1:1
            if !iszero(M_aug[i,k])
                M_aug[:,k] = M_aug[i,j]*M_aug[:,k] - M_aug[i,k] * M_aug[:,j]
            end
        end

        @assert all(iszero, M_aug[i, 1:(j-1)])

        # move one row up and one column to the left
        i -= 1
        j -= 1
    end

    return M_aug

end

function colspan(M::AbstractMatrix{N}) where N <: Number
    M_aug = echelon(M)

    nonzero_cols = [ j for j in 1:size(M, 2) if any(m != 0 for m in M_aug[1:size(M,1),j])]

    return M_aug[1:size(M,1), nonzero_cols]
end

function nullspace(M::StridedMatrix{N}) where N <: ExactNumber
    M_aug = echelon(M)

    zero_cols = [ j for j in 1:size(M, 2) if all(m == 0 for m in M_aug[1:size(M,1),j])]

    return M_aug[(size(M,1)+1):end, zero_cols]
end


end
