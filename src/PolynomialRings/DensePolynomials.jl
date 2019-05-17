module DensePolynomials

import ..IndexedMonomials: IndexedMonomial
import ..MonomialIterators: MonomialIter, degrevlex_index
import ..Polynomials: Polynomial, leading_monomial, nztermscount
import PolynomialRings: monomialorder, monomialtype, basering, expansion

function todense(f::Polynomial)
    M = IndexedMonomial{typeof(monomialorder(f)), Int}
    C = basering(f)

    # TODO: need to assert degrevlex
    N = degrevlex_index(leading_monomial(f).e)
    monomials = MonomialIter{M, M}()
    coeffs = zeros(C, N)

    for (m, c) in expansion(f, monomialorder(f))
        coeffs[degrevlex_index(m.e)] = c
    end

    Polynomial(monomials, coeffs)
end

function tosparse(f::Polynomial)
    M = monomialtype(monomialorder(f))
    C = basering(f)

    N = nztermscount(f)
    monomials = Vector{M}(undef, N)
    coeffs = Vector{C}(undef, N)
    n = 0

    for (m, c) in expansion(f, monomialorder(f))
        if !iszero(c)
            n += 1
            monomials[n] = m
            coeffs[n] = c
        end
    end

    Polynomial(monomials, coeffs)
end

end
