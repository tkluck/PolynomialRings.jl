module MonomialOrderings

import Base: isless
import PolynomialRings.Monomials: AbstractMonomial, VectorMonomial, total_degree, num_variables

function isless(a::M,b::M,::Type{Val{:degrevlex}}) where M <: AbstractMonomial

    if total_degree(a) == total_degree(b)
        i = max(num_variables(a), num_variables(b))
        while i >= 1
            if a[i] != b[i]
                return a[i] > b[i]
            end
            i -= 1
        end
        return false
    else
        return total_degree(a) < total_degree(b)
    end
end

function isless(a::M,b::M,::Type{Val{:deglex}}) where M <: AbstractMonomial

    if total_degree(a) == total_degree(b)
        for i in 1:max(num_variables(a), num_variables(b))
            if a[i] != b[i]
                return a[i] < b[i]
            end
        end
        return false
    else
        return total_degree(a) < total_degree(b)
    end
end

function isless(a::VectorMonomial{V},b::VectorMonomial{V},::Type{Val{:deglex}}) where V <: AbstractSparseVector
    if total_degree(a) == total_degree(b)
        ia = findfirst(a.e)
        ib = findfirst(b.e)
        while (i = min(ia, ib)) > 0
            if a.e[i] != b.e[i]
                return a.e[i] < b.e[i]
            end
            ia = findnext(a.e,i+1)
            ib = findnext(b.e,i+1)
        end
        return ib != 0
    else
        return total_degree(a) < total_degree(b)
    end
end


end
