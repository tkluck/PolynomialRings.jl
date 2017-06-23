module MonomialOrderings

import Base: isless
import PolynomialRings.Monomials: AbstractMonomial, total_degree, num_variables

function isless(a::M,b::M,::Type{Val{:degrevlex}}) where M <: AbstractMonomial
    if total_degree(a) == total_degree(b)
        i = num_variables(a)
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

end
