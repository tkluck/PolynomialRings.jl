module MonomialOrderings

import Base: min, max, minimum, maximum
import Base.Order: Ordering, lt

import PolynomialRings.Monomials: AbstractMonomial, VectorMonomial, total_degree, index_union, rev_index_union

struct MonomialOrder{Name} <: Ordering end

function lt(::MonomialOrder{:degrevlex}, a::M,b::M) where M <: AbstractMonomial

    if total_degree(a) == total_degree(b)
        for i in rev_index_union(a,b)
            if a[i] != b[i]
                return a[i] > b[i]
            end
        end
        return false
    else
        return total_degree(a) < total_degree(b)
    end
end

function lt(::MonomialOrder{:deglex}, a::M,b::M) where M <: AbstractMonomial

    if total_degree(a) == total_degree(b)
        for i in index_union(a,b)
            if a[i] != b[i]
                return a[i] < b[i]
            end
        end
        return false
    else
        return total_degree(a) < total_degree(b)
    end
end

function lt(::MonomialOrder{:lex}, a::M,b::M) where M <: AbstractMonomial
    for i in index_union(a,b)
        if a[i] != b[i]
            return a[i] < b[i]
        end
    end
    return false
end

# This method is mostly for supporting leading monomials of elements of a free
# f.g. module which is a tuple (index, monomial). That's in use in Gröbner,
# and maybe this implementation detail should move there.
function lt(m::MonomialOrder, a::T, b::T) where T <: Tuple
    for i = 1:nfields(T)
        if fieldtype(T,i) <: AbstractMonomial
            if lt(m, a[i], b[i])
                return true
            elseif lt(m, b[i], a[i])
                return false
            end
        else
            if isless(a[i], b[i])
                return true
            elseif isless(b[i], a[i])
                return false
            end
        end
    end
    return false
end

min(m::MonomialOrder, x, y) = lt(m, x, y) ? x : y
max(m::MonomialOrder, x, y) = lt(m, x, y) ? y : x
min(m::MonomialOrder, a, b, c, xs...) = (op(x,y) = min(m,x,y); Base.afoldl(op, op(op(a,b),c), xs...))
max(m::MonomialOrder, a, b, c, xs...) = (op(x,y) = max(m,x,y); Base.afoldl(op, op(op(a,b),c), xs...))
minimum(m::MonomialOrder, iter) = (op(x,y) = min(m,x,y); reduce(op, iter))
maximum(m::MonomialOrder, iter) = (op(x,y) = max(m,x,y); reduce(op, iter))

end
