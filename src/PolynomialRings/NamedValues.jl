module NamedValues

const nextid = let ID=1; nextid() = ID += 1; end

struct KnownValues{Names, ID} end

const _knownvalues = Dict()

function type_with_named_values(f, T::Type)
    S = T{nextid()}
    _knownvalues[S] = Dict()
    f(S, _knownvalues[S])

    return S
end

@inline knownvalues(T::Type) = deepcopy(_knownvalues[T])
@inline knownvalue(T::Type, name) = _knownvalues[T][name]
@inline knownnames(T::Type) = tuple(keys(_knownvalues[T])...)

end
