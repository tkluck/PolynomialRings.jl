module VariableNames

import PolynomialRings: variablesymbols, namestype

variablesymbols(a) = variablesymbols(namestype(a))
numberedvariablename(a) = numberedvariablename(namestype(a))

abstract type AbstractVariableNames end

# -----------------------------------------------------------------------------
#
# Finite enumeration of variable names
#
# -----------------------------------------------------------------------------
struct Named{Names} <: AbstractVariableNames end
variablesymbols(::Type{Named{Names}}) where Names = Names

# -----------------------------------------------------------------------------
#
# Infinite series of variable names
#
# -----------------------------------------------------------------------------
struct Numbered{Name} <: AbstractVariableNames end
variablesymbols(::Type{Numbered{Name}}) where Name = tuple()
numberedvariablename(::Type{Numbered{Name}}) where Name = Name

flatvariablesymbols(::Type{Numbered{Name}}) where Name = Channel() do ch
    i = 0
    while true
        i += 1
        push!(ch, Symbol("$Name$i"))
    end
end

end
