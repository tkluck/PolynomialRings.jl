module VariableNames

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import PolynomialRings: variablesymbols, namestype

variablesymbols(a) = variablesymbols(namestype(a))
numberedvariablename(a) = numberedvariablename(namestype(a))

# -----------------------------------------------------------------------------
#
# Finite enumeration of variable names
#
# -----------------------------------------------------------------------------
struct Named{Names} end
variablesymbols(::Type{Named{Names}}) where Names = Names

# -----------------------------------------------------------------------------
#
# Infinite series of variable names
#
# -----------------------------------------------------------------------------
struct Numbered{Name} end
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
