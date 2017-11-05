module VariableNames

# -----------------------------------------------------------------------------
#
# Imports for overloading
#
# -----------------------------------------------------------------------------
import PolynomialRings: variablesymbols, namestype

variablesymbols(a) = variablesymbols(namestype(a))

# -----------------------------------------------------------------------------
#
# Finite enumeration of variable names
#
# -----------------------------------------------------------------------------
abstract type Named{Names} end
variablesymbols(::Type{Named{Names}}) where Names = Names

# -----------------------------------------------------------------------------
#
# Infinite series of variable names
#
# -----------------------------------------------------------------------------
abstract type Numbered{Name} end
variablesymbols(::Type{Numbered{Name}}) where Name = tuple()

flatvariablesymbols(::Type{Numbered{Name}}) where Name = Channel() do ch
    i = 0
    while true
        i += 1
        push!(ch, Symbol("$Name$i"))
    end
end

end
