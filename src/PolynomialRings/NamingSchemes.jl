module NamingSchemes

import PolynomialRings: variablesymbols, namingscheme

variablesymbols(a) = variablesymbols(namingscheme(a))
numberedvariablename(a) = numberedvariablename(namingscheme(a))

abstract type NamingScheme end

# -----------------------------------------------------------------------------
#
# Finite enumeration of variable names
#
# -----------------------------------------------------------------------------
struct Named{Names} <: NamingScheme end
variablesymbols(::Named{Names}) where Names = Names

# -----------------------------------------------------------------------------
#
# Infinite series of variable names
#
# -----------------------------------------------------------------------------
struct Numbered{Name} <: NamingScheme end
variablesymbols(::Numbered{Name}) where Name = tuple()
numberedvariablename(::Numbered{Name}) where Name = Name

flatvariablesymbols(::Numbered{Name}) where Name = Channel() do ch
    i = 0
    while true
        i += 1
        push!(ch, Symbol("$Name$i"))
    end
end

end
