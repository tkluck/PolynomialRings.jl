module NamingSchemes

import Base: issubset, *, promote_rule

import ..Util: isstrictlysorted

import PolynomialRings: variablesymbols, namingscheme, fullnamingscheme, num_variables
import PolynomialRings: boundnames, fullboundnames, iscanonical, canonicaltype

variablesymbols(a) = variablesymbols(namingscheme(a))
numberedvariablename(a) = numberedvariablename(namingscheme(a))

abstract type NamingScheme end

const FullNamingScheme = NTuple{N, NamingScheme} where N
const NoNamingScheme   = Tuple{}

(A::Type{<:FullNamingScheme})() = ntuple(i -> fieldtype(A, i)(), fieldcount(A))
*(::Nothing, a::NamingScheme) = (a,)
*(a::NamingScheme, ::Nothing) = (a,)
*(::Nothing, a::FullNamingScheme) = a
*(a::FullNamingScheme, ::Nothing) = b
*(a::NamingScheme, b::NamingScheme) = tuple(a, b)
*(a::NamingScheme, b::FullNamingScheme) = tuple(a, b...)
*(a::FullNamingScheme, b::NamingScheme) = tuple(a..., b)
*(a::FullNamingScheme, b::FullNamingScheme) = tuple(a..., b...)

# -----------------------------------------------------------------------------
#
# Finite enumeration of variable names
#
# -----------------------------------------------------------------------------
struct Named{Names} <: NamingScheme end
variablesymbols(::Named{Names}) where Names = Names
num_variables(named::Named) = length(variablesymbols(named))

# -----------------------------------------------------------------------------
#
# Indexed series of variable names (1-based)
#
# -----------------------------------------------------------------------------
struct Numbered{Name, Max} <: NamingScheme end
variablesymbols(::Numbered{Name}) where Name = tuple()
numberedvariablename(::Numbered{Name}) where Name = Name
num_variables(::Numbered{Name, Max}) where {Name, Max} = Max

isvalid(scheme::Named) = allunique(variablesymbols(scheme))
isvalid(scheme::Numbered) = true


@generated issubset(::Named{Names1}, ::Named{Names2}) where {Names1, Names2} = :($( Names1 ⊆ Names2 && issorted(indexin(collect(Names1), collect(Names2))) ))
issubset(::Named, ::Numbered) = false
issubset(::Numbered, ::Named) = false
issubset(::Numbered{Name1, Max1}, ::Numbered{Name2, Max2}) where {Name1, Name2, Max1, Max2} = Name1 == Name2 && Max1 <= Max2
issubset(::NamingScheme, ::Nothing) = false
issubset(::Nothing, ::NamingScheme) = true
issubset(::Nothing, ::Nothing) = true

issubset(::NamingScheme, ::NoNamingScheme) = false
issubset(::NoNamingScheme, ::NamingScheme) = true
issubset(S::NamingScheme, T::FullNamingScheme) = any(t -> S ⊆ t, T)
issubset(S::FullNamingScheme, T::NamingScheme) = all(s -> s ⊆ T, S)
@generated function issubset(::S, ::T) where {S <: FullNamingScheme, T <: FullNamingScheme}
    indices = map(s -> findfirst(t -> s ⊆ t, T()), S())
    res = all(!isequal(nothing), indices) && issorted(indices)
    return :($res)
end
@generated isdisjoint(::Named{Names1}, ::Named{Names2}) where {Names1, Names2} = :($( isempty(Names1 ∩ Names2) ))
isdisjoint(::Named, ::Numbered) = true
isdisjoint(::Numbered, ::Named) = true
isdisjoint(::Numbered{Name1}, ::Numbered{Name2}) where {Name1, Name2} = Name1 != Name2
isdisjoint(::NamingScheme, ::Nothing) = true
isdisjoint(::Nothing, ::NamingScheme) = true
isdisjoint(::Nothing, ::Nothing) = true

isdisjoint(::NamingScheme, ::NoNamingScheme) = true
isdisjoint(::NoNamingScheme, ::NamingScheme) = true

@generated function isdisjoint(::S, ::T) where {S <: NamingScheme, T <: FullNamingScheme}
    return :($( all(t -> isdisjoint(S(), t), T()) ))
end

@generated function isdisjoint(::S, ::T) where {S <: FullNamingScheme, T <: Union{FullNamingScheme, NamingScheme}}
    return :($( all(s -> isdisjoint(s, T()), S()) ))
end

@generated function remove_variables(::N, ::Vars) where N <: Named where Vars <: Named
    remaining = setdiff(variablesymbols(N()), variablesymbols(Vars()))
    isempty(remaining) && return :( nothing )
    :($( Named{tuple(remaining...)}() ))
end

remove_variables(N::Named, ::Numbered) = N
remove_variables(N::Numbered, ::Named) = N
remove_variables(N1::Numbered{Name}, N2::Numbered{Name}) where Name = (@assert num_variables(N2) >= num_variables(N1); return nothing)
remove_variables(N::Numbered, ::Numbered) = N

function remove_variables(N::Named, vars::FullNamingScheme)
    for v in vars
        N = remove_variables(N, v)
    end
    return N
end

function remove_variables(N::Numbered, vars::FullNamingScheme)
    for v in vars
        N = remove_variables(N, v)
    end
    return N
end

namingscheme(::Type) = nothing
fullnamingscheme(::Type) = NoNamingScheme()
boundnames(::Type) = nothing
fullboundnames(T::Type) = boundnames(T) == nothing ? NoNamingScheme() : (boundnames(T),)

≺(N1::Numbered, N2::Numbered) = numberedvariablename(N1) < numberedvariablename(N2)
≺(N1::Numbered, N2::Named) = true
≺(N1::Named, N2::NamingScheme) = false
≺(N1::Nothing, N2::NamingScheme) = true

iscanonical(N::Numbered) = true
iscanonical(N::Named) = issorted(variablesymbols(N))
iscanonical(a::FullNamingScheme) = isstrictlysorted(a, lt=≺) && all(iscanonical, a)
canonicalscheme(N::Numbered) = N
canonicalscheme(N::Named) = Named{tuple(sort(collect(variablesymbols(N)))...)}()
canonicalscheme(a::FullNamingScheme) = tuple(sort(map(canonicalscheme, a), lt=≺)...)

@generated function promote_rule(::Type{N1}, ::Type{N2}) where {N1 <: Named, N2 <: Named}
    symbols = sort(variablesymbols(N1()) ∪ variablesymbols(N2()))
    Names = tuple(symbols...)
    return :($( Named{Names} ))
end

@generated function promote_rule(::Type{N1}, ::Type{N2}) where {N1 <: Numbered{Name}, N2 <: Numbered{Name}} where Name
    max = max(num_variables(N1), num_variables(N2))
    return :($( Numbered{Name, max} ))
end

function parse_namingscheme(expr)
    if expr.head == :tuple
        if all(arg -> arg isa Symbol, expr.args)
            return Named{tuple(expr.args...)}()
        end
    elseif expr.head == :ref && expr.args[1] isa Symbol
        sym = expr.args[1]
        rangespec = expr.args[2:end]
        if length(rangespec) == 0
            return Numbered{sym, Inf}()
        elseif length(rangespec) == 1 && rangespec[1].head == :call &&
                rangespec[1].args[1] == :(:) && rangespec[1].args[2] == 1
            max = rangespec[1].args[3]
            return Numbered{sym, max}()
        end
    end
    throw("Can't parse namingscheme $expr")
end

macro namingscheme(expr)
    return parse_namingscheme(expr)
end

end
