module NamingSchemes

import Base: issubset, *

import ..Util: isstrictlysorted

import PolynomialRings: variablesymbols, namingscheme, fullnamingscheme
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

issubset(::Named{Names1}, ::Named{Names2}) where {Names1, Names2} = Names1 ⊆ Names2 && issorted(indexin(collect(Names1), collect(Names2)))
issubset(::Named, ::Numbered) = false
issubset(::Numbered, ::Named) = false
issubset(::Numbered{Name1}, ::Numbered{Name2}) where {Name1, Name2} = Name1 == Name2
issubset(::NamingScheme, ::Nothing) = false
issubset(::Nothing, ::NamingScheme) = true
issubset(::Nothing, ::Nothing) = true

issubset(::NamingScheme, ::NoNamingScheme) = false
issubset(::NoNamingScheme, ::NamingScheme) = true
issubset(S::NamingScheme, T::FullNamingScheme) = any(t -> S ⊆ t, T)
issubset(S::FullNamingScheme, T::NamingScheme) = all(s -> s ⊆ T, S)
function issubset(S::FullNamingScheme, T::FullNamingScheme)
    indices = map(s -> findfirst(t -> s ⊆ t, T), S)
    return all(!isequal(nothing), indices) && issorted(indices)
end
isdisjoint(::Named{Names1}, ::Named{Names2}) where {Names1, Names2} = isempty(Names1 ∩ Names2)
isdisjoint(::Named, ::Numbered) = true
isdisjoint(::Numbered, ::Named) = true
isdisjoint(::Numbered{Name1}, ::Numbered{Name2}) where {Name1, Name2} = Name1 != Name2
isdisjoint(::NamingScheme, ::Nothing) = true
isdisjoint(::Nothing, ::NamingScheme) = true
isdisjoint(::Nothing, ::Nothing) = true

isdisjoint(::NamingScheme, ::NoNamingScheme) = true
isdisjoint(::NoNamingScheme, ::NamingScheme) = true
isdisjoint(S::NamingScheme, T::FullNamingScheme) = all(t -> isdisjoint(S, t), T)
isdisjoint(S::FullNamingScheme, T::Union{FullNamingScheme, NamingScheme}) = all(s -> isdisjoint(s, T), S)

function remove_variables(N::Named, vars::Named)
    remaining = setdiff(variablesymbols(N), variablesymbols(vars))
    isempty(remaining) && return nothing
    Named{tuple(remaining...)}()
end

remove_variables(N::Named, ::Numbered) = N
remove_variables(N::Numbered, ::Named) = N

function remove_variables(N::Named, vars::FullNamingScheme)
    for v in vars
        N = remove_variables(N, v)
    end
    return N
end

namingscheme(::Type) = nothing
fullnamingscheme(::Type) = NoNamingScheme()
boundnames(::Type) = nothing
fullboundnames(T::Type) = nothing * boundnames(T)

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

end
