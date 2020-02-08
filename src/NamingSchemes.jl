"""
    module PolynomialRings.NamingSchemes

Contains data types and methods for describing the variables appearing in a
polynomial ring. Examples are `PolynomialRings.Named` (for variables named by a
symbol, e.g., `x`) and `PolynomialRings.Numbered` (for variables named by a
symbol together with an integer, e.g., `c[2]`).
"""
module NamingSchemes

import Base: @pure
import Base: issubset, isvalid, *, diff, indexin, promote_rule, promote_type

import ..Util: isdisjoint
import PolynomialRings: boundnames, fullboundnames, iscanonical, canonicaltype
import PolynomialRings: variablesymbols, namingscheme, nestednamingscheme, num_variables

variablesymbols(a) = variablesymbols(namingscheme(a))
numberedvariablename(a) = numberedvariablename(namingscheme(a))

abstract type NamingScheme end

struct NamingSchemeError end

const NestedNamingScheme = NTuple{N, NamingScheme} where N
const NoNamingScheme     = Tuple{}

(A::Type{<:NestedNamingScheme})() = ntuple(i -> fieldtype(A, i)(), fieldcount(A))

function composeschemes(scheme)
    isvalid(scheme) || throw(NamingSchemeError())
    return (scheme,)
end

function composeschemes(scheme, schemes...)
    s = composeschemes(schemes...)
    isdisjoint(scheme, s) || throw(NamingSchemeError())
    return tuple(scheme, s...)
end

*(a::NamingScheme) = a
*(a::NestedNamingScheme) = a
*(::Nothing, a::NamingScheme) = composeschemes(a)
*(a::NamingScheme, ::Nothing) = composeschemes(a)
*(::Nothing, a::NestedNamingScheme) = composeschemes(a...)
*(a::NestedNamingScheme, ::Nothing) = composeschemes(a...)
*(a::NamingScheme, b::NamingScheme) = composeschemes(a, b)
*(a::NamingScheme, b::NestedNamingScheme) = composeschemes(a, b...)
*(a::NestedNamingScheme, b::NamingScheme) = composeschemes(a..., b)
*(a::NestedNamingScheme, b::NestedNamingScheme) = composeschemes(a..., b...)

# -----------------------------------------------------------------------------
#
# Variables
#
# -----------------------------------------------------------------------------
abstract type Variable end

struct NamedVariable{Name}        <: Variable end
struct NumberedVariable{Name, Ix} <: Variable end

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

function namingscheme(names::Symbol...)
    res = Named{names}()
    isvalid(res) || error("Not a valid naming scheme: $names")
    return res
end

function namingscheme(name::Symbol, n::Number)
    n isa Integer || n == Inf || error("Not a valid naming scheme count: $n")
    res = Numbered{name, n}()
    isvalid(res) || error("Not a valid naming scheme: $name, $n")
    return res
end

isvalid(scheme::Named) = allunique(variablesymbols(scheme))
isvalid(scheme::Numbered) = true

function isvalid(scheme::NestedNamingScheme)
    all(isvalid, scheme) || return false
end

@pure indexin(x::Symbol, n::Named{Names}) where Names = findfirst(isequal(x), Names)
indexin(x::Symbol, n::Numbered) = nothing
@pure indexin(x::NamedVariable{Name}, n::Named{Names}) where {Name, Names} = findfirst(isequal(Name), Names)
indexin(x::NumberedVariable{Name, Ix}, n::Numbered{Name}) where {Name, Ix} = Ix
indexin(x::Variable, n::NamingScheme) = nothing

@generated issubset(::Named{Names1}, ::Named{Names2}) where {Names1, Names2} = Names1 ⊆ Names2 && issorted(indexin(collect(Names1), collect(Names2)))
issubset(::Named, ::Numbered) = false
issubset(::Numbered, ::Named) = false
issubset(::Numbered{Name1, Max1}, ::Numbered{Name2, Max2}) where {Name1, Name2, Max1, Max2} = Name1 == Name2 && Max1 <= Max2
issubset(::NamingScheme, ::Nothing) = false
issubset(::Nothing, ::NamingScheme) = true
issubset(::Nothing, ::Nothing) = true

issubset(::NamingScheme, ::NoNamingScheme) = false
issubset(::NoNamingScheme, ::NamingScheme) = true
issubset(S::NamingScheme, T::NestedNamingScheme) = any(t -> S ⊆ t, T)
issubset(S::NestedNamingScheme, T::NamingScheme) = all(s -> s ⊆ T, S)
@generated function issubset(::S, ::T) where {S <: NestedNamingScheme, T <: NestedNamingScheme}
    indices = map(s -> findfirst(t -> s ⊆ t, T()), S())
    return all(!isequal(nothing), indices) && issorted(indices)
end
@generated isdisjoint(::Named{Names1}, ::Named{Names2}) where {Names1, Names2} = isempty(Names1 ∩ Names2)
isdisjoint(::Named, ::Numbered) = true
isdisjoint(::Numbered, ::Named) = true
isdisjoint(::Numbered{Name1}, ::Numbered{Name2}) where {Name1, Name2} = Name1 != Name2
isdisjoint(::NamingScheme, ::Nothing) = true
isdisjoint(::Nothing, ::NamingScheme) = true
isdisjoint(::Nothing, ::NoNamingScheme) = true
isdisjoint(::Nothing, ::Nothing) = true

isdisjoint(::NamingScheme, ::NoNamingScheme) = true
isdisjoint(::NoNamingScheme, ::NamingScheme) = true
isdisjoint(::NoNamingScheme, ::Nothing) = true

isdisjoint(::Nothing, ::NestedNamingScheme) = true
isdisjoint(::NestedNamingScheme, ::Nothing) = true

@generated function isdisjoint(::S, ::T) where {S <: NamingScheme, T <: NestedNamingScheme}
    return all(t -> isdisjoint(S(), t), T())
end

@generated function isdisjoint(::S, ::T) where {S <: NestedNamingScheme, T <: Union{NestedNamingScheme, NamingScheme}}
    return all(s -> isdisjoint(s, T()), S())
end

@generated function remove_variables(::N, ::Vars) where N <: Named where Vars <: Named
    remaining = setdiff(variablesymbols(N()), variablesymbols(Vars()))
    isempty(remaining) && return nothing
    return Named{tuple(remaining...)}()
end

remove_variables(N::Named, ::Numbered) = N
remove_variables(N::Numbered, ::Named) = N
remove_variables(N1::Numbered{Name}, N2::Numbered{Name}) where Name = (@assert num_variables(N2) >= num_variables(N1); return nothing)
remove_variables(N::Numbered, ::Numbered) = N

function remove_variables(N::Named, vars::NestedNamingScheme)
    for v in vars
        N = remove_variables(N, v)
    end
    return N
end

function remove_variables(N::Numbered, vars::NestedNamingScheme)
    for v in vars
        N = remove_variables(N, v)
    end
    return N
end

diff(x::Union{NamingScheme, NestedNamingScheme}, y::Union{NamingScheme, NestedNamingScheme}) = remove_variables(x, y)

namingscheme(::Type) = nothing
nestednamingscheme(T::Type) = isnothing(namingscheme(T)) ? NoNamingScheme() : (namingscheme(T),)
boundnames(::Type) = nothing
fullboundnames(T::Type) = isnothing(boundnames(T)) ? NoNamingScheme() : (boundnames(T),)

iscanonical(T::NamingScheme) = (T,) == canonicalscheme(T)
iscanonical(T::NestedNamingScheme) = T == canonicalscheme(T)

@generated function canonicalscheme(N::Named{Names}) where Names
    sortedsyms = sort(collect(Names))
    return composeschemes(Named{tuple(sortedsyms...)}())
end

canonicalscheme(N::Numbered) = composeschemes(N)
canonicalscheme(a::Numbered, b::Named) = composeschemes(a, b)
canonicalscheme(a::Named, b::Numbered) = composeschemes(b, a)
@generated function canonicalscheme(a::Numbered{Name1}, b::Numbered{Name2}) where {Name1, Name2}
    if Name1 < Name2
        return composeschemes(a(), b())
    else
        return composeschemes(b(), a())
    end
end
@pure function canonicalscheme(a::Named{Names1}, b::Named{Names2}) where {Names1, Names2}
    sortedsyms = sort(Names1 ∪ Names2)
    return composeschemes(Named{tuple(sortedsyms...)}())
end

@pure function canonicalscheme(scheme, schemes...)
    cs = canonicalscheme(schemes...)
    s = first(cs)
    ss = cs[2:end]

    t = (scheme, s)
    tcan = canonicalscheme(t)
    if tcan == t
        return composeschemes(tcan..., ss...)
    else
        return canonicalscheme(tcan..., ss...)
    end
end

canonicalscheme(a::NestedNamingScheme) = canonicalscheme(a...)

# -----------------------------------------------------------------------------
#
# Promotions
#
# -----------------------------------------------------------------------------
@generated function promote_rule(::Type{N1}, ::Type{N2}) where {N1 <: Named, N2 <: Named}
    symbols = sort(variablesymbols(N1()) ∪ variablesymbols(N2()))
    Names = tuple(symbols...)
    return Named{Names}
end

@generated function promote_rule(::Type{N1}, ::Type{N2}) where {N1 <: Numbered{Name}, N2 <: Numbered{Name}} where Name
    max = max(num_variables(N1), num_variables(N2))
    return Numbered{Name, max}
end

promote_type(args::NamingScheme...) = promote_type(typeof.(args)...)()

# -----------------------------------------------------------------------------
#
# Constructors
#
# -----------------------------------------------------------------------------
macro variable(x)
    if x isa Symbol
        return NamedVariable{x}()
    elseif x isa Expr && x.head == :ref
        sym, ix = x.args
        return NumberedVariable{sym, ix}()
    else
        error("Usage: @variable(x) or @variable(x[3])")
    end
end

parse_namingscheme(s::Symbol) = Named{(s,)}()

function parse_namingscheme(expr::Expr)
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
    error("Can't parse namingscheme $expr")
end

macro namingscheme(expr)
    return parse_namingscheme(expr)
end

macro nestednamingscheme(expr...)
    schemes = map(parse_namingscheme, expr)
    return composeschemes(schemes...)
end

end # module
