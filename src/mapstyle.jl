#
# fast types
#

isfasttype(::Type) = false
isfasttype(::Type{<:Union{Base.HWReal, Bool, Char, Enum}}) = true

isfasttype(::Type{Complex{T}}) where T = isfasttype(T)
isfasttype(::Type{Pair{K,V}}) where {K,V} = isfasttype(K) && isfasttype(V)
isfasttype(::Type{T}) where T <: Tuple = all(isfasttype, fieldtypes(T))
isfasttype(::Type{NamedTuple{K,T}}) where {K,T} = isfasttype(T)
isfasttype(::Type{<:Ref{T}}) where T = isfasttype(T)

#
# MapStyle definitions
#

using Base: Fix1, Fix2

abstract type MapStyle end

struct PreservesDefault <: MapStyle end
struct WeaklyPreservesDefault <: MapStyle end
struct AcceptsDefault <: MapStyle end
struct DefaultMapStyle <: MapStyle end

iffasttypes(style::MapStyle) = style

function iffasttypes(style::MapStyle, ::Type{T}, types::Type...) where T
    isfasttype(T) ? iffasttypes(style, types...) : DefaultMapStyle()
end

MapStyle(::Any, ::Type...) = DefaultMapStyle()
# MapStyle(f, args...) = MapStyle(f, map(typeof, args)...)

MapStyle(::Union{typeof.(
        (-, identity, signbit, isodd, isone, isinf, isnan, issubnormal, zero, round, floor, ceil, trunc, abs, sign, sqrt, conj)
    )...}, ::Type{T}) where T = iffasttypes(PreservesDefault(), T)
MapStyle(::Union{typeof.(
        (&,)
    )...}, types::Type...) = iffasttypes(PreservesDefault(), types...)

MapStyle(::Union{typeof.(
        (!==, !=, <, >, cmp, -, abs2)
    )...}, ::Type{T1}, ::Type{T2}) where {T1,T2}= iffasttypes(WeaklyPreservesDefault(), T1, T2)
MapStyle(::Union{typeof.(
        (|, xor, +, min, max, minmax)
    )...}, types::Type...) = iffasttypes(WeaklyPreservesDefault(), types...)

MapStyle(::Union{typeof.(
        (!, ~, iseven, iszero, isfinite, one, inv)
    )...}, ::Type{T}) where T = iffasttypes(AcceptsDefault(), T)
MapStyle(::Union{typeof.(
        # note: 1/0 = Inf
        (===, isequal, ==, <=, >=, /)
    )...}, ::Type{T1}, ::Type{T2}) where {T1,T2}= iffasttypes(AcceptsDefault(), T1, T2)
MapStyle(::Union{typeof.(
        (nand, nor)
    )...}, types::Type...) = iffasttypes(AcceptsDefault(), types...)

# definitions depending on specific types

MapStyle(::Fix2{typeof(rem),Type{S}}, T::Type) where S = iffasttypes(PreservesDefault(), S, T)

MapStyle(::typeof(min), types::Type{<:Unsigned}...) = iffasttypes(PreservesDefault(), types...)

hasfloats(::Type) = false
hasfloats(::Type{<:AbstractFloat}) = true
hasfloats(::Type{<:Complex{T}}) where T = hasfloats(T)
hasfloats(::Type{<:AbstractArray{T}}) where T = hasfloats(T)
hasfloats(::Type{<:Ref{T}}) where T = hasfloats(T)

# -(0.0) === -0.0, not 0.0
MapStyle(::typeof(-), ::Type{T}) where T = iffasttypes(hasfloats(T) ? WeaklyPreservesDefault() : PreservesDefault(), T)

# (-1) * 0.0 === -0.0, not 0.0
function MapStyle(::typeof(*), ::Type{T}, types::Type...) where T
    style = if hasfloats(T) || MapStyle(*, types...) isa WeaklyPreservesDefault
        WeaklyPreservesDefault()
    else
        PreservesDefault()
    end
    iffasttypes(style, T, types...)
end

MapStyle(::typeof(length), ::Type{<:Union{AbstractVector, AbstractSet, AbstractDict}}) = StronlyPreservesDefault()
MapStyle(::typeof(in), ::Type, ::Type{<:Union{AbstractVector, AbstractSet, AbstractDict}}) = WeaklyPreservesDefault()

MapStyle(::typeof(intersect), ::Type{T}, types::Type...) where T <: AbstractSet = iffasttypes(PreservesDefault(), T, types...)
MapStyle(::Union{typeof.(
        (union, setdiff, symdiff)
    )...}, ::Type{T}, types::Type...) where T <: AbstractSet = iffasttypes(WeaklyPreservesDefault(), T, types...)

# definitions for constructors of new functions

MapStyle(f::Returns{T}, types::Type...) where T = iffasttypes(AcceptsDefault(), T)

function MapStyle(f::ComposedFunction, types::Type...)
    istyle = MapStyle(f.inner, types...)
    istyle isa DefaultMapStyle && return DefaultMapStyle()
    T = Core.Compiler.return_type(f.inner, Tuple{types...})
    isconcretetype(T) || return DefaultMapStyle()
    ostyle = MapStyle(f.outer, T)
    if ostyle isa Union{DefaultMapStyle, AcceptsDefault}
        ostyle
    elseif istyle isa Union{AcceptsDefault, WeaklyPreservesDefault}
        istyle
    else
        PreservesDefault()
    end
end

MapStyle(f::Base.Splat, ::Type{T}) where T <: Tuple = MapStyle(f.f, fieldtypes(T)...)

# TODO: use PreservesDefault
if VERSION > v"1.12-alpha"
    function MapStyle(g::Base.Fix{N,F,T}, types::Type...) where {N,F,T}
        style = MapStyle(g.f, types[1:N-1]..., T, types[N:end]...)
        style isa WeaklyPreservesDefault ? AcceptsDefault() : style
    end
else
    function MapStyle(g::Fix1{F,T}, types::Type...) where {F,T}
        style = MapStyle(g.f, T, types...)
        style isa WeaklyPreservesDefault ? AcceptsDefault() : style
    end
    function MapStyle(g::Fix2{F,T}, type1::Type, types::Type...) where {F,T}
        style = MapStyle(g.f, type1, T, types...)
        style isa WeaklyPreservesDefault ? AcceptsDefault() : style
    end
end
