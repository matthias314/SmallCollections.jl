#
# MapStyle definitions
#

using Base: Fix1, Fix2

abstract type MapStyle end

struct PreservesDefault <: MapStyle end
struct WeaklyPreservesDefault <: MapStyle end
struct AcceptsDefault <: MapStyle end
struct DefaultMapStyle <: MapStyle end

MapStyle(::Any, ::Type...) = DefaultMapStyle()
# MapStyle(f, args...) = MapStyle(f, map(typeof, args)...)

MapStyle(::Union{typeof.(
        (-, identity, signbit, isodd, isone, isinf, isnan, zero, round, floor, ceil, trunc, abs, sign, sqrt)
    )...}, ::Type) = PreservesDefault()
MapStyle(::Union{typeof.(
        (&,)
    )...}, ::Type...) = PreservesDefault()

MapStyle(::Union{typeof.(
        (!==, !=, <, >, -, abs2)
    )...}, ::Type, ::Type) = WeaklyPreservesDefault()
MapStyle(::Union{typeof.(
        (|, xor, +)
    )...}, ::Type...) = WeaklyPreservesDefault()

MapStyle(::Union{typeof.(
        (!, ~, iseven, iszero, one)
    )...}, ::Type) = AcceptsDefault()
MapStyle(::Union{typeof.(
        # note: 1/0 = Inf
        (===, isequal, ==, <=, >=, /)
    )...}, ::Type, ::Type) = AcceptsDefault()
MapStyle(::Union{typeof.(
        (nand, nor)
    )...}, ::Type...) = AcceptsDefault()

# definitions depending on type

hasfloats(::Type) = false
hasfloats(::Type{<:AbstractFloat}) = true
hasfloats(::Type{<:Complex{T}}) where T = hasfloats(T)
hasfloats(::Type{<:AbstractArray{T}}) where T = hasfloats(T)
hasfloats(::Type{<:Ref{T}}) where T = hasfloats(T)

# -(0.0) === -0.0, not 0.0
MapStyle(::typeof(-), ::Type{T}) where T = hasfloats(T) ? WeaklyPreservesDefault() : PreservesDefault()

# (-1) * 0.0 === -0.0, not 0.0
function MapStyle(::typeof(*), ::Type{T}, types::Type...) where T
    if hasfloats(T) || MapStyle(*, types...) isa WeaklyPreservesDefault
        WeaklyPreservesDefault()
    else
        PreservesDefault()
    end
end

MapStyle(::typeof(length), ::Type{<:Union{AbstractVector, AbstractSet, AbstractDict}}) = StronlyPreservesDefault()
MapStyle(::typeof(in), ::Type, ::Type{<:Union{AbstractVector, AbstractSet, AbstractDict}}) = WeaklyPreservesDefault()

MapStyle(::typeof(intersect), ::Type{<:AbstractSet}, ::Type...) = PreservesDefault()
MapStyle(::Union{typeof.(
        (union, setdiff, symdiff)
    )...}, ::Type{<:AbstractSet}, ::Type...) = WeaklyPreservesDefault()

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
