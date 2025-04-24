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

using Base.FastMath: abs2_fast, abs_fast, add_fast, cmp_fast, conj_fast,
    eq_fast, ge_fast, gt_fast, inv_fast, isfinite_fast, isinf_fast,
    isnan_fast, issubnormal_fast, le_fast, lt_fast, max_fast, min_fast,
    minmax_fast, mul_fast, ne_fast, sign_fast, sqrt_fast, sub_fast

abstract type MapStyle end

struct StrictStyle <: MapStyle end
struct RigidStyle <: MapStyle end
struct EagerStyle <: MapStyle end
struct LazyStyle <: MapStyle end

iffasttypes(style::MapStyle) = style

function iffasttypes(style::MapStyle, ::Type{T}, types::Type...) where T
    isfasttype(T) ? iffasttypes(style, types...) : LazyStyle()
end

MapStyle(::Any, ::Type...) = LazyStyle()
# MapStyle(f, args...) = MapStyle(f, map(typeof, args)...)

MapStyle(::Union{typeof.(
        (-, identity, signbit, isodd, isone, isinf, isinf_fast, isnan, isnan_fast,
            issubnormal, issubnormal_fast, zero, round, floor, ceil, trunc,
            abs, abs_fast, sign, sign_fast, sqrt, sqrt_fast, conj, conj_fast)
    )...}, ::Type{T}) where T = iffasttypes(StrictStyle(), T)
MapStyle(::Union{typeof.(
        (&,)
    )...}, types::Type...) = iffasttypes(StrictStyle(), types...)

MapStyle(::Union{typeof.(
        (!==, !=, ne_fast, <, lt_fast, >, gt_fast, cmp, cmp_fast, -, abs2, abs2_fast)
    )...}, ::Type{T1}, ::Type{T2}) where {T1,T2}= iffasttypes(RigidStyle(), T1, T2)
MapStyle(::Union{typeof.(
        (|, xor, +, add_fast, min, min_fast, max, max_fast, minmax, minmax_fast)
    )...}, types::Type...) = iffasttypes(RigidStyle(), types...)

MapStyle(::Union{typeof.(
        (!, ~, iseven, iszero, isfinite, isfinite_fast, one, inv, inv_fast)
    )...}, ::Type{T}) where T = iffasttypes(EagerStyle(), T)
MapStyle(::Union{typeof.(
        # note: 1/0 = Inf
        (===, isequal, ==, eq_fast, <=, le_fast, >=, ge_fast, /)
    )...}, ::Type{T1}, ::Type{T2}) where {T1,T2}= iffasttypes(EagerStyle(), T1, T2)
MapStyle(::Union{typeof.(
        (nand, nor)
    )...}, types::Type...) = iffasttypes(EagerStyle(), types...)

# definitions depending on specific types

MapStyle(::Fix2{typeof(rem),Type{S}}, T::Type) where S = iffasttypes(StrictStyle(), S, T)

MapStyle(::typeof(min), types::Type{<:Unsigned}...) = iffasttypes(StrictStyle(), types...)

hasfloats(::Type) = false
hasfloats(::Type{<:AbstractFloat}) = true
hasfloats(::Type{<:Complex{T}}) where T = hasfloats(T)
hasfloats(::Type{<:AbstractArray{T}}) where T = hasfloats(T)
hasfloats(::Type{<:Ref{T}}) where T = hasfloats(T)

# -(0.0) === -0.0, not 0.0
MapStyle(::typeof(-), ::Type{T}) where T = iffasttypes(hasfloats(T) ? RigidStyle() : StrictStyle(), T)

# (-1) * 0.0 === -0.0, not 0.0
function MapStyle(::Union{typeof.(
        (*, mul_fast)
    )...}, ::Type{T}, types::Type...) where T
    style = if hasfloats(T) || MapStyle(*, types...) isa RigidStyle
        RigidStyle()
    else
        StrictStyle()
    end
    iffasttypes(style, T, types...)
end

MapStyle(::typeof(length), ::Type{<:Union{AbstractVector, AbstractSet, AbstractDict}}) = StronlyStrictStyle()
MapStyle(::typeof(in), ::Type, ::Type{<:Union{AbstractVector, AbstractSet, AbstractDict}}) = RigidStyle()

MapStyle(::typeof(intersect), ::Type{T}, types::Type...) where T <: AbstractSet = iffasttypes(StrictStyle(), T, types...)
MapStyle(::Union{typeof.(
        (union, setdiff, symdiff)
    )...}, ::Type{T}, types::Type...) where T <: AbstractSet = iffasttypes(RigidStyle(), T, types...)

# definitions for constructors of new functions

MapStyle(f::Returns{T}, types::Type...) where T = iffasttypes(EagerStyle(), T)

function MapStyle(f::ComposedFunction, types::Type...)
    istyle = MapStyle(f.inner, types...)
    istyle isa LazyStyle && return LazyStyle()
    T = Core.Compiler.return_type(f.inner, Tuple{types...})
    isconcretetype(T) || return LazyStyle()
    ostyle = MapStyle(f.outer, T)
    if ostyle isa Union{LazyStyle, EagerStyle}
        ostyle
    elseif istyle isa Union{EagerStyle, RigidStyle}
        istyle
    else
        StrictStyle()
    end
end

MapStyle(f::Base.Splat, ::Type{T}) where T <: Tuple = MapStyle(f.f, fieldtypes(T)...)

# TODO: use StrictStyle
if VERSION > v"1.12-alpha"
    function MapStyle(g::Base.Fix{N,F,T}, types::Type...) where {N,F,T}
        style = MapStyle(g.f, types[1:N-1]..., T, types[N:end]...)
        style isa RigidStyle ? EagerStyle() : style
    end
else
    function MapStyle(g::Fix1{F,T}, types::Type...) where {F,T}
        style = MapStyle(g.f, T, types...)
        style isa RigidStyle ? EagerStyle() : style
    end
    function MapStyle(g::Fix2{F,T}, type1::Type, types::Type...) where {F,T}
        style = MapStyle(g.f, type1, T, types...)
        style isa RigidStyle ? EagerStyle() : style
    end
end
