#
# fast types
#

"""
    $(@__MODULE__).isfasttype(::Type{T}) where T -> Bool

Return `true` if elements of type `T` permit fast (for instance, vectorized) operations.

By default, `Base.HWReal`, `Bool`, `Char`, and `Enum` types are considered
fast, as well as `Complex`, `Pair`, `Tuple`, `NamedTuple` and `Ref` with
fast components.

See `Base.HWReal`.
"""
isfasttype(::Type) = false
isfasttype(::Type{<:HWType}) = true

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

"""
    $(@__MODULE__).MapStyle

    MapStyle(f, types::Type...) -> MapStyle


A `MapStyle` determines how `$(@__MODULE__)` evaluates certain functions like
`map` or `findfirst` that take a function `f` as argument. The available subtypes
of `MapStyle` are as follows, from the least to the most efficient:

- `LazyStyle`: the function `f` is only evaluated when strictly necessary,
  and it is not assumed to be defined for default values. This is the default
  `MapStyle` for unknown functions.

- `EagerStyle`: `f` may be evaluated more often than strictly necessary,
  and it is assumed to be defined for default values. However, it need not
  map default values to default values.

- `RigidStyle`: `f` may be evaluated more often than strictly necessary. It is
  assumed to be defined for default values and to return a default value if all
  arguments are default values.

- `StrictStyle`: `f` may be evaluated more often than strictly necessary. It is
  assumed to be defined for default values and to return a default value if at
  least one argument is a default value. (This is the same as `RigidStyle` for
  functions with a single argument.)

The `MapStyle` is predefined for many functions from `Base` as well as for operations
that produce new functions out of old. Unnamed functions are not recognized. However,
several functions from `$(@__MODULE__)` allow to specify a `MapStyle` as keyword argument.
In addition, users can define a `MapStyle` for their own types.

See also [`$(@__MODULE__).default`](@ref), [`$(@__MODULE__).isfasttype`](@ref).

# Examples
```jldoctest
julia> using SmallCollections: MapStyle

julia> MapStyle(iszero, Int)   # not RigidStyle: iszero(0) is true, not false
SmallCollections.EagerStyle()

julia> MapStyle(+, Int, Int)
SmallCollections.RigidStyle()

julia> MapStyle(*, Int, Float64)   # not StrictStyle: 0 * Inf is NaN, not 0.0
SmallCollections.RigidStyle()

julia> MapStyle(*, Int, Int)
SmallCollections.StrictStyle()

julia> MapStyle(-, Int)
SmallCollections.StrictStyle()

julia> MapStyle(x -> -x, Int)   # not StrictStyle: anonymous function not recognized
SmallCollections.LazyStyle()

julia> MapStyle(-, Int128)   # Int128 is not a fast type, so better be lazy
SmallCollections.LazyStyle()

julia> MapStyle(isfinite∘inv, Float64)   # function composition is recognized
SmallCollections.EagerStyle()

julia> MapStyle(!iszero, Int)   # function composition again
SmallCollections.EagerStyle()

julia> MapStyle(>=(1), Int)   # >=(1) is Base.Fix2(>=, 1), which is recognized
SmallCollections.EagerStyle()
```
"""
abstract type MapStyle end,
struct LazyStyle <: MapStyle end,
struct EagerStyle <: MapStyle end,
struct RigidStyle <: MapStyle end,
struct StrictStyle <: MapStyle end

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
MapStyle(::typeof(-), ::Type{T}) where T = iffasttypes(hasfloats(T) ? EagerStyle() : StrictStyle(), T)

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

MapStyle(::typeof(length), ::Type{<:Union{AbstractVector, AbstractSet, AbstractDict}}) = StrictStyle()
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
