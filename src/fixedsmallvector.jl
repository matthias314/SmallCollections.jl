#
# common definitions for AbstractFixedVector and AbstractSmallVector
#

export support

import Base: findall, findfirst, findlast, findprev, findnext, findmin, findmax,
    any, all, allequal, allunique, count, getindex, filter, checkindex

const AbstractFixedOrSmallVector{N,T} = Union{AbstractFixedVector{N,T}, AbstractSmallVector{N,T}}

support(v::AbstractFixedOrSmallVector) = _SmallBitSet(bits(map(!iszero, v)))

_support(f, v::AbstractFixedVector; style) = support(f, v)
_support(f, v::AbstractSmallVector; style) = support(f, v; style)

_map(f, v::AbstractFixedVector; style) = map(f, v)
_map(f, v::AbstractSmallVector; style) = map(f, v; style)

assertbool(f) = x -> f(x)::Bool

findall(v::AbstractFixedOrSmallVector; kw...) = findall(identity, v; kw...)

function findall(f::F, v::AbstractFixedOrSmallVector{N}; kw...) where {F<:Function,N}
    SmallVector{N,SmallLength}(support(assertbool(f), v; kw...))
end

findfirst(v::AbstractFixedOrSmallVector{N,Bool}) where N = findfirst(identity, v; style = StrictStyle())
findlast(v::AbstractFixedOrSmallVector{N,Bool}) where N = findlast(identity, v; style = StrictStyle())

findnext(v::AbstractFixedOrSmallVector{N,Bool}, k::Integer) where N = findnext(identity, v, k; style = StrictStyle())
findprev(v::AbstractFixedOrSmallVector{N,Bool}, k::Integer) where N = findprev(identity, v, k; style = StrictStyle())

function findfirst(f::F, v::AbstractFixedOrSmallVector{N,T}; style = MapStyle(f, T)) where {F <: Function, N, T}
    findnext(f, v, 1; style)
end

function findnext(f::F, v::AbstractFixedOrSmallVector{N,T}, k::Integer; style = MapStyle(f, T)) where {F<: Function, N, T}
    @inline
    if style isa LazyStyle
        invoke(findnext, Tuple{F,AbstractVector{T},Integer}, f, v, k)
    else
        m = bits(filter(>=(k), @inline support(assertbool(f), fixedvector(v))))
        i = trailing_zeros(m)+1
        i <= length(v) ? i : nothing
    end
end

function findlast(f::F, v::AbstractFixedOrSmallVector{N,T}; style = MapStyle(f, T)) where {F <: Function, N, T}
    findprev(f, v, length(v); style)
end

function findprev(f::F, v::AbstractFixedOrSmallVector{N,T}, k::Integer; style = MapStyle(f, T)) where {F <: Function, N, T}
    @inline
    if style isa LazyStyle
        invoke(findprev, Tuple{F,AbstractVector{T},Integer}, f, v, k)
    else
        m = bits(filter(<=(k), @inline support(assertbool(f), fixedvector(v))))
        i = bitsize(m)-leading_zeros(m)
        0 != i <= length(v) ? i : nothing
    end
end

@inline function findmin(v::AbstractFixedOrSmallVector{N,T}) where {N, T <: BitInteger}
    @boundscheck isempty(v) && error("argument must not be empty")
    x = minimum(v)
    x, findfirst(==(x), fixedvector(v))::Int
end

@inline function findmax(v::AbstractFixedOrSmallVector{N,T}) where {N, T <: BitInteger}
    @boundscheck isempty(v) && error("argument must not be empty")
    x = maximum(v)
    x, findfirst(==(x), fixedvector(v))::Int
end

any(v::AbstractFixedOrSmallVector; kw...) = any(identity, v; kw...)
all(v::AbstractFixedOrSmallVector; kw...) = all(identity, v; kw...)

function any(f::F, v::AbstractFixedOrSmallVector{N,T}; dims = :, style::MapStyle = MapStyle(f, T)) where {F<:Function,N,T}
    @inline
    if style isa LazyStyle || !(dims isa Colon)
        invoke(any, Tuple{F,AbstractVector{T}}, f, v; dims)
    else
        u = map(assertbool(f), fixedvector(v))
        trailing_zeros(bits(u)) < length(v)
    end
end

function all(f::F, v::AbstractFixedOrSmallVector{N,T}; dims = :, style::MapStyle = MapStyle(f, T)) where {F<:Function,N,T}
    @inline
    if style isa LazyStyle || !(dims isa Colon)
        invoke(all, Tuple{F,AbstractVector{T}}, f, v; dims)
    else
        u = map(assertbool(f), fixedvector(v))
        trailing_ones(bits(u)) >= length(v)
    end
end

allequal(v::AbstractFixedOrSmallVector) = isempty(v) ? true : all(isequal(@inbounds v[1]), v)

function allequal(f::F, v::AbstractFixedOrSmallVector{N,T}; style::MapStyle = MapStyle(f, T)) where {F,N,T}
    @inline
    if style isa LazyStyle
        invoke(allequal, Tuple{F,AbstractVector{T}}, f, v)
    else
        allequal(_map(f, v; style))
    end
end

allunique(v::AbstractFixedOrSmallVector) = all(x -> count(isequal(x), v) == 1, v)

function allunique(f::F, v::AbstractFixedOrSmallVector{N,T}; style::MapStyle = MapStyle(f, T)) where {F,N,T}
    @inline
    if style isa LazyStyle
        invoke(allunique, Tuple{F,AbstractVector{T}}, f, v)
    else
        allunique(_map(f, v; style))
    end
end

count(v::AbstractFixedOrSmallVector; kw...) = count(identity, v; kw...)

function count(f::F, v::AbstractFixedOrSmallVector{N,T}; dims = :, init::S = 0, style = MapStyle(f, T)) where {F,N,T,S}
    if style isa LazyStyle || !(dims isa Colon)
        invoke(count, Tuple{Any, AbstractVector}, f, v; dims, init)
    else
        k = length(_support(assertbool(f), v; style))
        init + (S <: Integer ? k % S : k)
    end
end

function checkindex(::Type{Bool}, inds::AbstractUnitRange, v::AbstractFixedOrSmallVector{N,T}) where {N, T <: Base.HWReal}
    if isempty(v)
        true
    else
        min, max = extrema(v)
        first(inds) <= min && max <= last(inds)
    end
end

@inline function getindex(v::AbstractFixedOrSmallVector{N,T}, ii::OrdinalRange) where {N,T}
    @boundscheck checkbounds(v, ii)
    @inbounds SmallVector{N,T}(v[i] for i in ii)
end

"""
    getindex(v::Union{AbstractFixedVector{N,T}, AbstractSmallVector{N,T}}, s::SmallBitSet) where {N,T} -> SmallVector{N,T}

Returns the vector with elements `v[i]` where `i` runs through the elements of `s` in increasing order.
This operation is analogous to `v[collect(s)]`, but faster.

# Example
```jldoctest
julia> v = SmallVector{8}('a':'f'); s = SmallBitSet{UInt16}(1:2:5)
SmallBitSet{UInt16} with 3 elements:
  1
  3
  5

julia> v[s]
3-element SmallVector{8, Char}:
 'a': ASCII/Unicode U+0061 (category Ll: Letter, lowercase)
 'c': ASCII/Unicode U+0063 (category Ll: Letter, lowercase)
 'e': ASCII/Unicode U+0065 (category Ll: Letter, lowercase)
```
"""
getindex(v::AbstractFixedOrSmallVector, s::SmallBitSet)

@inline function getindex(v::AbstractFixedOrSmallVector{N,T}, s::SmallBitSet{U}) where {N,T,U}
    @boundscheck isempty(s) || checkbounds(v, last(s))
    if HAS_PEXT && T == Bool && bitsize(U) <= bitsize(UInt)
        m = pext(bits(fixedvector(v)), bits(s))
        b = convert(FixedVector{N,Bool}, m)
        SmallVector(b, length(s))
    elseif T <: HWType && N <= 32  # slows down for larger N
        SmallVector(compress(fixedvector(v), s), length(s))
    else
        SmallVector{N,T}(@inbounds v[i] for i in s)
    end
end

const AbstractFixedOrSmallOrPackedVector{T} = Union{AbstractFixedOrSmallVector{<:Any,T},PackedVector{<:Any,<:Any,T}}

@inline function getindex(v::AbstractFixedOrSmallOrPackedVector, ii::AbstractFixedOrSmallOrPackedVector{Bool})
    @boundscheck checkbounds(v, ii)
    @inbounds v[support(ii)]
end

@inline function getindex(v::V, ii::AbstractFixedOrSmallOrPackedVector{T}) where {V <: AbstractVector, T <: Integer}
    @boundscheck checkbounds(v, ii)
    if T == Bool
        @inbounds invoke(getindex, Tuple{V,AbstractVector{Bool}}, v, ii)
    else
        map(i -> @inbounds(v[i]), ii)
    end
end

@inline function getindex(v::AbstractFixedOrSmallOrPackedVector, ii::AbstractFixedOrSmallVector{T}) where T <: Integer
    @boundscheck checkbounds(v, ii)
    map(i -> @inbounds(v[i]), ii)
end

function filter(f::F, v::AbstractFixedOrSmallVector; kw...) where F
    @inbounds v[support(f, v; kw...)]
end
