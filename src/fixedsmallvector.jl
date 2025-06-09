#
# common definitions for AbstractFixedVector and AbstractSmallVector
#

export support

import Base: findall, findfirst, findlast, findprev, findnext, findmin, findmax,
    any, all, allequal, allunique, count

const AbstractFixedOrSmallVector{N,T} = Union{AbstractFixedVector{N,T}, AbstractSmallVector{N,T}}

support(v::AbstractFixedOrSmallVector) = _SmallBitSet(bits(map(!iszero, v)))

_support(f, v::AbstractFixedVector; style) = support(f, v)
_support(f, v::AbstractSmallVector; style) = support(f, v; style)

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
        s = filter(>=(k), _support(assertbool(f), v; style))
        isempty(s) ? nothing : first(s)
    end
end

function findlast(f::F, v::AbstractFixedOrSmallVector{N,T}; style = MapStyle(f, T)) where {F <: Function, N, T}
    findprev(f, v, N; style)  # TODO: better use length(v) ?
end

function findprev(f::F, v::AbstractFixedOrSmallVector{N,T}, k::Integer; style = MapStyle(f, T)) where {F <: Function, N, T}
    @inline
    if style isa LazyStyle
        invoke(findprev, Tuple{F,AbstractVector{T},Integer}, f, v, k)
    else
        s = filter(<=(k), _support(assertbool(f), v; style))
        isempty(s) ? nothing : last(s)
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
        allequal(map(f, v; style))
    end
end

allunique(v::AbstractFixedOrSmallVector) = all(x -> count(isequal(x), v) == 1, v)

function allunique(f::F, v::AbstractFixedOrSmallVector{N,T}; style::MapStyle = MapStyle(f, T)) where {F,N,T}
    @inline
    if style isa LazyStyle
        invoke(allunique, Tuple{F,AbstractVector{T}}, f, v)
    else
        allunique(map(f, v; style))
    end
end

count(v::AbstractFixedOrSmallVector; kw...) = count(identity, v; kw...)

function count(f::F, v::AbstractFixedOrSmallVector{N,T}; dims = :, init::S = 0, style = MapStyle(f, T)) where {F,N,T,S}
    if style isa LazyStyle || !(dims isa Colon)
        invoke(count, Tuple{Any, AbstractVector}, f, v; dims, init)
    else
        init + length(_support(assertbool(f), v; style)) % S
    end
end
