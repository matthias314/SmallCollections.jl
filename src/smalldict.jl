#
# small dictionaries
#

export AbstractSmallDict, SmallDict, MutableSmallDict, capacity,
    setindex, push, delete, pop

import Base: copy, length, iterate, haskey, getindex, get,
    setindex, setindex!, empty!, delete!, pop!

"""
    AbstractSmallDict{N,K,V} <: AbstractDict{K,V}

This is the supertype of `SmallDict{N,K,V}` and `MutableSmallDict{N,K,V}`.
"""
abstract type AbstractSmallDict{N,K,V} <: AbstractDict{K,V} end

"""
    SmallDict{N,K,V} <: AbstractSmallDict{N,K,V}

    SmallDict{N,K,V}()
    SmallDict{N,K,V}(itr; unique = false)

An immutable dictionary with key type `K` and value type `V` that can store up to `N` entries.
All entries come from the key-value iterator `itr` provided at construction time.

If `unique` is set to `true`, then the elements of `itr` are assumed to have distinct keys.

# Example
```jldoctest
julia> SmallDict{8,Char,Int}('a'+k => k^2 for k in 0:2; unique = true)
SmallDict{8, Char, Int64} with 3 entries:
  'a' => 0
  'b' => 1
  'c' => 4
```
"""
struct SmallDict{N,K,V} <: AbstractSmallDict{N,K,V}
    v::SmallVector{N,Pair{K,V}}
    SmallDict(v::AbstractSmallVector{N,Pair{K,V}}) where {N,K,V} = new{N,K,V}(v)
end

SmallDict(d::AbstractSmallDict) = SmallDict(d.v)

SmallDict{N,K,V}() where {N,K,V} = SmallDict(SmallVector{N,Pair{K,V}}())

function SmallDict{N,K,V}(itr; unique = false) where {N,K,V}
    if unique
        SmallDict(SmallVector{N,Pair{K,V}}(itr))
    else
        d = MutableSmallDict{N,K,V}(itr)
        SmallDict(SmallVector(d.v))
    end
end

"""
    MutableSmallDict{N,K,V} <: AbstractSmallDict{N,K,V}

    MutableSmallDict{N,K,V}()
    MutableSmallDict{N,K,V}(itr; unique = false)

An dictionary with key type `K` and value type `V` that can store up to `N` entries.
The dictionary is mutable and implements Julia's dictionary interface.

If `unique` is set to `true`, then the elements of `itr` are assumed to have distinct keys.

# Example
```jldoctest
julia> d = MutableSmallDict{8,Char,Int}('a'+k => k^2 for k in 0:2)
MutableSmallDict{8, Char, Int64} with 3 entries:
  'a' => 0
  'b' => 1
  'c' => 4

julia> delete!(d, 'b')
MutableSmallDict{8, Char, Int64} with 2 entries:
  'a' => 0
  'c' => 4
```
"""
struct MutableSmallDict{N,K,V} <: AbstractSmallDict{N,K,V}
    v::MutableSmallVector{N,Pair{K,V}}
    MutableSmallDict(v::AbstractSmallVector{N,Pair{K,V}}) where {N,K,V} = new{N,K,V}(v)
end

MutableSmallDict(d::AbstractSmallDict) = MutableSmallDict(d.v)

MutableSmallDict{N,K,V}() where {N,K,V} = MutableSmallDict(MutableSmallVector{N,Pair{K,V}}())

function MutableSmallDict{N,K,V}(itr; unique = false) where {N,K,V}
    if unique
        MutableSmallDict(MutableSmallVector{N,Pair{K,V}}(itr))
    else
        foldl(push!, itr; init = MutableSmallDict{N,K,V}())
    end
end

capacity(::Type{<:AbstractSmallDict{N}}) where N = N

copy(d::D) where D <: AbstractSmallDict = D(d.v)

length(d::AbstractSmallDict) = length(d.v)

iterate(d::AbstractSmallDict, state...) = iterate(d.v, state...)

@inline function token(d::AbstractSmallDict{N,K}, key) where {N,K}
    findfirst(kv -> kv.first == convert(K, key), d.v)
end

haskey(d::AbstractSmallDict, key) = token(d, key) !== nothing

function getindex(d::AbstractSmallDict, key)
    i = token(d, key)
    if i === nothing
        error("key not found")
    else
        @inbounds d.v[i].second
    end
end

function get(d::AbstractSmallDict, key, default)
    i = token(d, key)
    i === nothing ? default : @inbounds d.v[i].second
end

@propagate_inbounds function push(d::AbstractSmallDict, kv::Pair)
    i = token(d, kv.first)
    if i === nothing
        v = push(d.v, kv)
    else
        v = @inbounds setindex(d.v, kv, i)
    end
    SmallDict(v)
end

@propagate_inbounds function setindex(d::AbstractSmallDict{N,K,V}, val, key) where {N,K,V}
    push(d, Pair{K,V}(key, val))
end

function delete(d::AbstractSmallDict, key)
    i = token(d, key)
    i === nothing ? SmallDict(d) : (@inbounds v = deleteat(d.v, i); SmallDict(v))
end

@propagate_inbounds function pop(d::AbstractSmallDict)
    v, kv = pop(d.v)
    SmallDict(v), kv.second
end

function pop(d::AbstractSmallDict, key)
    i = token(d, key)
    i === nothing && error("key not found")
    @inbounds v, kv = popat(d.v, i)
    SmallDict(v), kv.second
end

function pop(d::AbstractSmallDict, key, default)
    i = token(d, key)
    i === nothing && return SmallDict(d), default
    @inbounds v, kv = popat(d.v, i)
    SmallDict(v), kv.second
end

function setindex!(d::MutableSmallDict{N,K,V}, val, key) where {N,K,V}
    i = token(d, key)
    if i === nothing
        push!(d.v, Pair{K,V}(key, val))
    else
        @inbounds d.v[i] = Pair{K,V}(key, val)
    end
    d
end

empty!(d::MutableSmallDict) = (empty!(d.v); d)

function delete!(d::MutableSmallDict, key)
    i = token(d, key)
    i === nothing ? d : (@inbounds deleteat!(d.v, i); d)
end

@propagate_inbounds function pop!(d::MutableSmallDict)
    kv = pop!(d.v)
    kv.second
end

function pop!(d::MutableSmallDict, key)
    i = token(d, key)
    i === nothing && error("key not found")
    @inbounds kv = popat!(d.v, i)
    kv.second
end

function pop!(d::MutableSmallDict, key, default)
    i = token(d, key)
    i === nothing && return default
    @inbounds kv = popat!(d.v, i)
    kv.second
end
