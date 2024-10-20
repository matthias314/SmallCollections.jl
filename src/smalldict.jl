#
# small dictionaries
#

export AbstractSmallDict, SmallDict, MutableSmallDict, capacity,
    setindex, push, delete, pop

import Base: keys, values, copy, length, iterate, haskey, getindex, get, getkey,
    setindex, setindex!, empty!, delete!, pop!

"""
    AbstractSmallDict{N,K,V} <: AbstractDict{K,V}

This is the supertype of `SmallDict{N,K,V}` and `MutableSmallDict{N,K,V}`.

See also [`SmallDict`](@ref), [`MutableSmallDict`](@ref).
"""
abstract type AbstractSmallDict{N,K,V} <: AbstractDict{K,V} end

"""
    SmallDict{N,K,V} <: AbstractSmallDict{N,K,V}

    SmallDict{N,K,V}()
    SmallDict{N,K,V}(itr; unique = false)
    SmallDict{N,K,V}(key1 => val1, key2 => val2, ...; unique = false)

An immutable dictionary with key type `K` and value type `V` that can store up to `N` entries.
All entries come from the key-value iterator `itr` provided at construction time or from the
explicitly given pairs.

If the key and value types are omitted, they will be inferred from the pairs or, if possible,
from the iterator. If `unique` is set to `true`, then the elements of `itr` are assumed to have
distinct keys.

See also [`AbstractSmallDict`](@ref), [`MutableSmallDict`](@ref).

# Examples
```jldoctest
julia> SmallDict{8}(Int16(1) => 2, Int32(3) => 4.0)
SmallDict{8, Int32, Float64} with 2 entries:
  1 => 2.0
  3 => 4.0

julia> SmallDict{8,Char,Int}('a'+k => k^2 for k in 0:2; unique = true)
SmallDict{8, Char, Int64} with 3 entries:
  'a' => 0
  'b' => 1
  'c' => 4
```
"""
struct SmallDict{N,K,V} <: AbstractSmallDict{N,K,V}
    keys::SmallVector{N,K}
    vals::SmallVector{N,V}
    SmallDict{N,K,V}(keys::AbstractSmallVector{N,K}, vals::AbstractSmallVector{N,V}) where {N,K,V} = new{N,K,V}(keys, vals)
    SmallDict(keys::AbstractSmallVector{N,K}, vals::AbstractSmallVector{N,V}) where {N,K,V} = new{N,K,V}(keys, vals)
end

SmallDict(d::AbstractSmallDict) = SmallDict(d.keys, d.vals)

SmallDict{N,K,V}() where {N,K,V} = SmallDict(SmallVector{N,K}(), SmallVector{N,V}())

@inline function keys_vals_unique(::Val{N}, ::Type{K}, ::Type{V}, itr) where {N,K,V}
    keys = MutableSmallVector{N,K}()
    vals = MutableSmallVector{N,V}()
    i = 0
    for ikv::Tuple{Int,Pair} in enumerate(itr)
        i, (key, val) = ikv
        i <= N || error("dictionary cannot have more than $N elements")
        unsafe_setindex!(keys, key, i)
        unsafe_setindex!(vals, val, i)
    end
    vals.n = keys.n = i
    keys, vals
end

function SmallDict{N,K,V}(itr; unique = false) where {N,K,V}
    if unique && isbitstype(Tuple{K,V})
        SmallDict(keys_vals_unique(Val(N), K, V, itr)...)
    elseif N <= 32 || !isbitstype(Tuple{K,V})
        foldl(push, itr; init = SmallDict{N,K,V}())
    else
        SmallDict(MutableSmallDict{N,K,V}(itr))   # allocates
    end
end

"""
    MutableSmallDict{N,K,V} <: AbstractSmallDict{N,K,V}

    MutableSmallDict{N,K,V}()
    MutableSmallDict{N,K,V}(itr; unique = false)
    MutableSmallDict{N,K,V}(key1 => val1, key2 => val2, ...; unique = false)

An dictionary with key type `K` and value type `V` that can store up to `N` entries.
The dictionary is mutable and implements Julia's dictionary interface.

If the key and value types are omitted, they will be inferred from the pairs or, if possible,
from the iterator. If `unique` is set to `true`, then the elements of `itr` are assumed to have
distinct keys.

See also [`AbstractSmallDict`](@ref), [`SmallDict`](@ref).

# Examples
```jldoctest
julia> d = MutableSmallDict{8}('a' => 0, 'b' => 1, 'c' => 4)
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
    keys::MutableSmallVector{N,K}
    vals::MutableSmallVector{N,V}
    MutableSmallDict{N,K,V}(keys::AbstractSmallVector{N,K}, vals::AbstractSmallVector{N,V}) where {N,K,V} = new{N,K,V}(keys, vals)
    MutableSmallDict(keys::AbstractSmallVector{N,K}, vals::AbstractSmallVector{N,V}) where {N,K,V} = new{N,K,V}(keys, vals)
end

MutableSmallDict(d::AbstractSmallDict) = MutableSmallDict(d.keys, d.vals)

MutableSmallDict{N,K,V}() where {N,K,V} = MutableSmallDict(MutableSmallVector{N,K}(), MutableSmallVector{N,V}())

function MutableSmallDict{N,K,V}(itr; unique = false) where {N,K,V}
    if unique
        MutableSmallDict(keys_vals_unique(Val(N), K, V, itr)...)
    else
        foldl(push!, itr; init = MutableSmallDict{N,K,V}())
    end
end

function (::Type{D})(itr::I; kw...) where {N, D <: AbstractSmallDict{N}, I}
    Base.IteratorEltype(I) isa Base.HasEltype || error("cannot determine element type")
    KV = element_type(I)
    D{fieldtypes(KV)...}(itr; kw...)
end

(::Type{D})(kv::Pair...; kw...) where D <: AbstractSmallDict = D(kv; kw...)

keys(d::AbstractSmallDict) = SmallVector(d.keys)

values(d::AbstractSmallDict) = SmallVector(d.vals)

capacity(::Type{<:AbstractSmallDict{N}}) where N = N

copy(d::SmallDict) = d
copy(d::MutableSmallDict) = MutableSmallDict(copy(d.keys), copy(d.vals))

length(d::AbstractSmallDict) = length(d.keys)

function iterate(d::AbstractSmallDict{N,K,V}, i = 1) where {N,K,V}
    i <= length(d) ? (@inbounds Pair{K,V}(d.keys[i], d.vals[i]), i+1) : nothing
end

@inline function token(d::AbstractSmallDict, key)
    findfirst(==(key), d.keys)
end

@inline function token(d::AbstractSmallDict{N,K}, key) where {N, K <: Union{Base.HWReal, Char}}
    i = findfirst(map(==(convert(K, key)), d.keys.b))  # TODO: implement elsewhere
    i === nothing || i > length(d) ? nothing : i
end

haskey(d::AbstractSmallDict, key) = token(d, key) !== nothing

function getindex(d::AbstractSmallDict, key)
    i = token(d, key)
    if i === nothing
        error("key not found")
    else
        @inbounds d.vals[i]
    end
end

function get(d::AbstractSmallDict, key, default)
    i = token(d, key)
    i === nothing ? default : @inbounds d.vals[i]
end

function getkey(d::AbstractSmallDict, key, default)
    i = token(d, key)
    i === nothing ? default : @inbounds d.keys[i]
end

@propagate_inbounds function push(d::AbstractSmallDict, (key, val)::Pair)
    i = token(d, key)
    if i === nothing
        keys = push(d.keys, key)
        vals = push(d.vals, val)
    else
        keys = @inbounds setindex(d.keys, key, i)
        vals = @inbounds setindex(d.vals, val, i)
    end
    SmallDict(keys, vals)
end

@propagate_inbounds function setindex(d::AbstractSmallDict{N,K,V}, val, key) where {N,K,V}
    push(d, key => val)
end

function delete(d::AbstractSmallDict, key)
    i = token(d, key)
    if i === nothing
        SmallDict(d)
    else
        @inbounds keys = deleteat(d.keys, i)
        @inbounds vals = deleteat(d.vals, i)
        SmallDict(keys, vals)
    end
end

@propagate_inbounds function pop(d::AbstractSmallDict)
    keys, _ = pop(d.keys)
    @inbounds vals, val = pop(d.vals)
    SmallDict(keys, vals), val
end

function pop(d::AbstractSmallDict, key)
    i = token(d, key)
    i === nothing && error("key not found")
    @inbounds keys, _ = popat(d.keys, i)
    @inbounds vals, val = popat(d.vals, i)
    SmallDict(keys, vals), val
end

function pop(d::AbstractSmallDict, key, default)
    i = token(d, key)
    i === nothing && return SmallDict(d), default
    @inbounds keys, _ = popat(d.keys, i)
    @inbounds vals, val = popat(d.vals, i)
    SmallDict(keys, vals), val
end

function setindex!(d::MutableSmallDict, val, key)
    i = token(d, key)
    if i === nothing
        push!(d.keys, key)
        @inbounds push!(d.vals, val)
    else
        @inbounds d.vals[i] = val
    end
    d
end

empty!(d::MutableSmallDict) = (empty!(d.keys); empty!(d.vals); d)

function delete!(d::MutableSmallDict, key)
    i = token(d, key)
    i === nothing ? d : (@inbounds deleteat!(d.keys, i), deleteat!(d.vals, i); d)
end

@propagate_inbounds function pop!(d::MutableSmallDict)
    pop!(d.keys)
    @inbounds pop!(d.vals)
end

function pop!(d::MutableSmallDict, key)
    i = token(d, key)
    i === nothing && error("key not found")
    @inbounds popat!(d.keys, i)
    @inbounds popat!(d.vals, i)
end

function pop!(d::MutableSmallDict, key, default)
    i = token(d, key)
    i === nothing && return default
    @inbounds popat!(d.keys, i)
    @inbounds popat!(d.vals, i)
end