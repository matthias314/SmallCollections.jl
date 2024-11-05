#
# small dictionaries
#

export AbstractSmallDict, SmallDict, MutableSmallDict, capacity,
    setindex, push, delete, pop

import Base: keys, values, copy, length, iterate, haskey, getindex, get, getkey,
    setindex, mergewith, setindex!, empty!, delete!, pop!, filter!, mergewith!

"""
    AbstractSmallDict{N,K,V} <: AbstractDict{K,V}

This is the supertype of `SmallDict{N,K,V}` and `MutableSmallDict{N,K,V}`.

See also [`SmallDict`](@ref), [`MutableSmallDict`](@ref).
"""
abstract type AbstractSmallDict{N,K,V} <: AbstractDict{K,V} end

"""
    SmallDict{N,K,V} <: AbstractSmallDict{N,K,V}

    SmallDict{N,K,V}()
    SmallDict{N,K,V}(itr; unique = itr isa AbstractDict)
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
    SmallDict{N,K,V}(keys::AbstractSmallVector, vals::AbstractSmallVector) where {N,K,V} = new{N,K,V}(keys, vals)
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

function SmallDict{N,K,V}(itr; unique = itr isa AbstractDict) where {N,K,V}
    if unique && isbitstype(Tuple{K,V})
        SmallDict(keys_vals_unique(Val(N), K, V, itr)...)
    elseif N <= 32 || !isbitstype(Tuple{K,V})
        foldl(push, itr; init = SmallDict{N,K,V}())
    else
        SmallDict(MutableSmallDict{N,K,V}(itr))   # allocates
    end
end

function SmallDict{N,K,V}(d::AbstractSmallDict; unique = false) where {N,K,V}
    SmallDict{N,K,V}(d.keys, d.vals)
end

"""
    MutableSmallDict{N,K,V} <: AbstractSmallDict{N,K,V}

    MutableSmallDict{N,K,V}()
    MutableSmallDict{N,K,V}(itr; unique = itr isa AbstractDict)
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
    MutableSmallDict{N,K,V}(keys::AbstractSmallVector, vals::AbstractSmallVector) where {N,K,V} = new{N,K,V}(keys, vals)
    MutableSmallDict(keys::AbstractSmallVector{N,K}, vals::AbstractSmallVector{N,V}) where {N,K,V} = new{N,K,V}(keys, vals)
end

MutableSmallDict(d::AbstractSmallDict) = MutableSmallDict(d.keys, d.vals)

MutableSmallDict{N,K,V}() where {N,K,V} = MutableSmallDict(MutableSmallVector{N,K}(), MutableSmallVector{N,V}())

function MutableSmallDict{N,K,V}(itr; unique = itr isa AbstractDict) where {N,K,V}
    if unique
        MutableSmallDict(keys_vals_unique(Val(N), K, V, itr)...)
    else
        foldl(push!, itr; init = MutableSmallDict{N,K,V}())
    end
end

function MutableSmallDict{N,K,V}(d::AbstractSmallDict; unique = false) where {N,K,V}
    MutableSmallDict{N,K,V}(d.keys, d.vals)
end

function (::Type{D})(itr::I; kw...) where {N, D <: AbstractSmallDict{N}, I}
    Base.IteratorEltype(I) isa Base.HasEltype || error("cannot determine element type")
    KV = element_type(I)
    D{fieldtypes(KV)...}(itr; kw...)
end

SmallDict{N,K,V}(kvs::Pair...; kw...) where {N,K,V} = SmallDict{N,K,V}(kvs; kw...)
MutableSmallDict{N,K,V}(kvs::Pair...; kw...) where {N,K,V} = MutableSmallDict{N,K,V}(kvs; kw...)
(::Type{D})(kvs::Pair...; kw...) where {N, D <: AbstractSmallDict{N}} = D(kvs; kw...)

keys(d::AbstractSmallDict) = SmallVector(d.keys)

values(d::AbstractSmallDict) = SmallVector(d.vals)

"""
    capacity(::Type{<:AbstractSmallDict}) -> Int
    capacity(d::AbstractSmallDict) -> Int

Return the largest number of elements the given dictionary type can hold.
"""
capacity(::Type{<:AbstractSmallDict}),
capacity(::AbstractSmallDict)

capacity(::Type{<:AbstractSmallDict{N}}) where N = N

copy(d::SmallDict) = d
copy(d::MutableSmallDict) = MutableSmallDict(copy(d.keys), copy(d.vals))

length(d::AbstractSmallDict) = length(d.keys)

function iterate(d::AbstractSmallDict{N,K,V}, i = 1) where {N,K,V}
    i <= length(d) ? (@inbounds Pair{K,V}(d.keys[i], d.vals[i]), i+1) : nothing
end

@inline token(d::AbstractSmallDict, key) = findfirst(isequal(key), d.keys)

haskey(d::AbstractSmallDict, key) = token(d, key) !== nothing

Base.hasfastin(::Type{D}) where D <: AbstractSmallDict = Base.hasfastin(fieldtype(D, :keys))

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

"""
    push(d::AbstractSmallDict{N,K,V}, key1 => val1, key2 => val2, ...) where {N,K,V} -> Tuple{SmallDict{N,K,V}, V}

Return the dictionary that is obtained from `d` by adding the mappings given as arguments.

See also `Base.push!`, [`setindex`](@ref setindex(::AbstractSmallDict, ::Any, ::Any)).
"""
@propagate_inbounds function push(d::AbstractSmallDict, kvs::Pair...)
    foldl(kvs; init = d) do d, (key, val)
        setindex(d, val, key)
    end
end

"""
    setindex(d::AbstractSmallDict{N,K,V}, val, key) where {N,K,V} -> Tuple{SmallDict{N,K,V}, V}

Return the dictionary that is obtained from `d` by adding the mapping `key => val`.

See also `Base.setindex!`, [`push`](@ref push(::AbstractSmallDict, ::Pair)).
"""
@propagate_inbounds function setindex(d::AbstractSmallDict, val, key)
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

@inline function unsafe_pop(d::AbstractSmallDict, i::Int)
    @inbounds keys, key = popat(d.keys, i)
    @inbounds vals, val = popat(d.vals, i)
    SmallDict(keys, vals), key => val
end

"""
    delete(d::AbstractSmallDict{N,K,V}, key) where {N,K,V} -> SmallDict{N,K,V}

Remove the mapping for `key` from `d` (if it exists) and return the new dictionary.

See also `Base.delete!`, [`pop`](@ref pop(::AbstractSmallDict, ::Any)).
"""
function delete(d::AbstractSmallDict, key)
    i = token(d, key)
    i === nothing ? SmallDict(d) : first(unsafe_pop(d, i))
end

"""
    pop(d::AbstractSmallDict{N,K,V}) where {N,K,V} -> Tuple{SmallDict{N,K,V}, V}

Remove a mapping `key => val` from `d` and return the new dictionary together with `val`.
The dictionary `d` must not be empty.

See also `Base.pop!`.
"""
@propagate_inbounds function pop(d::AbstractSmallDict)
    keys, key = pop(d.keys)
    @inbounds vals, val = pop(d.vals)
    SmallDict(keys, vals), key => val
end

"""
    pop(d::AbstractSmallDict{N,K,V}, key) where {N,K,V} -> Tuple{SmallDict{N,K,V}, V}

Remove the mapping for `key` from `d` and return the new dictionary together with the value `d[key]`.

See also `Base.pop!`, [`delete`](@ref delete(::AbstractSmallDict, ::Any)).
"""
function pop(d::AbstractSmallDict, key)
    i = token(d, key)
    i === nothing && error("key not found")
    e, kv = unsafe_pop(d, i)
    e, last(kv)
end

"""
    pop(d::AbstractSmallDict{N,K,V}, key, default::U) where {N,K,V,U} -> Tuple{SmallDict{N,K,V}, Union{V,U}}

If `d` has the key `key`, remove it and return the new dictionary together with `d[key]`.
Otherwise return the tuple `(SmallDict(d), default)`.

See also `Base.pop!`.
"""
function pop(d::AbstractSmallDict, key, default)
    i = token(d, key)
    i === nothing && return SmallDict(d), default
    e, kv = unsafe_pop(d, i)
    e, last(kv)
end

function mergewith(op, d::AbstractSmallDict{N,K,V}, e::AbstractDict) where {N,K,V}
    foldl(e; init = SmallDict(d)) do d, (key, val)
        i = token(d, key)
        newval = i === nothing ? val : op(@inbounds(d.vals[i]), val)
        setindex(d, newval, key)
    end::SmallDict{N,K,V}
end

function mergewith(op, d::AbstractSmallDict, es::AbstractDict...)
    foldl((d, e) -> mergewith(op, d, e), es; init = SmallDict(d))
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

@inline function unsafe_pop!(d::MutableSmallDict, i::Int)
    @inbounds key = d.keys[i]
    @inbounds unsafe_setindex!(d.keys, pop!(d.keys), i)
    @inbounds val = d.vals[i]
    @inbounds unsafe_setindex!(d.vals, pop!(d.vals), i)
    key => val
end

function delete!(d::MutableSmallDict, key)
    i = token(d, key)
    i === nothing || unsafe_pop!(d, i)
    d
end

@propagate_inbounds function pop!(d::MutableSmallDict)
    key = pop!(d.keys)
    val = @inbounds pop!(d.vals)
    key => val
end

function pop!(d::MutableSmallDict, key)
    i = token(d, key)
    i === nothing && error("key not found")
    last(unsafe_pop!(d, i))
end

function pop!(d::MutableSmallDict, key, default)
    i = token(d, key)
    i === nothing && return default
    last(unsafe_pop!(d, i))
end

function filter!(f, d::MutableSmallDict{N,K,V}) where {N,K,V}
    j = 0
    n = length(d)
    for i in 1:n
        key, val = @inbounds d.keys[i], d.vals[i]
        f(key => val) || continue
        j += 1
        @inbounds d.keys[j], d.vals[j] = key, val
    end
    for i in j+1:n
        @inbounds d.keys[i], d.vals[i] = default(K), default(V)
    end
    d.vals.n = d.keys.n = j
    d
end

function mergewith!(op, d::MutableSmallDict, e::AbstractDict)
    for (key, val) in e
        i = token(d, key)
        if i === nothing
            d[key] = val
            # push!(d.keys, key)
            # @inbounds push!(d.vals, val)
        else
            @inbounds d.vals[i] = op(d.vals[i], val)
        end
    end
    d
end
