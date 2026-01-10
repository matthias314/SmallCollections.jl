#
# small dictionaries
#

export AbstractSmallDict, SmallDict, MutableSmallDict, capacity,
    setindex, push, delete, pop, invget,
    popmin, popmax, popmin!, popmax!

import Base: keys, values, copy, length, iterate, haskey,
    empty, getindex, get, getkey, setindex, filter, mergewith,
    setindex!, get!, empty!, delete!, pop!, filter!, mergewith!,
    replace!, push!, findmin, findmax, findall

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
    SmallDict{N,K,V}(key1 => val1, (key2, val2), ...; unique = false)

An immutable dictionary with key type `K` and value type `V` that can store up to `N` entries.
All entries come from the key-value iterator `itr` provided at construction time or from the
explicitly given pairs or tuples.

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

SmallDict(d::AbstractSmallDict{N,K,V}) where {N,K,V} = SmallDict{N,K,V}(d)

SmallDict{N,K,V}() where {N,K,V} = SmallDict(SmallVector{N,K}(), SmallVector{N,V}())

to_pair(kv::Pair) = kv
to_pair((k, v)::Tuple) = k => v

@inline function keys_vals_unique(::Val{N}, ::Type{K}, ::Type{V}, itr) where {N,K,V}
    keys = MutableSmallVector{N,K}()
    vals = MutableSmallVector{N,V}()
    i = 0
    for ikv::Tuple{Int,Pair} in enumerate(to_pair(kv) for kv in itr)
        i, (key, val) = ikv
        i <= N || error("dictionary cannot have more than $N elements")
        unsafe_setindex!(keys, key, i)
        unsafe_setindex!(vals, val, i)
    end
    vals.n = keys.n = i % SmallLength
    keys, vals
end

function SmallDict{N,K,V}(itr; unique = itr isa AbstractDict) where {N,K,V}
    if unique && isbitstype(Tuple{K,V})
        SmallDict(keys_vals_unique(Val(N), K, V, itr)...)
    elseif !isbitstype(Tuple{K,V})
        foldl(itr; init = SmallDict{N,K,V}()) do d, kv
            push(d, to_pair(kv))
        end::SmallDict{N,K,V}   # type annotation needed for inference
    else
        d = MutableSmallDict{N,K,V}()
        if itr isa Tuple
            @inline push!(d, map(to_pair, itr)...)
        else
            for p in itr
                @inline push!(d, to_pair(p))
            end
        end
        SmallDict(d)
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

MutableSmallDict(d::AbstractSmallDict{N,K,V}) where {N,K,V} = MutableSmallDict{N,K,V}(d)

MutableSmallDict{N,K,V}() where {N,K,V} = MutableSmallDict(SmallVector{N,K}(), SmallVector{N,V}())

function MutableSmallDict{N,K,V}(itr; unique = itr isa AbstractDict) where {N,K,V}
    if unique
        MutableSmallDict(keys_vals_unique(Val(N), K, V, itr)...)
    else
        foldl(itr; init = MutableSmallDict{N,K,V}()) do d, kv
            push!(d, to_pair(kv))
        end
    end
end

function MutableSmallDict{N,K,V}(d::AbstractSmallDict; unique = false) where {N,K,V}
    MutableSmallDict{N,K,V}(MutableSmallVector{N,K}(d.keys), MutableSmallVector{N,V}(d.vals))
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
copy(d::MutableSmallDict) = MutableSmallDict(d)

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
        keyerror(key)
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
    invget(d::AbstractSmallDict{N,K}, val) where {N,K} -> K

Return a key in `d` whose value is equal to `val` (in the sense of `isequal`).
If there is no such key, an error is raised.

This reverse lookup is as fast as "forward" lookup by keys.
The key returned is the first matching one in `keys(d)`.
"""
function invget(d::AbstractSmallDict, val)
    key = invget(d, val, Void())
    key isa Void ? error("value not found") : key
end

"""
    invget(d::AbstractSmallDict{N,K}, val, default::T) where {N,K,T} -> Union{K,T}

Return a key in `d` whose value is equal to `val` (in the sense of `isequal`).
If there is no such key, return `default`.

This reverse lookup is as fast as "forward" lookup by keys.
The key returned is the first matching one in `keys(d)`.
"""
function invget(d::AbstractSmallDict{N,K,V}, val, default) where {N,K,V}
    i = findfirst(isequal(val), d.vals)
    i === nothing ? default : @inbounds d.keys[i]
end

@inline unsafe_get(d::AbstractSmallDict, i::Int) = @inbounds d.keys[i] => d.vals[i]

for g in (:findmin, :findmax)
    @eval @propagate_inbounds $g(d::AbstractSmallDict) = $g(identity, d)
    @eval @propagate_inbounds function $g(f::F, d::AbstractSmallDict{N,K,V}; style = MapStyle(f, V)) where {F,N,K,V}
        v, i = $g(f, d.vals; style)
        @inbounds v, d.keys[i]
    end
end

"""
    push(d::AbstractSmallDict{N,K,V}, key1 => val1, key2 => val2, ...) where {N,K,V} -> Tuple{SmallDict{N,K,V}, V}

Return the dictionary that is obtained from `d` by adding the mappings given as arguments.

See also `Base.push!`, [`setindex`](@ref setindex(::AbstractSmallDict, ::Any, ::Any)).
"""
@propagate_inbounds function push(d::AbstractSmallDict{N,K,V}, kvs::Vararg{Pair,M}) where {N,K,V,M}
    if isbitstype(Tuple{K,V}) && N >= 8
        e = MutableSmallDict(d)
        @inline push!(e, kvs...)
        SmallDict(e)
    else
        foldl(kvs; init = SmallDict(d)) do d, (key, val)
            setindex(d, val, key)
        end
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
        vals = @inbounds push(d.vals, val)
    else
        keys = @inbounds setindex(d.keys, key, i)
        vals = @inbounds setindex(d.vals, val, i)
    end
    SmallDict(keys, vals)
end

"""
    empty(d::AbstractSmallDict{N,K,V}) where {N,K,V} -> AbstractSmallDict{N,K,V}
    empty(d::AbstractSmallDict{N,K,V}, W::Type) where {N,K,V,W} -> AbstractSmallDict{N,K,W}
    empty(d::AbstractSmallDict{N,K,V}, L::Type, W::Type) where {N,K,V,L,W} -> AbstractSmallDict{N,L,W}

Return an empty `AbstractSmallDict` with the same capacity as `d`,
and with `valtype` changed to `W` and `keytype` changed to `L` if so specified.
The resulting dictionary is mutable if and only if `d` is so.
"""
empty(::AbstractSmallDict),
empty(::AbstractSmallDict, ::Type),
empty(::AbstractSmallDict, ::Type, ::Type)

empty(d::SmallDict{N,K,V}, ::Type{W} = V) where {N,K,V,W} = SmallDict{N,K,W}()
empty(d::MutableSmallDict{N,K,V}, ::Type{W} = V) where {N,K,V,W} = MutableSmallDict{N,K,W}()
empty(d::SmallDict{N}, ::Type{L}, ::Type{W}) where {N,L,W} = SmallDict{N,L,W}()
empty(d::MutableSmallDict{N}, ::Type{L}, ::Type{W}) where {N,L,W} = MutableSmallDict{N,L,W}()

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
    pop(d::AbstractSmallDict{N,K,V}) where {N,K,V} -> Tuple{SmallDict{N,K,V}, Pair{<:K,<:V}}

Remove a mapping `key => val` from `d` and return the new dictionary together with the mapping.
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
function pop(d::AbstractSmallDict{N,K,V}, key) where {N,K,V}
    if isbitstype(Tuple{K,V})
        e = MutableSmallDict(d)
        val = @inline pop!(e, key)
        return SmallDict(e), val
    end
    i = token(d, key)
    i === nothing && keyerror(key)
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

"""
    popmin(d::AbstractSmallDict) -> Tuple{SmallDict{N,K,V}, Pair{<:K,<:V}}
    popmax(d::AbstractSmallDict) -> Tuple{SmallDict{N,K,V}, Pair{<:K,<:V}}

Find a key-values pair that realizes the minimum (or maximum) among the values
of the non-empty dictionary `d`. Return the pair together with a dictionary
obtained from `d` by removing that pair.

See also [`popmin!`](@ref), `Base.findmin`, `Base.findmax`.
"""
popmin, popmax

@propagate_inbounds popmin(d::AbstractSmallDict) = unsafe_pop(d, last(findmin(d.vals)))
@propagate_inbounds popmax(d::AbstractSmallDict) = unsafe_pop(d, last(findmax(d.vals)))

function filter(f, d::AbstractSmallDict{N,K,V}) where {N,K,V}
    if isbitstype(Tuple{K,V})
        e = MutableSmallDict(d)
        @inline filter!(f, e)
        return SmallDict(e)
    end
    keys = SmallVector{N,K}()
    vals = SmallVector{N,V}()
    for (k, v) in zip(d.keys, d.vals)
        f(Pair{K,V}(k, v))::Bool || continue
        keys = @inbounds push(keys, k)
        vals = @inbounds push(vals, v)
    end
    SmallDict(keys, vals)
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

@inline function setindex!(d::MutableSmallDict, val, key)
    i = token(d, key)
    if i === nothing
        @inline push!(d.keys, key)
        @inbounds push!(d.vals, val)
    else
        @inbounds d.vals[i] = val
    end
    d
end

push!(d::MutableSmallDict) = d
push!(d::MutableSmallDict, (key, val)::Pair) = @inline setindex!(d, val, key)
push!(d::MutableSmallDict, p::Pair, ps::Vararg{Pair,M}) where M = @inline push!(push!(d, p), ps...)

function get!(f::Base.Callable, d::MutableSmallDict{N,K,V}, key) where {N,K,V}
    i = token(d, key)
    if i === nothing
        val::V = f()   # we convert to V because get! for Dict does so
        push!(d.keys, key)
        @inbounds push!(d.vals, val)
        val
    else
        d.vals[i]
    end
end

empty!(d::MutableSmallDict) = (empty!(d.keys); empty!(d.vals); d)

@inline function unsafe_pop!(d::MutableSmallDict, i::Int)
    @inbounds key = pop!(d.keys)
    @inbounds val = pop!(d.vals)
    if i <= length(d)
        @inbounds key, _ = d.keys[i], unsafe_setindex!(d.keys, key, i)
        @inbounds val, _ = d.vals[i], unsafe_setindex!(d.vals, val, i)
    end
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
    i === nothing && keyerror(key)
    last(unsafe_pop!(d, i))
end

function pop!(d::MutableSmallDict, key, default)
    i = token(d, key)
    i === nothing && return default
    last(unsafe_pop!(d, i))
end

"""
    popmin!(d::MutableSmallDict) -> Pair{<:K,<:V}
    popmax!(d::MutableSmallDict) -> Pair{<:K,<:V}

Find a key-values pair that realizes the minimum (or maximum) among the values
of the non-empty dictionary `d`. Return that pair and delete it from `d`.

See also [`popmin`](@ref).
"""
popmin!, popmax!

@propagate_inbounds popmin!(d::MutableSmallDict) = unsafe_pop!(d, last(findmin(d.vals)))
@propagate_inbounds popmax!(d::MutableSmallDict) = unsafe_pop!(d, last(findmax(d.vals)))

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
    d.vals.n = d.keys.n = j % SmallLength
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

function smalldict_replace!(d, count, ps::Tuple{Pair})
    (oldkey, oldval), (newkey, newval) = only(ps)
    i = token(d, oldkey)
    @inbounds if count > 0 && i !== nothing && isequal(d.vals[i], oldval)
        j = token(d, newkey)
        if j === nothing
            d.keys[i] = newkey
            d.vals[i] = newval
        else
            d.vals[j] = newval
            unsafe_pop!(d, i)
        end
    end
    d
end

function smalldict_replace!(d0, count, ps::Tuple{Vararg{Pair}})
    d1 = empty(d0)
    for ((oldkey, oldval), (newkey, newval)) in ps
        i = token(d0, oldkey)
        if count > 0 && i !== nothing && isequal(@inbounds(d0.vals[i]), oldval)
            unsafe_pop!(d0, i)
            d1[newkey] = newval
            count -= one(count)
        end
    end
    @inline merge!(d0, d1)
end

function replace!(d::MutableSmallDict, ps::Vararg{Pair{<:Pair,<:Pair},M}; count::Integer = typemax(Int)) where M
    smalldict_replace!(d, count, ps)
end

function replace(d::AbstractSmallDict, ps::Vararg{Pair{<:Pair,<:Pair},M}; count::Integer = typemax(Int)) where M
    e = MutableSmallDict(d)
    @inline smalldict_replace!(e, count, ps)
    SmallDict(e)
end

findall(d::AbstractSmallDict) = findall(identity, d)

"""
    findall(f::Function, d::AbstractSmallDict{N,K}; [style::MapStyle]) where {N,K} -> SmallVector{N,K}

With an `AbstractSmallDict` `d` as second argument, this function accepts
the keyword argument `style`. If it equals `LazyStyle()`, then the
function `f` is only evaluated on the actual values of `d`. For any
other value of `style`, `f` is evaluated on `values(d)` as well as on
the default values used for padding this `SmallVector`. This is often faster for simple functions.

As discussed under `MapStyle`, the default value for `style` is based on a list
of known functions.

See also [`$(@__MODULE__).default`](@ref), [`$(@__MODULE__).MapStyle`](@ref).
"""
function findall(f::F, d::AbstractSmallDict{N,K}; kw...) where {F<:Function,N,K}
    @inline
    SmallVector{N,K}(@inbounds(d.keys[i]) for i in support(AssertBool(f), d.vals; kw...))
end

if VERSION >= v"1.11"

function Random.rand(rng::AbstractRNG, ::SamplerType{SmallDict{N,K,V}}) where {N,K,V}
    keys = SmallVector{N,K}()
    for _ in 1:rand(0:N)
        key = rand(K)
        if !(key in keys)
            keys = @inbounds push(keys, key)
        end
    end
    vals = smallvector_rand(rng, Val(N), V, length(keys))
    SmallDict(keys, vals)
end

function Random.rand(rng::AbstractRNG, ::SamplerType{MutableSmallDict{N,K,V}}) where {N,K,V}
    keys = MutableSmallVector{N,K}()
    for _ in 1:rand(0:N)
        key = rand(K)
        key in keys || @inbounds push!(keys, key)
    end
    vals = smallvector_rand(rng, Val(N), V, length(keys))
    MutableSmallDict(keys, vals)
end

end
