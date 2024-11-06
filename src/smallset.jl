#
# small sets
#

export AbstractSmallSet, SmallSet, MutableSmallSet, capacity,
    empty, push, pop, delete

import Base: show, copy, length, iterate, in,
    push!, pop!, delete!, filter!, setdiff!

"""
    AbstractSmallSet{N,T} <: AbstractSet{T}

This is the supertype of `SmallSet{N,T}` and `MutableSmallSet{N,T}`.

See also [`SmallSet`](@ref), [`MutableSmallSet`](@ref).
"""
abstract type AbstractSmallSet{N,T} <: AbstractSet{T} end

"""
    SmallSet{N,T} <: AbstractSmallSet{N,T}

    SmallSet{N,T}()
    SmallSet{N,T}(itr; unique = itr isa AbstractSet)

An immutable set with element type `T` that can store up to `N` entries.
All entries come from the iterator `itr` provided at construction time.

If the element type is omitted, it will be inferred from the iterator, if possible.
If `unique` is set to `true`, then the elements of `itr` are assumed to be distinct.

See also [`AbstractSmallSet`](@ref), [`MutableSmallSet`](@ref).
"""
struct SmallSet{N,T} <: AbstractSmallSet{N,T}
    d::SmallDict{N,T,Nothing}
    SmallSet(::Nothing, d::AbstractSmallDict{N,T,Nothing}) where {N,T} = new{N,T}(d)
end

_SmallSet(d) = SmallSet(nothing, d)

"""
    MutableSmallSet{N,T} <: AbstractSmallSet{N,T}

    MutableSmallSet{N,T}()
    MutableSmallSet{N,T}(itr; unique = itr isa AbstractSet)

A set with element type `T` that can store up to `N` entries.
The set is mutable and implements Julia's set interface.

If the element type is omitted, it will be inferred from the iterator, if possible.
If `unique` is set to `true`, then the elements of `itr` are assumed to be distinct.

See also [`AbstractSmallSet`](@ref), [`SmallSet`](@ref).
"""
struct MutableSmallSet{N,T} <: AbstractSmallSet{N,T}
    d::MutableSmallDict{N,T,Nothing}
    MutableSmallSet(::Nothing, d::AbstractSmallDict{N,T,Nothing}) where {N,T} = new{N,T}(d)
end

_MutableSmallSet(d) = MutableSmallSet(nothing, d)

function SmallSet{N,T}(itr; unique = itr isa AbstractSet) where {N,T}
    if unique
        keys = SmallVector{N,T}(itr)
        vals = SmallVector(default(Values{N,Nothing}), length(keys))
        d = SmallDict(keys, vals)
    else
        d = SmallDict{N,T,Nothing}(x => nothing for x in itr)
    end
    _SmallSet(d)
end

SmallSet{N,T}(s::AbstractSmallSet; unique = false) where {N,T} =
    _SmallSet(SmallDict{N,T,Nothing}(s.d))

function MutableSmallSet{N,T}(itr; unique = itr isa AbstractSet) where {N,T}
    if unique
        keys = MutableSmallVector{N,T}(itr)
        vals = MutableSmallVector{N,Nothing}(undef, length(keys))
        d = MutableSmallDict(keys, vals)
    else
        d = MutableSmallDict{N,T,Nothing}(x => nothing for x in itr)
    end
    _MutableSmallSet(d)
end

MutableSmallSet{N,T}(s::AbstractSmallSet; unique = false) where {N,T} =
    _MutableSmallSet(MutableSmallDict{N,T,Nothing}(s.d))

function (::Type{S})(itr::I; kw...) where {N,S<:AbstractSmallSet{N},I}
    Base.IteratorEltype(I) isa Base.HasEltype || error("cannot determine element type")
    T = element_type(I)
    S{T}(itr; kw...)
end

(::Type{S})() where {N,T,S<:AbstractSmallSet{N,T}} = S((); unique = true)

SmallSet(s::AbstractSmallSet) = _SmallSet(s.d)
MutableSmallSet(s::AbstractSmallSet) = _MutableSmallSet(s.d)

function show(io::IO, s::S) where {N, T, S <: AbstractSmallSet{N,T}}
    if isempty(s) || get(io, :compact, false) || haskey(io, :SHOWN_SET)
        print(io, S <: SmallSet ? "SmallSet" : "MutableSmallSet")
        print(io, '{', N)
        if isempty(s)
            print(io, ", ", T, "}()")
        else
            isconcretetype(T) || get(io, :typeinfo, Any) == S || print(io, ", ", T)
            print(io, "}([")
            join(io, s, ", ")
            print(io, "])")
        end
    else
        invoke(show, Tuple{IO, AbstractSet}, io, s)
    end
end

"""
    capacity(::Type{<:AbstractSmallSet}) -> Int
    capacity(d::AbstractSmallSet) -> Int

Return the largest number of elements the given dictionary type can hold.
"""
capacity(::Type{<:AbstractSmallSet}),
capacity(::AbstractSmallSet)

capacity(::Type{<:AbstractSmallSet{N}}) where N = N

copy(s::MutableSmallSet) = MutableSmallSet(nothing, copy(s.d))

length(s::AbstractSmallSet) = length(s.d)

iterate(s::AbstractSmallSet, state...) = iterate(s.d.keys, state...)

Base.hasfastin(::Type{S}) where S <: AbstractSmallSet = Base.hasfastin(fieldtype(S, :d))

in(x, s::AbstractSmallSet) = haskey(s.d, x)

"""
    empty(d::AbstractSmallDict{N,K,V}) where {N,K,V,W} -> AbstractSmallVector{N,K,V}
    empty(d::AbstractSmallDict{N,K,V}, W::Type) where {N,K,V,W} -> AbstractSmallVector{N,K,W}
    empty(d::AbstractSmallDict{N,K,V}, L::Type, W::Type) where {N,K,V,L,W} -> AbstractSmallVector{N,L,W}

Return an empty `AbstractSmallDictionary` with the same capacity as `d`,
and with `valtype` changed to `W` and `keytype` changed to `L` if so specified.
The resulting dictionary is mutable if and only if `d` is so.
"""
empty(::AbstractSmallSet),
empty(::AbstractSmallSet, ::Type)

empty(s::SmallSet{N,T}, ::Type{U} = T) where {N,T,U} = SmallSet{N,U}()
empty(s::MutableSmallSet{N,T}, ::Type{U} = T) where {N,T,U} = MutableSmallSet{N,U}()

Base.emptymutable(s::AbstractSmallSet{N,T}, ::Type{U} = T) where {N,T,U} = MutableSmallSet{N,U}()

"""
    push(s::AbstractSmallSet{N,T}, xs...) where {N,T} -> Tuple{SmallSet{N,T}, T}

Return the set that is obtained from `s` by adding the elements given as arguments.

See also `Base.push!`.
"""
function push(s::AbstractSmallSet, xs...)
    _SmallSet(push(s.d, map(x -> x => nothing, xs)...))
end

"""
    delete(s::AbstractSmallSet{N,T}, x) where {N,T} -> SmallSet{N,T}

Remove the element `x` from `s` (if it exists) and return the new set.

See also `Base.delete!`, [`pop`](@ref pop(::AbstractSmallSet, ::Any)).
"""
delete(s::AbstractSmallSet, x) = _SmallSet(delete(s.d, x))

"""
    pop(s::AbstractSmallSet{N,T}) where {N,T} -> Tuple{SmallSet{N,T}, T}

Remove an element `x` from `s` and return the new set together with `x`.
The set `s` must not be empty.

See also `Base.pop!`.
"""
function pop(s::AbstractSmallSet)
    d, kv = pop(s.d)
    _SmallSet(d), first(kv)
end

"""
    pop(s::AbstractSmallSet{N,T}, x) where {N,T} -> Tuple{SmallSet{N,T}, T}

Remove the element `x` from `s` and return the new set together with the stored element equal to `x`.

See also `Base.pop!`, [`delete`](@ref delete(::AbstractSmallSet, ::Any)).
"""
function pop(s::AbstractSmallSet, x)
    i = token(s.d, x)
    i === nothing && error("key not found")
    d, kv = delete_token(s.d, i)
    _SmallSet(d), first(kv)
end

"""
    pop(s::AbstractSmallSet{N,T}, x, default::U) where {N,T,U} -> Tuple{SmallSet{N,T}, Union{T,U}}

If `s` has the element `x`, remove it and return the new set together with the stored element equal to `x`.
Otherwise return the tuple `(SmallSet(d), default)`.

See also `Base.pop!`.
"""
function pop(s::AbstractSmallSet, x, default)
    i = token(s.d, x)
    i === nothing && return default
    d, kv = delete_token(s.d, i)
    _SmallSet(d), first(kv)
end

function push!(s::MutableSmallSet, xs...)
    push!(s.d, map(x -> x => nothing, xs)...)
    s
end

delete!(s::MutableSmallSet, x) = (delete!(s.d, x); s)

pop!(s::MutableSmallSet) = first(pop!(s.d))

function pop!(s::MutableSmallSet, x)
    i = token(s.d, x)
    i === nothing && error("key not found")
    first(unsafe_pop!(s.d, i))
end

function pop!(s::MutableSmallSet, x, default)
    i = token(s.d, x)
    i === nothing && return default
    first(unsafe_pop!(s.d, i))
end

filter!(f, s::MutableSmallSet) = (filter!(f∘first, s.d); s)

setdiff!(s::MutableSmallSet, t) = _setdiff!(s, t)
setdiff!(s::MutableSmallSet, t::AbstractSet) = _setdiff!(s, t)

function _setdiff!(s::MutableSmallSet, t)
    if Base.hasfastin(t) && length(s) < 2*length(t)
        filter!(!in(t), s)
    else
        foldl(delete!, t; init = s)
    end
end
