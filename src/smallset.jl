#
# small sets
#

export AbstractSmallSet, SmallSet, MutableSmallSet, capacity,
    push, pop, delete

import Base: show, copy, length, iterate, in,
    push!, pop!, delete!, filter!, setdiff!

abstract type AbstractSmallSet{N,T} <: AbstractSet{T} end

struct SmallSet{N,T} <: AbstractSmallSet{N,T}
    d::SmallDict{N,T,Nothing}
    SmallSet(::Nothing, d::AbstractSmallDict{N,T,Nothing}) where {N,T} = new{N,T}(d)
end

_SmallSet(d) = SmallSet(nothing, d)

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

SmallSet(s::AbstractSmallSet) = _SmallSet(s.d)
MutableSmallSet(s::AbstractSmallSet) = _MutableSmallSet(s.d)

function show(io::IO, s::S) where {N, T, S <: AbstractSmallSet{N,T}}
    get(io, :compact, false) || haskey(io, :SHOWN_SET) || invoke(show, Tuple{IO,AbstractSet}, io, s)
    print(io, S <: SmallSet ? "SmallSet" : "MutableSmallSet")
    print(io, '{', N)
    isconcretetype(T) || get(io, :typeinfo, Any) == S || print(io, ", ", T)
    print(io, "}([")
    join(io, s, ", ")
    print(io, "])")
end

capacity(::Type{<:AbstractSmallSet{N}}) where N = N

copy(s::MutableSmallSet) = MutableSmallSet(nothing, copy(s.d))

length(s::AbstractSmallSet) = length(s.d)

iterate(s::AbstractSmallSet, state...) = iterate(s.d.keys, state...)

Base.hasfastin(::Type{S}) where S <: AbstractSmallSet = Base.hasfastin(fieldtype(S, :d))

in(x, s::AbstractSmallSet) = haskey(s.d, x)

function push(s::AbstractSmallSet, xs...)
    _SmallSet(push(s.d, map(x -> x => nothing, xs)...))
end

delete(s::AbstractSmallSet, x) = _SmallSet(delete(s.d, x))

function pop(s::AbstractSmallSet)
    d, kv = pop(s.d)
    _SmallSet(d), first(kv)
end

function pop(s::AbstractSmallSet, x)
    i = token(s.d, x)
    i === nothing && error("key not found")
    d, kv = delete_token(s.d, i)
    _SmallSet(d), first(kv)
end

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
