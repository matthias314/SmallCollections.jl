#
# small sets
#

export AbstractSmallSet, MutableSmallSet

import Base: copy, length, iterate, in, push!, pop!, delete!

abstract type AbstractSmallSet{N,T} <: AbstractSet{T} end

struct MutableSmallSet{N,T} <: AbstractSmallSet{N,T}
    d::MutableSmallDict{N,T,Nothing}
    MutableSmallSet(::Nothing, d::MutableSmallDict{N,T,Nothing}) where {N,T} = new{N,T}(d)
end

_MutableSmallSet(d) = MutableSmallSet(nothing, d)

function MutableSmallSet{N,T}(itr; unique = false) where {N,T}
    if unique
        keys = MutableSmallVector{N,T}(itr)
        vals = MutableSmallVector{N,Nothing}(undef, length(keys))
        d = MutableSmallDict(keys, vals)
    else
        d = MutableSmallDict{N,T,Nothing}(x => nothing for x in itr)
    end
    _MutableSmallSet(d)
end

function MutableSmallSet{N}(itr::I; kw...) where {N,I}
    Base.IteratorEltype(I) isa Base.HasEltype || error("cannot determine element type")
    T = element_type(I)
    MutableSmallSet{N,T}(itr; kw...)
end

copy(s::MutableSmallSet) = MutableSmallSet(nothing, copy(s.d))

length(s::AbstractSmallSet) = length(s.d)

iterate(s::AbstractSmallSet, state...) = iterate(s.d.keys, state...)

in(s::AbstractSmallSet, x) = haskey(s.d, x)

push!(s::MutableSmallSet, x) = (setindex!(s.d, nothing, x); s)

delete!(s::MutableSmallSet, x) = (delete!(s.d, x); s)

pop!(s::MutableSmallSet) = first(pop!(s.d))

function pop!(s::MutableSmallSet, x)
    i = token(s.d, x)
    i === nothing && error("key not found")
    unsafe_pop!(s.d, i)
    x
end

function pop!(s::MutableSmallSet, x, default)
    i = token(s.d, x)
    i === nothing && return default
    unsafe_pop!(s.d, i)
    x
end
