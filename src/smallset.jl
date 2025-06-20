#
# small sets
#

export AbstractSmallSet, SmallSet, MutableSmallSet, capacity,
    empty, push, pop, delete, sum_fast, extrema_fast

import Base: show, copy, length, iterate, values, in, empty!,
    push!, pop!, delete!, filter!, filter,
    union!, intersect!, setdiff!, symdiff!,
    union, intersect, setdiff, symdiff

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

function SmallSet{N,T}(itr; unique = itr isa Union{AbstractSet,OrdinalRange}) where {N,T}
    if unique
        keys = SmallVector{N,T}(itr)
        vals = SmallVector(default(Values{N,Nothing}), length(keys))
        d = SmallDict(keys, vals)
    elseif itr isa Tuple
        d = SmallDict{N,T,Nothing}(map(x -> x => nothing, itr))
    else
        d = SmallDict{N,T,Nothing}(x => nothing for x in itr)
    end
    _SmallSet(d)
end

SmallSet{N,T}(s::AbstractSmallSet; unique = false) where {N,T} =
    _SmallSet(SmallDict{N,T,Nothing}(s.d))

function MutableSmallSet{N,T}(itr; unique = itr isa Union{AbstractSet,OrdinalRange}) where {N,T}
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

SmallSet(s::AbstractSmallSet{N,T}) where {N,T} = SmallSet{N,T}(s)
MutableSmallSet(s::AbstractSmallSet{N,T}) where {N,T} = MutableSmallSet{N,T}(s)

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

copy(s::SmallSet) = s
copy(s::MutableSmallSet) = MutableSmallSet(s)

length(s::AbstractSmallSet) = length(s.d)

iterate(s::AbstractSmallSet, state...) = iterate(s.d.keys, state...)

"""
    values(s::AbstractSmallSet{N,T}) where {N,T} -> SmallVector{N,T}

Return the values of the set `s` as a `SmallVector`.
"""
values(s::AbstractSmallSet) = keys(s.d)

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

Base.copymutable(s::AbstractSmallSet) = MutableSmallSet(s)
Base.emptymutable(s::AbstractSmallSet{N,T}, ::Type{U} = T) where {N,T,U} = MutableSmallSet{N,U}()

"""
    push(s::AbstractSmallSet{N,T}, xs...) where {N,T} -> Tuple{SmallSet{N,T}, T}

Return the set that is obtained from `s` by adding the elements given as arguments.

See also `Base.push!`.
"""
function push(s::AbstractSmallSet, xs::Vararg{Any,M}) where M
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
    i === nothing && keyerror(x)
    d, kv = unsafe_pop(s.d, i)
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
    i === nothing && return SmallSet(s), default
    d, kv = unsafe_pop(s.d, i)
    _SmallSet(d), first(kv)
end

filter(f::F, s::AbstractSmallSet) where F = _SmallSet(filter(f∘first, s.d))

function replace(s::AbstractSmallSet, ps::Vararg{Pair,M}; kw...) where M
    qs = map(p -> (p[1] => nothing) => (p[2] => nothing), ps)
    _SmallSet(replace(s.d, qs...; kw...))
end

empty!(s::MutableSmallSet) = (@inline empty!(s.d); s)

function push!(s::MutableSmallSet, xs...)
    @inline push!(s.d, map(x -> x => nothing, xs)...)
    s
end

delete!(s::MutableSmallSet, x) = (@inline(delete!(s.d, x)); s)

pop!(s::MutableSmallSet) = first(pop!(s.d))

function pop!(s::MutableSmallSet, x)
    i = token(s.d, x)
    i === nothing && keyerror(x)
    first(unsafe_pop!(s.d, i))
end

function pop!(s::MutableSmallSet, x, default)
    i = token(s.d, x)
    i === nothing && return default
    first(unsafe_pop!(s.d, i))
end

filter!(f::F, s::MutableSmallSet) where F = (@inline filter!(f∘first, s.d); s)

function replace!(s::MutableSmallSet, ps::Vararg{Pair,M}; kw...) where M
    qs = map(p -> (p[1] => nothing) => (p[2] => nothing), ps)
    replace!(s.d, qs...; kw...)
    s
end

function smallset_union!(s::MutableSmallSet, t)
    for x in t
        @inline push!(s, x)
    end
    s
end

function smallset_intersect!(s::MutableSmallSet, t)
    if Base.hasfastin(t)
        @inline filter!(in(t), s)
    else
        u = copy(s)
        @inline empty!(s)
        for x in t
            x in u && @inline push!(s, x)
        end
    end
    s
end

function smallset_setdiff!(s::MutableSmallSet, t)
    if Base.hasfastin(t) && length(s) < 2*length(t)
        @inline filter!(!in(t), s)
    else
        for x in t
            @inline delete!(s, x)
        end
        s
    end
end

function smallset_symdiff!(s::MutableSmallSet, t)
    for x in t
        @inline(pop!(s, x, Void())) isa Void && @inline(push!(s, x))
    end
    s
end

for g in (:union, :intersect, :setdiff, :symdiff)
    g! = Symbol(g, '!')
    gsmall = Symbol("smallset_", g!)
    if g in (:intersect, :setdiff)
        def_u = :(u = MutableSmallSet(s))
    else
        def_u = :(U = promote_type(T, eltype(t)); u = MutableSmallSet{N,U}(s))
    end
    # we need both methods for g! to avoid method ambiguities
    @eval $g!(s::MutableSmallSet, t) = @inline $gsmall(s, t)
    @eval $g!(s::MutableSmallSet, t::AbstractSet) = @inline $gsmall(s, t)
    @eval function $g(s::AbstractSmallSet{N,T}, t) where {N,T}
        isbitstype(T) || error("not implemented") # TODO
        $def_u
        @inline $g!(u, t)
        SmallSet(u)
    end
end

for g in (:sum, :prod, :minimum, :maximum, :extrema)
    @eval $g(s::AbstractSmallSet;  kw...) = $g(values(s);  kw...)
    @eval $g(f::F, s::AbstractSmallSet;  kw...) where F = $g(f, values(s);  kw...)
end

"""
    sum_fast(s::AbstractSmallSet{N,T}) where {N,T}

Return the `@fastmath` sum of the elements of `s`.
Unlike for `sum`, the return value always is of the element type of `s`, even for small bit integers.

See also `Base.sum`, `Base.@fastmath`.
"""
sum_fast(s::AbstractSmallSet) = sum_fast(values(s))

"""
    extrema_fast(s::AbstractSmallSet; [init])

Return the `@fastmath` minimum and maximum of the elements of `s`.
The `init` keyword argument may not be used.

See also `Base.extrema`, `Base.@fastmath`.
"""
extrema_fast(s::AbstractSmallSet; kw...) = extrema_fast(values(s); kw...)

if VERSION >= v"1.11"

function Random.rand(rng::AbstractRNG, ::SamplerType{SmallSet{N,T}}) where {N,T}
    _SmallSet(rand(rng, SmallDict{N,T,Nothing}))
end

function Random.rand(rng::AbstractRNG, ::SamplerType{MutableSmallSet{N,T}}) where {N,T}
    _MutableSmallSet(rand(rng, MutableSmallDict{N,T,Nothing}))
end

end
