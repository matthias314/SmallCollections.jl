#
# small sets
#

export SmallSet, bits, delete, pop, push

using Base: hasfastin

import Base: show, ==, hash, copy, convert,
    isempty, in, first, last, iterate,
    length, issubset, maximum, minimum,
    union, intersect, setdiff, symdiff

"""
    SmallSet{U<:Unsigned} <: AbstractSet{Int}

    SmallSet{U}([iter])
    SmallSet([iter])

`SmallSet{U}` is an immutable set that can hold integers between `1` and the bit length of `U`.
Called without an argument, it returns an empty set. If `U` is omitted, then `UInt` is taken.

All non-mutating functions for sets are supported. The non-mutating analogs [`push`](@ref),
[`pop`](@ref) and [`delete`](@ref) of the corresponding `!`-functions are also provided.
"""
struct SmallSet{U<:Unsigned} <: AbstractSet{Int}
    mask::U
    SmallSet(::Nothing, mask::U) where U = new{U}(mask)
end

_SmallSet(mask) = SmallSet(nothing, mask)

function show(io::IO, s::SmallSet)
    print(io, "SmallSet([")
    join(io, s, ',')
    print(io, "])")
end

==(s::SmallSet, t::SmallSet) = s.mask == t.mask

copy(s::SmallSet) = s

"""
    bits(s::SmallSet{U}) where U -> U

Return the bit mask used internally to store the elements of the set `s`.

See also [`convert(::Type{SmallSet}, ::Integer)`](@ref).
"""
bits(s::SmallSet) = s.mask

"""
    capacity(::Type{<:SmallSet}) -> Int
    capacity(s::SmallSet) -> Int

Return the largest number that the given set or `SmallSet` type can store.
"""
capacity(::Type{<:SmallSet}),
capacity(::SmallSet)

capacity(::Type{SmallSet{U}}) where U = bitsize(U)
capacity(::Type{SmallSet}) = capacity(SmallSet{UInt})

"""
    fasthash(s::SmallSet [, h0::UInt]) -> UInt

Return a hash for `s` that can be computed fast. This hash is consistent across
all `SmallSet`s, but it is not compatible with the `hash` used for sets.

See also `Base.hash`.

# Examples
```jldoctest
julia> s = SmallSet(1:3);

julia> fasthash(s)
0x828a4cc485149963

julia> fasthash(s) == hash(s)
false

julia> t = SmallSet{UInt16}(s);

julia> fasthash(s) == fasthash(t)
true
```
"""
fasthash(s::SmallSet, h0::UInt) = hash(bits(s), h0)

"""
    convert(::Type{SmallSet{U}}, mask::Integer) where U -> SmallSet{U}
    convert(::Type{SmallSet}, mask::Integer) -> SmallSet{UInt}

Convert a bit mask to a `SmallSet` of the given type. This is the inverse operation to `bits`.

See also [`bits`](@ref).

# Examples
```jldoctest
julia> s = SmallSet{UInt16}([1, 5, 6]);

julia> u = bits(s)
0x0031

julia> convert(SmallSet, u)
SmallSet{UInt64} with 3 elements:
  1
  5
  6
```
"""
convert(::Type{SmallSet{U}}, ::Integer) where U <: Unsigned,
convert(::Type{SmallSet}, ::Integer)

convert(::Type{SmallSet{U}}, mask::Integer) where U = _SmallSet(U(mask))

convert(::Type{SmallSet}, mask::Integer) = convert(SmallSet{UInt}, mask)

@propagate_inbounds function _push(mask::U, iter) where U
    for n in iter
        @boundscheck if !isinteger(n) || n <= 0 || n > bitsize(U)
                error("SmallSet{$U} can only contain integers between 1 and $(bitsize(U))")
            end
        mask |= one(U) << (Int(n)-1)
    end
    _SmallSet(mask)
end

SmallSet(args...) = SmallSet{UInt}(args...)

SmallSet{U}(s::SmallSet) where U = _SmallSet(s.mask % U)

SmallSet{U}(ns::Real...) where U = SmallSet{U}(ns)

@propagate_inbounds SmallSet{U}(iter) where U = _push(zero(U), iter)

function SmallSet{U}(r::AbstractUnitRange{<:Integer}) where U
    r0, r1 = first(r), last(r)
    if r0 <= 0 || r1 > bitsize(U)
        error("SmallSet{$U} can only contain integers between 1 and $(bitsize(U))")
    end
    if r1 < r0
        _SmallSet(zero(U))
    else
        m = one(U) << (r1-r0+1) - one(U)
        _SmallSet(m << (r0-1))
    end
end

isempty(s::SmallSet) = iszero(bits(s))

length(s::SmallSet) = count_ones(bits(s))

function iterate(s::SmallSet, state = (s.mask, 0))
    mask, n = state
    if iszero(mask)
        return nothing
    else
        t = trailing_zeros(mask)+1
        n += t
        return (n, (mask >> t, n))
    end
end

@inline function first(s::SmallSet)
    @boundscheck isempty(s) && error("collection must be non-empty")
    trailing_zeros(bits(s))+1
end

@inline function last(s::SmallSet)
    @boundscheck isempty(s) && error("collection must be non-empty")
    top_set_bit(bits(s))
end

function minimum(s::SmallSet; init = missing)
    if !isempty(s)
        @inbounds first(s)
    elseif init !== missing
        init
    else
        error("collection must be non-empty unless `init` is given")
    end
end

function maximum(s::SmallSet; init = missing)
    if !isempty(s)
        @inbounds last(s)
    elseif init !== missing
        init
    else
        error("collection must be non-empty unless `init` is given")
    end
end

# hasfastin(::Type{<:SmallSet}) = true
# this is the default for AbstractSet

function in(n, s::SmallSet{U}) where U <: Unsigned
    if isinteger(n)
        n = Int(n)
        !iszero(s.mask & one(U) << (n-1))
    else
        false
    end
end

issubset(s::SmallSet, t::SmallSet) = isempty(setdiff(s, t))

"""
    push(s::S, xs...) where S <: SmallSet -> S

Return the `SmallSet` obtained from `s` by adding the other arguments `xs`.
"""
@propagate_inbounds push(s::SmallSet, ns...) = _push(s.mask, ns)

"""
    pop(s::S) where S <: SmallSet -> Tuple{S, Int}

Return the pair `(t, x)` where `x` is the smallest element from `s` and
`t` is the set `s` with `x` deleted. The set `s` must be non-empty.

See also `Base.pop!`.
"""
@inline function pop(s::SmallSet)
    @boundscheck isempty(s) && error("collection must be non-empty")
    n = last(s)
    delete(s, n), n
end

"""
    pop(s::S, x) where S <: SmallSet -> Tuple{S, Int}

Return the pair `(t, x)` where `t` is the set `s` with `x` deleted.
The set `s` must be non-empty.

See also `Base.pop!`.
"""
@inline function pop(s::SmallSet, n)
    @boundscheck n in s || error("set does not contain the element")
    delete(s, n), n
end

"""
    pop(s::S, x, default::T) where S <: SmallSet -> Tuple{S, Union{Int,T}}

If `s` contains `x`, return the pair `(t, x)` where `t` is the set `s` with `x` deleted.
Otherwise return `(s, default)`

See also `Base.pop!`.
"""
function pop(s::SmallSet, n, default)
    n in s ? (delete(s, n), Int(n)) : (s, default)
end

"""
    delete(s::S, x) where S <: SmallSet -> S

If `s` contains `x`, return the set obtained by deleting that element.
Otherwise return `s`.

See also `Base.delete!`.
"""
function delete(s::SmallSet{U}, n) where U
    if isinteger(n)
        m = one(U) << (Int(n)-1)
        _SmallSet(s.mask & ~m)
    else
        s
    end
end

union(s::SmallSet, t::SmallSet) = _SmallSet(s.mask | t.mask)

union(s::SmallSet, ts::SmallSet...) = foldl(union, ts; init = s)

intersect(s::SmallSet{U}, t::SmallSet) where U <: Unsigned = _SmallSet(s.mask & (t.mask % U))

function intersect(s::SmallSet{U}, t) where U <: Unsigned
    u = _SmallSet(zero(U))
    for n in (hasfastin(t) ? s : t)
        if n in (hasfastin(t) ? t : s)
            @inbounds u = push(u, n)
        end
    end
    u
end

intersect(s::SmallSet, ts...) = foldl(intersect, ts; init = s)

setdiff(s::SmallSet{U}, t::SmallSet) where U <: Unsigned = _SmallSet(s.mask & ~(t.mask % U))

function setdiff(s::SmallSet, t)
    if hasfastin(t)
        u = s
        for n in s
            if n in t
                u = delete(u, n)
            end
        end
        return u
    else
        foldl(delete, t; init = s)
    end
end

setdiff(s::SmallSet, ts...) = foldl(setdiff, ts; init = s)

symdiff(s::SmallSet, t::SmallSet) = _SmallSet(s.mask ⊻ t.mask)

symdiff(s::SmallSet, ts::SmallSet...) = foldl(symdiff, ts; init = s)
