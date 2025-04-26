#
# small sets
#

export SmallBitSet, bits, delete, pop, push, exchange

using Base: hasfastin

import Base: show, ==, hash, copy, convert,
    empty, isempty, in, first, last, iterate,
    length, issubset, ⊊, maximum, minimum, extrema,
    union, intersect, setdiff, symdiff, filter,
    count, any, all, replace

isinteger(x) = x isa Number && Base.isinteger(x)

"""
    SmallBitSet{U<:Unsigned} <: AbstractSet{Int}

    SmallBitSet{U}([iter])
    SmallBitSet([iter])

`SmallBitSet{U}` is an immutable set that can hold integers between `1` and the bit length of `U`.
Called without an argument, it returns an empty set. If `U` is omitted, then `UInt` is taken.

All non-mutating functions for sets are supported. The non-mutating analogs
[`push`](@ref push(::SmallBitSet, ::Vararg{Any})), [`pop`](@ref pop(::SmallBitSet)) and
[`delete`](@ref) of the corresponding `!`-functions are also provided.
"""
struct SmallBitSet{U<:Unsigned} <: AbstractSet{Int}
    mask::U
    global _SmallBitSet(mask::U) where U = new{U}(mask)
end

function show(io::IO, s::SmallBitSet{U}) where U
    print(io, "SmallBitSet")
    if bitsize(U) > bitsize(UInt) || get(io, :typeinfo, Any) != SmallBitSet{U}
        print(io, '{', U, '}')
    end
    print(io, "([")
    join(io, s, ", ")
    print(io, "])")
end

isfasttype(::Type{SmallBitSet{U}}) where U = isfasttype(U)

==(s::SmallBitSet, t::SmallBitSet) = s.mask == t.mask

copy(s::SmallBitSet) = s

"""
    bits(s::SmallBitSet{U}) where U -> U

Return the bit mask used internally to store the elements of the set `s`.

See also [`convert(::Type{SmallBitSet}, ::Integer)`](@ref).
"""
bits(s::SmallBitSet) = s.mask

"""
    capacity(::Type{<:SmallBitSet}) -> Int
    capacity(s::SmallBitSet) -> Int

Return the largest number that the given set or `SmallBitSet` type can store.
"""
capacity(::Type{<:SmallBitSet}),
capacity(::SmallBitSet)

capacity(::Type{SmallBitSet{U}}) where U = bitsize(U)
capacity(::Type{SmallBitSet}) = capacity(SmallBitSet{UInt})

"""
    fasthash(s::SmallBitSet [, h0::UInt]) -> UInt

Return a hash for `s` that can be computed fast. This hash is consistent across
all `SmallBitSet`s, but it is not compatible with the `hash` used for sets.

See also `Base.hash`.

# Examples
```jldoctest
julia> s = SmallBitSet(1:3);

julia> fasthash(s)
0x828a4cc485149963

julia> fasthash(s) == hash(s)
false

julia> t = SmallBitSet{UInt16}(s);

julia> fasthash(s) == fasthash(t)
true
```
"""
fasthash(s::SmallBitSet, h0::UInt) = hash(bits(s), h0)

"""
    convert(::Type{SmallBitSet{U}}, mask::Integer) where U -> SmallBitSet{U}
    convert(::Type{SmallBitSet}, mask::Integer) -> SmallBitSet{UInt}

Convert a bit mask to a `SmallBitSet` of the given type. This is the inverse operation to `bits`.

See also [`bits`](@ref).

# Examples
```jldoctest
julia> s = SmallBitSet{UInt16}([1, 5, 6]);

julia> u = bits(s)
0x0031

julia> convert(SmallBitSet, u)
SmallBitSet{UInt64} with 3 elements:
  1
  5
  6
```
"""
convert(::Type{SmallBitSet{U}}, ::Integer) where U <: Unsigned,
convert(::Type{SmallBitSet}, ::Integer)

convert(::Type{SmallBitSet{U}}, mask::Integer) where U = _SmallBitSet(U(mask))

convert(::Type{SmallBitSet}, mask::Integer) = convert(SmallBitSet{UInt}, mask)

@inline function _push(mask::U, iter) where U
    for n in iter
        @boundscheck if !isinteger(n) || n <= 0 || n > bitsize(U)
                error("SmallBitSet{$U} can only contain integers between 1 and $(bitsize(U))")
            end
        mask |= unsafe_shl(one(U), Integer(n-one(n)))
    end
    _SmallBitSet(mask)
end

@propagate_inbounds SmallBitSet(args...) = SmallBitSet{UInt}(args...)

@inline function SmallBitSet{U}(s::SmallBitSet) where U
    mask = s.mask % U
    @boundscheck if mask != s.mask
        error("SmallBitSet{$U} can only contain integers between 1 and $(bitsize(U))")
    end
    _SmallBitSet(mask)
end

SmallBitSet{U}() where U = _SmallBitSet(zero(U))

@propagate_inbounds SmallBitSet{U}(iter) where U = _push(zero(U), iter)

function SmallBitSet{U}(r::AbstractUnitRange{<:Integer}) where U
    r0, r1 = first(r), last(r)
    if r0 <= 0 || r1 > bitsize(U)
        error("SmallBitSet{$U} can only contain integers between 1 and $(bitsize(U))")
    end
    if r1 < r0
        _SmallBitSet(zero(U))
    else
        m = one(U) << (r1-r0+1) - one(U)
        _SmallBitSet(m << (r0-1))
    end
end

isempty(s::SmallBitSet) = iszero(bits(s))

"""
    empty(s::S) where S <: SmallBitSet -> S

Return an empty `SmallBitSet` of the same type as `s`.
"""
empty(s::SmallBitSet)

empty(s::S) where S <: SmallBitSet = S()

default(::Type{S}) where S <: SmallBitSet = S()

length(s::SmallBitSet) = count_ones(bits(s))

# from https://discourse.julialang.org/t/faster-way-to-find-all-bit-arrays-of-weight-n/113658/12
iterate(s::SmallBitSet, m = bits(s)) =
    iszero(m) ? nothing : (trailing_zeros(m)+1, blsr(m))

@inline function first(s::SmallBitSet)
    @boundscheck isempty(s) && error("collection must be non-empty")
    trailing_zeros(bits(s))+1
end

@inline function last(s::SmallBitSet)
    @boundscheck isempty(s) && error("collection must be non-empty")
    top_set_bit(bits(s))
end

function minimum(s::SmallBitSet; init = missing)
    if !isempty(s)
        @inbounds first(s)
    elseif init !== missing
        init
    else
        error("collection must be non-empty unless `init` is given")
    end
end

function maximum(s::SmallBitSet; init = missing)
    if !isempty(s)
        @inbounds last(s)
    elseif init !== missing
        init
    else
        error("collection must be non-empty unless `init` is given")
    end
end

extrema(v::SmallBitSet; init::Tuple{Any,Any} = (missing, missing)) =
    (minimum(v; init = init[1]), maximum(v; init = init[2]))

# hasfastin(::Type{<:SmallBitSet}) = true
# this is the default for AbstractSet

function in(n, s::SmallBitSet{U}) where U <: Unsigned
    isinteger(n) && 1 <= n <= bitsize(U) && !iszero(s.mask & unsafe_shl(one(U), Int(n)-1))
end

issubset(s::SmallBitSet, t::SmallBitSet) = isempty(setdiff(s, t))

⊊(s::SmallBitSet, t::SmallBitSet) = issubset(s, t) && s != t

"""
    push(s::S, xs...) where S <: SmallBitSet -> S

Return the `SmallBitSet` obtained from `s` by adding the other arguments `xs`.

See also `Base.push!`, `BangBang.push!!`.
"""
@propagate_inbounds push(s::SmallBitSet, ns...) = _push(s.mask, ns)

"""
    pop(s::S) where S <: SmallBitSet -> Tuple{S, Int}

Return the pair `(t, x)` where `x` is the smallest element from `s` and
`t` is the set `s` with `x` deleted. The set `s` must be non-empty.

See also `Base.pop!`, `BangBang.pop!!`.
"""
@inline function pop(s::SmallBitSet)
    @boundscheck isempty(s) && error("collection must be non-empty")
    n = last(s)
    delete(s, n), n
end

"""
    pop(s::S, x) where S <: SmallBitSet -> Tuple{S, Int}

Return the pair `(t, x)` where `t` is the set `s` with `x` deleted.
The set `s` must be non-empty.

See also `Base.pop!`, `BangBang.pop!!`.
"""
@inline function pop(s::SmallBitSet, n)
    @boundscheck n in s || error("set does not contain the element")
    delete(s, n), n
end

"""
    pop(s::S, x, default::T) where S <: SmallBitSet -> Tuple{S, Union{Int,T}}

If `s` contains `x`, return the pair `(t, x)` where `t` is the set `s` with `x` deleted.
Otherwise return `(s, default)`

See also `Base.pop!`, `BangBang.pop!!`.
"""
function pop(s::SmallBitSet, n, default)
    n in s ? (delete(s, n), Int(n)) : (s, default)
end

"""
    delete(s::S, x) where S <: SmallBitSet -> S

If `s` contains `x`, return the set obtained by deleting that element.
Otherwise return `s`.

See also `Base.delete!`, `BangBang.delete!!`.
"""
function delete(s::SmallBitSet{U}, n) where U
    if isinteger(n)
        m = one(U) << (Int(n)-1)
        _SmallBitSet(s.mask & ~m)
    else
        s
    end
end

@inline function replace(s::SmallBitSet{U}, ps::Vararg{Pair,N}) where {U,N}
    @boundscheck all(ps) do p
        p[1] isa Integer && p[2] isa Integer && 1 <= minimum(p) && maximum(p) <= bitsize(U)
    end || error("SmallBitSet{$U} can only contain integers between 1 and $(bitsize(U))")

    v, u = foldl(ps; init = (bits(s), zero(U))) do (v, u), p
        m = v & unsafe_shl(U(1), p[1]-1)
        v & ~m, u | bitrotate(m, p[2]-p[1])
    end
    convert(SmallBitSet{U}, v | u)
end

"""
    exchange(s::S, i::Integer, j::Integer) where S <: SmallBitSet -> S

Return the set `s` with the element `i`, if present, replaced by `j` and vice versa.
If `i` equals `j`, then the set is not modified.

This function is faster than the equivalent `replace(s, i => j, j => i)`.

See also `Base.replace`.

# Examples
```jldoctest
julia> s = SmallBitSet((1, 2)); exchange(s, 1, 2)
SmallBitSet{UInt64} with 2 elements:
  1
  2

julia> s = SmallBitSet((1, 2)); exchange(s, 2, 3)
SmallBitSet{UInt64} with 2 elements:
  1
  3

julia> s = SmallBitSet((1, 2)); exchange(s, 3, 4)
SmallBitSet{UInt64} with 2 elements:
  1
  2

julia> s = SmallBitSet((1, 2)); exchange(s, 1, 1)
SmallBitSet{UInt64} with 2 elements:
  1
  2
```
"""
@inline function exchange(s::SmallBitSet{U}, i::Integer, j::Integer) where U
    @boundscheck (1 <= i <= bitsize(U) && 1 <= j <= bitsize(U)) ||
        error("SmallBitSet{$U} can only contain integers between 1 and $(bitsize(U))")
    t = unsafe_shl(one(U), i-1) ⊻ unsafe_shl(one(U), j-1) # xor needed for the case i == j
    m = bits(s)
    convert(SmallBitSet{U}, ifelse(iszero(m & t) || m & t == t, m, m ⊻ t))
end

"""
    any(f::Function, s::SmallBitSet{U}; [style::MapStyle]) where U
    all(f::Function, s::SmallBitSet{U}; [style::MapStyle]) where U
    count(f, s::SmallBitSet{U}; init = 0, [style::MapStyle]) where U
    filter(f, s::SmallBitSet{U}; [style::MapStyle]) where U

With a `SmallBitSet` `s` as second argument, these functions accept
the additional keyword argument `style`. If it equals `LazyStyle()`, then the
function `f` is only evaluated for elements of `s`. For any
other value of `style`, `f` is evaluated on all numbers between `1` and the
bit size of `U`. This is often faster for simple functions.

As discussed under `MapStyle`, the default value for `style` is based on a list
of known functions.

See also [`$(@__MODULE__).MapStyle`](@ref).
"""
any(::Function, ::SmallBitSet),
all(::Function, ::SmallBitSet),
count(::Any, ::SmallBitSet),
filter(::Any, ::SmallBitSet)

filter(f, s::SmallBitSet; style::MapStyle = MapStyle(f, Int)) = smallbitset_filter(style, f, s)

function smallbitset_filter(::MapStyle, f::F, s::SmallBitSet{U}) where {F,U}
    N = bitsize(U)
    v = map(f, FixedVector{N}(1:N))
    eltype(v) == Bool || error("given function must return Bool values")
    _SmallBitSet((bits(v) % U) & bits(s))
end

function smallbitset_filter(::LazyStyle, f::F, s::SmallBitSet) where F
    m = bits(s)
    q = zero(m)
    while !iszero(m)
        p = blsr(m)
        n = trailing_zeros(m)+1
        if f(n)
            q |= m ⊻ p
        end
        m = p
    end
    _SmallBitSet(q)
end

function any(f::F, s::SmallBitSet; style::MapStyle = MapStyle(f, Int)) where F <: Function
    if style isa LazyStyle
        invoke(any, Tuple{F, AbstractSet}, f, s)
    else
        !isempty(filter(f, s; style))
    end
end

function all(f::F, s::SmallBitSet; style::MapStyle = MapStyle(f, Int)) where F <: Function
    if style isa LazyStyle
        invoke(all, Tuple{F, AbstractSet}, f, s)
    else
        filter(f, s; style) == s
    end
end

count(f, s::SmallBitSet; init = 0, style::MapStyle = MapStyle(f, Int)) = smallbitset_count(style, f, s, init)

smallbitset_count(::LazyStyle, f::F, s, init) where F = invoke(count, Tuple{Any, AbstractSet}, f, s; init)

smallbitset_count(::MapStyle, f::F, s, init::T) where {F,T} = init + (length(filter(f, s)) % T)

union(s::SmallBitSet, t::SmallBitSet) = _SmallBitSet(s.mask | t.mask)

union(s::SmallBitSet, ts::SmallBitSet...) = foldl(union, ts; init = s)

intersect(s::SmallBitSet{U}, t::SmallBitSet) where U <: Unsigned = _SmallBitSet(s.mask & (t.mask % U))

function intersect(s::SmallBitSet{U}, t) where U <: Unsigned
    u = _SmallBitSet(zero(U))
    for n in (hasfastin(t) ? s : t)
        if n in (hasfastin(t) ? t : s)
            @inbounds u = push(u, n)
        end
    end
    u
end

intersect(s::SmallBitSet, ts...) = foldl(intersect, ts; init = s)

setdiff(s::SmallBitSet{U}, t::SmallBitSet) where U <: Unsigned = _SmallBitSet(s.mask & ~(t.mask % U))

function setdiff(s::SmallBitSet, t)
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

setdiff(s::SmallBitSet, ts...) = foldl(setdiff, ts; init = s)

symdiff(s::SmallBitSet, t::SmallBitSet) = _SmallBitSet(s.mask ⊻ t.mask)

symdiff(s::SmallBitSet, ts::SmallBitSet...) = foldl(symdiff, ts; init = s)
