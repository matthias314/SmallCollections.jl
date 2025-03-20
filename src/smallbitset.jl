#
# small sets
#

export SmallBitSet, bits, delete, pop, push, exchange

using Base: hasfastin

import Base: show, ==, hash, copy, convert,
    empty, isempty, in, first, last, iterate,
    length, issubset, maximum, minimum, extrema,
    union, intersect, setdiff, symdiff, filter

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
    if isinteger(n)
        n = Int(n)
        !iszero(s.mask & one(U) << (n-1))
    else
        false
    end
end

issubset(s::SmallBitSet, t::SmallBitSet) = isempty(setdiff(s, t))

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

"""
    exchange(s::S, i::Integer, j::Integer) where S <: SmallBitSet -> S

Return the set `s` with the element `i`, if present, replaced by `j` and vice versa.
If `i` equals `j`, then the set is not modified.

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

function filter(f::F, s::SmallBitSet) where F
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

#
# subset iterators
#

export compositions, subsets, shuffles, shuffle_signbit

using Base: Generator
import Base: eltype, length, size, IndexStyle, getindex

struct Shuffles{N,S}
    set::S
    ks::NTuple{N,Int}
end

"""
    shuffles(s::S, ks::Vararg{Integer,N}) where {S <: SmallBitSet, N}
    shuffles(ks::Vararg{Integer,N}) where N

In the first form, return an iterator that yields all `ks`-compositions of the set `s`
together with the sign of the permutation that puts the elements back into an increasing order.
See `compositions` and `shuffle_signbit` for details.
The iterator returns tuples `(t, s)`, where `t` is of type `NTuple{N, S}`
and the sign bit `s` is of type `Bool` where `false` means `+1` and `true` means `-1`.
The partition sizes in `ks` must be non-negative and add up to `length(s)`.

In the second form the set `s` is taken to be `SmallBitSet(1:sum(ks))`.

See also [`compositions`](@ref), [`shuffle_signbit`](@ref).

# Examples
```jldoctest
julia> collect(shuffles(SmallBitSet([2, 4, 5]), 1, 2))
3-element Vector{Tuple{Tuple{SmallBitSet{UInt64}, SmallBitSet{UInt64}}, Bool}}:
 ((SmallBitSet([2]), SmallBitSet([4, 5])), 0)
 ((SmallBitSet([4]), SmallBitSet([2, 5])), 1)
 ((SmallBitSet([5]), SmallBitSet([2, 4])), 0)

julia> all(s == shuffle_signbit(a, b) for ((a, b), s) in shuffles(1, 2))
true
```
"""
function shuffles(ks::Integer...)
    any(signbit, ks) && error("part sizes must be non-negative")
    sum(ks; init = 0) <= bitsize(UInt) || error("at most $(bitsize(UInt)) elements supported")
    Shuffles(missing, ks)
end,
function shuffles(s::SmallBitSet, ks::Integer...)
    sum(ks; init = 0) == length(s) || error("part lengths must add up to size of the set")
    any(signbit, ks) && error("part sizes must be non-negative")
    Shuffles(s, ks)
end

eltype(sh::Shuffles{N,Missing}) where N = Tuple{NTuple{N,SmallBitSet{UInt}}, Bool}
eltype(sh::Shuffles{N,S}) where {N, S <: SmallBitSet} = Tuple{NTuple{N,S}, Bool}

length(sh::Shuffles{0}) = 1

function length(sh::Shuffles{N}) where N
    foldl(sh.ks[2:end]; init = (1, sh.ks[1])) do (p, k), l
        p*binomial(k+l, k), k+l
    end |> first
end

iterate(sh::Shuffles{0}) = ((), false), nothing
iterate(sh::Shuffles{0}, _) = nothing

iterate(sh::Shuffles{1}) = ((sh.set,), false), nothing
iterate(sh::Shuffles{1,Missing}) = ((SmallBitSet(1:sh.ks[1]),), false), nothing
iterate(sh::Shuffles{1}, _) = nothing

@inline iterate(sh::Shuffles{2}) = any(signbit, sh.ks) ? nothing : _iterate(sh)

@inline function _iterate(sh::Shuffles{2,S}; signint = UInt(0)) where S
    k, l = sh.ks
    U = S == Missing ? UInt : typeof(bits(sh.set))
    mask = U(1) << k - U(1)
    lastmask = mask << l

    set = S == Missing ? SmallBitSet{U}(1:k+l) : sh.set   # TODO: is SmallBitSet{U}(...) too slow?
    part1 = _SmallBitSet(S == Missing ? mask : pdep(mask, bits(set)))
    part2 = symdiff(part1, set)
    signbit = isodd(signint)
    state = (; mask, lastmask, signint, set, part2)
    ((part1, part2), signbit), (state,)
end

@inline function iterate(sh::Shuffles{2,S}, (state,)) where S
    (; mask, lastmask, signint, set) = state

    # see also https://graphics.stanford.edu/~seander/bithacks.html#NextBitPermutation
    # and https://discourse.julialang.org/t/faster-way-to-find-all-bit-arrays-of-weight-n/113658/12
    mask == lastmask && return nothing
    p = mask + blsi(mask)
    t = trailing_zeros(mask)
    q = unsafe_lshr(mask ⊻ p, t) >>> 2
    # q = unsafe_lshr(blsmsk(p), t) >>> 2
    # t+2 can be the bit size of mask, so we can't use unsafe_lshr with t+2
    mask = p | q
    signint ⊻= ~(t & count_ones(q))

    part1 = _SmallBitSet(S == Missing ? mask : pdep(mask, bits(set)))
    part2 = symdiff(part1, set)
    signbit = isodd(signint)
    state = (; mask, lastmask, signint, set, part2)
    ((part1, part2), signbit), (state,)
end

@inline iterate(sh::Shuffles) = _iterate(sh)

@inline function _iterate(sh::Shuffles{N}) where N
    sh2 = Shuffles(sh.set, (sh.ks[1]+sh.ks[2], sh.ks[3:end]...))
    ((set1, _), _), states_rest = _iterate(sh2)
    ((part1, part2), _), (state1,) = _iterate(Shuffles(set1, sh.ks[1:2]))
    states = (state1, states_rest...)
    parts = (part1, map(state -> state.part2, states)...)
    signbit = false
    (parts, signbit), states
end

@inline function iterate(sh::Shuffles{N}, states) where N
    ts1 = iterate(Shuffles(states[1].set, sh.ks[1:2]), (states[1],))
    if ts1 === nothing
        sh_rest = Shuffles(states[2].set, (sh.ks[1]+sh.ks[2], sh.ks[3:end]...))
        ts_rest = iterate(sh_rest, states[2:end])
        ts_rest === nothing && return nothing
        ((set1, _), _), states_rest = ts_rest
        ((part1, _), signbit), (state1,) = _iterate(Shuffles(set1, sh.ks[1:2]); signint = states_rest[1].signint)
        states = (state1, states_rest...)
    else
        ((part1, _), signbit), (state1,) = ts1
        states = (state1, states[2:end]...)
    end
    parts = (part1, map(state -> state.part2, states)...)
    (parts, signbit), states
end

"""
    shuffle_signbit(ss::SmallBitSet...) -> Bool

Return `true` if an odd number of transpositions is needed to transform the elements of the
sets `ss` into an increasing sequence, and `false` otherwise. The sets are considered as
increasing sequences and assumed to be disjoint.

See also [`shuffles`](@ref).

# Examples
```
julia> s, t, u = SmallBitSet([2, 3, 8]), SmallBitSet([1, 4, 6]), SmallBitSet([5, 7]);

julia> shuffle_signbit(s, t), shuffle_signbit(s, t, u)
(true, false)
```
"""
shuffle_signbit(ss::Vararg{SmallBitSet,N}) where N =
    shuffle_signbit(ss[N-1], ss[N]) ⊻ (@inline shuffle_signbit(ss[1:N-2]..., ss[N-1] ∪ ss[N]))

shuffle_signbit() = false
shuffle_signbit(::SmallBitSet) = false

function shuffle_signbit(s::SmallBitSet, t::SmallBitSet)
    m = bits(s)
    p = zero(m)
    while !iszero(m)
        # p ⊻= blsi(m)-one(m)
        p ⊻= blsmsk(m)
        m = blsr(m)
    end
    isodd(count_ones(p & bits(t)))
end

"""
    compositions(s::S, ks::Vararg{Integer,N}) where {S <: SmallBitSet, N}
    compositions(ks::Vararg{Integer,N}) where N

In the first form, return an iterator that yields all `ks`-compositions of the set `s`, that is,
all ordered partitions of `s` into `N` sets of size `ks[1]` to `ks[N]`, respectively. The element type
is `NTuple{N, S}`. The partition sizes in `ks` must be non-negative and add up to `length(s)`.

In the second form the set `s` is taken to be `SmallBitSet(1:sum(ks))`.
This gives an iterator over all set compositions of the integer `sum(ks)`.

See also [`subsets`](@ref subsets(::SmallBitSet, ::Integer)),
[`shuffles`](@ref shuffles(::Vararg{Integer,N}) where N).

# Examples
```jldoctest
julia> collect(compositions(SmallBitSet([2, 4, 5]), 1, 2))
3-element Vector{Tuple{SmallBitSet{UInt64}, SmallBitSet{UInt64}}}:
 (SmallBitSet([2]), SmallBitSet([4, 5]))
 (SmallBitSet([4]), SmallBitSet([2, 5]))
 (SmallBitSet([5]), SmallBitSet([2, 4]))

julia> collect(compositions(1, 1, 1))
6-element Vector{Tuple{SmallBitSet{UInt64}, SmallBitSet{UInt64}, SmallBitSet{UInt64}}}:
 (SmallBitSet([1]), SmallBitSet([2]), SmallBitSet([3]))
 (SmallBitSet([2]), SmallBitSet([1]), SmallBitSet([3]))
 (SmallBitSet([1]), SmallBitSet([3]), SmallBitSet([2]))
 (SmallBitSet([3]), SmallBitSet([1]), SmallBitSet([2]))
 (SmallBitSet([2]), SmallBitSet([3]), SmallBitSet([1]))
 (SmallBitSet([3]), SmallBitSet([2]), SmallBitSet([1]))

julia> collect(compositions(SmallBitSet([2, 4, 5]), 1, 0, 2))
3-element Vector{Tuple{SmallBitSet{UInt64}, SmallBitSet{UInt64}, SmallBitSet{UInt64}}}:
 (SmallBitSet([2]), SmallBitSet([]), SmallBitSet([4, 5]))
 (SmallBitSet([4]), SmallBitSet([]), SmallBitSet([2, 5]))
 (SmallBitSet([5]), SmallBitSet([]), SmallBitSet([2, 4]))

julia> collect(compositions(SmallBitSet()))
1-element Vector{Tuple{}}:
 ()
```
"""
compositions(args...) = Generator(first, shuffles(args...))

eltype(g::Generator{<:Shuffles, typeof(first)}) = fieldtype(eltype(g.iter), 1)

struct Subsets{T,S<:SmallBitSet} <: AbstractVector{S}
    set::T
    length::Int
end

"""
    subsets(s::S) where S <: SmallBitSet -> AbstractVector{S}
    subsets(n::Integer) -> AbstractVector{SmallBitSet{UInt}}

In the first form, return a vector of length `2^length(s)` whose elements are the subsets of the set `s`.

In the second form the set `s` is taken to be `SmallBitSet(1:n)`.

See also [`subsets(::Integer, ::Integer)`](@ref).

# Examples
```jldoctest
julia> collect(subsets(SmallBitSet{UInt8}([3, 5])))
4-element Vector{SmallBitSet{UInt8}}:
 SmallBitSet([])
 SmallBitSet([3])
 SmallBitSet([5])
 SmallBitSet([3, 5])

julia> collect(subsets(2))
4-element Vector{SmallBitSet{UInt64}}:
 SmallBitSet([])
 SmallBitSet([1])
 SmallBitSet([2])
 SmallBitSet([1, 2])

julia> subsets(2)[2]
SmallBitSet{UInt64} with 1 element:
  1
```
"""
function subsets(n::T) where T <: Integer
    n >= 0 || error("argument must be non-negative")
    n <= bitsize(UInt)-2 || error("at most $(bitsize(UInt)-2) elements supported")
    Subsets{T,SmallBitSet{UInt}}(n, n >= 0 ? unsafe_shl(1, n) : 0)
end,
function subsets(s::S) where {U <: Unsigned, S <: SmallBitSet{U}}
    bitsize(U) < bitsize(UInt) || length(s) <= bitsize(UInt)-2 ||
        error("at most $(bitsize(UInt)-2) elements supported")
    Subsets{S,S}(s, unsafe_shl(1, length(s)))
end

show(io::IO, ss::Subsets) = print(io, "Subsets(", ss.set, ')')
show(io::IO, ::MIME"text/plain", ss::Subsets) = print(io, "Subsets(", ss.set, ')')

size(ss::Subsets) = (ss.length,)

IndexStyle(::Type{<:Subsets}) = IndexLinear()

@inline function getindex(ss::Subsets{<:Integer}, i::Int)
    @boundscheck checkbounds(ss, i)
    _SmallBitSet((i-1) % UInt)
end

@inline function getindex(ss::Subsets{<:SmallBitSet}, i::Int)
    @boundscheck checkbounds(ss, i)
    _SmallBitSet(pdep((i-1) % UInt, bits(ss.set)))
end

"""
    subsets(s::SmallBitSet, k::Integer)
    subsets(n::Integer, k::Integer)

In the first form, return an iterator that yields all `k`-element subsets of the set `s`.
The element type is the type of `s`.
If `k` is negative or larger than `length(s)`, then the iterator is empty.

In the second form the set `s` is taken to be `SmallBitSet(1:n)`.

See also [`subsets(::Integer)`](@ref), [`shuffles`](@ref shuffles(::Vararg{Integer,N}) where N).

# Example
```jldoctest
julia> collect(subsets(SmallBitSet{UInt8}(2:2:8), 3))
4-element Vector{SmallBitSet{UInt8}}:
 SmallBitSet([2, 4, 6])
 SmallBitSet([2, 4, 8])
 SmallBitSet([2, 6, 8])
 SmallBitSet([4, 6, 8])

julia> collect(subsets(3, 2))
3-element Vector{SmallBitSet{UInt64}}:
 SmallBitSet([1, 2])
 SmallBitSet([1, 3])
 SmallBitSet([2, 3])

julia> collect(subsets(3, 4))
SmallBitSet{UInt64}[]
```
"""
function subsets(n::Integer, k::Integer)
    n >= 0 || error("first argument must be non-negative")
    n <= bitsize(UInt) || error("at most $(bitsize(UInt)) elements supported")
    Generator(first∘first, Shuffles(missing, (k, n-k)))
end,
function subsets(s::SmallBitSet, k::Integer)
    Generator(first∘first, Shuffles(s, (k, length(s)-k)))
end

eltype(::Generator{Shuffles{2,Missing}, typeof(first∘first)}) = SmallBitSet{UInt}
eltype(::Generator{Shuffles{2,S}, typeof(first∘first)}) where S <: SmallBitSet = S
