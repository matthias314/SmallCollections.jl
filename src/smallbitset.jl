#
# small sets
#

export SmallBitSet, bits, delete, pop, push

using Base: hasfastin

import Base: show, ==, hash, copy, convert,
    empty, isempty, in, first, last, iterate,
    length, issubset, maximum, minimum, extrema,
    union, intersect, setdiff, symdiff

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

function show(io::IO, s::SmallBitSet)
    print(io, "SmallBitSet([")
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

@propagate_inbounds function _push(mask::U, iter) where U
    for n in iter
        @boundscheck if !isinteger(n) || n <= 0 || n > bitsize(U)
                error("SmallBitSet{$U} can only contain integers between 1 and $(bitsize(U))")
            end
        mask |= one(U) << (Int(n)-1)
    end
    _SmallBitSet(mask)
end

SmallBitSet(args...) = SmallBitSet{UInt}(args...)

SmallBitSet{U}(s::SmallBitSet) where U = _SmallBitSet(s.mask % U)

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

export Subsets, AllSubsets, Shuffles

import Base: eltype, length, size, getindex

"""
    Subsets(n::Integer, k::Integer)
    Subsets(sh::Shuffles)

Iterating over `Subsets(n, k)` gives all `k`-element subsets of the set of integers from `1` to `n`.
The element type is `SmallBitSet`.

The call `Subsets(Shuffles(k, l))` returns `Subsets(k+l, k)`.

See also [`AllSubsets`](@ref), [`Shuffles`](@ref).

# Example
```jldoctest
julia> collect(Subsets(3, 2))
3-element Vector{SmallBitSet{UInt64}}:
 SmallBitSet([1, 2])
 SmallBitSet([1, 3])
 SmallBitSet([2, 3])

julia> Subsets(Shuffles(2, 3))
Subsets(5, 2)
```
"""
struct Subsets
    n::Int
    k::Int
    function Subsets(n::Integer, k::Integer)
        0 <= k <= n || error("illegal arguments")
        new(n, k)
    end
end

eltype(::Subsets) = SmallBitSet{UInt}

#=
length(ss::Subsets) = 0 <= ss.k <= ss.n ? binomial(ss.n, ss.k) : 0

function iterate(ss::Subsets)
    0 <= ss.k <= ss.n || return nothing
    m = UInt(1) << ss.k - UInt(1)
    last = m << (ss.n-ss.k)
    _SmallBitSet(m), (m, last)
end

# from https://graphics.stanford.edu/~seander/bithacks.html#NextBitPermutation
# via https://discourse.julialang.org/t/faster-way-to-find-all-bit-arrays-of-weight-n/113658/12
function iterate(ss::Subsets, (m, last))
    m == last && return nothing
    t = m | (m-one(m))
    m = (t+one(t)) | unsafe_lshr((~t & -~t) - one(t), trailing_zeros(m)+1)
    return _SmallBitSet(m), (m, last)
end
=#

length(ss::Subsets) = binomial(ss.n, ss.k)

function iterate(ss::Subsets, state...)
    xs = iterate(Shuffles(ss), state...)
    if xs === nothing
        nothing
    else
        x, state = xs
        first(x), state
    end
end

"""
    AllSubsets <: AbstractVector{SmallBitSet{UInt}}

    AllSubsets(n::Integer)
    Subsets(n::Integer)

`AllSubsets(n)` is a vector whose `2^n` elements of type `SmallBitSet` are the
subsets of the set of integers from `1` to `n`. `Subsets(n)` is a shorthand notation
for `AllSubsets(n)`.

See also [`Subsets`](@ref).

# Example
```jldoctest
julia> collect(Subsets(2))
4-element Vector{SmallBitSet{UInt64}}:
 SmallBitSet([])
 SmallBitSet([1])
 SmallBitSet([2])
 SmallBitSet([1, 2])
```
"""
struct AllSubsets <: AbstractVector{SmallBitSet{UInt}}
    n::Int
    function AllSubsets(n::Integer)
        n >= 0 || error("illegal argument")
        new(n)
    end
end

"""
    Subsets(n::Integer)

`Subsets(n)` is a shorthand notation for `AllSubsets(n)`.

See also [`Subsets`](@ref), [`AllSubsets`](@ref).
"""
Subsets(n::Integer) = AllSubsets(n)

show(io::IO, ss::AllSubsets) = print(io, "AllSubsets(", ss.n, ')')
show(io::IO, ::MIME"text/plain", ss::AllSubsets) = print(io, "AllSubsets(", ss.n, ')')

size(ss::AllSubsets) = (ss.n >= 0 ? 1 << ss.n : 0,)

getindex(ss::AllSubsets, i::Int) = _SmallBitSet((i-1) % UInt)

"""
    Shuffles(k::Integer, l::Integer)
    Shuffles(ss::Subsets)

Iterating over `Shuffles(k, l)` gives all `(k, l)`-shuffles, that is, all partitions
of the integers from `1` to `k+l` into two sets of size `k` and `l`, respectively.
The sets are of type `SmallBitSet`. The sign of the shuffle is returned as a `Bool`
where `false` means `+1` and `true` means `-1`. The two sets and the sign are returned
as a triple.

The call `Shuffles(Subsets(n, k))` returns `Shuffles(k, n-k)`.

See also [`Subsets`](@ref).

# Examples
```jldoctest
julia> collect(Shuffles(2, 1))
3-element Vector{Tuple{SmallBitSet{UInt64}, SmallBitSet{UInt64}, Bool}}:
 (SmallBitSet([1, 2]), SmallBitSet([3]), 0)
 (SmallBitSet([1, 3]), SmallBitSet([2]), 1)
 (SmallBitSet([2, 3]), SmallBitSet([1]), 0)

julia> eltype(Shuffles(2, 1))
Tuple{SmallBitSet{UInt64}, SmallBitSet{UInt64}, Bool}

julia> [(-1)^s * maximum(a) for (a, _, s) in Shuffles(2, 1)]
3-element Vector{Int64}:
  2
 -3
  3

julia> Shuffles(Subsets(5, 2))
Shuffles(2, 3)
```
"""
struct Shuffles
    k::Int
    l::Int
    function Shuffles(k::Integer, l::Integer)
        (k >= 0 && l >= 0) || error("arguments must be non-negative")
        k+l <= bitsize(UInt) || error("arguments too large")
        new(k, l)
    end
end

Shuffles(ss::Subsets) = Shuffles(ss.k, ss.n-ss.k)
Subsets(sh::Shuffles) = Subsets(sh.k+sh.l, sh.k)

eltype(::Shuffles) = Tuple{SmallBitSet{UInt}, SmallBitSet{UInt}, Bool}

length(sh::Shuffles) = length(Subsets(sh))

function iterate(sh::Shuffles)
    m = UInt(1) << sh.k - UInt(1)
    last = m << sh.l
    mc = one(m) << (sh.k+sh.l) - one(m)
    (_SmallBitSet(m), _SmallBitSet(mc ⊻ m), false), (m, last, mc, zero(m))
end

# adapted from https://graphics.stanford.edu/~seander/bithacks.html#NextBitPermutation
# via https://discourse.julialang.org/t/faster-way-to-find-all-bit-arrays-of-weight-n/113658/12
function iterate(sh::Shuffles, (m, last, mc, s))
    m == last && return nothing
    t = m | (m-one(m))
    t1 = t+one(t)
    zm = trailing_zeros(m)
    zt = trailing_zeros(t1)
    m = t1 | unsafe_lshr((~t & -~t) - one(t), zm+1)
    s ⊻= ~(zm & zt)
    return (_SmallBitSet(m), _SmallBitSet(mc ⊻ m), isodd(s)), (m, last, mc, s)
end
