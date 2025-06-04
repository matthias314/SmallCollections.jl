export Combinatorics

"""
    $(@__MODULE__)

    This module contains functions related to enumerative combinatorics.
"""
module Combinatorics

using ..SmallCollections
using SmallCollections: bitsize, padtail, unsafe_shl, unsafe_lshr,
    blsi, blsr, blsmsk, pdep

using Base: Fix2, Generator

_SmallBitSet(mask::U) where U <: Unsigned = convert(SmallBitSet{U}, mask)

#
# partitions
#

export partitions

import Base: IteratorSize, eltype, iterate

const PartN = 64

const PartEltype = Int8

struct Partitions
    n::Int
end

"""
    partitions(n::Integer)

Return an iterator over the partitions of `n`.
A partition of `n` is a weakly decreasing sequence of positive integers that add up to `n`.
Each partition is of type `SmallVector{$PartN,$PartEltype}`, but this may change in the future.

See also [`partitions(::Integer, ::Integer)`](@ref).

# Examples
```jldoctest
julia> partitions(3) |> collect
3-element Vector{SmallVector{64, Int8}}:
 [3]
 [2, 1]
 [1, 1, 1]

julia> partitions(0) |> collect
1-element Vector{SmallVector{64, Int8}}:
 0-element SmallVector{64, Int8}
```
"""
function partitions(n::Integer)
    0 <= n <= PartN || error("argument must be between 0 and $(PartN)")
    Partitions(n)
end

IteratorSize(::Type{Partitions}) = Base.SizeUnknown()

eltype(::Type{Partitions}) = SmallVector{PartN,PartEltype}

@inline function iterate(p::Partitions)
    v = MutableSmallVector{PartN,PartEltype}()
    # creating two separate MutableSmallVector below would lead to allocations
    if iszero(p.n)
        SmallVector(v), (v, 0, PartEltype(0))
    else
        @inbounds push!(v, p.n % PartEltype)
        SmallVector(v), (v, 1-isone(p.n), PartEltype(isone(p.n)))
    end
end

@inline function iterate(p::Partitions, (v, i, s)::Tuple{MutableSmallVector,Int,PartEltype})
    @inbounds if i == 0
        nothing
    elseif v[i] == 2
        v[i] = 1
        push!(v, one(PartEltype))
        SmallVector(v), (v, i-1, s+PartEltype(2))
    else
        c = (v[i] -= one(PartEltype))
        s += one(PartEltype)
        while s >= c
            i += 1
            v[i] = c
            s -= c
        end
        if s == 0
            resize!(v, i)
            SmallVector(v), (v, length(v), zero(PartEltype))
        else
            resize!(v, i+1)
            v[i+1] = s
            SmallVector(v), (v, length(v)-isone(s), PartEltype(isone(s)))
        end
    end
end

struct Partitions2
    n::Int
    k::Int
end

"""
    partitions(n::Integer, k::Integer)

Return an iterator over the partitions of `n` into `k` parts.
A partition of `n` is a weakly decreasing sequence of positive integers that add up to `n`.
Each partition is of type `SmallVector{$PartN,$PartEltype}`, but this may change in the future.

See also [`partitions(::Integer)`](@ref).

# Examples
```jldoctest
julia> partitions(7, 3) |> collect
4-element Vector{SmallVector{64, Int8}}:
 [5, 1, 1]
 [4, 2, 1]
 [3, 3, 1]
 [3, 2, 2]

julia> partitions(7, 0) |> collect
SmallVector{64, Int8}[]

julia> partitions(0, 0) |> collect
1-element Vector{SmallVector{64, Int8}}:
 0-element SmallVector{64, Int8}
```
"""
function partitions(n::Integer, k::Integer)
    (n >= 0 && k >= 0) || error("arguments must be non-negative")
    n <= typemax(PartEltype) || error("only partitions of integers <= $(typemax(PartEltype)) are supported")
    k <= PartN || error("only partitions into at most $PartN parts are supported")
    Partitions2(n, k)
end

IteratorSize(::Type{Partitions2}) = Base.SizeUnknown()

eltype(::Type{Partitions2}) = SmallVector{PartN,PartEltype}

@inline function iterate(p::Partitions2)
    (p.n < p.k || p.n > p.k == 0) && return nothing
    v = MutableSmallVector{PartN,PartEltype}(undef, p.k)
    for i in eachindex(v)
        @inbounds v[i] = (i == 1 ? p.n-p.k+1 : 1) % PartEltype
    end
    SmallVector(v), v
end

@inline function iterate(p::Partitions2, v)
    @inbounds begin
        local c
        if p.k == 0 || (c = v[1] - one(PartEltype); c <= v[p.k])
            return nothing
        end
        i = findfirst(<(c), v)::Int
        c = (v[i] += one(PartEltype))
        # unsafe_copyto!(v, map(Fix2(min, c), v; style = RigidStyle()))  # allocates
        v.b = min.(v.b, c)
        v[1] += p.n % PartEltype - sum_fast(v)
    end
    SmallVector(v), v
end

#
# compositions
#

export compositions, weakcompositions, compositions_cumsum, weakcompositions_cumsum

import Base: IteratorSize, HasLength, eltype, length, iterate

const CompN = 16
const CompEltype = Int8

export WeakCompositions

struct WeakCompositions
    n::Int  # may be negative (for compositions)
    k::Int  # always >= 0
end

"""
    weakcompositions_cumsum(n::Integer, k::Integer)

Return an iterator over the cumulative sums of the weak compositions of `n` of length `k`.
A weak composition of `n` of length `k` is a `k`-tuple of non-negative integers that add up to `n`.
The cumulative sum of such a composition is a vector with `k+1` elements, starting with `0` and ending with `n`.
Each vector is of type `SmallVector{$CompN,$CompEltype}`, but this may change in the future.

See also [`weakcompositions`](@ref), [`compositions_cumsum`](@ref).

# Examples
```jldoctest
julia> weakcompositions_cumsum(3, 2) |> collect
4-element Vector{SmallVector{16, Int8}}:
 [0, 0, 3]
 [0, 1, 3]
 [0, 2, 3]
 [0, 3, 3]

julia> weakcompositions_cumsum(3, 0) |> collect
SmallVector{16, Int8}[]

julia> weakcompositions_cumsum(0, 0) |> collect
1-element Vector{SmallVector{16, Int8}}:
 [0]
```
"""
function weakcompositions_cumsum(n::Integer, k::Integer)
    (n >= 0 && k >= 0) || error("arguments must be non-negative")
    k < CompN || error("only compositions into at most $(CompN-1) parts are supported")
    WeakCompositions(n, k)
end

IteratorSize(::WeakCompositions) = HasLength()

function length(c::WeakCompositions)
    if c.n+c.k-1 >= 0
        binomial(c.n+c.k-1, c.k-1)
    else #  we have c.n <= 0 && c.k == 0
        Int(iszero(c.n))
    end
end

eltype(::Type{WeakCompositions}) = SmallVector{CompN,CompEltype}

@inline function iterate(c::WeakCompositions)
    if c.n < 0 || (c.n > 0 && c.k == 0)
        nothing
    else
        v = zeros(MutableSmallVector{CompN,CompEltype}, c.k+1)
        @inbounds v[end] = c.n % CompEltype
        SmallVector(v), (v, c.k+1)
    end
end

@inline function iterate(c::WeakCompositions, (v, i)::Tuple{MutableSmallVector,Int})
    while i > 0 && @inbounds v[i] == c.n
        i -= 1
    end
    i <= 1 && return nothing
    a = @inbounds v[i] += one(CompEltype)
    for j in i+1:c.k
        @inbounds v[j] = v[i]
    end
    SmallVector(v), (v, c.k)
end

"""
    compositions_cumsum(n::Integer, k::Integer)

Return an iterator over the cumulative sums of the compositions of `n` of length `k`.
A composition of `n` of length `k` is a `k`-tuple of positive integers that add up to `n`.
The cumulative sum of such a composition is a vector with `k+1` elements, starting with `0` and ending with `n`.
Each vector is of type `SmallVector{$CompN,$CompEltype}`, but this may change in the future.

See also [`compositions`](@ref), [`weakcompositions_cumsum`](@ref).

# Examples
```jldoctest
julia> compositions_cumsum(3, 2) |> collect
2-element Vector{SmallVector{16, Int8}}:
 [0, 1, 3]
 [0, 2, 3]

julia> compositions_cumsum(3, 0) |> collect
SmallVector{16, Int8}[]

julia> compositions_cumsum(0, 0) |> collect
1-element Vector{SmallVector{16, Int8}}:
 [0]
```
"""
function compositions_cumsum(n::Integer, k::Integer)
    (n >= 0 && k >= 0) || error("arguments must be non-negative")
    k < CompN || error("only compositions into at most $(CompN-1) parts are supported")
    Generator(Fix2(composition_cumsum, k), WeakCompositions(n-k, k))
end

@inline function composition_cumsum(v::AbstractSmallVector{N,T}, k) where {N,T}
    t = ntuple(i -> ifelse(i <= k+1, T(i-1), zero(T)), Val(N))
    w = SmallVector(FixedVector(t), k+1)
    @inbounds v+w
end

eltype(::Type{<:Generator{WeakCompositions, <:Fix2{typeof(composition_cumsum)}}}) = eltype(WeakCompositions)

"""
    weakcompositions(n::Integer, k::Integer)

Return an iterator over the weak compositions of `n` of length `k`.
A weak composition of `n` of length `k` is a `k`-tuple of non-negative integers that add up to `n`.
Each composition is of type `SmallVector{$CompN,$CompEltype}`, but this may change in the future.

See also [`compositions`](@ref), [`weakcompositions_cumsum`](@ref).

# Examples
```jldoctest
julia> weakcompositions(3, 2) |> collect
4-element Vector{SmallVector{16, Int8}}:
 [0, 3]
 [1, 2]
 [2, 1]
 [3, 0]

julia> weakcompositions(3, 0) |> collect
SmallVector{16, Int8}[]

julia> weakcompositions(0, 0) |> collect
1-element Vector{SmallVector{16, Int8}}:
 0-element SmallVector{16, Int8}
```
"""
weakcompositions(n::Integer, k::Integer) = Generator(Fix2(weakcomposition, k), weakcompositions_cumsum(n, k))

@inline function weakcomposition(v::AbstractSmallVector{N,T}, k) where {N,T}
    # @inbounds first(popfirst(v)) - first(pop(v))  # too slow
    b = circshift(v.b, Val(-1)) - v.b
    SmallVector(padtail(b, k), k)
end

eltype(::Type{<:Generator{WeakCompositions, <:Fix2{typeof(weakcomposition)}}}) = eltype(WeakCompositions)

"""
    compositions(n::Integer, k::Integer)

Return an iterator over the compositions of `n` of length `k`.
A composition of `n` of length `k` is a `k`-tuple of positive integers that add up to `n`.
Each composition is of type `SmallVector{$CompN,$CompEltype}`, but this may change in the future.

See also [`weakcompositions`](@ref), [`compositions_cumsum`](@ref).

# Examples
```jldoctest
julia> compositions(3, 2) |> collect
2-element Vector{SmallVector{16, Int8}}:
 [1, 2]
 [2, 1]

julia> compositions(3, 0) |> collect
SmallVector{16, Int8}[]

julia> compositions(0, 0)  |> collect
1-element Vector{SmallVector{16, Int8}}:
 0-element SmallVector{16, Int8}
```
"""
function compositions(n::Integer, k::Integer)
    (n >= 0 && k >= 0) || error("arguments must be non-negative")
    k < CompN || error("only compositions into at most $(CompN-1) parts are supported")
    Generator(Fix2(composition, k), WeakCompositions(n-k, k))
end

@inline function composition(v::AbstractSmallVector{N,T}, k) where {N,T}
    t = ntuple(i -> T(i <= k), Val(N))
    w = SmallVector(FixedVector(t), k)
    @inbounds weakcomposition(v, k)+w
end

eltype(::Type{<:Generator{WeakCompositions, <:Fix2{typeof(composition)}}}) = eltype(WeakCompositions)

#
# subset iterators
#

export setcompositions, subsets, setcompositions_parity, setcomposition_parity

using Base: @propagate_inbounds, Generator
import Base: eltype, length, size, IndexStyle, getindex, iterate

struct SetCompositions{N,S}
    set::S
    ks::NTuple{N,Int}
end

"""
    setcompositions_parity(s::S, ks::Vararg{Integer,N}) where {S <: SmallBitSet, N}
    setcompositions_parity(ks::Vararg{Integer,N}) where N

In the first form, return an iterator that yields all `ks`-compositions of the set `s`
together with the parity of the permutation that puts the elements back into an increasing order.
See `setcompositions` and `setcomposition_parity` for details.
The iterator returns tuples `(t, p)`, where `t` is of type `NTuple{N, S}`
and the parity `p` is of type `Bool` where `false` means even and `true` means odd.
The partition sizes in `ks` must be non-negative and add up to `length(s)`.

In the second form the set `s` is taken to be `SmallBitSet(1:sum(ks))`.

See also [`setcompositions`](@ref), [`setcomposition_parity`](@ref).

# Examples
```jldoctest
julia> setcompositions_parity(SmallBitSet([2, 4, 5]), 1, 2) |> collect
3-element Vector{Tuple{Tuple{SmallBitSet{UInt64}, SmallBitSet{UInt64}}, Bool}}:
 ((SmallBitSet([2]), SmallBitSet([4, 5])), 0)
 ((SmallBitSet([4]), SmallBitSet([2, 5])), 1)
 ((SmallBitSet([5]), SmallBitSet([2, 4])), 0)

julia> all(s == setcomposition_parity(a, b) for ((a, b), s) in setcompositions_parity(1, 2))
true
```
"""
function setcompositions_parity(ks::Integer...)
    any(signbit, ks) && error("part sizes must be non-negative")
    sum(ks; init = 0) <= bitsize(UInt) || error("at most $(bitsize(UInt)) elements supported")
    SetCompositions(missing, ks)
end,
function setcompositions_parity(s::SmallBitSet, ks::Integer...)
    sum(ks; init = 0) == length(s) || error("part lengths must add up to size of the set")
    any(signbit, ks) && error("part sizes must be non-negative")
    SetCompositions(s, ks)
end

eltype(::Type{SetCompositions{N,Missing}}) where N = Tuple{NTuple{N,SmallBitSet{UInt}}, Bool}
eltype(::Type{SetCompositions{N,S}}) where {N, S <: SmallBitSet} = Tuple{NTuple{N,S}, Bool}

length(sh::SetCompositions{0}) = 1

function length(sh::SetCompositions{N}) where N
    foldl(sh.ks[2:end]; init = (1, sh.ks[1])) do (p, k), l
        p*binomial(k+l, k), k+l
    end |> first
end

iterate(sh::SetCompositions{0}) = ((), false), nothing
iterate(sh::SetCompositions{0}, _) = nothing

iterate(sh::SetCompositions{1}) = ((sh.set,), false), nothing
iterate(sh::SetCompositions{1,Missing}) = ((SmallBitSet(1:sh.ks[1]),), false), nothing
iterate(sh::SetCompositions{1}, _) = nothing

@inline iterate(sh::SetCompositions{2}) = any(signbit, sh.ks) ? nothing : _iterate(sh)

@inline function _iterate(sh::SetCompositions{2,S}; signint = UInt(0)) where S
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

@inline function iterate(sh::SetCompositions{2,S}, (state,)) where S
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

@inline iterate(sh::SetCompositions) = _iterate(sh)

@inline function _iterate(sh::SetCompositions{N}) where N
    sh2 = SetCompositions(sh.set, (sh.ks[1]+sh.ks[2], sh.ks[3:end]...))
    ((set1, _), _), states_rest = _iterate(sh2)
    ((part1, part2), _), (state1,) = _iterate(SetCompositions(set1, sh.ks[1:2]))
    states = (state1, states_rest...)
    parts = (part1, map(state -> state.part2, states)...)
    signbit = false
    (parts, signbit), states
end

@inline function iterate(sh::SetCompositions{N}, states) where N
    ts1 = iterate(SetCompositions(states[1].set, sh.ks[1:2]), (states[1],))
    if ts1 === nothing
        sh_rest = SetCompositions(states[2].set, (sh.ks[1]+sh.ks[2], sh.ks[3:end]...))
        ts_rest = iterate(sh_rest, states[2:end])
        ts_rest === nothing && return nothing
        ((set1, _), _), states_rest = ts_rest
        ((part1, _), signbit), (state1,) = _iterate(SetCompositions(set1, sh.ks[1:2]); signint = states_rest[1].signint)
        states = (state1, states_rest...)
    else
        ((part1, _), signbit), (state1,) = ts1
        states = (state1, states[2:end]...)
    end
    parts = (part1, map(state -> state.part2, states)...)
    (parts, signbit), states
end

"""
    setcomposition_parity(ss::SmallBitSet...) -> Bool

Return `true` if an odd number of transpositions is needed to transform the elements of the
sets `ss` into an increasing sequence, and `false` otherwise. The sets are considered as
increasing sequences and assumed to be disjoint.

See also [`setcompositions_parity`](@ref).

# Examples
```
julia> s, t, u = SmallBitSet([2, 3, 8]), SmallBitSet([1, 4, 6]), SmallBitSet([5, 7]);

julia> setcomposition_parity(s, t), setcomposition_parity(s, t, u)
(true, false)
```
"""
setcomposition_parity(ss::Vararg{SmallBitSet,N}) where N =
    setcomposition_parity(ss[N-1], ss[N]) ⊻ (@inline setcomposition_parity(ss[1:N-2]..., ss[N-1] ∪ ss[N]))

setcomposition_parity() = false
setcomposition_parity(::SmallBitSet) = false

function setcomposition_parity(s::SmallBitSet, t::SmallBitSet)
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
    setcompositions(s::S, ks::Vararg{Integer,N}) where {S <: SmallBitSet, N}
    setcompositions(ks::Vararg{Integer,N}) where N

In the first form, return an iterator that yields all `ks`-compositions of the set `s`, that is,
all ordered partitions of `s` into `N` sets of size `ks[1]` to `ks[N]`, respectively. The element type
is `NTuple{N, S}`. The partition sizes in `ks` must be non-negative and add up to `length(s)`.

In the second form the set `s` is taken to be `SmallBitSet(1:sum(ks))`.
This gives an iterator over all set compositions of the integer `sum(ks)`.

See also [`subsets`](@ref subsets(::SmallBitSet, ::Integer)),
[`setcompositions_parity`](@ref setcompositions_parity(::Vararg{Integer,N}) where N).

# Examples
```jldoctest
julia> setcompositions(SmallBitSet([2, 4, 5]), 1, 2) |> collect
3-element Vector{Tuple{SmallBitSet{UInt64}, SmallBitSet{UInt64}}}:
 (SmallBitSet([2]), SmallBitSet([4, 5]))
 (SmallBitSet([4]), SmallBitSet([2, 5]))
 (SmallBitSet([5]), SmallBitSet([2, 4]))

julia> setcompositions(1, 1, 1) |> collect
6-element Vector{Tuple{SmallBitSet{UInt64}, SmallBitSet{UInt64}, SmallBitSet{UInt64}}}:
 (SmallBitSet([1]), SmallBitSet([2]), SmallBitSet([3]))
 (SmallBitSet([2]), SmallBitSet([1]), SmallBitSet([3]))
 (SmallBitSet([1]), SmallBitSet([3]), SmallBitSet([2]))
 (SmallBitSet([3]), SmallBitSet([1]), SmallBitSet([2]))
 (SmallBitSet([2]), SmallBitSet([3]), SmallBitSet([1]))
 (SmallBitSet([3]), SmallBitSet([2]), SmallBitSet([1]))

julia> setcompositions(SmallBitSet([2, 4, 5]), 1, 0, 2) |> collect
3-element Vector{Tuple{SmallBitSet{UInt64}, SmallBitSet{UInt64}, SmallBitSet{UInt64}}}:
 (SmallBitSet([2]), SmallBitSet([]), SmallBitSet([4, 5]))
 (SmallBitSet([4]), SmallBitSet([]), SmallBitSet([2, 5]))
 (SmallBitSet([5]), SmallBitSet([]), SmallBitSet([2, 4]))

julia> setcompositions(SmallBitSet()) |> collect
1-element Vector{Tuple{}}:
 ()
```
"""
setcompositions(args...) = Generator(first, setcompositions_parity(args...))

eltype(g::Type{Generator{I, typeof(first)}}) where I <: SetCompositions = fieldtype(eltype(I), 1)

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
julia> subsets(SmallBitSet{UInt8}([3, 5])) |> collect
4-element Vector{SmallBitSet{UInt8}}:
 SmallBitSet([])
 SmallBitSet([3])
 SmallBitSet([5])
 SmallBitSet([3, 5])

julia> subsets(2) |> collect
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

See also [`subsets(::Integer)`](@ref), [`setcompositions_parity`](@ref setcompositions_parity(::Vararg{Integer,N}) where N).

# Example
```jldoctest
julia> subsets(SmallBitSet{UInt8}(2:2:8), 3) |> collect
4-element Vector{SmallBitSet{UInt8}}:
 SmallBitSet([2, 4, 6])
 SmallBitSet([2, 4, 8])
 SmallBitSet([2, 6, 8])
 SmallBitSet([4, 6, 8])

julia> subsets(3, 2) |> collect
3-element Vector{SmallBitSet{UInt64}}:
 SmallBitSet([1, 2])
 SmallBitSet([1, 3])
 SmallBitSet([2, 3])

julia> subsets(3, 4) |> collect
SmallBitSet{UInt64}[]
```
"""
function subsets(n::Integer, k::Integer)
    n >= 0 || error("first argument must be non-negative")
    n <= bitsize(UInt) || error("at most $(bitsize(UInt)) elements supported")
    Generator(first∘first, SetCompositions(missing, (k, n-k)))
end,
function subsets(s::SmallBitSet, k::Integer)
    Generator(first∘first, SetCompositions(s, (k, length(s)-k)))
end

eltype(::Type{Generator{SetCompositions{2,Missing}, typeof(first∘first)}}) = SmallBitSet{UInt}
eltype(::Type{Generator{SetCompositions{2,S}, typeof(first∘first)}}) where S <: SmallBitSet = S

#
# permutations
#

export Permutations, permutations, permutations_parity_transposition

import Base: length, eltype, iterate

struct Permutations
    n::Int
end

const PermN = 16
const PermEltype = Int8

"""
    permutations(n::Integer)

Return an iterator that yields all permutations of the integers from `1` to `n`.

The argument `n` must be between `0` and `$PermN`.
The identity permutation is returned first.
Each permutation is of type `SmallVector{$PermN,$PermEltype}`, but this may change in the future.

See also [`permutations_parity_transposition`](@ref).

# Examples
```jldoctest
julia> permutations(3) |> collect
6-element Vector{SmallVector{16, Int8}}:
 [1, 2, 3]
 [2, 1, 3]
 [3, 1, 2]
 [1, 3, 2]
 [2, 3, 1]
 [3, 2, 1]

julia> permutations(0) |> collect
1-element Vector{SmallVector{16, Int8}}:
 0-element SmallVector{16, Int8}
```
"""
permutations(n::Integer) = (p for (p, _, _) in permutations_parity_transposition(n))

"""
    permutations_parity_transposition(n::Integer)

Return an iterator that yields all permutations `p` of the integers from `1` to `n`
together with some extra data. The first element of the tuple returned is the permutation `p`.
The second element is the parity of `p` (`false` for even and `true` for odd permutations).
The third element is a pair `(i, j)` that indicates the transposition `t` by which `p` differs
from the previously returned permutation `q`. (More precisely, the new permutations `p` is
obtained by first applying `t` and then `q`.)

The argument `n` must be between `0` and `$PermN`.
The iterator returns the identity permutation first;
in this case the transposition pair is set to `(0, 0)`.
The true transpositions `(i, j)` satisfy `i < j`.
Each permutation is of type `SmallVector{$PermN,$PermEltype}`, but this may change in the future.

See also [`permutations`](@ref).

# Examples
```jldoctest
julia> permutations_parity_transposition(3) |> collect
6-element Vector{Tuple{SmallVector{16, Int8}, Int64, Tuple{Int64, Int64}}}:
 ([1, 2, 3], 0, (0, 0))
 ([2, 1, 3], 1, (1, 2))
 ([3, 1, 2], 0, (1, 3))
 ([1, 3, 2], 1, (1, 2))
 ([2, 3, 1], 0, (1, 3))
 ([3, 2, 1], 1, (1, 2))

julia> permutations_parity_transposition(0) |> collect
1-element Vector{Tuple{SmallVector{16, Int8}, Int64, Tuple{Int64, Int64}}}:
 ([], 0, (0, 0))
```
"""
function permutations_parity_transposition(n::Integer)
    0 <= n <= PermN || error("argument must be between 0 and $PermN")
    Permutations(n)
end

length(perm::Permutations) = factorial(perm.n)

eltype(::Type{Permutations}) = Tuple{SmallVector{PermN,PermEltype},Int,NTuple{2,Int}}

# we use Heap's algorithm to iterate over all permutations

@propagate_inbounds function swap!(v::AbstractVector, i, j)
    v[i], v[j] = v[j], v[i]
    v
end

@inline function iterate(perm::Permutations)
    p = MutableSmallVector{PermN,PermEltype}(1:perm.n)
    (SmallVector(p), false, (0, 0)), (p, zero(p), false)
end

@inline function iterate(perm::Permutations, (p, c, s)::Tuple{AbstractSmallVector,MutableSmallVector,Bool})
    i = 1
    @inbounds while i < perm.n
        if c[i] < i
            t = iseven(i) ? (swap!(p, 1, i+1); (1, i+1)) : (swap!(p, c[i]+1, i+1); (c[i]+1, i+1))
            c[i] += one(PermEltype)
            return (SmallVector(p), !s, t), (p, c, !s)
        else
            c[i] = 0
            i += 1
        end
    end
    nothing
end

end # module
