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

#
# permutations
#

export Permutations, permutations, permutations_sign_transposition

import Base: length, eltype, iterate

struct Permutations
    n::Int
end

const PermN = 16
const PermElType = Int8

"""
    permutations(n::Integer)

Return an iterator that yields all permutations of the integers from `1` to `n`.

The argument `n` must be between `0` and `$PermN`.
The identity permutation is returned first.
Each permutation is of type `SmallVector{$PermN,$PermElType}`, but this may change in the future.

See also [`permutations_sign_transposition`](@ref).

# Examples
```jldoctest
julia> collect(permutations(3))
6-element Vector{SmallVector{16, Int8}}:
 [1, 2, 3]
 [2, 1, 3]
 [3, 1, 2]
 [1, 3, 2]
 [2, 3, 1]
 [3, 2, 1]

julia> collect(permutations(0))
1-element Vector{SmallVector{16, Int8}}:
 0-element SmallVector{16, Int8}
```
"""
permutations(n::Integer) = (p for (p, _, _) in permutations_sign_transposition(n))

"""
    permutations_sign_transposition(n::Integer)

Return an iterator that yields all permutations `p` of the integers from `1` to `n`
together with some extra data. The first element of the tuple returned is the permutation `p`.
The second element is the sign of `p` (`+1` for even and `-1` for odd permutations).
The third element is a pair `(i, j)` that indicates the transposition `t` by which `p` differs
from the previously returned permutation `q`. (More precisely, the new permutations `p` is
obtained by first applying `t` and then `q`.)

The argument `n` must be between `0` and `$PermN`.
The iterator returns the identity permutation first;
in this case the transposition pair is set to `(0, 0)`.
The true transpositions `(i, j)` satisfy `i < j`.
Each permutation is of type `SmallVector{$PermN,$PermElType}`, but this may change in the future.

See also [`permutations`](@ref), `Base.signbit`.

# Examples
```jldoctest
julia> collect(permutations_sign_transposition(3))
6-element Vector{Tuple{SmallVector{16, Int8}, Int64, Tuple{Int64, Int64}}}:
 ([1, 2, 3], 1, (0, 0))
 ([2, 1, 3], -1, (1, 2))
 ([3, 1, 2], 1, (1, 3))
 ([1, 3, 2], -1, (1, 2))
 ([2, 3, 1], 1, (1, 3))
 ([3, 2, 1], -1, (1, 2))

julia> collect(SmallCollections.permutations_sign_transposition(0))
1-element Vector{Tuple{SmallVector{16, Int8}, Int64, Tuple{Int64, Int64}}}:
 ([], 1, (0, 0))
```
"""
function permutations_sign_transposition(n::Integer)
    0 <= n <= PermN || error("argument must be between 0 and $PermN")
    Permutations(n)
end

length(perm::Permutations) = factorial(perm.n)

eltype(::Type{Permutations}) = Tuple{SmallVector{PermN,PermElType},Int,NTuple{2,Int}}

# we use Heap's algorithm to iterate over all permutations

@propagate_inbounds function swap!(v::AbstractVector, i, j)
    v[i], v[j] = v[j], v[i]
    v
end

@inline function iterate(perm::Permutations)
    p = MutableSmallVector{PermN,PermElType}(1:perm.n)
    (SmallVector(p), 1, (0, 0)), (p, zero(p), 1)
end

@inline function iterate(perm::Permutations, (p, c, s)::Tuple{AbstractSmallVector,MutableSmallVector,Int})
    i = 1
    @inbounds while i < perm.n
        if c[i] < i
            t = iseven(i) ? (swap!(p, 1, i+1); (1, i+1)) : (swap!(p, c[i]+1, i+1); (c[i]+1, i+1))
            c[i] += one(PermElType)
            return (SmallVector(p), -s, t), (p, c, -s)
        else
            c[i] = 0
            i += 1
        end
    end
    nothing
end
