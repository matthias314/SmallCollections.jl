export Combinatorics

"""
    $(@__MODULE__)

    This module contains functions related to enumerative combinatorics.
"""
module Combinatorics

using ..SmallCollections
using SmallCollections: bitsize, unsafe_shl, unsafe_lshr,
    blsi, blsr, blsmsk, pdep, _SmallBitSet

#
# subset iterators
#

export set_compositions, subsets, set_compositions_parity, set_composition_parity

using Base: @propagate_inbounds, Generator
import Base: eltype, length, size, IndexStyle, getindex, iterate

struct SetCompositions{N,S}
    set::S
    ks::NTuple{N,Int}
end

"""
    set_compositions_parity(s::S, ks::Vararg{Integer,N}) where {S <: SmallBitSet, N}
    set_compositions_parity(ks::Vararg{Integer,N}) where N

In the first form, return an iterator that yields all `ks`-compositions of the set `s`
together with the parity of the permutation that puts the elements back into an increasing order.
See `set_compositions` and `set_composition_parity` for details.
The iterator returns tuples `(t, p)`, where `t` is of type `NTuple{N, S}`
and the parity `p` is of type `Bool` where `false` means even and `true` means odd.
The partition sizes in `ks` must be non-negative and add up to `length(s)`.

In the second form the set `s` is taken to be `SmallBitSet(1:sum(ks))`.

See also [`set_compositions`](@ref), [`set_composition_parity`](@ref).

# Examples
```jldoctest
julia> collect(set_compositions_parity(SmallBitSet([2, 4, 5]), 1, 2))
3-element Vector{Tuple{Tuple{SmallBitSet{UInt64}, SmallBitSet{UInt64}}, Bool}}:
 ((SmallBitSet([2]), SmallBitSet([4, 5])), 0)
 ((SmallBitSet([4]), SmallBitSet([2, 5])), 1)
 ((SmallBitSet([5]), SmallBitSet([2, 4])), 0)

julia> all(s == set_composition_parity(a, b) for ((a, b), s) in set_compositions_parity(1, 2))
true
```
"""
function set_compositions_parity(ks::Integer...)
    any(signbit, ks) && error("part sizes must be non-negative")
    sum(ks; init = 0) <= bitsize(UInt) || error("at most $(bitsize(UInt)) elements supported")
    SetCompositions(missing, ks)
end,
function set_compositions_parity(s::SmallBitSet, ks::Integer...)
    sum(ks; init = 0) == length(s) || error("part lengths must add up to size of the set")
    any(signbit, ks) && error("part sizes must be non-negative")
    SetCompositions(s, ks)
end

eltype(sh::SetCompositions{N,Missing}) where N = Tuple{NTuple{N,SmallBitSet{UInt}}, Bool}
eltype(sh::SetCompositions{N,S}) where {N, S <: SmallBitSet} = Tuple{NTuple{N,S}, Bool}

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
    set_composition_parity(ss::SmallBitSet...) -> Bool

Return `true` if an odd number of transpositions is needed to transform the elements of the
sets `ss` into an increasing sequence, and `false` otherwise. The sets are considered as
increasing sequences and assumed to be disjoint.

See also [`set_compositions_parity`](@ref).

# Examples
```
julia> s, t, u = SmallBitSet([2, 3, 8]), SmallBitSet([1, 4, 6]), SmallBitSet([5, 7]);

julia> set_composition_parity(s, t), set_composition_parity(s, t, u)
(true, false)
```
"""
set_composition_parity(ss::Vararg{SmallBitSet,N}) where N =
    set_composition_parity(ss[N-1], ss[N]) ⊻ (@inline set_composition_parity(ss[1:N-2]..., ss[N-1] ∪ ss[N]))

set_composition_parity() = false
set_composition_parity(::SmallBitSet) = false

function set_composition_parity(s::SmallBitSet, t::SmallBitSet)
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
    set_compositions(s::S, ks::Vararg{Integer,N}) where {S <: SmallBitSet, N}
    set_compositions(ks::Vararg{Integer,N}) where N

In the first form, return an iterator that yields all `ks`-compositions of the set `s`, that is,
all ordered partitions of `s` into `N` sets of size `ks[1]` to `ks[N]`, respectively. The element type
is `NTuple{N, S}`. The partition sizes in `ks` must be non-negative and add up to `length(s)`.

In the second form the set `s` is taken to be `SmallBitSet(1:sum(ks))`.
This gives an iterator over all set compositions of the integer `sum(ks)`.

See also [`subsets`](@ref subsets(::SmallBitSet, ::Integer)),
[`set_compositions_parity`](@ref set_compositions_parity(::Vararg{Integer,N}) where N).

# Examples
```jldoctest
julia> collect(set_compositions(SmallBitSet([2, 4, 5]), 1, 2))
3-element Vector{Tuple{SmallBitSet{UInt64}, SmallBitSet{UInt64}}}:
 (SmallBitSet([2]), SmallBitSet([4, 5]))
 (SmallBitSet([4]), SmallBitSet([2, 5]))
 (SmallBitSet([5]), SmallBitSet([2, 4]))

julia> collect(set_compositions(1, 1, 1))
6-element Vector{Tuple{SmallBitSet{UInt64}, SmallBitSet{UInt64}, SmallBitSet{UInt64}}}:
 (SmallBitSet([1]), SmallBitSet([2]), SmallBitSet([3]))
 (SmallBitSet([2]), SmallBitSet([1]), SmallBitSet([3]))
 (SmallBitSet([1]), SmallBitSet([3]), SmallBitSet([2]))
 (SmallBitSet([3]), SmallBitSet([1]), SmallBitSet([2]))
 (SmallBitSet([2]), SmallBitSet([3]), SmallBitSet([1]))
 (SmallBitSet([3]), SmallBitSet([2]), SmallBitSet([1]))

julia> collect(set_compositions(SmallBitSet([2, 4, 5]), 1, 0, 2))
3-element Vector{Tuple{SmallBitSet{UInt64}, SmallBitSet{UInt64}, SmallBitSet{UInt64}}}:
 (SmallBitSet([2]), SmallBitSet([]), SmallBitSet([4, 5]))
 (SmallBitSet([4]), SmallBitSet([]), SmallBitSet([2, 5]))
 (SmallBitSet([5]), SmallBitSet([]), SmallBitSet([2, 4]))

julia> collect(set_compositions(SmallBitSet()))
1-element Vector{Tuple{}}:
 ()
```
"""
set_compositions(args...) = Generator(first, set_compositions_parity(args...))

eltype(g::Generator{<:SetCompositions, typeof(first)}) = fieldtype(eltype(g.iter), 1)

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

See also [`subsets(::Integer)`](@ref), [`set_compositions_parity`](@ref set_compositions_parity(::Vararg{Integer,N}) where N).

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
    Generator(first∘first, SetCompositions(missing, (k, n-k)))
end,
function subsets(s::SmallBitSet, k::Integer)
    Generator(first∘first, SetCompositions(s, (k, length(s)-k)))
end

eltype(::Generator{SetCompositions{2,Missing}, typeof(first∘first)}) = SmallBitSet{UInt}
eltype(::Generator{SetCompositions{2,S}, typeof(first∘first)}) where S <: SmallBitSet = S

#
# permutations
#

export Permutations, permutations, permutations_parity_transposition

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

See also [`permutations_parity_transposition`](@ref).

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
Each permutation is of type `SmallVector{$PermN,$PermElType}`, but this may change in the future.

See also [`permutations`](@ref).

# Examples
```jldoctest
julia> collect(permutations_parity_transposition(3))
6-element Vector{Tuple{SmallVector{16, Int8}, Int64, Tuple{Int64, Int64}}}:
 ([1, 2, 3], 0, (0, 0))
 ([2, 1, 3], 1, (1, 2))
 ([3, 1, 2], 0, (1, 3))
 ([1, 3, 2], 1, (1, 2))
 ([2, 3, 1], 0, (1, 3))
 ([3, 2, 1], 1, (1, 2))

julia> collect(permutations_parity_transposition(0))
1-element Vector{Tuple{SmallVector{16, Int8}, Int64, Tuple{Int64, Int64}}}:
 ([], 0, (0, 0))
```
"""
function permutations_parity_transposition(n::Integer)
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
    (SmallVector(p), false, (0, 0)), (p, zero(p), false)
end

@inline function iterate(perm::Permutations, (p, c, s)::Tuple{AbstractSmallVector,MutableSmallVector,Bool})
    i = 1
    @inbounds while i < perm.n
        if c[i] < i
            t = iseven(i) ? (swap!(p, 1, i+1); (1, i+1)) : (swap!(p, c[i]+1, i+1); (c[i]+1, i+1))
            c[i] += one(PermElType)
            return (SmallVector(p), !s, t), (p, c, !s)
        else
            c[i] = 0
            i += 1
        end
    end
    nothing
end

end # module
