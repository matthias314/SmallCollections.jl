# permutations

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
