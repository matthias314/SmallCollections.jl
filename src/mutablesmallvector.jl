using Base: haslength

import Base:
    copy, copyto!, resize!, similar,
    strides, elsize, unsafe_convert,
    getindex, setindex!, insert!, deleteat!, pop!, popfirst!, popat!,
    append!, prepend!, pushfirst!, empty, empty!, map!, filter!

export duplicate!

# functions also for Variables

@inline function unsafe_shl!(v::AbstractVector{T}, N, i, xs::Vararg{Any,M}) where {T,M}
    GC.@preserve v begin
        unsafe_copyto!(pointer(v, i+M), pointer(v, i), (N-(i+M-1)) % UInt)
        unsafe_store!(Ptr{NTuple{M,T}}(pointer(v, i)), xs)
    end
    v
end

@inline function unsafe_shr!(v::AbstractVector{T}, N, i, xs::Vararg{Any,M}) where {T,M}
    GC.@preserve v begin
        unsafe_copyto!(pointer(v, i), pointer(v, i+M), (N-(i+M-1)) % UInt)
        unsafe_store!(Ptr{NTuple{M,T}}(pointer(v, N-M+1)), xs)
    end
    v
end

@inline function insert_pop!(v::Variables{N}, i::Integer, xs::Vararg{Any,M}) where {N,M}
    @boundscheck checkbounds(v, i+M-1)
    unsafe_shl!(v, N, i, xs...)
end

@inline function deleteat_push!(v::Variables{N}, i::Integer, xs::Vararg{Any,M}) where {N,M}
    @boundscheck checkbounds(v, i+M-1)
    unsafe_shr!(v, N, i, xs...)
end

# MutableSmallVector

export MutableSmallVector

"""
    MutableSmallVector{N,T} <: AbstractSmallVector{N,T}

    MutableSmallVector{N,T}()
    MutableSmallVector{N,T}(iter)
    MutableSmallVector{N}(iter)
    MutableSmallVector(v::PackedVector{T})
    MutableSmallVector(v::AbstractSmallVector)

    MutableSmallVector{N,T}(undef, n::Integer)

`MutableSmallVector{N,T}` is a mutable vector type that can hold up to `N` elements of type `T`.
It is the mutable analog of `SmallVector{N,T}`.

Note that setting individual vector elements (via `setindex!`) is only supported for `isbits`
element types.

The special form `MutableSmallVector{N,T}(undef, n)` returns a non-initialized vector of length `n`.

See also [`SmallVector`](@ref), `Base.isbitstype`.
"""
mutable struct MutableSmallVector{N,T} <: AbstractSmallVector{N,T}
    b::Values{N,T}
    n::SmallLength
    MutableSmallVector{N,T}(v::Values{N}, n::Integer) where {N,T} = new{N,T}(v, n % SmallLength)
    global _MutableSmallVector(::Val{N}, ::Type{T}) where {N,T} = new{N,T}()
end

function MutableSmallVector{N,T}(::UndefInitializer, n::Integer) where {N,T}
    0 <= n <= N || error("length must be between 0 and $N")
    v = _MutableSmallVector(Val(N), T)
    for i in n+1:N
        unsafe_setindex!(v, default(T), i)
    end
    v.n = n % SmallLength
    v
end

MutableSmallVector{N,T}(v::AbstractSmallVector{N}) where {N,T} = MutableSmallVector{N,T}(v.b, v.n)

function MutableSmallVector{N,T}(itr) where {N,T}
    isbitstype(T) || return MutableSmallVector(SmallVector{N,T}(itr))
    v = MutableSmallVector{N,T}()
    i = 0
    for ix in enumerate(itr)
        i, x = ix
        i <= N || error("vector cannot have more than $N elements")
        unsafe_setindex!(v, x, i)
    end
    v.n = i % SmallLength
    v
end

MutableSmallVector(v::AbstractSmallVector{N,T}) where {N,T} = MutableSmallVector{N,T}(v.b, v.n)
SmallVector(v::AbstractSmallVector{N,T}) where {N,T} = SmallVector{N,T}(v.b, v.n)

@inline function unsafe_getindex(v::MutableSmallVector, i::Int)
    GC.@preserve v unsafe_load(pointer(v, i))
end

@inline function getindex(v::MutableSmallVector{N,T}, i::Int) where {N,T}
    @boundscheck checkbounds(v, i)
    isbitstype(T) ? unsafe_getindex(v, i) : @inbounds v.b[i]
end

@inline function unsafe_setindex!(v::MutableSmallVector{N,T}, x, i) where {N,T}
    isbitstype(T) || error("setindex! is only supported for isbits element types, not for $T")
    GC.@preserve v unsafe_store!(pointer(v, i), x)
    v
end

@inline function setindex!(v::MutableSmallVector, x, i::Int)
    @boundscheck checkbounds(v, i)
    unsafe_setindex!(v, x, i)
end

copy(v::MutableSmallVector{N,T}) where {N,T} = MutableSmallVector{N,T}(v.b, v.n)

function copyto!(v::MutableSmallVector{N}, w::AbstractSmallVector{N}) where N
    v.b, v.n = w.b, w.n
    v
end

similar(v::AbstractSmallVector{N}, ::Type{T}, (n,)::Tuple{Int}) where {N,T} =
    isbitstype(T) ? MutableSmallVector{N,T}(undef, n) : Vector{T}(undef, n)

strides(::MutableSmallVector) = (1,)
elsize(::Type{MutableSmallVector{N,T}}) where {N,T} = elsize(Variables{N,T})

unsafe_convert(::Type{Ptr{T}}, v::MutableSmallVector{N,T}) where {N,T} =
    Ptr{T}(pointer_from_objref(v))

empty(v::MutableSmallVector{N,T}, ::Type{U} = T) where {N,T,U} = MutableSmallVector{N,U}()

empty!(v::MutableSmallVector) = resize!(v, 0)

@inline function resize!(v::MutableSmallVector{N,T}, n::Integer) where {N,T}
    @boundscheck 0 <= n <= N || error("length must be between 0 and $N")
    v.n = n % SmallLength
    for i in n+1:length(v)
        @inbounds v[i] = default(T)
    end
    v
end

@propagate_inbounds deleteat!(v::MutableSmallVector, i::Integer) = deleteat!(v, i, 1)

@inline function deleteat!(v::MutableSmallVector{N,T}, i::Integer, n::Integer) where {N,T}
    @boundscheck (1 <= i <= length(v)-n+1 && n >= 0) || throw(BoundsError(v, i))
    b = sizeof(T)
    GC.@preserve v begin
        unsafe_copyto!(pointer(v, i), pointer(v, i+n), (length(v)-(i+n-1)) % UInt)
        for j in length(v)-n+1:length(v)
            unsafe_store!(pointer(v, j), default(T))
        end
    end
    v.n -= n % SmallLength
    v
end

@inline function pop!(v::MutableSmallVector{N,T}) where {N,T}
    @boundscheck isempty(v) && error("vector must not be empty")
    n = length(v)
    @inbounds x, v[n] = v[n], default(T)
    v.n -= 1
    x
end

@propagate_inbounds popfirst!(v::MutableSmallVector) = popat!(v, 1)

@inline function popat!(v::MutableSmallVector, i::Integer)
    @boundscheck checkbounds(v, i)
    @inbounds (x = v[i]; deleteat!(v, i))
    x
end

@inline function insert!(v::MutableSmallVector{N,T}, i::Integer, xs::Vararg{Any,M}) where {N,T,M}
    @boundscheck 1 <= i <= length(v)+1 <= N-M+1 || throw(BoundsError(v, i))
    v.n += M
    unsafe_shl!(v, v.n, i, xs...)
end

if VERSION < v"1.11-"
    const MemoryVector{T} = Union{Variables{<:Any,T}, MutableSmallVector{<:Any,T}, Vector{T}}
else
    const MemoryVector{T} = Union{Variables{<:Any,T}, MutableSmallVector{<:Any,T}, Vector{T}, Memory{T}}
end

@inline function append!(v::MutableSmallVector{N,T}, w::MemoryVector{T}) where {N,T}
    n = length(v)+length(w)
    @boundscheck n <= N || error("vector cannot have more than $N elements")
    GC.@preserve v unsafe_copyto!(pointer(v, length(v)+1), pointer(w), length(w))
    v.n = n % SmallLength
    v
end

@propagate_inbounds pushfirst!(v::MutableSmallVector, xs::Vararg{Any,M}) where M =
    prepend!(v, xs)

@inline function prepend!(v::MutableSmallVector{N,T}, w::MemoryVector{T}) where {N,T}
    n = length(v)+length(w)
    @boundscheck n <= N || error("vector cannot have more than $N elements")
    GC.@preserve v begin
        unsafe_copyto!(pointer(v, length(w)+1), pointer(v), length(v))
        unsafe_copyto!(pointer(v), pointer(w), length(w))
    end
    v.n = n % SmallLength
    v
end

@inline function prepend!(v::MutableSmallVector{N}, w) where N
    if haslength(w)
        n = length(v)+length(w)
        @boundscheck n <= N || error("vector cannot have more than $N elements")
        GC.@preserve v unsafe_copyto!(pointer(v, length(w)+1), pointer(v), length(v))
        v.n = n % SmallLength
        for (i, x) in enumerate(w)
            @inbounds v[i] = x
        end
        v
    else
        n = length(v)
        foldl(pushfirst!, w; init = v)
        reverse!(v, 1, length(v)-n)
    end
end

@inline function duplicate!(v::MutableSmallVector{N}, i::Integer) where N
    @boundscheck begin
        checkbounds(v, i)
        @boundscheck length(v) < N || error("vector cannot have more than $N elements")
    end
    GC.@preserve v unsafe_copyto!(pointer(v, i+1), pointer(v, i), (length(v)-(i-1)) % UInt)
    v.n += 1
    v
end

function filter!(f, v::MutableSmallVector)
    j = 1
    @inbounds for i in eachindex(v)
        f(v[i]) || continue
        v[j] = v[i]
        j += 1
    end
    @inbounds resize!(v, j-1)
end

function map!(f::F, w::MutableSmallVector, vs::Vararg{AbstractSmallVector,N}) where {F,N}
    copyto!(w, map(f, vs...))
end

# broadcast

copyto!(v::MutableSmallVector, bc::Broadcasted{SmallVectorStyle}) = copyto!(v, copy(bc))

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
