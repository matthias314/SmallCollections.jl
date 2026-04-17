#
# common definitions for AbstractFixedVector and AbstractSmallVector
#

export fixedvector, support, invreplace

import Base: findall, findfirst, findlast, findprev, findnext, findmin, findmax,
    any, all, allequal, allunique, count, getindex, filter, checkindex, copy,
    issorted, checkbounds, isless, <=

capacity(::Type{<:AbstractFixedOrSmallVector{N}}) where N = N

copy(v::V) where V <: AbstractFixedOrSmallVector = V(v)

function fixedvector(v::AbstractFixedOrSmallVector{N,T}, ::Val{M}) where {N,T,M}
    b = fixedvector(v)
    FixedVector{M,T}(ntuple(i -> i <= N ? b[i] : default(T), Val(M)))
end

function isless(v::V, w::V) where V <: Union{AbstractFixedOrSmallVector{8,UInt8}, AbstractFixedOrSmallVector{16,UInt8}}
    bv = bswap(bits(v))
    bw = bswap(bits(w))
    bv < bw || (bv == bw) & (length(v) < length(w))
end

for T in (:Integer, :AbstractChar, :AbstractString)
    @eval function <=(v::AbstractFixedOrSmallVector{<:Any, <:$T}, w::AbstractFixedOrSmallVector{<:Any, <:$T})
        !(w < v)
    end
end

support(v::AbstractFixedOrSmallVector) = _SmallBitSet(bits(map(!iszero, v)))

@inline _support(f, v::AbstractFixedVector; style) = (@inline; support(f, v))
@inline _support(f, v::AbstractSmallVector; style) = (@inline; support(f, v; style))

_map(f, v::AbstractFixedVector; style) = map(f, v)
_map(f, v::AbstractSmallVector; style) = map(f, v; style)

struct AssertBool{F}
    f::F
end

(ab::AssertBool)(x) = ab.f(x)::Bool

MapStyle(ab::AssertBool, types::Type...) = MapStyle(ab.f, types...)

findall(v::AbstractFixedOrSmallVector; kw...) = findall(identity, v; kw...)

@inline function findall(f::F, v::AbstractFixedOrSmallVector{N}; kw...) where {F <: Function, N}
    @inline
    @inbounds SmallVector{N,SmallLength}(support(AssertBool(f), v; kw...))
end

findfirst(v::AbstractFixedOrSmallVector{N,Bool}) where N = findfirst(identity, v; style = StrictStyle())
findlast(v::AbstractFixedOrSmallVector{N,Bool}) where N = findlast(identity, v; style = StrictStyle())

findnext(v::AbstractFixedOrSmallVector{N,Bool}, k::Integer) where N = findnext(identity, v, k; style = StrictStyle())
findprev(v::AbstractFixedOrSmallVector{N,Bool}, k::Integer) where N = findprev(identity, v, k; style = StrictStyle())

function findfirst(f::F, v::AbstractFixedOrSmallVector{N,T}; style = MapStyle(f, T)) where {F <: Function, N, T}
    findnext(f, v, 1; style)
end

function findnext(f::F, v::AbstractFixedOrSmallVector{N,T}, k::Integer; style = MapStyle(f, T)) where {F<: Function, N, T}
    @inline
    if style isa LazyStyle
        invoke(findnext, Tuple{F,AbstractVector{T},Integer}, f, v, k)
    else
        m = bits(filter(>=(k), @inline support(AssertBool(f), fixedvector(v))))
        i = trailing_zeros(m)+1
        i <= length(v) ? i : nothing
    end
end

function findlast(f::F, v::AbstractFixedOrSmallVector{N,T}; style = MapStyle(f, T)) where {F <: Function, N, T}
    findprev(f, v, length(v); style)
end

function findprev(f::F, v::AbstractFixedOrSmallVector{N,T}, k::Integer; style = MapStyle(f, T)) where {F <: Function, N, T}
    @inline
    if style isa LazyStyle
        invoke(findprev, Tuple{F,AbstractVector{T},Integer}, f, v, k)
    else
        m = bits(filter(<=(k), @inline support(AssertBool(f), fixedvector(v))))
        i = bitsize(m)-leading_zeros(m)
        0 != i <= length(v) ? i : nothing
    end
end

@propagate_inbounds findmin(v::AbstractFixedOrSmallVector) = findmin(identity, v)
@propagate_inbounds findmax(v::AbstractFixedOrSmallVector) = findmax(identity, v)

@inline function findmin(f::F, v::AbstractFixedOrSmallVector{N,T}; style = MapStyle(f, T)) where {F,N,T}
    @boundscheck isempty(v) && error("argument must not be empty")
    y = minimum(f, v)
    y, findfirst(isequal(y)∘f, fixedvector(v); style)::Int
end

@inline function findmax(f::F, v::AbstractFixedOrSmallVector{N,T}; style = MapStyle(f, T)) where {F,N,T}
    @boundscheck isempty(v) && error("argument must not be empty")
    y = maximum(f, v)
    y, findfirst(isequal(y)∘f, fixedvector(v); style)::Int
end

if VERSION < v"1.14-"
    any(v::AbstractFixedOrSmallVector; kw...) = any(identity, v; kw...)
    all(v::AbstractFixedOrSmallVector; kw...) = all(identity, v; kw...)
end

function any(f::F, v::AbstractFixedOrSmallVector{N,T}; dims = :, style::MapStyle = MapStyle(f, T)) where {F<:Function,N,T}
    @inline
    if style isa LazyStyle || !(dims isa Colon)
        invoke(any, Tuple{F,AbstractVector{T}}, f, v; dims)
    else
        u = map(AssertBool(f), fixedvector(v))
        trailing_zeros(bits(u)) < length(v)
    end
end

function all(f::F, v::AbstractFixedOrSmallVector{N,T}; dims = :, style::MapStyle = MapStyle(f, T)) where {F<:Function,N,T}
    @inline
    if style isa LazyStyle || !(dims isa Colon)
        invoke(all, Tuple{F,AbstractVector{T}}, f, v; dims)
    else
        u = map(AssertBool(f), fixedvector(v))
        trailing_ones(bits(u)) >= length(v)
    end
end

allequal(v::AbstractFixedOrSmallVector) = isempty(v) ? true : all(isequal(@inbounds v[1]), v)

function allequal(f::F, v::AbstractFixedOrSmallVector{N,T}; style::MapStyle = MapStyle(f, T)) where {F,N,T}
    @inline
    if style isa LazyStyle
        invoke(allequal, Tuple{F,AbstractVector{T}}, f, v)
    else
        allequal(_map(f, v; style))
    end
end

allunique(v::AbstractFixedOrSmallVector) = all(x -> count(isequal(x), v) == 1, v)

function allunique(f::F, v::AbstractFixedOrSmallVector{N,T}; style::MapStyle = MapStyle(f, T)) where {F,N,T}
    @inline
    if style isa LazyStyle
        invoke(allunique, Tuple{F,AbstractVector{T}}, f, v)
    else
        allunique(_map(f, v; style))
    end
end

count(v::AbstractFixedOrSmallVector; kw...) = count(identity, v; kw...)

@inline function count(f::F, v::AbstractFixedOrSmallVector{N,T}; dims = :, init::S = 0, style = MapStyle(f, T)) where {F,N,T,S}
    @inline
    if style isa LazyStyle || !(dims isa Colon)
        invoke(count, Tuple{Any, AbstractVector}, f, v; dims, init)
    else
        k = length(_support(AssertBool(f), v; style))
        init + (S <: Integer ? k % S : k)
    end
end

"""
    issorted(v::AbstractFixedVector; [strict::Bool = false, style::MapStyle, ...]) -> Bool
    issorted(v::AbstractSmallVector; [strict::Bool = false, style::MapStyle, ...]) -> Bool

Returns `true` is `v` is sorted. In addition to the standard options `lt`, `by`, `rev` and `order`,
this dedicated method supports the keyword arguments `strict` and `style`.
If `style` is not `LazyStyle()`, then more comparisons than strictly necessary may be performed.
Setting `strict` to `true` checks if the vector is strictly sorted.

As discussed under `MapStyle`, the default value for `style` is based on a list
of known functions. Currently the `order` keyword, if present, enforces `LazyStyle`.

See also [`$(@__MODULE__).MapStyle`](@ref), `Base.issorted(::AbstractVector)`.

# Examples
```jldoctest
julia> v = SmallVector{8,Int8}([3, 2, 2]); issorted(v)
false

julia> v = SmallVector{8,Int8}([3, 2, 2]); issorted(v; rev = true)
true

julia> v = SmallVector{8,Int8}([3, 2, 2]); issorted(v; rev = true, strict = true)
false
```
"""
function issorted(v::AbstractFixedOrSmallVector{N,T};
        lt = isless, by = identity, rev::Union{Bool,Nothing} = nothing,
        order::Base.Order.Ordering = Base.Order.Forward,
        strict::Bool = false,
        style::MapStyle = begin
            U = Core.Compiler.return_type(by, Tuple{T})
            isconcretetype(U) ? MapStyle(lt, U, U) : LazyStyle()
        end) where {N,T}
    @inline
    if order === Base.Order.Forward && style != LazyStyle()
        w = map(by, fixedvector(v))
        u = popfirst(w)[1]
        if rev == true
            w, u = u, w
        end
        b = strict ? map(!lt, w, u) : map(lt, u, w)
        i = findfirst(b)
        i === nothing || i >= length(v)
    elseif strict
        issorted_strict(v, Base.Order.ord(lt, by, rev, order))  # function barrier
    else
        invoke(issorted, Tuple{AbstractVector}, v; lt, by, rev, order)
    end
end

issorted_strict(v, o) = all(i -> @inbounds(Base.Order.lt(o, v[i], v[i+1])), OneTo(length(v)-1))

function checkindex(::Type{Bool}, inds::AbstractUnitRange, v::AbstractFixedOrSmallVector{N,T}) where {N, T <: Base.HWReal}
    if isempty(v)
        true
    else
        min, max = extrema(v)
        first(inds) <= min && max <= last(inds)
    end
end

@inline function getindex(v::AbstractFixedOrSmallVector{N,T}, ii::OrdinalRange{<:Integer}) where {N,T}
    @boundscheck checkbounds(v, ii)
    if ii isa OneTo
        @inbounds resize(SmallVector(v), length(ii))
    elseif hasshuffle(v, Val(true))
        U = uinttype(T)
        u = fixedvector_range(Val(N), (first(ii)-1) % U, step(ii) % U)
        w = shuffle(fixedvector(v), u, Val(true))
        SmallVector(padtail(w, unsafe_length(ii)), unsafe_length(ii))
    elseif VERSION >= v"1.11" && ishwtype(T) && (HAS_COMPRESS || N <= 32)
        U = uinttype(Val(N))
        @inbounds v[SmallBitSet{U}(ii)]
    else
        @inbounds SmallVector{N,T}(v[i] for i in ii)
    end
end

"""
    getindex(v::Union{AbstractFixedVector{N,T}, AbstractSmallVector{N,T}}, s::SmallBitSet) where {N,T} -> SmallVector{N,T}

Returns the vector with elements `v[i]` where `i` runs through the elements of `s` in increasing order.
This operation is analogous to `v[collect(s)]`, but faster.

See also [`checkbounds`](@ref).

# Example
```jldoctest
julia> v = SmallVector{8}('a':'f'); s = SmallBitSet{UInt16}(1:2:5)
SmallBitSet{UInt16} with 3 elements:
  1
  3
  5

julia> v[s]
3-element SmallVector{8, Char}:
 'a': ASCII/Unicode U+0061 (category Ll: Letter, lowercase)
 'c': ASCII/Unicode U+0063 (category Ll: Letter, lowercase)
 'e': ASCII/Unicode U+0065 (category Ll: Letter, lowercase)
```
"""
getindex(v::AbstractFixedOrSmallVector, s::SmallBitSet)

@inline function getindex(v::AbstractFixedOrSmallVector{N,T}, s::SmallBitSet{U}) where {N,T,U}
    @boundscheck checkbounds(v, s)
    if HAS_PEXT && T == Bool && bitsize(U) <= bitsize(UInt)
        m = pext(bits(fixedvector(v)), bits(s))
        b = convert(FixedVector{N,Bool}, m)
        SmallVector(b, length(s))
    elseif VERSION >= v"1.11" && ishwtype(T) && (HAS_COMPRESS || N <= 32)  # slows down for larger N
        SmallVector(compress(fixedvector(v), s), length(s))
    else
        SmallVector{N,T}(@inbounds v[i] for i in s)
    end
end

const AbstractFixedOrSmallOrPackedVector{T} = Union{AbstractFixedOrSmallVector{<:Any,T},PackedVector{<:Any,<:Any,T}}

"""
    checkbounds(::Type{Bool}, v::Union{AbstractFixedVector, AbstractSmallVector, PackedVector}, s::SmallBitSet) -> Bool

Returns `true` if all elements of `s` are inbounds for `v`.

See alse `Base.checkbounds`.

# Examples
```jldoctest
julia> v = SmallVector{8,Int8}(1:3)
3-element SmallVector{8, Int8}:
 1
 2
 3

julia> s = SmallBitSet{UInt8}((1, 4))
SmallBitSet{UInt8} with 2 elements:
  1
  4

julia> checkbounds(Bool, v, s)
false

julia> checkbounds(v, s)
ERROR: BoundsError: attempt to access 3-element SmallVector{8, Int8} at index [SmallBitSet{UInt8}([1, 4])]
```
"""
function checkbounds(::Type{Bool}, v::AbstractFixedOrSmallOrPackedVector, s::SmallBitSet)
    isempty(s) || checkbounds(Bool, v, last(s))
end

@inline function getindex(v::AbstractFixedOrSmallOrPackedVector, ii::AbstractFixedOrSmallOrPackedVector{Bool})
    @boundscheck checkbounds(v, ii)
    @inbounds v[support(ii)]
end

@inline function getindex(v::V, ii::AbstractFixedOrSmallOrPackedVector{T}) where {V <: AbstractVector, T <: Integer}
    @boundscheck checkbounds(v, ii)
    if T == Bool
        @inbounds invoke(getindex, Tuple{V,AbstractVector{Bool}}, v, ii)
    else
        map(i -> @inbounds(v[i]), ii)
    end
end

@inline function getindex(v::PackedVector, ii::AbstractFixedOrSmallVector{<:Integer})
    @boundscheck checkbounds(v, ii)
    map(i -> @inbounds(v[i]), ii)
end

"""
    $(@__MODULE__).getindex0(
        v::Union{AbstractFixedVector{N,T}, AbstractSmallVector{N,T}},
        ii::AbstractFixedVector{M,S}
    ) where {N, T, M, S <: Integer} -> FixedVector{M,T}

    $(@__MODULE__).getindex0(
        v::Union{AbstractFixedVector{N,T}, AbstractSmallVector{N,T}},
        ii::AbstractSmallVector{M,S}
    ) where {N, T, M, S <: Integer} -> SmallVector{M,T}

This function for vector indexing is analogous to `getindex` with the difference
that the index vector `ii` is assumed to be `0`-based. This is particularly useful
for indexing a vector `v` with capacity `N = 256` efficiently via a vector `ii` with
element type `UInt8`.

See also `Base.getindex(::AbstractVector, ::AbstractVector{<:Integer})`.

# Example
```jldoctest
julia> using $(@__MODULE__): getindex0

julia> v = -FixedVector{8,Int8}(1:8);

julia> ii = FixedVector{4,UInt8}([0, 2, 3, 5]);

julia> getindex0(v, ii)
4-element FixedVector{4, Int8}:
 -1
 -3
 -4
 -6

julia> getindex0(v, ii) == v[ii .+ 1]
true
```
"""
getindex0

@inline function getindex0(v::AbstractFixedOrSmallVector{N,T}, ii::AbstractFixedVector{M,S}) where {N, T, M, S <: Integer}
    @boundscheck begin
        x, y = extrema(ii)
        checkbounds(v, x+1:y+1)
    end
    if hasshuffle(v, ii, Val(true))
        U = uinttype(T)
        shuffle(fixedvector(v), ii .% U, Val(true))
    elseif isbitstype(T)
        w = MutableFixedVector{M,T}(undef)
        for j in 1:M
            @inbounds w[j] = v[ii[j]+1]
        end
        FixedVector(w)
    else
        map(i -> @inbounds(v[i+1]), ii)
    end
end

@inline function getindex0(v::AbstractFixedOrSmallVector{N,T}, ii::AbstractSmallVector{M,S}) where {N, T, M, S <: Integer}
    @boundscheck isempty(ii) || begin
        x, y = extrema(fixedvector(ii))
        checkbounds(v, x+1:y+1)
    end
    @inbounds w = getindex0(v, fixedvector(ii))
    SmallVector(padtail(w, length(ii)), length(ii))
end

@inline function getindex(v::AbstractFixedOrSmallVector{N,T}, ii::AbstractFixedVector{M,S}) where {N, T, M, S <: BitInteger}
    @boundscheck checkbounds(v, ii)
    if hasshuffle(v, ii, Val(true))
        U = uinttype(T)
        shuffle(fixedvector(v), ii .% U .- one(U), Val(true))
    elseif isbitstype(T)
        w = MutableFixedVector{M,T}(undef)
        for j in 1:M
            @inbounds w[j] = v[ii[j]]
        end
        FixedVector(w)
    else
        map(i -> @inbounds(v[i]), ii)
    end
end

@inline function getindex(v::AbstractFixedOrSmallVector{N,T}, ii::AbstractSmallVector{M,S}) where {N, T, M, S <: BitInteger}
    @boundscheck checkbounds(v, ii)
    if hasshuffle(v, ii, Val(false))
        U = inttype(T)
        w = shuffle(fixedvector(v), (fixedvector(ii) .% U) .- one(U), Val(false))
        SmallVector(w, length(ii))
    elseif isbitstype(T)
        w = MutableSmallVector{M,T}(undef, length(ii))
        for j in 1:length(ii)
            @inbounds w[j] = v[ii[j]]
        end
        SmallVector(w)
    else
        map(i -> @inbounds(v[i]), ii)
    end
end

"""
    invreplace(s::SmallBitSet, v::Union{AbstractFixedVector{N,T}, AbstractSmallVector{N,T}}) where {N, T <: Integer} -> SmallBitSet

Returns the set of all integers `i` such that `v[i]` is in `s`. The elements
of `v` must be in the range `1:M` where `M` is the capacity of `s`.
Hence if `p` is a permutation (sending each `i` to `p[i]`), then `invreplace(s, p)`
contains the images of the elements of `s` under the permutation inverse to `p`.

See also `Base.replace`, [`exchange`](@ref), [`capacity`](@ref capacity(::SmallBitSet)).

# Example
```jldoctest
julia> s = SmallBitSet{UInt8}([1, 3, 7]);

julia> p = FixedVector{8,Int8}([3, 1, 2, 8, 4, 5, 6, 7]);

julia> t = invreplace(s, p)
SmallBitSet{UInt8} with 3 elements:
  1
  2
  8

julia> t == replace(s, (j => i for (i, j) in enumerate(p))...)
true

julia> v = SmallVector{16,UInt8}([3, 3, 3, 3]);

julia> invreplace(s, v)
SmallBitSet{UInt16} with 4 elements:
  1
  2
  3
  4
```
"""
@propagate_inbounds function invreplace(s::SmallBitSet, v::AbstractFixedOrSmallVector{N,T}) where {N, T <: Integer}
    M = bitsize(s)
    w = convert(FixedVector{M,Bool}, bits(s))
    _SmallBitSet(bits(w[v]))
end

function filter(f::F, v::AbstractFixedOrSmallVector; kw...) where F
    @inbounds v[support(f, v; kw...)]
end

const avx512_maxbits = 8192

"""
    $(@__MODULE__).hasshuffle(::Val{N}, ::Type{T}, ::Val{INB}) where {N,T,INB}
    $(@__MODULE__).hasshuffle(v::AbstractFixedOrSmallVector{N,T}, ::Val{INB}) where {N,T,INB}
    $(@__MODULE__).hasshuffle(v::AbstractFixedOrSmallVector{N,T}, ii::AbstractFixedOrSmallVector{M}, ::Val{INB}) where {N,T,M,INB}

Returns `true` if there is a hardware-accelerated method
for vector indexing of a vector with element type `T` and capacity (at most) `N`.
The index vector is assumed to have capacity at most `N`, too.
The Boolean parameter `INB` indicates if all indices are within bounds (`INB = true`) or
if negative indices are used to zero entries (`INB = false`).
The 3-argument version is equivalent to `hasshuffle(Val(max(N, M)), T, Val(INB))`.

The currently supported methods are
[AVX](https://en.wikipedia.org/wiki/Advanced_Vector_Extensions) (up to 128 bits),
[AVX2](https://en.wikipedia.org/wiki/AVX2) (up to 256 bits)
and [AVX-512](https://en.wikipedia.org/wiki/AVX-512), more precisely AVX-512_VBMI
(implemented for any bit size, but limited by `hasshuffle` to at most $avx512_maxbits bits).

See also [`$(@__MODULE__).shuffle`](@ref).
"""
hasshuffle

hasshuffle(v::AbstractFixedOrSmallVector{N,T}, inbounds) where {N,T} = hasshuffle(Val(N), T, inbounds)
hasshuffle(v::AbstractFixedOrSmallVector{N,T}, ii::AbstractFixedOrSmallVector{M}, inbounds) where {N,T,M} = hasshuffle(Val(max(N, M)), T, inbounds)

"""
    $(@__MODULE__).shuffle(v::AbstractFixedVector{NT,T}, p::AbstractFixedVector{M}, ::Val{INB}) where {NT,T,M,INB} -> FixedVector{M,T}

Uses hardware acceleration to permute the elements of `v` and returns the new vector `w`, and `false` otherwise.
The permutation `p` must be 0-based. In other words, `w[i] == v[p[i]+1]` for any index `i` of `p`.
If `p[i]` is negative, then `w[i]` is set to `default(T)`.
Bounds are not checked. Moreover, negative indices must be in the range `-M:-1`.
The Boolean parameter `INB` indicates whether all indices are within bounds (`INB = true`) or
if negative indices may occur (`INB = false`).

See also [`$(@__MODULE__).hasshuffle`](@ref), [`$(@__MODULE__).default`](@ref), [`$(@__MODULE__).getindex0`](@ref).
"""
shuffle
