#
# common definitions for AbstractFixedVector and AbstractSmallVector
#

export support

import Base: findall, findfirst, findlast, findprev, findnext, findmin, findmax,
    any, all, allequal, allunique, count, getindex, filter, checkindex, copy,
    issorted, checkbounds

capacity(::Type{<:AbstractFixedOrSmallVector{N}}) where N = N

copy(v::V) where V <: AbstractFixedOrSmallVector = V(v)

support(v::AbstractFixedOrSmallVector) = _SmallBitSet(bits(map(!iszero, v)))

@inline _support(f, v::AbstractFixedVector; style) = (@inline; support(f, v))
@inline _support(f, v::AbstractSmallVector; style) = (@inline; support(f, v; style))

_map(f, v::AbstractFixedVector; style) = map(f, v)
_map(f, v::AbstractSmallVector; style) = map(f, v; style)

assertbool(f) = x -> f(x)::Bool

findall(v::AbstractFixedOrSmallVector; kw...) = findall(identity, v; kw...)

function findall(f::F, v::AbstractFixedOrSmallVector{N}; kw...) where {F<:Function,N}
    SmallVector{N,SmallLength}(support(assertbool(f), v; kw...))
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
        m = bits(filter(>=(k), @inline support(assertbool(f), fixedvector(v))))
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
        m = bits(filter(<=(k), @inline support(assertbool(f), fixedvector(v))))
        i = bitsize(m)-leading_zeros(m)
        0 != i <= length(v) ? i : nothing
    end
end

@inline function findmin(v::AbstractFixedOrSmallVector{N,T}) where {N, T <: BitInteger}
    @boundscheck isempty(v) && error("argument must not be empty")
    x = minimum(v)
    x, findfirst(==(x), fixedvector(v))::Int
end

@inline function findmax(v::AbstractFixedOrSmallVector{N,T}) where {N, T <: BitInteger}
    @boundscheck isempty(v) && error("argument must not be empty")
    x = maximum(v)
    x, findfirst(==(x), fixedvector(v))::Int
end

any(v::AbstractFixedOrSmallVector; kw...) = any(identity, v; kw...)
all(v::AbstractFixedOrSmallVector; kw...) = all(identity, v; kw...)

function any(f::F, v::AbstractFixedOrSmallVector{N,T}; dims = :, style::MapStyle = MapStyle(f, T)) where {F<:Function,N,T}
    @inline
    if style isa LazyStyle || !(dims isa Colon)
        invoke(any, Tuple{F,AbstractVector{T}}, f, v; dims)
    else
        u = map(assertbool(f), fixedvector(v))
        trailing_zeros(bits(u)) < length(v)
    end
end

function all(f::F, v::AbstractFixedOrSmallVector{N,T}; dims = :, style::MapStyle = MapStyle(f, T)) where {F<:Function,N,T}
    @inline
    if style isa LazyStyle || !(dims isa Colon)
        invoke(all, Tuple{F,AbstractVector{T}}, f, v; dims)
    else
        u = map(assertbool(f), fixedvector(v))
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
        k = length(_support(assertbool(f), v; style))
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

issorted_strict(v, o) = all(i -> @inbounds(Base.Order.lt(o, v[i], v[i+1])), Base.OneTo(length(v)-1))

function checkindex(::Type{Bool}, inds::AbstractUnitRange, v::AbstractFixedOrSmallVector{N,T}) where {N, T <: Base.HWReal}
    if isempty(v)
        true
    else
        min, max = extrema(v)
        first(inds) <= min && max <= last(inds)
    end
end

@inline function getindex(v::AbstractFixedOrSmallVector{N,T}, ii::OrdinalRange) where {N,T}
    @boundscheck checkbounds(v, ii)
    @inbounds SmallVector{N,T}(v[i] for i in ii)
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
    elseif VERSION >= v"1.11" && T <: HWType && (HAS_COMPRESS || N <= 32)  # slows down for larger N
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

function getindex_shuffle(::Val{M}, v::AbstractFixedOrSmallVector, ii::AbstractFixedVector) where M
    p1 = one(inttype(eltype(v)))
    p = map(i -> (i % typeof(p1)) - p1, ii)
    shuffle(Val(M), fixedvector(v), Tuple(p))
end

@inline function getindex(v::AbstractFixedOrSmallVector, ii::AbstractFixedVector{<:Any,<:BitInteger})
    @boundscheck checkbounds(v, ii)
    M = shufflewidth(v, ii)
    if M != 0
        getindex_shuffle(Val(M), v, ii)
    else
        map(i -> @inbounds(v[i]), ii)
    end
end

@inline function getindex(v::AbstractFixedOrSmallVector, ii::AbstractSmallVector{<:Any,<:BitInteger})
    @boundscheck checkbounds(v, ii)
    M = shufflewidth(v, ii)
    if M != 0
        SmallVector(getindex_shuffle(Val(M), v, fixedvector(ii)), length(ii))
    else
        map(i -> @inbounds(v[i]), ii)
    end
end

function filter(f::F, v::AbstractFixedOrSmallVector; kw...) where F
    @inbounds v[support(f, v; kw...)]
end

"""
    $(@__MODULE__).shufflewidth(::Val{N}, ::Type{T}) where {N,T}
    $(@__MODULE__).shufflewidth(v::AbstractFixedOrSmallVector{N,T}) where {N,T}
    $(@__MODULE__).shufflewidth(v::AbstractFixedOrSmallVector{N,T}, ii::AbstractFixedOrSmallVector{NI}) where {N,T,NI}

Returns a value `M` indicating which hardware-accelerated method to use
for vector indexing of a vector with element type `T` and capacity (at most) `N`.
The index vector is assumed to have capacity at most `N`, too.
The 2-argument version is equivalent to `shufflewidth(Val(max(N, NI)), T)`.

The value `0` indicates no hardware acceleration. The currently supported methods have values
`16` ([AVX](https://en.wikipedia.org/wiki/Advanced_Vector_Extensions)),
`32` ([AVX2](https://en.wikipedia.org/wiki/AVX2))
and `64` ([AVX-512](https://en.wikipedia.org/wiki/AVX-512), more precisely AVX-512_VBMI).

See also [`$(@__MODULE__).shuffle`](@ref).
"""
shufflewidth

shufflewidth(::Val, ::Type) = 0
shufflewidth(v::AbstractFixedOrSmallVector{N,T}) where {N,T} = shufflewidth(Val(N), T)
shufflewidth(v::AbstractFixedOrSmallVector{N,T}, ii::AbstractFixedOrSmallVector{NI}) where {N,T,NI} = shufflewidth(Val(max(N, NI)), T)

"""
    $(@__MODULE__).shuffle(::Val{M}, v::AbstractFixedVector{NV,VT}, p::NTuple{NP}) where {M,NV,VT,NP} -> FixedVector{NP,VT}

Uses hardware acceleration to permute the elements of `v` and returns the new vector `w`.
The permutation `p` must be 0-based. In other words, `w[i] == v[p[i]+1]` for any index `i` of `p`.
If `p[i]` is negative, then `w[i]` is set to zero.
Bounds are not checked. Moreover, negative index values must be in the range `-NV:-1`.

The parameter `M` indicates which hardware-accelerated method to use, as determined by `shufflewidth`.

See also [`$(@__MODULE__).shufflewidth`](@ref).
"""
shuffle
