#
# small vectors
#

export SmallVector, setindex,
    push, pop, pushfirst, popfirst, insert, deleteat, popat,
    support, fasthash

import Base: show, ==, copy, Tuple, empty,
    length, size, getindex, setindex,
    zero, zeros, ones, map,
    +, -, *, sum, prod, maximum, minimum

"""
    SmallVector{N,T} <: AbstractVector{T}

    SmallVector{N,T}(iter)
    SmallVector{N}(v::AbstractVector{T})
    SmallVector{N}(t::Tuple)

`SmallVector{N,T}` is an immutable vector type that can hold up to `N` elements of type `T`.
Here `N` can be any (small) positive integer. However, at least for bit integer
and hardware float types, one usually takes `N` to be a power of `2`.

The element type `T` can be omitted when creating the `SmallVector` from an `AbstractVector`
or from a tuple. In the latter case, `T` is determined by promoting the element types of the tuple.

The unused elements of a `SmallVector{N,T}` are filled with the value `default(T)`. This is
pre-defined for number types, `Char`, `String` and `Symbol`. For other types it must be set
explicitly.

See also [`capacity`](@ref), [`$(@__MODULE__).default`](@ref), `promote_type`.
"""
struct SmallVector{N,T} <: AbstractVector{T}
    b::Values{N,T}
    n::Int
end

"""
    capacity(::Type{<:SmallVector{N}}) where N -> N
    capacity(v::SmallVector{N}) where N -> N

Return `N`, which is the largest number of elements this vector type can hold.
"""
capacity(::Type{<:SmallVector{N}}) where N,
capacity(::SmallVector)

capacity(::Type{<:SmallVector{N}}) where N = N

function show(io::IO, v::SmallVector{N,T}) where {N,T}
    print(io, "$T[")
    join(io, v, ',')
    print(io, ']')
end

function Base.FastMath.eq_fast(v::SmallVector{N1,T1}, w::SmallVector{N2,T2}) where
        {N1, T1<:Union{FastInteger,FastFloat}, N2, T2<:Union{FastInteger,FastFloat}}
    length(v) == length(w) && iszero(padded_sub(v.b, w.b))
end

function ==(v::SmallVector{N1}, w::SmallVector{N2}) where {N1,N2}
    N = min(N1, N2)
    length(v) == length(w) && all(ntuple(i -> v.b[i] == w.b[i], Val(N)))
end

==(v::SmallVector{N1,T1}, w::SmallVector{N2,T2}) where {N1,T1<:FastInteger,N2,T2<:FastInteger} = @fastmath v == w

==(v::SmallVector{N1,T1}, w::SmallVector{N2,T2}) where {N1,T1<:FastInteger,N2,T2<:FastFloat} = @fastmath v == w

==(v::SmallVector{N1,T1}, w::SmallVector{N2,T2}) where {N1,T1<:FastFloat,N2,T2<:FastInteger} = @fastmath v == w

"""
    fasthash(v::SmallVector [, h0::UInt]) -> UInt

Return a hash for `v` that may be computed faster than the standard `hash`
for vectors. This new hash is consistent across all `SmallVectors`s
of the same element type, but it may not be compatible with `hash` or
with `fasthash` for a `SmallVector` having a different element type.

Currently, `fasthash` differs from `hash` only if the element type of `v`
is a bit integer type with at most 32 bits, `Bool` or `Char`.

See also `Base.hash`.

# Examples
```jldoctest
julia> v = SmallVector{8,Int8}([1, 5, 6]);

julia> fasthash(v)
0x6466067ab41d0916

julia> fasthash(v) == hash(v)
false

julia> w = SmallVector{16,Int8}(v); fasthash(v) == fasthash(w)
true

julia> w = SmallVector{8,Int16}(v); fasthash(v) == fasthash(w)
false
```
"""
fasthash(v::SmallVector, h0::UInt)

function fasthash(v::SmallVector{N,T}, h0::UInt) where {N,T}
    if (T <: BitInteger && bitsize(T) <= 32) || T == Bool || T == Char
        Base.hash_integer(bits(v.b), hash(length(v), h0))
    else
        hash(v, h0)
    end
end

copy(v::SmallVector) = v

convert(::Type{V}, v::AbstractVector) where {N, V <: SmallVector{N}} = V(v)

Tuple(v::SmallVector) = ntuple(i -> v[i], length(v))
# this seems to be fast for length(v) <= 10

length(v::SmallVector) = v.n

size(v::SmallVector) = (length(v),)

@inline function getindex(v::SmallVector, i::Int)
    @boundscheck checkbounds(v, i)
    @inbounds v.b[i]
end

@inline function setindex(v::SmallVector, x, i::Integer)
    @boundscheck checkbounds(v, i)
    SmallVector((@inbounds setindex(v.b, x, i)), length(v))
end

"""
    empty(v::V) where V <: SmallVector -> V

Return an empty `SmallVector` of the same type as `v`.
"""
empty(v::SmallVector{N,T}) where {N,T} = SmallVector(default(Values{N,T}), 0)

zero(v::SmallVector) = SmallVector(zero(v.b), length(v))

"""
    zeros(::Type{V}, n::Integer) where V <: SmallVector -> V

Return a `SmallVector` of type `V` containing `n` zeros.

See also [`ones(::Type{<:SmallVector}, ::Integer)`](@ref).
"""
zeros(::Type{<:SmallVector}, ::Integer)

function zeros(::Type{SmallVector{N,T}}, n::Integer) where {N,T}
    n <= N || error("vector cannot have more than $N elements")
    SmallVector(zero(Values{N,T}), n)
end

"""
    ones(::Type{V}, n::Integer) where V <: SmallVector -> V

Return a `SmallVector` of type `V` containing `n` ones.

See also [`zeros(::Type{<:SmallVector}, ::Integer)`](@ref).
"""
ones(::Type{<:SmallVector}, ::Integer)

function ones(::Type{SmallVector{N,T}}, n::Integer) where {N,T}
    n <= N || error("vector cannot have more than $N elements")
    b = ones(Values{N,T})
    SmallVector((@inbounds padtail(b, -one(T), n)), n)
end

function SmallVector{N,T}(v::SmallVector{M}) where {N,T,M}
    M <= N || length(v) <= N || error("vector cannot have more than $N elements")
    t = ntuple(i -> i <= M ? T(v.b[i]) : default(T), Val(N))
    SmallVector{N,T}(t, length(v))
end

function SmallVector{N,T}(v::Union{AbstractVector,Tuple}) where {N,T}
    n = length(v)
    n <= N || error("vector cannot have more than $N elements")
    i1 = firstindex(v)
    t = ntuple(i -> i <= n ? T(v[i+i1-1]) : default(T), Val(N))
    SmallVector{N,T}(t, n)
end

function SmallVector{N,T}(iter) where {N,T}
    b = default(Values{N,T})
    n = 0
    for (i, x) in enumerate(iter)
        (n = i) <= N || error("vector cannot have more than $N elements")
        b = @inbounds setindex(b, x, i)
    end
    SmallVector(b, n)
end

SmallVector{N}(v::AbstractVector{T}) where {N,T} = SmallVector{N,T}(v)

function SmallVector{N}(v::V) where {N, V <: Tuple}
    T = promote_type(fieldtypes(V)...)
    SmallVector{N,T}(v)
end

+(v::SmallVector) = v

@inline function +(v::SmallVector, w::SmallVector)
    @boundscheck length(v) == length(w) || error("vectors must have the same length")
    SmallVector(padded_add(v.b, w.b), length(v))
end

-(v::SmallVector) = SmallVector(-v.b, length(v))

@inline function -(v::SmallVector, w::SmallVector)
    @boundscheck length(v) == length(w) || error("vectors must have the same length")
    SmallVector(padded_sub(v.b, w.b), length(v))
end

Base.FastMath.mul_fast(c, v::SmallVector) = SmallVector(c*v.b, length(v))

*(c::Integer, v::SmallVector{N}) where N = @fastmath c*v

function *(c::Number, v::SmallVector{N}) where N
# multiplication by Inf and NaN does not preserve zero padding
    c0 = zero(c)
    n = length(v)
    t = ntuple(i -> (i <= n ? c : c0) * v.b[i], Val(N))
    SmallVector(Values{N}(t), n)
end

*(v::SmallVector, c::Number) = c*v

function sum(v::SmallVector{N,T}) where {N,T}
    if T <: Base.BitSignedSmall
        sum(Int, v.b)
    elseif T <: Base.BitUnsignedSmall
        sum(UInt, v.b)
    elseif T <: Union{Base.BitInteger,Base.HWReal}
        sum(v.b)
    else
        invoke(sum, Tuple{AbstractVector}, v)
    end
end

function prod(v::SmallVector{N,T}) where {N,T}
    if !(T <: Union{Base.BitInteger,Base.HWReal})
        invoke(prod, Tuple{AbstractVector}, v)
    else
        b = padtail(v.b, one(T), length(v))
        if T <: Base.BitSignedSmall
            prod(Int, b)
        elseif T <: Base.BitUnsignedSmall
            prod(UInt, b)
        else
            prod(b)
        end
    end
end

function maximum(v::SmallVector{N,T}; init = missing) where {N,T}
    if isempty(v)
        if init === missing
            error("collection must be non-empty unless `init` is given")
        else
            return init
        end
    elseif T <: Unsigned && T <: Base.HWReal
        maximum(v.b)
    elseif T <: Integer && T <: Base.HWReal
        @inbounds maximum(padtail(v.b, typemin(T), length(v)))
    else
        invoke(maximum, Tuple{AbstractVector}, v)
    end
end

function minimum(v::SmallVector{N,T}; init = missing) where {N,T}
    if isempty(v)
        if init === missing
            error("collection must be non-empty unless `init` is given")
        else
            return init
        end
    elseif T <: Integer && T <: Base.HWReal
        @inbounds minimum(padtail(v.b, typemax(T), length(v)))
    else
        invoke(minimum, Tuple{AbstractVector}, v)
    end
end

@inline function push(v::SmallVector{N}, x) where N
    n = length(v)
    @boundscheck n < N || error("vector cannot have more than $N elements")
    @inbounds SmallVector(setindex(v.b, x, n+1), n+1)
end

"""
    push(v::SmallVector{N,T}, xs...) where {N,T} -> SmallVector{N,T}

Return the `SmallVector` obtained from `v` by appending the other arguments `xs`.
The length of `v` must be less than `N`.

This is the non-mutating analog of `Base.push!`.
"""
@propagate_inbounds push(v::SmallVector, xs...) = foldl(push, xs; init = v)

"""
    pop(v::SmallVector{N,T}) where {N,T} -> Tuple{SmallVector{N,T},T}

Return the tuple `(w, x)` where `x` is the last element of `v`
and `w` obtained from `v` by dropping this element.
The vector `v` must not be empty.

This is the non-mutating analog of `Base.pop!`.
"""
pop(v::SmallVector)

@inline function pop(v::SmallVector{N,T}) where {N,T}
    n = length(v)
    @boundscheck iszero(n) && error("vector must not be empty")
    @inbounds SmallVector(setindex(v.b, default(T), n), n-1), v[n]
end

@inline function pushfirst(v::SmallVector{N}, x) where N
    n = length(v)
    @boundscheck n < N || error("vector cannot have more than $N elements")
    SmallVector(pushfirst(v.b, x), n+1)
end

"""
    pushfirst(v::SmallVector{N,T}, xs...) where {N,T} -> SmallVector{N,T}

Return the `SmallVector` obtained from `v` by prepending the other arguments `xs`.
The length of `v` must be less than `N`.

This is the non-mutating analog of `Base.pushfirst!`.
"""
@propagate_inbounds pushfirst(v::SmallVector, xs...) = foldr((x, v) -> pushfirst(v, x), xs; init = v)

"""
    popfirst(v::SmallVector{N,T}) where {N,T} -> Tuple{SmallVector{N,T},T}

Return the tuple `(w, x)` where `x` is the first element of `v`
and `w` obtained from `v` by dropping this element.
The vector `v` must not be empty.

This is the non-mutating analog of `Base.popfirst!`.
"""
@inline function popfirst(v::SmallVector)
    n = length(v)
    @boundscheck iszero(n) && error("vector must not be empty")
    c, x = popfirst(v.b)
    SmallVector(c, n-1), x
end

"""
    insert(v::SmallVector{N,T}, i::Integer, x) where {N,T} -> SmallVector{N,T}

Return the `SmallVector` obtained from `v` by inserting `x` at position `i`.
The position `i` must be between `1` and `length(v)+1`, and `length(v)` must be less than `N`.

This is the non-mutating analog of `Base.insert!`.
"""
@inline function insert(v::SmallVector{N}, i::Integer, x) where N
    n = length(v)
    @boundscheck begin
        1 <= i <= n+1 || throw(BoundsError(v, i))
        n < N || error("vector cannot have more than $N elements")
    end
    @inbounds SmallVector(insert(v.b, i, x), n+1)
end

"""
    deleteat(v::V, i::Integer) where V <: SmallVector -> V

Return the `SmallVector` obtained from `v` by deleting the element at position `i`.
The position `i` must be between `1` and `length(v)`.

This is the non-mutating analog of `Base.deleteat!`.
"""
@propagate_inbounds deleteat(v::SmallVector, i::Integer) = first(popat(v, i))

"""
    popat(v::SmallVector{N,T}, i::Integer) where {N,T} -> Tuple{SmallVector{N,T},T}

Return the tuple `(w, x)` where `w` obtained from `v` by deleting the element `x`
at position `i`. The latter must be between `1` and `length(v)`.

This is the non-mutating analog of `Base.popat!`.
"""
@inline function popat(v::SmallVector, i::Integer)
    n = length(v)
    @boundscheck checkbounds(v, i)
    c, x = @inbounds popat(v.b, i)
    SmallVector(c, n-1), x
end

"""
    support(v::SmallVector) -> SmallSet

Return the `SmallSet` with the indices of the non-zero elements of `v`.

See also [`SmallSet`](@ref).

# Example
```jldoctest
julia> v = SmallVector{8,Int8}([1, 0, 2, 0, 0, 3]);

julia> support(v)
SmallSet{UInt64} with 3 elements:
  1
  3
  6
```
"""
support(v::SmallVector) = convert(SmallSet{UInt}, bits(map(!iszero, v.b)))

Base.@assume_effects :total _return_type(f, args) = typeof(f(args...))

function map(f::F, vs::Vararg{SmallVector,M}) where {F,M}
    N = minimum(map(capacity, vs))
    n = minimum(map(length, vs))
    tt = ntuple(Val(N)) do i
        ntuple(j -> @inbounds(vs[j].b[i]), Val(M))
    end
    T = _return_type(f, tt[1])
    t = ntuple(i -> i <= n ? f(tt[i]...) : default(T), Val(N))
    SmallVector(Values{N,T}(t), n)
end

map_fast(f::F, v::SmallVector) where F = SmallVector(map(f, v.b), length(v))

for f in (abs, abs2, sign, signbit, sqrt)
    @eval map(::$(typeof(f)), v::SmallVector) = map_fast($f, v)
end
