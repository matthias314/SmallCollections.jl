#
# small vectors
#

export SmallVector, fasthash, sum_fast

import Base: ==, copy, Tuple, empty,
    length, size, getindex, setindex, rest,
    zero, map,
    +, -, *, sum, prod, maximum, minimum, extrema

"""
    SmallVector{N,T} <: AbstractSmallVector{T}

    SmallVector{N,T}()
    SmallVector{N,T}(iter)
    SmallVector{N}(v::AbstractVector{T})
    SmallVector{N}(t::Tuple)

`SmallVector{N,T}` is an immutable vector type that can hold up to `N` elements of type `T`.
Here `N` can be any (small) positive integer. However, at least for bit integer
and hardware float types, one usually takes `N` to be a power of `2`.

The element type `T` can be omitted when creating the `SmallVector` from an `AbstractVector`
or from a tuple. In the latter case, `T` is determined by promoting the element types of the tuple.
If no argument is given, then an empty vector is returned.

The unused elements of a `SmallVector{N,T}` are filled with the value `default(T)`, which is
predefined for several types including `Number`. Default values for other types must be defined
explicitly.

Addition and subtraction of two `SmallVector`s is possible even if the vectors have different
capacity. (Of course, their lengths must agree.) The capacity of the result is the smaller
of the arguments' capacities in this case.

See also [`capacity`](@ref), [`$(@__MODULE__).default`](@ref), `promote_type`.

# Examples
```jldoctest
julia> v = SmallVector{8,Int8}(2*x for x in 1:3)
3-element SmallVector{8, Int8}:
 2
 4
 6

julia> w = SmallVector{9}((1, 2.5, 4))
3-element SmallVector{9, Float64}:
 1.0
 2.5
 4.0

julia> v+w
3-element SmallVector{8, Float64}:
  3.0
  6.5
 10.0
```
"""
struct SmallVector{N,T} <: AbstractSmallVector{T}
    b::Values{N,T}
    n::Int
end

capacity(::Type{<:SmallVector{N}}) where N = N

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

rest(v::SmallVector, (r, i)) = @inbounds v[i+1:last(r)]

@inline function getindex(v::SmallVector, i::Int)
    @boundscheck checkbounds(v, i)
    @inbounds v.b[i]
end

#=
@propagate_inbounds getindex(v::V, ii::AbstractVector{<:Integer}) where V <: SmallVector =
    V(v[i] for i in ii)
=#

@inline function getindex(v::SmallVector{N,T}, ii::AbstractVector{<:Integer}) where {N,T}
    n = length(ii)
    @boundscheck begin
        n <= N || error("vector cannot have more than $N elements")
        checkbounds(v, ii)
    end
    t = ntuple(Val(N)) do i
        @inbounds i <= n ? v[ii[i]] : default(T)
    end
    SmallVector(Values{N,T}(t), n)
end

@inline function setindex(v::SmallVector, x, i::Integer)
    @boundscheck checkbounds(v, i)
    SmallVector((@inbounds _setindex(v.b, x, i)), length(v))
end

@inline function addindex(v::SmallVector, x, i::Integer)
    @boundscheck checkbounds(v, i)
    @inbounds v += setindex(zero(v), x, i)
end

"""
    empty(v::V) where V <: SmallVector -> V
    empty(v::SmallVector{N}, U::Type) where {N,U} -> SmallVector{N,U}

Called with one argument, return an empty `SmallVector` of the same type as `v`.
Called with two arguments, return an empty `SmallVector` with the same capacity as `v`
and element type `U`.
"""
empty(v::SmallVector),
empty(v::SmallVector, ::Type)

empty(v::SmallVector{N,T}, ::Type{U} = T) where {N,T,U} = SmallVector{N,U}()

default(::Type{SmallVector{N,T}}) where {N,T} = SmallVector{N,T}()

zero(v::SmallVector) = SmallVector(zero(v.b), length(v))

function zeros(::Type{SmallVector{N,T}}, n::Integer) where {N,T}
    n <= N || error("vector cannot have more than $N elements")
    SmallVector(zero(Values{N,T}), n)
end

function ones(::Type{SmallVector{N,T}}, n::Integer) where {N,T}
    n <= N || error("vector cannot have more than $N elements")
    t = ntuple(Val(N)) do i
        i <= n ? one(T) : zero(T)
    end
    SmallVector{N,T}(Values{N,T}(t), n)
end

SmallVector{N,T}() where {N,T} = SmallVector{N,T}(default(Values{N,T}), 0)

function SmallVector{N,T}(v::SmallVector{M}) where {N,T,M}
    M <= N || length(v) <= N || error("vector cannot have more than $N elements")
    t = ntuple(i -> i <= M ? convert(T, v.b[i]) : default(T), Val(N))
    SmallVector{N,T}(t, length(v))
end

function SmallVector{N,T}(v::Union{AbstractVector,Tuple}) where {N,T}
    n = length(v)
    n <= N || error("vector cannot have more than $N elements")
    i1 = firstindex(v)
    t = ntuple(i -> i <= n ? convert(T, @inbounds(v[i+i1-1])) : default(T), Val(N))
    SmallVector{N,T}(t, n)
end

function SmallVector{N,T}(g::Base.Generator{<:Union{AbstractVector,Tuple}}) where {N,T}
    v = g.iter
    n = length(v)
    n <= N || error("vector cannot have more than $N elements")
    i1 = firstindex(v)
    t = ntuple(i -> i <= n ? convert(T, g.f(@inbounds(v[i+i1-1]))) : default(T), Val(N))
    SmallVector{N,T}(t, n)
end

function SmallVector{N,T}(iter) where {N,T}
    b = default(Values{N,T})
    n = 0
    for (i, x) in enumerate(iter)
        (n = i) <= N || error("vector cannot have more than $N elements")
        b = @inbounds _setindex(b, x, i)
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
    elseif T <: Base.BitInteger
        sum(v.b)
    else
        n = length(v)
        n == 0 && return zero(T)
        @inbounds s = v[1]
        for i in 2:n
            @inbounds s += v[i]
        end
        s
    end
end

"""
    sum_fast(v::SmallVector{N,T}) where {N,T}

Return the sum of the elements of `v` using `@fastmath` arithmetic
if `T` is `Float32` or `Float64`. Otherwise return `sum(v)`.

See also `Base.@fastmath`.

# Example
```jldoctest
julia> v = SmallVector{4}([-0.0, -0.0])
2-element SmallVector{4, Float64}:
 -0.0
 -0.0

julia> sum(v), sum_fast(v)
(-0.0, 0.0)
```
"""
sum_fast(v::SmallVector) = sum(v)
sum_fast(v::SmallVector{N,T}) where {N, T <: FastFloat} = @fastmath foldl(+, v.b)

function prod(v::SmallVector{N,T}) where {N,T}
    if T <: Base.BitInteger
        b = padtail(v.b, length(v), one(T))
        if T <: Base.BitSignedSmall
            prod(Int, b)
        elseif T <: Base.BitUnsignedSmall
            prod(UInt, b)
        else
            prod(b)
        end
    else
        n = length(v)
        n == 0 && return one(T)
        @inbounds s = v[1]
        for i in 2:n
            @inbounds s *= v[i]
        end
        s
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
        @inbounds maximum(padtail(v.b, length(v), typemin(T)))
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
        @inbounds minimum(padtail(v.b, length(v), typemax(T)))
    else
        invoke(minimum, Tuple{AbstractVector}, v)
    end
end

extrema(v::SmallVector; init::Tuple{Any,Any} = (missing, missing)) =
    (minimum(v; init = init[1]), maximum(v; init = init[2]))

@propagate_inbounds push(v::SmallVector, xs...) = append(v, xs)

# TODO: needed?
@inline function push(v::SmallVector{N}, x) where N
    n = length(v)
    @boundscheck n < N || error("vector cannot have more than $N elements")
    @inbounds SmallVector(_setindex(v.b, x, n+1), n+1)
end

@inline function pop(v::SmallVector{N,T}) where {N,T}
    n = length(v)
    @boundscheck iszero(n) && error("vector must not be empty")
    @inbounds SmallVector(_setindex(v.b, default(T), n), n-1), v[n]
end

@inline function pushfirst(v::SmallVector{N}, xs...) where N
    n = length(xs)+length(v)
    @boundscheck n <= N || error("vector cannot have more $N elements")
    SmallVector(pushfirst(v.b, xs...), n)
end

@inline function popfirst(v::SmallVector)
    n = length(v)
    @boundscheck iszero(n) && error("vector must not be empty")
    c, x = popfirst(v.b)
    SmallVector(c, n-1), x
end

@inline function insert(v::SmallVector{N}, i::Integer, x) where N
    n = length(v)
    @boundscheck begin
        1 <= i <= n+1 || throw(BoundsError(v, i))
        n < N || error("vector cannot have more than $N elements")
    end
    @inbounds SmallVector(insert(v.b, i, x), n+1)
end

@inline function duplicate(v::SmallVector{N,T}, i::Integer) where {N,T}
    @boundscheck begin
        checkbounds(v, i)
        length(v) < N || error("vector cannot have more than $N elements")
    end
    t = ntuple(Val(N)) do j
        j <= i ? v.b[j] : v.b[j-1]
    end
    SmallVector(Values{N,T}(t), length(v)+1)
end

@propagate_inbounds deleteat(v::SmallVector, i::Integer) = first(popat(v, i))

@inline function popat(v::SmallVector, i::Integer)
    n = length(v)
    @boundscheck checkbounds(v, i)
    c, x = @inbounds popat(v.b, i)
    SmallVector(c, n-1), x
end

@propagate_inbounds append(v::SmallVector, ws...) = foldl(append, ws; init = v)

@propagate_inbounds append(v::SmallVector, w) = foldl(push, w; init = v)

@inline function append(v::SmallVector{N,T}, w::Union{AbstractVector,Tuple}) where {N,T}
    n = length(v)
    m = n+length(w)
    @boundscheck m <= N || error("vector cannot have more than $N elements")
    t = ntuple(Val(N)) do i
        @inbounds n < i <= m ? convert(T, w[i-n]) : v.b[i]
    end
    SmallVector{N,T}(Values{N,T}(t), m)
end

@propagate_inbounds function prepend(v::SmallVector, ws...)
    foldr((w, v) -> prepend(v, w), ws; init = v)
end

@inline function prepend(v::SmallVector{N,T}, w::Union{AbstractVector,Tuple}) where {N,T}
    n = length(v)
    m = n+length(w)
    @boundscheck m <= N || error("vector cannot have more than $N elements")
    SmallVector{N,T}(prepend(v.b, w), m)
end

prepend(v::SmallVector{N,T}, w) where {N,T} = append(SmallVector{N,T}(w), v)

support(v::SmallVector) = convert(SmallBitSet{UInt}, bits(map(!iszero, v.b)))

"""
    map(f, v::SmallVector...) -> SmallVector

Apply `f` to the argument vectors elementwise and stop when one of them is exhausted.
Note that the capacity of the resulting `SmallVector` is the minimum of the argument
vectors' capacities.

See also [`capacity`](@ref), `Base.map(f, v::AbstractVector...)`,
[Section "Broadcasting"](@ref sec-broadcasting).

# Examples
```jldoctest
julia> v = SmallVector{8}(1:3); w = SmallVector{4}(2.0:4.0); map(*, v, w)
3-element SmallVector{4, Float64}:
  2.0
  6.0
 12.0

julia> v = SmallVector{8}('a':'e'); w = SmallVector{4}('x':'z'); map(*, v, w)
3-element SmallVector{4, String}:
 "ax"
 "by"
 "cz"
```
"""
function map(f::F, vs::Vararg{SmallVector,M}) where {F,M}
    n = minimum(length, vs)
    _map(f, n, vs...)
end

function map_fast(f::F, n, vs::Vararg{SmallVector{N},M}) where {F,N,M}
    bs = map(v -> v.b, vs)
    SmallVector(map(f, bs...), n)
end

function map_fast_pad(f::F, n, vs::Vararg{SmallVector{N},M}) where {F,N,M}
    bs = map(v -> v.b, vs)
    b = map(f, bs...)
    SmallVector(padtail(b, n), n)
end

#
# broadcast
#

using Base.Broadcast: AbstractArrayStyle, DefaultArrayStyle, Broadcasted, flatten
import Base.Broadcast: BroadcastStyle

"""
    $(@__MODULE__).SmallVectorStyle <: Broadcast.AbstractArrayStyle{1}

The broadcasting style used for `SmallVector`.

See also `Broadcast.AbstractArrayStyle`.
"""
struct SmallVectorStyle <: AbstractArrayStyle{1} end

BroadcastStyle(::Type{<:SmallVector}) = SmallVectorStyle()
BroadcastStyle(::SmallVectorStyle, ::DefaultArrayStyle{0}) = SmallVectorStyle()
BroadcastStyle(::SmallVectorStyle, ::DefaultArrayStyle{N}) where N = DefaultArrayStyle{N}()

function copy(bc::Broadcasted{SmallVectorStyle})
    bcflat = flatten(bc)
    i = findfirst(x -> x isa SmallVector, bcflat.args)
    n = length(bcflat.args[i])
    _map(bcflat.f, n, bcflat.args...)
end

_eltype(v::Union{AbstractVector,Tuple}) = eltype(v)
_eltype(x::T) where T = T

_capacity(v::SmallVector) = capacity(v)
_capacity(_) = typemax(Int)

_getindex(v::SmallVector, i) = @inbounds v.b[i]
_getindex(v::Tuple, i) = i <= length(v) ? @inbounds(v[i]) : default(v[1])
_getindex(x, i) = x

function _map(f::F, n, vs::Vararg{Any,M}) where {F,M}
    N = minimum(_capacity, vs)
    TT = map(_eltype, vs)
    U = Core.Compiler.return_type(f, Tuple{TT...})
    if isconcretetype(U)
        tt = ntuple(Val(N)) do i
            ntuple(j -> _getindex(vs[j], i), Val(M))
        end
        t = ntuple(Val(N)) do i
            i <= n ? f(tt[i]...) : default(U)
        end
        SmallVector(Values{N,U}(t), n)
    else
        VT = map(vs) do v
            T = typeof(v)
            T <: SmallVector ? AbstractVector{eltype(T)} : T
        end
        w = invoke(map, Tuple{F,VT...}, f, vs...)
        SmallVector{N}(w)
    end
end

_map(f::Union{typeof.(
        (&, round, floor, ceil, trunc, abs, abs2, sign, sqrt)
    )...}, n, vs::SmallVector{N}...) where N = map_fast(f, n, vs...)

_map(::typeof(*), n, vs::SmallVector{N,<:Integer}...) where N = map_fast(*, n, vs...)
_map(::typeof(signbit), n, v::SmallVector{N,<:Integer}) where N = map_fast(signbit, n, v)

_map(f::Union{typeof.(
        (+, -, *, ~, |, xor, nand, nor, ==, !=, <, >, <=, >=, ===, isequal, signbit)
    )...}, n, vs::SmallVector{N}...) where N = map_fast_pad(f, n, vs...)

_map(::typeof(/), n,
        v::SmallVector{N,<:Union{Integer,AbstractFloat}},
        w::SmallVector{N,<:Union{Integer,AbstractFloat}}) where N =
    map_fast_pad(/, n, v, w)
