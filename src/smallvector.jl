#
# small vectors
#

export AbstractSmallVector, SmallVector, sum_fast, extrema_fast

import Base: ==, Tuple, empty,
    length, size, getindex, setindex, rest, split_rest,
    zero, map, reverse, findfirst, findlast, in,
    +, -, *, sum, prod, maximum, minimum, extrema

import Base.FastMath: eq_fast, mul_fast

"""
    AbstractSmallVector{N,T} <: AbstractVector{T}

`AbstractSmallVector{N,T}` is the supertype of `SmallVector{N,T}` and `MutableSmallVector{N,T}`.

See also [`SmallVector`](@ref), [`MutableSmallVector`](@ref).
"""
abstract type AbstractSmallVector{N,T} <: AbstractCapacityVector{T} end

const SmallLength = Int16

"""
    SmallVector{N,T} <: AbstractSmallVector{N,T}

    SmallVector{N,T}()
    SmallVector{N,T}(iter)
    SmallVector{N}(iter)
    SmallVector(v::PackedVector{T})
    SmallVector(v::AbstractSmallVector)

`SmallVector{N,T}` is an immutable vector type that can hold up to `N` elements of type `T`.
Here `N` can be any (small) positive integer. However, at least for bit integer
and hardware float types, one usually takes `N` to be a power of `2`.

The element type `T` can be omitted when creating the `SmallVector` from an iterator
that has an element type, for example from an `AbstractVector` or a tuple.
In the latter case, `T` is determined by promoting the element types of the tuple.
If no argument is given, then an empty vector is returned.
If the `SmallVector` is created from an `AbstractSmallVector` or `PackedVector` `v`
and the parameter `N` is omitted, then it is set to capacity of `v`.

The unused elements of a `SmallVector{N,T}` are filled with the value `default(T)`, which is
predefined for several types including `Number`. Default values for other types must be defined
explicitly.

Addition and subtraction of two `SmallVector`s is possible even if the vectors have different
capacity. (Of course, their lengths must agree.) The capacity of the result is the smaller
of the arguments' capacities in this case.

See also [`MutableSmallVector`](@ref), [`capacity`](@ref), [`$(@__MODULE__).default`](@ref),
`Base.IteratorEltype`, `promote_type`.

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
struct SmallVector{N,T} <: AbstractSmallVector{N,T}
    b::Values{N,T}
    n::SmallLength
end

SmallVector(v::AbstractFixedVector, n::Integer) = SmallVector(v, n % SmallLength)

capacity(::Type{<:AbstractSmallVector{N}}) where N = N

for cmp in (:(==), :(eq_fast))
    @eval $cmp(v::AbstractSmallVector, w::AbstractSmallVector) =
        length(v) == length(w) && all(map($cmp, v.b, w.b))
end

"""
    fasthash(v::AbstractSmallVector [, h0::UInt]) -> UInt

Return a hash for `v` that may be computed faster than the standard `hash`
for vectors. This new hash is consistent across all `AbstractSmallVector`s
of the same element type, but it may not be compatible with `hash` or
with `fasthash` for a `AbstractSmallVector` having a different element type.

Currently, `fasthash` differs from `hash` only if the element type of `v`
is a bit integer type with at most 32 bits, `Bool` or `Char`.

See also [`fasthash(::PackedVector, ::UInt)`](@ref), `Base.hash`.

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
fasthash(::AbstractSmallVector, ::UInt)

function fasthash(v::AbstractSmallVector{N,T}, h0::UInt) where {N,T}
    if (T <: BitInteger && bitsize(T) <= 32) || T == Bool || T == Char
        fasthash(v.b, hash(length(v), h0))
    else
        hash(v, h0)
    end
end

convert(::Type{V}, v::V) where V <: AbstractSmallVector = v
convert(::Type{V}, v::Union{AbstractVector,Tuple}) where V <: AbstractSmallVector = V(v)

Tuple(v::AbstractSmallVector) = ntuple(i -> v[i], length(v))
# this seems to be fast for length(v) <= 10

size(v::AbstractSmallVector) = (v.n % Int,)

rest(v::AbstractSmallVector, (r, i) = (eachindex(v), 0)) = @inbounds v[i+1:last(r)]

if VERSION >= v"1.9"
    @inline function split_rest(v::AbstractSmallVector, n::Int, (r, i) = (eachindex(v), 0))
        m = length(r)-n
        @boundscheck (n >= 0 && m >= i) || error("impossible number of elements requested")
        @inbounds v[i+1:m], v[m+1:end]
    end
end

@inline function getindex(v::AbstractSmallVector, i::Int)
    @boundscheck checkbounds(v, i)
    @inbounds v.b[i]
end

#=
@propagate_inbounds getindex(v::V, ii::AbstractVector{<:Integer}) where V <: AbstractSmallVector =
    V(v[i] for i in ii)
=#

@inline function getindex(v::AbstractSmallVector{N,T}, ii::AbstractVector{<:Integer}) where {N,T}
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

@inline function setindex(v::AbstractSmallVector, x, i::Integer)
    @boundscheck checkbounds(v, i)
    SmallVector((@inbounds setindex(v.b, x, i)), length(v))
end

@inline function addindex(v::AbstractSmallVector, x, i::Integer)
    @boundscheck checkbounds(v, i)
    @inbounds v + setindex(zero(v), x, i)
end

"""
    empty(v::AbstractSmallVector{N}, S::Type) where {N,S} -> AbstractSmallVector{N,S}

Return an empty `AbstractSmallVector` with the same capacity as `v` and element type `U`.
The resulting vector is mutable if and only if `v` is so.

See also [`empty(v::AbstractCapacityVector)`](@ref).
"""
empty(v::AbstractSmallVector, ::Type)

empty(v::SmallVector{N,T}, ::Type{U} = T) where {N,T,U} = SmallVector{N,U}()

default(::Type{V}) where V <: AbstractSmallVector = V()

@inline zero(v::V) where V <: AbstractSmallVector = V(zero(v.b), length(v))

function zeros(::Type{V}, n::Integer) where {N, T, V <: AbstractSmallVector{N,T}}
    n <= N || error("vector cannot have more than $N elements")
    V(zero(Values{N,T}), n)
end

function ones(::Type{V}, n::Integer) where {N, T, V <: AbstractSmallVector{N,T}}
    n <= N || error("vector cannot have more than $N elements")
    t = ntuple(Val(N)) do i
        i <= n ? one(T) : zero(T)
    end
    V(Values{N,T}(t), n)
end

(::Type{V})() where {N,T,V<:AbstractSmallVector{N,T}} = V(default(Values{N,T}), 0)

SmallVector{N,T}(v::AbstractSmallVector{N}) where {N,T} = SmallVector{N,T}(v.b, v.n)

function SmallVector{N,T}(iter) where {N,T}
    isbitstype(T) && return @inline SmallVector(MutableSmallVector{N,T}(iter))
    b = default(Values{N,T})
    n = 0
    for (i, x) in enumerate(iter)
        (n = i) <= N || error("vector cannot have more than $N elements")
        b = @inbounds setindex(b, x, i)
    end
    SmallVector{N,T}(b, n)
end

function (::Type{V})(iter::I) where {N,V<:AbstractSmallVector{N},I}
    Base.IteratorEltype(I) isa Base.HasEltype || error("cannot determine element type")
    T = element_type(I)
    V{T}(iter)
end

+(v::AbstractSmallVector) = v
-(v::AbstractSmallVector) = SmallVector(-v.b, length(v))

for op in (:+, :-)
    @eval @inline function $op(v::AbstractSmallVector, w::AbstractSmallVector)
        @boundscheck length(v) == length(w) || error("vectors must have the same length")
        SmallVector(map($op, v.b, w.b), length(v))
    end
end

@inline mul_fast(c::Number, v::AbstractSmallVector) = SmallVector(c*v.b, length(v))
mul_fast(v::AbstractSmallVector, c::Number) = mul_fast(c, v)

*(c::Integer, v::AbstractSmallVector{N}) where N = @fastmath c*v

function *(c::Number, v::AbstractSmallVector{N}) where N
# multiplication by Inf and NaN does not preserve zero padding
    c0 = zero(c)
    n = length(v)
    t = ntuple(i -> (i <= n ? c : c0) * v.b[i], Val(N))
    SmallVector(Values{N}(t), n)
end

*(v::AbstractSmallVector, c::Number) = c*v

function sum(v::AbstractSmallVector{N,T}) where {N,T}
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
    sum_fast(v::AbstractSmallVector{N,T}) where {N,T}

Return the sum of the elements of `v` using `@fastmath` arithmetic
if `T` is `Float32` or `Float64`. Otherwise return `sum(v)`.

See also `Base.sum`, `Base.@fastmath`.

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
sum_fast(v::AbstractSmallVector) = sum(v)
sum_fast(v::AbstractSmallVector{N,T}) where {N, T <: FastFloat} = @fastmath foldl(+, v.b)

function prod(v::AbstractSmallVector{N,T}) where {N,T}
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

function maximum(v::AbstractSmallVector{N,T}; init = missing) where {N,T}
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

@fastmath function maximum(v::AbstractSmallVector{N,T}; init = missing) where {N,T}
    if isempty(v)
        if init === missing
            error("collection must be non-empty unless `init` is given")
        else
            return init
        end
    elseif T <: Unsigned && T <: Base.HWReal
        maximum(v.b)
    elseif T <: Base.HWReal
        @inbounds maximum(padtail(v.b, length(v), typemin(T)))
    else
        invoke(maximum, Tuple{AbstractVector}, v)
    end
end

function minimum(v::AbstractSmallVector{N,T}; init = missing) where {N,T}
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

@fastmath function minimum(v::AbstractSmallVector{N,T}; init = missing) where {N,T}
    if isempty(v)
        if init === missing
            error("collection must be non-empty unless `init` is given")
        else
            return init
        end
    elseif T <: Base.HWReal
        @inbounds minimum(padtail(v.b, length(v), typemax(T)))
    else
        invoke(minimum, Tuple{AbstractVector}, v)
    end
end

extrema(v::AbstractSmallVector; init::Tuple{Any,Any} = (missing, missing)) =
    (minimum(v; init = init[1]), maximum(v; init = init[2]))

"""
    extrema_fast(v::AbstractSmallVector; [init])

Return the `@fastmath` minimum and maximum of the elements of `v`.
The `init` keyword argument may not be used.

See also `Base.extrema`, `Base.@fastmath`.
"""
extrema_fast(v::AbstractSmallVector; init::Tuple{Any,Any} = (missing, missing)) =
    @fastmath (minimum(v; init = init[1]), maximum(v; init = init[2]))

@inline function reverse(v::AbstractSmallVector, start::Integer = 1, stop::Integer = length(v))
    @boundscheck checkbounds(v, start:stop)
    @inbounds b = reverse(v.b, start, stop)
    SmallVector(b, length(v))
end

findfirst(v::AbstractSmallVector{N,Bool}) where N = findfirst(v.b)
findlast(v::AbstractSmallVector{N,Bool}) where N = findlast(v.b)

function findfirst(pred::FastTest, v::AbstractSmallVector{<:Any,<:FastTestType})
    i = @inline findfirst(pred, v.b)
    i === nothing || i > length(v) ? nothing : i
end

function findlast(pred::FastTest, v::AbstractSmallVector{<:Any,<:FastTestType})
    m = bits(map(pred, v.b))
    m &= unsafe_shl(one(m), length(v)) - one(m)
    iszero(m) ? nothing : bitsize(m)-leading_zeros(m)
end

Base._any(f, v::AbstractSmallVector, ::Colon) = findfirst(f, v) !== nothing
Base._all(f, v::AbstractSmallVector, ::Colon) = findfirst((!)∘f, v) === nothing

Base.hasfastin(::Type{V}) where V <: AbstractSmallVector = Base.hasfastin(fieldtype(V, :b))

in(x, v::AbstractSmallVector) = findfirst(==(x), v) !== nothing

@propagate_inbounds push(v::AbstractSmallVector, xs...) = append(v, xs)

# TODO: needed?
@inline function push(v::AbstractSmallVector{N}, x) where N
    n = length(v)
    @boundscheck n < N || error("vector cannot have more than $N elements")
    @inbounds SmallVector(setindex(v.b, x, n+1), n+1)
end

@inline function pop(v::AbstractSmallVector{N,T}) where {N,T}
    n = length(v)
    @boundscheck iszero(n) && error("vector must not be empty")
    @inbounds SmallVector(setindex(v.b, default(T), n), n-1), v[n]
end

@inline function pushfirst(v::AbstractSmallVector{N}, xs...) where N
    n = length(xs)+length(v)
    @boundscheck n <= N || error("vector cannot have more than $N elements")
    SmallVector(pushfirst(v.b, xs...), n)
end

@inline function popfirst(v::AbstractSmallVector)
    n = length(v)
    @boundscheck iszero(n) && error("vector must not be empty")
    c, x = popfirst(v.b)
    SmallVector(c, n-1), x
end

@inline function insert(v::AbstractSmallVector{N}, i::Integer, x) where N
    n = length(v)
    @boundscheck begin
        1 <= i <= n+1 || throw(BoundsError(v, i))
        n < N || error("vector cannot have more than $N elements")
    end
    @inbounds SmallVector(insert(v.b, i, x), n+1)
end

@inline function duplicate(v::AbstractSmallVector{N,T}, i::Integer) where {N,T}
    @boundscheck begin
        checkbounds(v, i)
        length(v) < N || error("vector cannot have more than $N elements")
    end
    t = ntuple(Val(N)) do j
        j <= i ? v.b[j] : v.b[j-1]
    end
    SmallVector(Values{N,T}(t), length(v)+1)
end

@propagate_inbounds deleteat(v::AbstractSmallVector, i::Integer) = first(popat(v, i))

@inline function popat(v::AbstractSmallVector, i::Integer)
    n = length(v)
    @boundscheck checkbounds(v, i)
    c, x = @inbounds popat(v.b, i)
    SmallVector(c, n-1), x
end

@propagate_inbounds append(v::AbstractSmallVector, ws...) = foldl(append, ws; init = SmallVector(v))

@propagate_inbounds append(v::AbstractSmallVector, w) = foldl(push, w; init = SmallVector(v))

@inline function append(v::AbstractSmallVector{N,T}, w::Union{AbstractVector,Tuple}) where {N,T}
    n = length(v)
    m = n+length(w)
    @boundscheck m <= N || error("vector cannot have more than $N elements")
    t = ntuple(Val(N)) do i
        @inbounds n < i <= m ? convert(T, w[i-n]) : v.b[i]
    end
    SmallVector{N,T}(Values{N,T}(t), m)
end

@propagate_inbounds function prepend(v::AbstractSmallVector, ws...)
    foldr((w, v) -> prepend(v, w), ws; init = SmallVector(v))
end

@inline function prepend(v::AbstractSmallVector{N,T}, w::Union{AbstractVector,Tuple}) where {N,T}
    n = length(v)
    m = n+length(w)
    @boundscheck m <= N || error("vector cannot have more than $N elements")
    SmallVector{N,T}(prepend(v.b, w), m)
end

prepend(v::AbstractSmallVector{N,T}, w) where {N,T} = append(SmallVector{N,T}(w), v)

support(v::AbstractSmallVector) = support(v.b)
# here we assume that the padding is via zeros

"""
    map(f, v::AbstractSmallVector...) -> SmallVector

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
function map(f::F, vs::Vararg{AbstractSmallVector,M}) where {F,M}
    n = minimum(length, vs)
    _map(f, n, vs...)
end

function map_fast(f::F, n, vs::Vararg{AbstractSmallVector{N},M}) where {F,N,M}
    bs = map(v -> v.b, vs)
    SmallVector(map(f, bs...), n)
end

function map_fast_pad(f::F, n, vs::Vararg{AbstractSmallVector{N},M}) where {F,N,M}
    bs = map(v -> v.b, vs)
    b = map(f, bs...)
    SmallVector(padtail(b, n), n)
end

#
# broadcast
#

using Base.Broadcast: AbstractArrayStyle, DefaultArrayStyle, Broadcasted, flatten
import Base.Broadcast: BroadcastStyle, instantiate

"""
    $(@__MODULE__).SmallVectorStyle <: Broadcast.AbstractArrayStyle{1}

The broadcasting style used for `AbstractSmallVector`.

See also [`AbstractSmallVector`](@ref), `Broadcast.AbstractArrayStyle`.
"""
struct SmallVectorStyle <: AbstractArrayStyle{1} end

BroadcastStyle(::Type{<:AbstractSmallVector}) = SmallVectorStyle()
BroadcastStyle(::SmallVectorStyle, ::DefaultArrayStyle{0}) = SmallVectorStyle()
BroadcastStyle(::SmallVectorStyle, ::DefaultArrayStyle{N}) where N = DefaultArrayStyle{N}()

instantiate(bc::Broadcasted{SmallVectorStyle}) = bc

function copy(bc::Broadcasted{SmallVectorStyle})
    bcflat = flatten(bc)
    i = findfirst(x -> x isa AbstractSmallVector, bcflat.args)::Int
    n = length(bcflat.args[i])
    foreach(bcflat.args) do x
        x isa Union{Tuple, AbstractSmallVector} && length(x) != n &&
            error("vectors must have the same length")
    end
    _map(bcflat.f, n, bcflat.args...)
end

_eltype(v::Union{AbstractVector,Tuple}) = eltype(v)
_eltype(x::T) where T = T

_capacity(v::AbstractSmallVector) = capacity(v)
_capacity(_) = typemax(Int)

_getindex(v::AbstractSmallVector, i) = @inbounds v.b[i]
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
            T <: AbstractSmallVector ? AbstractVector{eltype(T)} : T
        end
        w = invoke(map, Tuple{F,VT...}, f, vs...)
        SmallVector{N}(w)
    end
end

_map(f::Union{typeof.(
        (&, round, floor, ceil, trunc, abs, abs2, sign, sqrt)
    )...}, n, vs::AbstractSmallVector{N}...) where N = map_fast(f, n, vs...)

_map(::typeof(*), n, vs::AbstractSmallVector{N,<:Integer}...) where N = map_fast(*, n, vs...)
_map(::typeof(signbit), n, v::AbstractSmallVector{N,<:Integer}) where N = map_fast(signbit, n, v)

_map(f::Union{typeof.(
        (+, -, *, ~, |, xor, nand, nor, ==, !=, <, >, <=, >=, ===, isequal, signbit)
    )...}, n, vs::AbstractSmallVector{N}...) where N = map_fast_pad(f, n, vs...)

_map(::typeof(/), n,
        v::AbstractSmallVector{N,<:Union{Integer,AbstractFloat}},
        w::AbstractSmallVector{N,<:Union{Integer,AbstractFloat}}) where N =
    map_fast_pad(/, n, v, w)
