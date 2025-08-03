#
# small vectors
#

export AbstractSmallVector, SmallVector, fixedvector, bits, resize, sum_fast, extrema_fast,
    capacity, support, setindex, addindex, push, pop, pushfirst, popfirst,
    insert, duplicate, deleteat, popat, append, prepend, unsafe_circshift

import Base: ==, Tuple, empty, iterate,
    length, size, getindex, setindex, rest, split_rest,
    zeros, ones, zero, map, reverse, in,
    +, -, *, sum, prod, maximum, minimum, extrema, replace,
    circshift

import Base.FastMath: eq_fast, mul_fast

"""
    AbstractSmallVector{N,T} <: AbstractVector{T}

`AbstractSmallVector{N,T}` is the supertype of `SmallVector{N,T}` and `MutableSmallVector{N,T}`.

See also [`SmallVector`](@ref), [`MutableSmallVector`](@ref).
"""
abstract type AbstractSmallVector{N,T} <: AbstractVector{T} end

const SmallLength = Int16

"""
    SmallVector{N,T} <: AbstractSmallVector{N,T}

    SmallVector{N,T}()
    SmallVector{N,T}(iter)
    SmallVector{N}(iter)
    SmallVector(v::PackedVector)
    SmallVector(v::Union{AbstractSmallVector, AbstractFixedVector})

`SmallVector{N,T}` is an immutable vector type that can hold up to `N` elements of type `T`.
Here `N` can be any (small) positive integer. However, at least for bit integer
and hardware float types, one usually takes `N` to be a power of `2`.

The element type `T` can be omitted when creating the `SmallVector` from an iterator
that has an element type, for example from an `AbstractVector` or a tuple.
In the latter case, `T` is determined by promoting the element types of the tuple.
If no argument is given, then an empty vector is returned.
If the `SmallVector` is created from an `AbstractSmallVector`, `AbstractFixedVector` or `PackedVector` `v`
and the parameter `N` is omitted, then it is set to capacity of `v`.

The unused elements of a `SmallVector{N,T}` are filled with the value `default(T)`, which is
predefined for several types including `Number`. Default values for other types must be defined
explicitly.

Addition and subtraction of two `SmallVector`s is possible even if the vectors have different
capacity. (Of course, their lengths must agree.) The capacity of the result is the smaller
of the arguments' capacities in this case.

See also [`MutableSmallVector`](@ref), [`capacity`](@ref capacity(::Type{<:AbstractSmallVector})), [`$(@__MODULE__).default`](@ref),
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
    b::FixedVector{N,T}
    n::SmallLength
end

SmallVector(v::AbstractFixedVector, n::Integer) = SmallVector(v, n % SmallLength)

"""
    fixedvector(v::AbstractSmallVector{N,T}) where {N,T} -> FixedVector{N,T}

Return the `FixedVector` underlying `v`. It agrees with `v` at all positions up to `length(v)`;
the remaining elements are equal to `default(T)`.

See also [`$(@__MODULE__).default`](@ref), [`fixedvector(::AbstractFixedVector)`](@ref).

# Example
```jldoctest
julia> v = SmallVector{4}(1:2)
2-element SmallVector{4, Int64}:
 1
 2

julia> fixedvector(v)
4-element FixedVector{4, Int64}:
 1
 2
 0
 0
```
"""
fixedvector(v::AbstractSmallVector) = v.b

"""
    bits(v::AbstractSmallVector) -> Unsigned

Return the bit representation of `fixedvector(v)`.

See also [`fixedvector`](@ref fixedvector(::AbstractSmallVector)), [`bits(::AbstractFixedVector)`](@ref).

# Example
```jldoctest
julia> SmallVector{4,Int8}(1:3) |> bits
0x00030201
```
"""
bits(v::AbstractSmallVector) = bits(fixedvector(v))

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

"""
    capacity(::Type{<:AbstractSmallVector{N}}) where N -> N
    capacity(v::AbstractSmallVector{N}) where N -> N

Return the largest number of elements this vector type can hold.
"""
capacity(::Type{<:AbstractSmallVector}),
capacity(::AbstractSmallVector)

@inline function iterate(v::AbstractSmallVector, i = 1)
    i <= length(v) ? (@inbounds v[i], i+1) : nothing
end

rest(v::AbstractSmallVector, i = 1) = @inbounds v[i:end]

if VERSION >= v"1.9"
    @inline function split_rest(v::AbstractSmallVector, n::Int, i = 1)
        m = length(v)-n
        @boundscheck (n >= 0 && m >= i-1) || error("impossible number of elements requested")
        @inbounds v[i:m], v[m+1:end]
    end
end

@inline function getindex(v::AbstractSmallVector, i::Int)
    @boundscheck checkbounds(v, i)
    @inbounds v.b[i]
end

"""
    setindex(v::AbstractSmallVector{N,T}, x, i::Integer) where {N,T} -> SmallVector{N,T}

Substitute `x` for the `i`-th component of `v` and return the new vector.

See also `Base.setindex`,  [`addindex`](@ref addindex(::AbstractSmallVector, ::Any, ::Integer)).
"""
@inline function setindex(v::AbstractSmallVector, x, i::Integer)
    @boundscheck checkbounds(v, i)
    SmallVector((@inbounds setindex(v.b, x, i)), length(v))
end

"""
    addindex(v::AbstractSmallVector{N,T}, x, i::Integer) where {N,T} -> SmallVector{N,T}

Add `x` to the `i`-th component of `v` and return the new vector.

See also [`setindex`](@ref setindex(::AbstractSmallVector, ::Any, ::Integer)).
"""
@inline function addindex(v::AbstractSmallVector, x, i::Integer)
    @boundscheck checkbounds(v, i)
    @inbounds v + setindex(zero(v), x, i)
end

"""
    empty(v::V) where V <: AbstractSmallVector -> V
    empty(v::AbstractSmallVector{N}, T::Type) where {N,T} -> AbstractSmallVector{N,T}

In the first form, return an empty `AbstractSmallVector` of the same type as `v`.
In the second form, the capacity is the same as for `v`,
but the element type is `T`.
"""
empty(::AbstractSmallVector),
empty(::AbstractSmallVector, ::Type)

empty(v::SmallVector{N,T}, ::Type{U} = T) where {N,T,U} = SmallVector{N,U}()

"""
    resize(v::AbstractSmallVector{N,T}, n::Integer) -> SmallVector{N,T}

Return a vector of length `n` by making `v` longer or shorter. If the new vector
is longer, then the new elements are initialized with `default(T)`.

See also `Base.resize!`, [`$(@__MODULE__).default`](@ref).
"""
@inline function resize(v::AbstractSmallVector{N}, n::Integer) where N
    @boundscheck 0 <= n <= N || error("length must be between 0 and $N")
    b = n < v.n ? padtail(v.b, n) : v.b
    SmallVector(b, n % SmallLength)
end

default(::Type{V}) where V <: AbstractSmallVector = V()

@inline zero(v::V) where V <: AbstractSmallVector = V(zero(v.b), length(v))

"""
    zeros(::Type{V}, n::Integer) where V <: AbstractSmallVector -> V

Return an `AbstractSmallVector` of type `V` containing `n` zeros.

See also [`ones`](@ref ones(::Type{<:AbstractSmallVector}, ::Integer)).
"""
zeros(::Type{<:AbstractSmallVector}, ::Integer)

function zeros(::Type{V}, n::Integer) where {N, T, V <: AbstractSmallVector{N,T}}
    n <= N || error("vector cannot have more than $N elements")
    V(zero(FixedVector{N,T}), n)
end

"""
    ones(::Type{V}, n::Integer) where V <: AbstractSmallVector -> V

Return an `AbstractSmallVector` of type `V` containing `n` ones.

See also [`zeros`](@ref zeros(::Type{<:AbstractSmallVector}, ::Integer)).
"""
ones(::Type{<:AbstractSmallVector}, ::Integer)

function ones(::Type{V}, n::Integer) where {N, T, V <: AbstractSmallVector{N,T}}
    n <= N || error("vector cannot have more than $N elements")
    t = ntuple(Val(N)) do i
        i <= n ? one(T) : zero(T)
    end
    V(FixedVector{N,T}(t), n)
end

(::Type{V})() where {N,T,V<:AbstractSmallVector{N,T}} = V(default(FixedVector{N,T}), 0)

SmallVector{N,T}(v::AbstractSmallVector{N}) where {N,T} = SmallVector{N,T}(v.b, v.n)

function SmallVector{N,T}(iter) where {N,T}
    isbitstype(T) && return @inline SmallVector(MutableSmallVector{N,T}(iter))
    b = default(FixedVector{N,T})
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

SmallVector(v::AbstractSmallVector{N,T}) where {N,T} = SmallVector{N,T}(v)

function (::Type{V})(v::AbstractFixedVector{N,T}) where {V <: AbstractSmallVector, N, T}
    V{N,T}(FixedVector(v), N)
end

+(v::AbstractSmallVector) = map(+, v)  # +true = 1::Int
-(v::AbstractSmallVector) = map(-, v)

for op in (:+, :-)
    @eval @inline function $op(v::AbstractSmallVector, w::AbstractSmallVector)
        @boundscheck length(v) == length(w) || error("vectors must have the same length")
        SmallVector(map($op, v.b, w.b), length(v))
    end
end

@inline mul_fast(c::Number, v::AbstractSmallVector) = mul_fast.(c, v)
@inline mul_fast(v::AbstractSmallVector, c::Number) = mul_fast.(v, c)

*(c::Number, v::AbstractSmallVector) = c .* v
*(v::AbstractSmallVector, c::Number) = v .* c

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

Return the `@fastmath` sum of the elements of `v`.
Unlike for `sum`, the return value always is of the element type of `v`, even for small bit integers.

See also `Base.sum`, `Base.@fastmath`.

# Example
```jldoctest
julia> v = SmallVector{4}([-0.0, -0.0])
2-element SmallVector{4, Float64}:
 -0.0
 -0.0

julia> sum(v), sum_fast(v)
(-0.0, 0.0)

julia> v = SmallVector{4}(Int8[80, 90])
2-element SmallVector{4, Int8}:
 80
 90

julia> sum(v), sum_fast(v)
(170, -86)
```
"""
sum_fast(v::AbstractSmallVector) = @fastmath foldl(+, v.b)

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
    @boundscheck 0 < start <= stop+1 <= length(v)+1 || Base.throw_boundserror(v, start:stop)
    @inbounds b = reverse(v.b, start, stop)
    SmallVector(b, length(v))
end

reverse(v::AbstractSmallVector{N,T}) where {N, T <: HWType} = @inbounds reverse(v, 1)

@inline function reverse(v::AbstractSmallVector{N,T}, start::Integer) where {N, T <: HWType}
    M = shufflewidth(v)
    if M != 0
        @boundscheck 0 < start <= length(v)+1 || Base.throw_boundserror(v, start)
        PT = inttype(T)
        k = start % PT
        l = (length(v) % PT) + k
        p = ntuple(Val(N)) do i
            i = i % PT
            ifelse(i < k, i, l-i) - one(PT)
        end
        SmallVector(shuffle(Val(M), fixedvector(v), p), length(v))
    else
        invoke(reverse, Tuple{AbstractSmallVector,Integer}, v, start)
    end
end

for g in (:sum, :prod, :minimum, :maximum, :extrema)
    @eval $g(f::F, v::AbstractSmallVector;  kw...) where F = $g(map(f, v);  kw...)
end

"""
    any(f::Function, v::AbstractSmallVector; dims = :, [style::MapStyle])
    all(f::Function, v::AbstractSmallVector; dims = :, [style::MapStyle])
    allequal(f, v::AbstractSmallVector; [style::MapStyle})
    allunique(f, v::AbstractSmallVector; [style::MapStyle])
    findall(f::Function, v::AbstractSmallVector; [style::MapStyle])
    findfirst(f::Function, v::AbstractSmallVector; [style::MapStyle])
    findlast(f::Function, v::AbstractSmallVector; [style::MapStyle])
    findnext(f::Function, v::AbstractSmallVector, k::Integer; [style::MapStyle])
    findprev(f::Function, v::AbstractSmallVector, k::Integer; [style::MapStyle])
    count(f, v::AbstractSmallVector; dims = :, init = 0, [style::MapStyle])
    filter(f, v::AbstractSmallVector; [style::MapStyle])
    filter!(f, v::MutableSmallVector; [style::MapStyle])

With an `AbstractSmallVector` `v` as second argument, these functions accept
the additional keyword argument `style`. If it equals `LazyStyle()`, then the
function `f` is only evaluated until the result has been determined. For any
other value of `style`, `f` is evaluated on all elements of `v` as well as on
the default values used for padding. This is often faster for simple functions.

As discussed under `MapStyle`, the default value for `style` is based on a list
of known functions.

See also [`$(@__MODULE__).default`](@ref), [`$(@__MODULE__).MapStyle`](@ref).
"""
any(::Function, ::AbstractSmallVector),
all(::Function, ::AbstractSmallVector),
allequal(::Any, ::AbstractSmallVector),
allunique(::Any, ::AbstractSmallVector),
findall(::Function, ::AbstractSmallVector),
findfirst(::Function, ::AbstractSmallVector),
findlast(::Function, ::AbstractSmallVector),
findnext(::Function, ::AbstractSmallVector, ::Integer),
findprev(::Function, ::AbstractSmallVector, ::Integer),
count(::Any, ::AbstractSmallVector)

Base.hasfastin(::Type{V}) where V <: AbstractSmallVector = Base.hasfastin(fieldtype(V, :b))

in(x, v::AbstractSmallVector) = findfirst(==(x), v) !== nothing

function replace(v::AbstractSmallVector{N,T}, ps::Vararg{Pair,M}; kw...) where {N,T,M}
    if isfasttype(T) && isempty(kw)
        b = replace(v.b, ps...)
        if default(T) in map(first, ps)
            b = padtail(b, v.n)
        end
        SmallVector(b, v.n)
    else
        SmallVector(invoke(replace, Tuple{AbstractVector,Vararg{Pair,M}}, v, ps...; kw...))
    end
end

"""
    push(v::AbstractSmallVector{N,T}, xs...) where {N,T} -> SmallVector{N,T}

Return the `SmallVector` obtained from `v` by appending the arguments `xs`.

See also `Base.push!`, `BangBang.push!!`.
"""
@propagate_inbounds push(v::AbstractSmallVector, xs...) = append(v, xs)

@propagate_inbounds function push(v::AbstractSmallVector{N,T}, x) where {N,T}
    isbitstype(T) && bitsize(T) < bitsize(Int) && return append(v, (x,))
    n = length(v)
    @boundscheck n < N || error("vector cannot have more than $N elements")
    @inbounds SmallVector(setindex(v.b, x, n+1), n+1)
end

"""
    pop(v::AbstractSmallVector{N,T}) where {N,T} -> Tuple{SmallVector{N,T}, T}

Return the tuple `(w, x)` where `x` is the last element of `v`
and `w` obtained from `v` by dropping this element.
The vector `v` must not be empty.

See also `Base.pop!`, `BangBang.pop!!`.
"""
pop(::AbstractSmallVector)

@inline function pop(v::AbstractSmallVector{N,T}) where {N,T}
    n = length(v)
    @boundscheck iszero(n) && error("vector must not be empty")
    @inbounds SmallVector(setindex(v.b, default(T), n), n-1), v[n]
end

"""
    pushfirst(v::AbstractSmallVector{N,T}, xs...) where {N,T} -> SmallVector{N,T}

Return the `SmallVector` obtained from `v` by prepending the arguments `xs`.

See also `Base.pushfirst!`, `BangBang.pushfirst!!`.
"""
@inline function pushfirst(v::AbstractSmallVector{N}, xs...) where N
    n = length(xs)+length(v)
    @boundscheck n <= N || error("vector cannot have more than $N elements")
    SmallVector(pushfirst(v.b, xs...), n)
end

"""
    popfirst(v::AbstractSmallVector{N,T}) where {N,T} -> Tuple{SmallVector{N,T}, T}

Return the tuple `(w, x)` where `x` is the first element of `v`
and `w` obtained from `v` by dropping this element.
The vector `v` must not be empty.

See also `Base.popfirst!`, `BangBang.popfirst!!`.
"""
@inline function popfirst(v::AbstractSmallVector)
    n = length(v)
    @boundscheck iszero(n) && error("vector must not be empty")
    c, x = popfirst(v.b)
    SmallVector(c, n-1), x
end

"""
    insert(v::AbstractSmallVector{N,T}, i::Integer, x) where {N,T} -> SmallVector{N,T}

Return the `SmallVector` obtained from `v` by inserting `x` at position `i`.
The position `i` must be between `1` and `length(v)+1`.

This is the non-mutating analog of `Base.insert!`.

See also [`duplicate`](@ref duplicate(::AbstractSmallVector, ::Integer)).
"""
@inline function insert(v::AbstractSmallVector{N}, i::Integer, x) where N
    n = length(v)
    @boundscheck begin
        1 <= i <= n+1 || throw(BoundsError(v, i))
        n < N || error("vector cannot have more than $N elements")
    end
    @inbounds SmallVector(insert(v.b, i, x), n+1)
end

"""
    duplicate(v::AbstractSmallVector{N,T}, i::Integer) where {N,T} -> SmallVector{N,T}

Duplicate the `i`-th entry of `v` by inserting it at position `i+1` and return the new vector.

See also [`insert`](@ref insert(::AbstractSmallVector, ::Integer, ::Any)).

# Example
```jldoctest
julia> v = SmallVector{8,Int8}(1:3)
3-element SmallVector{8, Int8}:
 1
 2
 3

julia> duplicate(v, 2)
4-element SmallVector{8, Int8}:
 1
 2
 2
 3
```
"""
@inline function duplicate(v::AbstractSmallVector{N,T}, i::Integer) where {N,T}
    @boundscheck begin
        checkbounds(v, i)
        length(v) < N || error("vector cannot have more than $N elements")
    end
    t = ntuple(Val(N)) do j
        j <= i ? v.b[j] : v.b[j-1]
    end
    SmallVector(FixedVector{N,T}(t), length(v)+1)
end

"""
    deleteat(v::AbstractSmallVector{N,T}, i::Integer) where {N,T} -> SmallVector{N,T}

Return the `SmallVector` obtained from `v` by deleting the element at position `i`.
The latter must be between `1` and `length(v)`.

See also `Base.deleteat!`, `BangBang.deleteat!!`.
"""
@propagate_inbounds deleteat(v::AbstractSmallVector, i::Integer) = first(popat(v, i))

"""
    popat(v::AbstractSmallVector{N,T}, i::Integer) where {N,T} -> Tuple{SmallVector{N,T}, T}

Return the tuple `(w, x)` where `w` obtained from `v` by deleting the element `x`
at position `i`. The latter must be between `1` and `length(v)`.

See also `Base.popat!`, `BangBang.popat!!`.
"""
@inline function popat(v::AbstractSmallVector, i::Integer)
    n = length(v)
    @boundscheck checkbounds(v, i)
    c, x = @inbounds popat(v.b, i)
    SmallVector(c, n-1), x
end

"""
    append(v::AbstractSmallVector{N,T}, ws...) where {N,T} -> SmallVector{N,T}

Append all elements of the collections `ws` to `v` and return the new vector.
Note that the resulting `SmallVector` has the same capacity as `v`.

See also `Base.append!`, `BangBang.append!!`.
"""
@propagate_inbounds append(v::AbstractSmallVector, ws...) = foldl(append, ws; init = SmallVector(v))

@propagate_inbounds append(v::AbstractSmallVector, w) = foldl(push, w; init = SmallVector(v))

@inline function append(v::AbstractSmallVector{N,T}, w::Union{AbstractVector,Tuple}) where {N,T}
    if isbitstype(T) && N >= 8
        u = MutableSmallVector(v)
        append!(u, w)
        return SmallVector(u)
    end
    n = length(v)
    m = n+length(w)
    @boundscheck m <= N || error("vector cannot have more than $N elements")
    t = ntuple(Val(N)) do i
        @inbounds n < i <= m ? convert(T, w[i-n]) : v.b[i]
    end
    SmallVector{N,T}(FixedVector{N,T}(t), m)
end

"""
    prepend(v::AbstractSmallVector{N,T}, ws...) where {N,T} -> SmallVector{N,T}

Prepend all elements of the collections `ws` to `v` and return the new vector.
Note that the resulting `SmallVector` has the same capacity as `v`.

See also `Base.prepend!`.
"""
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

function unsafe_circshift(v::AbstractSmallVector{N,T}, k::Integer) where {N,T}
    M = shufflewidth(v)
    if M != 0
        P = inttype(T)
        n1 = length(v) % P
        k1 = ifelse(signbit(k), (k%P)+n1, k%P)
        p = ntuple(Val(N)) do i
            i = i % P
            i-k1 + (i > k1 ? -P(1) : n1-P(1))
        end
        w = shuffle(Val(M), fixedvector(v), p)
        SmallVector(padtail(w, length(v)), length(v))
    elseif N <= 16 || !isbitstype(T)
        n2 = length(v)
        k2 = ifelse(signbit(k), (k % SmallLength) + v.n, k % SmallLength)
        t = ntuple(Val(N)) do i
            i = i % SmallLength
            @inbounds if i <= k2
                v[(i-k2)+n2]
            elseif i <= n2 % SmallLength
                v[i-k2]
            else
                default(T)
            end
        end
        SmallVector{N,T}(t, n2)
    else
        n3 = length(v)
        k3 = ifelse(signbit(k), k+n3, k) % Int
        u = MutableSmallVector(v)
        w = similar(v)
        unsafe_copyto!(pointer(w, k3), pointer(u, 1), n3-(k3-1))
        unsafe_copyto!(pointer(w, 1), pointer(u, n3-(k3-1)+1), k3-1)
        SmallVector(w)
    end
end

function circshift(v::AbstractSmallVector{N,T}, k::Integer) where {N,T}
    if isempty(v)
        SmallVector(v)
    else
        unsafe_circshift(v, unsafe_rem(k, unsigned(v.n)))
    end
end

"""
    support(v::AbstractSmallVector) -> SmallBitSet

Return the `SmallBitSet` with the indices of the non-zero elements of `v`.
If `v` has `Bool` elements, then this means the elements that are `true`.

See also [`SmallBitSet`](@ref), [`support(::Any, ::AbstractSmallVector)`](@ref).

# Example
```jldoctest
julia> v = SmallVector{8,Int8}([1, 0, 2, 0, 0, 3]);

julia> support(v)
SmallBitSet{UInt8} with 3 elements:
  1
  3
  6
```
"""
support(v::AbstractSmallVector) = support(v.b)
# here we assume that the padding is via zeros

"""
    support(f, v::AbstractSmallVector; [style::MapStyle]) -> SmallBitSet

Return the `SmallBitSet` with the indices of the elements `x` of `v` for which `f(x)` is non-zero.
If `f` has `Bool` values, then this means that `f(x)` has to be `true`.

The `style` keyword argument determines how the padding used for `AbstractSmallVector` is treated.
As discussed under `MapStyle`, the default value is based on a list of known functions.

See also [`SmallBitSet`](@ref), [`support(::AbstractSmallVector)`](@ref),
[`$(@__MODULE__).MapStyle`](@ref).

# Example
```jldoctest
julia> v = SmallVector{8,Int8}(3:8);

julia> support(isodd, v)
SmallBitSet{UInt8} with 3 elements:
  1
  3
  5
```
"""
support(::Any, ::AbstractSmallVector)

support(f::F, v::AbstractSmallVector{N,T}; style::MapStyle = MapStyle(f, T)) where {F,N,T} = support(map(f, v; style))

#
# map
#

"""
    map(f, v::AbstractSmallVector...; [style::MapStyle]) -> SmallVector

Apply `f` to the argument vectors elementwise and stop when one of them is exhausted.
Note that the capacity of the resulting `SmallVector` is the minimum of the argument
vectors' capacities.

The `style` keyword argument determines how `map` treats the padding used for
`AbstractSmallVector`. As discussed under `MapStyle`, the default value is based on
a list of known functions.

See also [`capacity`](@ref capacity(::Type{<:AbstractSmallVector})), `Base.map(f, v::AbstractVector...)`,
[`$(@__MODULE__).MapStyle`](@ref), [Section "Broadcasting"](@ref sec-broadcasting).

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
function map(f::F, vs::Vararg{AbstractSmallVector,M}; style::MapStyle = MapStyle(f, map(eltype, vs)...)) where {F,M}
    n, eq = minlength(vs)
    if style isa LazyStyle
        @inline smallvector_bc(LazyStyle(), n, f, vs...)
    elseif style isa StrictStyle || (style isa RigidStyle && (M == 1 || eq))
        @inline smallvector_bc(StrictStyle(), n, f, vs...)
    else
        @inline smallvector_bc(EagerStyle(), n, f, vs...)
    end
end

function minlength(vs)
    foldl(vs[2:end]; init = (length(vs[1]), true)) do (n, eq), v
        min(n, length(v)), eq & (n == length(v))
    end
end

if VERSION >= v"1.11"

function smallvector_rand(rng::AbstractRNG, ::Val{N}, ::Type{T}, n::Integer) where {N,T}
    SmallVector(padtail(rand(rng, FixedVector{N,T}), n), n)
end

function smallvector_rand(rng::AbstractRNG, ::Val{N}, ::Type{Nothing}, n::Integer) where N
    vals = SmallVector(default(FixedVector{N,Nothing}), n)
end

function Random.rand(rng::AbstractRNG, ::SamplerType{SmallVector{N,T}}) where {N,T}
    smallvector_rand(rng, Val(N), T, rand(0:N))
end

end

#
# broadcast
#

using Base: Fix2

using Base.Broadcast: AbstractArrayStyle, DefaultArrayStyle, Broadcasted, broadcasted, flatten, materialize
import Base.Broadcast: BroadcastStyle

"""
    $(@__MODULE__).SmallVectorStyle <: Broadcast.AbstractArrayStyle{1}

The broadcasting style used for `AbstractSmallVector`.

See also [`AbstractSmallVector`](@ref), `Broadcast.AbstractArrayStyle`.
"""
struct SmallVectorStyle <: AbstractArrayStyle{1} end

BroadcastStyle(::Type{<:AbstractSmallVector}) = SmallVectorStyle()
BroadcastStyle(::SmallVectorStyle, ::DefaultArrayStyle{0}) = SmallVectorStyle()
BroadcastStyle(::SmallVectorStyle, ::DefaultArrayStyle{N}) where N = DefaultArrayStyle{N}()

bc_return_type(x) = _eltype(x)

function bc_return_type(bc::Broadcasted)
    TT = map(bc_return_type, bc.args)
    Core.Compiler.return_type(bc.f, Tuple{TT...})
end

bc_mapstyle(::Any) = EagerStyle()
bc_mapstyle(::AbstractSmallVector) = StrictStyle()

function bc_mapstyle(bc::Broadcasted)
    TT = map(bc_return_type, bc.args)
    all(T -> isconcretetype(T) || T <: DataType, TT) || return LazyStyle()
    fstyle = MapStyle(bc.f, TT...)
    argstyles = map(bc_mapstyle, bc.args)
    if fstyle isa LazyStyle || any(Fix2(isa, LazyStyle), argstyles)
        LazyStyle()
    elseif fstyle isa RigidStyle && all(Fix2(isa, StrictStyle), argstyles)
        StrictStyle()
    elseif fstyle isa StrictStyle && any(Fix2(isa, StrictStyle), argstyles)
        StrictStyle()
    else
        EagerStyle()
    end
end

function copy(bc::Broadcasted{SmallVectorStyle})
    bcflat = flatten(bc)
    @inline smallvector_bc(bc_mapstyle(bc), size(bc)[1], bcflat.f, bcflat.args...)
end

_capacity(x) = typemax(Int)
_capacity(v::AbstractSmallVector) = capacity(v)

function smallvector_bc(::StrictStyle, n, f::F, vs::Vararg{Any,M}) where {F,M}
    N = minimum(_capacity, vs)
    ts = map(vs) do v
        v isa AbstractSmallVector ? Tuple(v.b)[1:N] : v
    end
    t = materialize(broadcasted(f, ts...))
    SmallVector(FixedVector(t), n)
end

function smallvector_bc(::EagerStyle, n, f::F, vs::Vararg{Any,M}) where {F,M}
    w = smallvector_bc(StrictStyle(), n, f, vs...)
    SmallVector(padtail(w.b, n), n)
end

_eltype(v::Union{AbstractVector,Tuple}) = eltype(v)
_eltype(x::Base.RefValue{T}) where T = T
_eltype(x::T) where T = T

_getindex(v::AbstractSmallVector, i) = @inbounds v.b[i]
_getindex(v::Tuple, i) = i <= length(v) ? @inbounds(v[i]) : default(v[1])
_getindex(x::Base.RefValue, i) = x[]
_getindex(x, i) = x

function smallvector_bc(::LazyStyle, n, f::F, vs::Vararg{Any,M}) where {F,M}
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
        SmallVector(FixedVector{N,U}(t), n)
    else
        VT = map(vs) do v
            T = typeof(v)
            T <: AbstractSmallVector ? AbstractVector{eltype(T)} : T
        end
        w = invoke(map, Tuple{F,VT...}, f, vs...)
        SmallVector{N}(w)
    end
end
