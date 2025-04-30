export AbstractFixedVector, FixedVector, MutableFixedVector,
    sum_fast, extrema_fast, bits, fasthash

using Base: @propagate_inbounds, tail, haslength, BitInteger,
    IteratorEltype, HasEltype, Generator

import Base: Tuple, ==, isequal, size,
    IndexStyle, getindex, setindex!, iterate, iszero, zero, +, -, *, map, map!,
    minimum, maximum, extrema, any, all, allequal, allunique, in, reverse,
    findfirst, findlast, findmin, findmax, vcat, copy, copyto!, convert,
    strides, elsize, unsafe_convert, muladd, replace, replace!

"""
    AbstractFixedVector{N,T} <: AbstractVector{T}

`AbstractFixedVector{N,T}` is the supertype of `FixedVector{N,T}` and `MutableFixedVector{N,T}`.

See also [`FixedVector`](@ref), [`MutableFixedVector`](@ref).
"""
abstract type AbstractFixedVector{N,T} <: AbstractVector{T} end

"""
    FixedVector{N,T} <: AbstractFixedVector{N,T}

    FixedVector{N,T}(iter)
    FixedVector{N}(iter)
    FixedVector(iter)

`FixedVector{N,T}` is an immutable vector type that holds exactly `N` elements of type `T`.
(It is analogous to `StaticArrays.SVector` and `StaticVectors.Values`.)
The size `N` can be any (small) positive integer. However, at least for bit integer
and hardware float types, one usually takes `N` to be a power of `2`.

If the element type `T` or the size `N` are omitted, they are determined from the iterator
given as argument. Performance degrades if this is not possible at compile time.
(For tuples, the element type is determined via `promote_type`.)
As a rule of thumb, the size should only be omitted for `Tuple` arguments.

See also [`MutableFixedVector`](@ref), `Base.promote_type`.
"""
struct FixedVector{N,T} <: AbstractFixedVector{N,T}
    t::NTuple{N,T}
    FixedVector{N,T}(t::NTuple{N,Any}) where {N,T} = new{N,T}(t)
end

"""
    MutableFixedVector{N,T} <: AbstractFixedVector{N,T}

    MutableFixedVector{N,T}(iter)
    MutableFixedVector{N}(iter)
    MutableFixedVector(iter)

    MutableFixedVector{N,T}(undef)

`MutableFixedVector{N,T}` is a mutable vector type that holds exactly `N` elements of type `T`.
(It is analogous to `StaticArrays.MVector` and `StaticVectors.Variables`.)
The size `N` can be any (small) positive integer. However, at least for bit integer
and hardware float types, one usually takes `N` to be a power of `2`.

If the element type `T` or the size `N` are omitted, they are determined from the iterator
given as argument. Performance degrades if this is not possible at compile time.
As a rule of thumb, the size should only be omitted for `Tuple` arguments.

Note that setting individual vector elements (via `setindex!`) is only supported for `isbits`
element types.

The special form `MutableFixedVector{N,T}(undef)` returns a non-initialized vector.

See also [`FixedVector`](@ref), `Base.isbitstype`.
"""
mutable struct MutableFixedVector{N,T} <: AbstractFixedVector{N,T}
    t::NTuple{N,T}
    MutableFixedVector{N,T}(t::NTuple{N,Any}) where {N,T} = new{N,T}(t)
    MutableFixedVector{N,T}(::UndefInitializer) where {N,T} = new{N,T}()
end

function FixedVector{N,T}(v::AbstractVector) where {N,T}
    length(v) == N || error("argument is not of length ", N)
    t = ntuple(i -> convert(T, @inbounds v[i+firstindex(v)-1]), Val(N))
    FixedVector{N,T}(t)
end

function MutableFixedVector{N,T}(v::AbstractVector) where {N,T}
    w = FixedVector{N,T}(v)
    MutableFixedVector{N,T}(w.t)
end

function FixedVector{N,T}(itr::Generator) where {N,T}
    if IteratorEltype(itr.iter) isa HasEltype
        v = @inline FixedVector{N}(itr.iter)
        map(itr.f, v)
    else
        invoke(FixedVector{N,T}, Tuple{Any}, itr)
    end
end

function MutableFixedVector{N,T}(itr::Generator) where {N,T}
    if IteratorEltype(itr.iter) isa HasEltype
        MutableFixedVector(FixedVector{N,T}(itr))
    else
        invoke(MutableFixedVector{N,T}, Tuple{Any}, itr)
    end
end

@generated function FixedVector{N,T}(itr) where {N,T}
    ex1 = (quote
        xs = iterate(itr, $((k == 1 ? () : (:s,))...))
        xs === nothing && @goto err
        $(Symbol(:x, k))::T, s = xs
    end for k in 1:N)
    ex2 = Expr(:tuple, (Symbol(:x, k) for k in 1:N)...)
    quote
        $(ex1...)
        iterate(itr, s) === nothing && return FixedVector{N,T}($ex2)
        @label err
        error("argument is not of length ", N)
    end
end

#=
@generated function MutableFixedVector{N,T}(itr) where {N,T}
    ex = (quote v[$k], s = iterate(itr, $((k == 1 ? () : (:s,))...))::Tuple end for k in 1:N)
    quote
        isbitstype(T) || return MutableFixedVector(FixedVector{N,T}(itr))
        !haslength(itr) || length(itr) == N || error("argument is not of length ", N)
        v = MutableFixedVector{N,T}(undef)
        $(ex...)
        haslength(itr) || iterate(itr, s) === nothing || error("argument is not of length ", N)
        v
    end
end
=#

function MutableFixedVector{N,T}(itr) where {N,T}
    isbitstype(T) || return MutableFixedVector(FixedVector{N,T}(itr))
    v = MutableFixedVector{N,T}(undef)
    i = 0
    xs = iterate(itr)
    while i < N && xs !== nothing
        i += 1
        x, s = xs
        @inbounds v[i] = x
        xs = iterate(itr, s)
    end
    (i == N && xs === nothing) || error("argument is not of length ", N)
    v
end

function (::Type{V})(t) where {N,V<:AbstractFixedVector{N}}
    if Base.IteratorEltype(t) isa Base.HasEltype
        T = element_type(t)
        @inline V{T}(t)
    else
        V(NTuple{N}(t))
    end
end

function (::Type{V})(t) where {V<:AbstractFixedVector}
    if haslength(t)
        N = length(t)
        V{N}(t)
    else
        V(Tuple(t))
    end
end

convert(::Type{V}, v::V) where V <: AbstractFixedVector = v
convert(::Type{V}, v::Union{AbstractVector,Tuple}) where V <: AbstractFixedVector = V(v)

copy(v::V) where V <: AbstractFixedVector = V(v)

copyto!(v::MutableFixedVector{N}, t::Tuple{Vararg{Any,N}}) where N = (v.t = t; v)

copyto!(v::MutableFixedVector{N}, w::AbstractFixedVector{N}) where N = copyto!(v, Tuple(w))

Tuple(v::AbstractFixedVector) = v.t

size(v::AbstractFixedVector{N}) where N = (N,)

strides(::MutableFixedVector) = (1,)

elsize(::Type{MutableFixedVector{N,T}}) where {N,T} = elsize(Vector{T})

unsafe_convert(::Type{Ptr{T}}, v::MutableFixedVector{N,T}) where {N,T} =
    Ptr{T}(pointer_from_objref(v))

"""
    fasthash(v::AbstractFixedVector [, h0::UInt]) -> UInt

Return a hash for `v` that may be computed faster than the standard `hash`
for vectors. This new hash is consistent across all `AbstractFixedVector`s
of the same element type, but it may not be compatible with `hash` or
with `fasthash` for a `AbstractFixedVector` having a different element type.

Currently, `fasthash` differs from `hash` only if the element type of `v`
is a bit integer type with at most 32 bits, `Bool` or `Char`.

See also `Base.hash`.
"""
fasthash(::AbstractFixedVector, ::UInt)

function fasthash(v::AbstractFixedVector{N,T}, h0::UInt) where {N,T}
    if (T <: BitInteger && bitsize(T) <= 32) || T == Bool || T == Char
        Base.hash_integer(bits(v), h0)
    else
        hash(v, h0)
    end
end

IndexStyle(::Type{<:AbstractFixedVector}) = IndexLinear()

@propagate_inbounds getindex(v::AbstractFixedVector, i::Int) = v.t[i]

@inline function unsafe_getindex(v::MutableFixedVector, i::Int)
    GC.@preserve v unsafe_load(pointer(v, i))
end

@inline function getindex(v::MutableFixedVector{N,T}, i::Int) where {N,T}
    @boundscheck checkbounds(v, i)
    isbitstype(T) ? unsafe_getindex(v, i) : @inbounds v.t[i]
end

@propagate_inbounds function setindex!(v::MutableFixedVector{N,T}, x, i::Int) where {N,T}
    @boundscheck checkbounds(v, i)
    isbitstype(T) || error("setindex! is only supported for isbits element types, not for $T")
    GC.@preserve v unsafe_store!(Ptr{T}(pointer_from_objref(v)), x, i)
    return v
end

iterate(v::AbstractFixedVector, state...) = iterate(v.t, state...)

zero(::Type{V}) where {N,T,V<:AbstractFixedVector{N,T}} = V(ntuple(Returns(zero(T)), Val(N)))
zero(::V) where V <: AbstractFixedVector = zero(V)

@inline +(v::AbstractFixedVector) = map(+, v)  # +true = 1::Int
@inline -(v::AbstractFixedVector) = map(-, v)

@inline +(v::AbstractFixedVector{N}, w::AbstractFixedVector{N}) where N = map(+, v, w)
@inline -(v::AbstractFixedVector{N}, w::AbstractFixedVector{N}) where N = map(-, v, w)

@inline *(c::Number, v::AbstractFixedVector) = FixedVector(c .* v.t)
*(v::AbstractFixedVector, c::Number) = c*v

@inline muladd(c::Number, v::AbstractFixedVector{N}, w::AbstractFixedVector{N}) where N =
    FixedVector(muladd.(c, Tuple(v), Tuple(w)))

muladd(v::AbstractFixedVector{N}, c::Number, w::AbstractFixedVector{N}) where N = muladd(c, v, w)

@inline @generated function map_tuple(f, xs::Tuple...)
    M = length(xs)
    N = minimum(fieldcount, xs)
    Expr(:tuple, (Expr(:call, :f, (:(xs[$j][$i]) for j in 1:M)...) for i in 1:N)...)
end

map_tuple(::typeof(identity), x::Tuple) = x

function map(f::F, vs::Vararg{AbstractFixedVector,N}) where {F,N}
    FixedVector(map_tuple(f, map(Tuple, vs)...))
end

function map!(f::F, w::MutableFixedVector, vs::Vararg{AbstractFixedVector,N}) where {F,N}
    copyto!(w, map(f, map(Tuple, vs)...))
end

@generated function Base.mapfoldl_impl(f, op, init, v::AbstractFixedVector{N}) where N
    ex, start = init <: Void ? (:(f(v[1])), 2) : (:init, 1)
    for i in start:N
        ex = :(op($ex, f(v[$i])))
    end
    ex
end

@generated function Base.mapfoldr_impl(f, op, init, v::AbstractFixedVector{N}) where N
    ex, start = init <: Void ? (:(f(v[N])), N-1) : (:init, N)
    for i in start:-1:1
        ex = :(op(f(v[$i]), $ex))
    end
    ex
end

function Base._mapreduce_dim(f, op, init::Void, v::AbstractFixedVector, ::Colon)
    Base.mapfoldl_impl(f, op, init, v)
end

for f in [:(==), :isequal]
    @eval $f(v::AbstractFixedVector{N}, w::AbstractFixedVector{N}) where N = all(map($f, v, w))
end

for (g, op, init) in ((:_sum, :+, 0), (:_prod, :*, 1))
    @eval function Base.$g(f::F, v::AbstractFixedVector, ::Colon; kw...) where F
        w = map(f, v)
        T = eltype(w)
        if !(T <: Integer) || bitsize(T) >= bitsize(Int)
            foldl($op, w; kw...)
        elseif T <: Unsigned
            foldl($op, w; init = UInt($init), kw...)
        else
            foldl($op, w; init = Int($init), kw...)
        end
    end
end

"""
    sum_fast(v::AbstractFixedVector)

Return the `@fastmath` sum of the elements of `v`.
Unlike for `sum`, the return value always is of the element type of `v`, even for small bit integers.

See also `Base.sum`, `Base.@fastmath`.
"""
sum_fast(v::AbstractFixedVector) = @fastmath foldl(+, v)

Base._any(f, v::AbstractFixedVector, ::Colon) = findfirst(f, v) !== nothing
Base._all(f, v::AbstractFixedVector, ::Colon) = findfirst((!)∘f, v) === nothing

"""
    any(f::Function, v::AbstractFixedVector; dims = :, [style::MapStyle])
    all(f::Function, v::AbstractFixedVector; dims = :, [style::MapStyle])
    allequal(f, v::AbstractFixedVector; [style::MapStyle})
    allunique(f, v::AbstractFixedVector; [style::MapStyle])
    findfirst(f::Function, v::AbstractFixedVector; [style::MapStyle])
    findlast(f::Function, v::AbstractFixedVector; [style::MapStyle])

With an `AbstractFixedVector` `v` as second argument, these functions accept
the additional keyword argument `style`. If it equals `LazyStyle()`, then the
function `f` is only evaluated until the result has been determined. For any
other value of `style`, `f` is evaluated on all elements of `v`. This is often
faster for simple functions.

As discussed under `MapStyle`, the default value for `style` is based on a list
of known functions.

See also [`$(@__MODULE__).MapStyle`](@ref).
"""
any(::Function, ::AbstractFixedVector),
all(::Function, ::AbstractFixedVector),
allequal(::Any, ::AbstractFixedVector),
allunique(::Any, ::AbstractFixedVector),
findfirst(::Function, ::AbstractFixedVector),
findlast(::Function, ::AbstractFixedVector)

function any(f::F, v::AbstractFixedVector{N,T}; dims = :, style::MapStyle = MapStyle(f, T)) where {F <: Function, N, T}
    if !(dims isa Colon) || style isa LazyStyle
        invoke(any, Tuple{F,AbstractVector{T}}, f, v; dims)
    else
        Base._any(f, v, :)
    end
end

function all(f::F, v::AbstractFixedVector{N,T}; dims = :, style::MapStyle = MapStyle(f, T)) where {F <: Function, N, T}
    if !(dims isa Colon) || style isa LazyStyle
        invoke(all, Tuple{F,AbstractVector{T}}, f, v; dims)
    else
        Base._all(f, v, :)
    end
end

allequal(v::AbstractFixedVector) = all(isequal(v[1]), v)

function allequal(f::F, v::AbstractFixedVector{N,T}; style::MapStyle = MapStyle(f, T)) where {F,N,T}
    if style isa LazyStyle
        invoke(allequal, Tuple{F,AbstractVector{T}}, f, v)
    else
        allequal(map(f, v))
    end
end

allunique(v::AbstractFixedVector) = all(x -> count(isequal(x), v) == 1, v)

function allunique(f::F, v::AbstractFixedVector{N,T}; style::MapStyle = MapStyle(f, T)) where {F,N,T}
    if style isa LazyStyle
        invoke(allunique, Tuple{F,AbstractVector{T}}, f, v)
    else
        allunique(map(f, v))
    end
end

function Base._count(f::F, v::AbstractFixedVector, ::Colon, init::T) where {F,T}
    w = @inline map(f, v)
    eltype(w) == Bool || error("given function must return Bool values")
    init + count_ones(bits(w)) % T
end

Base._minimum(f, v::AbstractFixedVector, ::Colon; kw...) = mapfoldl(f, min, v; kw...)
Base._maximum(f, v::AbstractFixedVector, ::Colon; kw...) = mapfoldl(f, max, v; kw...)
Base._extrema(f, v::AbstractFixedVector, ::Colon; kw...) = mapfoldl(Base.ExtremaMap(f), Base._extrema_rf, v; kw...)

@fastmath maximum(v::AbstractFixedVector; kw...) = maximum(identity, v; kw...)

"""
    extrema_fast(v::AbstractFixedVector; [init])

Return the `@fastmath` minimum and maximum of the elements of `v`.
The `init` keyword argument may not be used.

See also `Base.extrema`, `Base.@fastmath`.
"""
extrema_fast(v::AbstractFixedVector; kw...) = extrema_fast(identity, v; kw...)

@fastmath function maximum(f::F, v::AbstractFixedVector{N,T}; kw...) where {F,N,T}
    if T <: AbstractFloat && T <: Base.HWReal
        -minimum(-map(f, v); kw...)   # work around LLVM bug for max_fast, see julia#56341
    else
        invoke(maximum, Tuple{F,AbstractVector}, f, v; kw...)
    end
end

"""
    extrema_fast(f, v::AbstractFixedVector; [init])

Return the `@fastmath` minimum and maximum of the values of `f` applied to the elements of `v`.
The `init` keyword argument may not be used.

See also `Base.extrema`, `Base.@fastmath`.
"""
function extrema_fast(f::F, v::AbstractFixedVector; init::Tuple{Any,Any} = (missing, missing)) where F
    if init === (missing, missing)
        @fastmath (minimum(f, v), maximum(f, v))
    else
        @fastmath (minimum(f, v; init = init[1]), maximum(f, v; init = init[2]))
    end
end

@inline function reverse(v::AbstractFixedVector{N,T}, start::Integer = 1, stop::Integer = N) where {N,T}
    @boundscheck checkbounds(v, start:stop)
    t = ntuple(Val(N)) do i
        @inbounds start <= i <= stop ? v[start+stop-i] : v[i]
    end
    FixedVector{N,T}(t)
end

vcat(v::AbstractFixedVector) = v

function vcat(v1::AbstractFixedVector{N1,T1}, v2::AbstractFixedVector{N2,T2}, vs::AbstractFixedVector...) where {N1,T1,N2,T2}
    T = promote_type(T1, T2)
    vcat(FixedVector{N1+N2,T}((v1..., v2...)), vs...)
 end

function findfirst(v::AbstractFixedVector{N,Bool}) where N
    m = bits(v)
    iszero(m) ? nothing : trailing_zeros(m)+1
end

function findlast(v::AbstractFixedVector{N,Bool}) where N
    m = bits(v)
    iszero(m) ? nothing : bitsize(m)-leading_zeros(m)
end

function findmin(v::AbstractFixedVector{N,T}) where {N, T <: BitInteger}
    m = minimum(v)
    m, findfirst(==(m), v)::Int
end

function findmax(v::AbstractFixedVector{N,T}) where {N, T <: BitInteger}
    m = maximum(v)
    m, findfirst(==(m), v)::Int
end

for f in (:findfirst, :findlast)
    @eval function $f(pred::F, v::AbstractFixedVector{N,T}; style::MapStyle = MapStyle(pred, T)) where {F <: Function, N, T}
        if style isa LazyStyle
            invoke($f, Tuple{F,AbstractVector{T}}, pred, v)
        else
            $f(map(x -> pred(x)::Bool, v))
        end
    end
end

Base.hasfastin(::Type{<:AbstractFixedVector{N,T}}) where {N,T} = isfasttype(T)

in(x, v::AbstractFixedVector) = any(==(x), v)

@inline replace_pair(v::AbstractFixedVector, w::AbstractFixedVector, p::Pair, ::Type{T}) where T =
    map((x, y) -> isequal(x, p[1]) ? convert(T, p[2]) : convert(T, y), v, w)

function replace(v::AbstractFixedVector{N,T}, ps::Vararg{Pair,M}; kw...) where {N,T,M}
    if isfasttype(T) && isempty(kw)
        foldl(ps; init = FixedVector(v)) do w, p
            U = promote_type(eltype(w), typeof(p[2]))
            replace_pair(v, w, p, U)  # separate function for type stability
        end
    else
        FixedVector(invoke(replace, Tuple{AbstractVector,Vararg{Pair,M}}, v, ps...; kw...))
    end
end

function replace!(v::MutableFixedVector{N,T}, ps::Vararg{Pair,M}; kw...) where {N,T,M}
    if isfasttype(T) && isempty(kw)
        v .= replace(v, ps...)
    else
        invoke(replace!, Tuple{AbstractVector,Vararg{Pair,M}}, v, ps...; kw...)
    end
end

"""
    support(v::AbstractFixedVector) -> SmallBitSet

Return the `SmallBitSet` with the indices of the non-zero elements of `v`.

See also [`SmallBitSet`](@ref).

# Example
```jldoctest
julia> v = FixedVector{4,Int8}([1, 0, 0, 3]);

julia> support(v)
SmallBitSet{UInt64} with 2 elements:
  1
  4
```
"""
support(v::AbstractFixedVector) = convert(SmallBitSet{UInt}, bits(map(!iszero, v)))

#
# broadcast
#

using Base.Broadcast:
    AbstractArrayStyle, DefaultArrayStyle, Broadcasted, broadcasted, materialize
import Base.Broadcast: BroadcastStyle
import Base: copy, copyto!

"""
    $(@__MODULE__).FixedVectorStyle <: Broadcast.AbstractArrayStyle{1}

The broadcasting style used for `AbstractFixedVector`.

See also [`AbstractFixedVector`](@ref), `Broadcast.AbstractArrayStyle`.
"""
struct FixedVectorStyle <: AbstractArrayStyle{1} end

BroadcastStyle(::Type{<:AbstractFixedVector}) = FixedVectorStyle()
BroadcastStyle(::FixedVectorStyle, ::DefaultArrayStyle{0}) = FixedVectorStyle()
BroadcastStyle(::FixedVectorStyle, ::DefaultArrayStyle{N}) where N = DefaultArrayStyle{N}()

bc_tuple(x) = x
bc_tuple(v::AbstractFixedVector) = Tuple(v)
bc_tuple(bc::Broadcasted{FixedVectorStyle}) = broadcasted(bc.f, map(bc_tuple, bc.args)...)

@inline copy(bc::Broadcasted{FixedVectorStyle}) = FixedVector(materialize(bc_tuple(bc)))

copyto!(v::MutableFixedVector, bc::Broadcasted{FixedVectorStyle}) = copyto!(v, copy(bc))

const TupleVector{N,T} = AbstractFixedVector{N,T}
const Values{N,T} = FixedVector{N,T}
const Variables{N,T} = MutableFixedVector{N,T}
