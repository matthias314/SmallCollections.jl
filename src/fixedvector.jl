export AbstractFixedVector, FixedVector, MutableFixedVector,
    sum_fast, extrema_fast

using Base: @propagate_inbounds, tail, haslength, BitInteger

import Base: Tuple, ==, isequal, size,
    IndexStyle, getindex, setindex!, iterate, iszero, zero, +, -, *, map, map!,
    sum, prod, minimum, maximum, extrema, count, any, all, in, reverse,
    findfirst, findlast, vcat, copy, copyto!, convert,
    strides, elsize, unsafe_convert, muladd

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

(::Type{V})(v::AbstractFixedVector{N}) where {N,T,V<:AbstractFixedVector{N,T}} = V(Tuple(v))
# to avoid (possibly allocating) NTuple in other constructor

function (::Type{V})(t) where {N,T,V<:AbstractFixedVector{N,T}}
    isconcretetype(V) || error("constructor type must be concrete")
    !haslength(t) || length(t) == N || error("argument is not of length $N")
    V(NTuple{N,T}(t))
end

function (::Type{V})(t) where {N,V<:AbstractFixedVector{N}}
    if Base.IteratorEltype(t) isa Base.HasEltype
        T = element_type(t)
        V{T}(t)
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

@inline -(v::AbstractFixedVector) = FixedVector(.- v.t)

@inline +(v::AbstractFixedVector{N}, w::AbstractFixedVector{N}) where N = FixedVector(v.t .+ w.t)

@inline -(v::AbstractFixedVector{N}, w::AbstractFixedVector{N}) where N = FixedVector(v.t .- w.t)

#=
function +(v::AbstractFixedVector{N,T1}, w::AbstractFixedVector{N,T2}) where {N,T1,T2}
    T = promote_type(T1, T2)
    AbstractFixedVector{N,T}(v.t .+ w.t)
end

function -(v::AbstractFixedVector{N,T1}, w::AbstractFixedVector{N,T2}) where {N,T1,T2}
    T = promote_type(T1, T2)
    AbstractFixedVector{N,T}(v.t .- w.t)
end
=#

@inline *(c::Number, v::AbstractFixedVector) = FixedVector(c .* v.t)
*(v::AbstractFixedVector, c::Number) = c*v

@inline muladd(c::Number, v::AbstractFixedVector{N}, w::AbstractFixedVector{N}) where N =
    FixedVector(muladd.(c, Tuple(v), Tuple(w)))

muladd(v::AbstractFixedVector{N}, c::Number, w::AbstractFixedVector{N}) where N = muladd(c, v, w)

@generated function map_tuple(f, xs::Tuple...)
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
    ex, start = init <: Base._InitialValue ? (:(f(v[1])), 2) : (:init, 1)
    for i in start:N
        ex = :(op($ex, f(v[$i])))
    end
    ex
end

@generated function Base.mapfoldr_impl(f, op, init, v::AbstractFixedVector{N}) where N
    ex, start = init <: Base._InitialValue ? (:(f(v[N])), N-1) : (:init, N)
    for i in start:-1:1
        ex = :(op(f(v[$i]), $ex))
    end
    ex
end

function Base._mapreduce_dim(f, op, init::Base._InitialValue, v::AbstractFixedVector, ::Colon)
    Base.mapfoldl_impl(f, op, init, v)
end

for f in [:(==), :isequal]
    @eval $f(v::AbstractFixedVector{N}, w::AbstractFixedVector{N}) where N = all(map($f, v, w))
end

for (g, op) in ((:_sum, :+), (:_prod, :*))
    @eval function Base.$g(f::F, v::AbstractFixedVector, ::Colon; kw...) where F
        w = map(f, v)
        T = eltype(w)
        if !(T <: Integer) || bitsize(T) >= bitsize(Int)
            foldl($op, w; kw...)
        elseif T <: Unsigned
            foldl($op, w; init = UInt(0), kw...)
        else
            foldl($op, w; init = Int(0), kw...)
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

Base._count(f, v::AbstractFixedVector, ::Colon, init) = Base._sum(x -> f(x)::Bool, v, :; init)

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
    vcat(AbstractFixedVector{N1+N2,T}((v1..., v2...)), vs...)
 end

function findfirst(v::AbstractFixedVector{N,Bool}) where N
    m = bits(v)
    iszero(m) ? nothing : trailing_zeros(m)+1
end

function findlast(v::AbstractFixedVector{N,Bool}) where N
    m = bits(v)
    iszero(m) ? nothing : bitsize(m)-leading_zeros(m)
end

const FastTestType = Union{Base.HWReal, Bool, Char}

const FastTest = Union{
    Base.Fix2{<:Union{typeof.((==, !=, <=, >=, <, >, isequal))...}, <:FastTestType},
    typeof.((identity, !, iszero, isone, iseven, isodd, isfinite, isnan, signbit))...,
    ComposedFunction{typeof(!),<:Union{
        Base.Fix2{<:Union{typeof.((==, !=, <=, >=, <, >, isequal))...}, <:FastTestType},
        typeof.((identity, iszero, isone, iseven, isodd, isfinite, isnan, signbit))...}
    }
}
# TODO: are "iseven" and "isodd" a good idea?

for f in (:findfirst, :findlast)
    @eval function $f(pred::FastTest, v::AbstractFixedVector{<:Any,<:FastTestType})
        $f(map(x -> pred(x)::Bool, v))
    end
end

Base.hasfastin(::Type{<:AbstractFixedVector{<:Any,<:FastTestType}}) = true

in(x, v::AbstractFixedVector) = any(==(x), v)

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
