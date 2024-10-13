export AbstractFixedVector, FixedVector, MutableFixedVector

using Base: @propagate_inbounds, tail, haslength, BitInteger

import Base: Tuple, ==, isequal, size,
    IndexStyle, getindex, setindex!, iterate, iszero, zero, +, -, *, map, map!,
    sum, prod, minimum, maximum, extrema, count, any, all, in, reverse,
    mapfoldl, mapfoldr, vcat, copy, copyto!, convert,
    strides, elsize, unsafe_convert, muladd

"""
    AbstractFixedVector{N,T} <: AbstractVector{T}

`AbstractFixedVector{N,T}` is the supertype of `FixedVector{N,T}` and `MutableFixedVector{N,T}`.

See also [`FixedVector{N,T}`](@ref), [`MutableFixedVector{N,T}`](@ref).
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
As a rule of thumb, the size should only be omitted for `Tuple` arguments.

See also [`MutableFixedVector{N,T}`](@ref).
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

See also [`FixedVector{N,T}`](@ref), `Base.isbits`.
"""
mutable struct MutableFixedVector{N,T} <: AbstractFixedVector{N,T}
    t::NTuple{N,T}
    MutableFixedVector{N,T}(t::NTuple{N,Any}) where {N,T} = new{N,T}(t)
    MutableFixedVector{N,T}(::UndefInitializer) where {N,T} = new{N,T}()
end

(::Type{V})(v::AbstractFixedVector{N}) where {N,T,V<:AbstractFixedVector{N,T}} = V(v.t)
# to avoid (possibly allocating) NTuple in other constructor

function (::Type{V})(t) where {N,T,V<:AbstractFixedVector{N,T}}
    isconcretetype(V) || error("constructor type must be concrete")
    !haslength(t) || length(t) == N || error("argument is not of length $N")
    V(NTuple{N,T}(t))
end

function (::Type{V})(t) where {N,V<:AbstractFixedVector{N}}
    if Base.IteratorEltype(t) isa Base.HasEltype
        T = eltype(t)
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
    isbits(T) ? unsafe_getindex(v, i) : @inbounds v.t[i]
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

function map(f::F, vs::Vararg{AbstractFixedVector,N}) where {F,N}
    FixedVector(map(f, map(Tuple, vs)...))
end

function map!(f::F, w::MutableFixedVector, vs::Vararg{AbstractFixedVector,N}) where {F,N}
    copyto!(w, map(f, map(Tuple, vs)...))
end

for f in (:sum, :prod, :minimum, :maximum)
    ff = Symbol('_', f)
    @eval $f(v::AbstractFixedVector; kw...) = $f(identity, v; kw...)
    @eval function $f(g, v::AbstractFixedVector; dims = :, kw...)
        if dims isa Colon
            $f(g, Tuple(v); kw...)
        else
            invoke($f, Tuple{typeof(g),AbstractVector}, g, v; dims, kw...)
        end
    end
end

extrema(v::AbstractFixedVector; kw...) = extrema(identity, v; kw...)

function extrema(g, v::AbstractFixedVector; init::Union{Missing,Tuple{Any,Any}} = missing)
    if init === missing
        (minimum(g, v), maximum(g, v))
    else
        (minimum(g, v; init = init[1]), maximum(g, v; init = init[2]))
    end
end

sum_fast(v::AbstractFixedVector) = sum(v)
sum_fast(v::AbstractFixedVector{N,T}) where {N, T <: FastFloat} = @fastmath foldl(+, Tuple(v))

for f in (:mapfoldl, :mapfoldr)
    @eval $f(g, op, v::AbstractFixedVector; kw...) = $f(g, op, v.t; kw...)
end

count(v::AbstractFixedVector{N,Bool}; kw...) where N = sum(v; kw...)

#=
_or(x, y) = x | y
@inline _or(x, ::Missing) = x ? true : missing
@inline _or(::Missing, x) = x ? true : missing
_or(::Missing, ::Missing) = missing
=#

#=
function _any(f::F, v::AbstractFixedVector{N,T}) where {F,N,T}
    if Missing <: Core.Compiler.return_type(f, Tuple{T})
        any(f, v.t)
    else
        reduce((b, x) -> b | f(x), v.t; init = false)
    end
end
=#

any(v::AbstractFixedVector; kw...) = any(identity, v; kw...)
any(f, v::AbstractFixedVector; dims = :) = _any(f, v, dims)
any(f::Function, v::AbstractFixedVector; dims = :) = _any(f, v, dims)

# TODO: Function should be replaced by Any in Julia 1.12
# _any(f::Function, v::AbstractFixedVector, dims) = invoke(any, Tuple{Function, AbstractArray}, f, v; dims)
# TODO: replace Function
_any(f, v::AbstractFixedVector, dims) = invoke(any, Tuple{Function, AbstractArray}, f, v; dims)

_any(f, v::AbstractFixedVector, dims::Colon) = reduce(v.t; init = false) do b, x
    c = f(x)
    (b === missing && c) || (c === missing && b) ? true : b | c
end

#=
any_tuple(t) = any(t)
any_tuple(t::Tuple{Vararg{Bool}}) = reduce(|, t; init = false)

any(v::AbstractFixedVector) = any_tuple(v.t)
any(f, v::AbstractFixedVector) = any_tuple(map(f, v.t))
any(f::Function, v::AbstractFixedVector) = any_tuple(map(f, v.t))
=#

all(v::AbstractFixedVector; kw...) = all(identity, v; kw...)
all(f, v::AbstractFixedVector; kw...) = !any(!f, v; kw...)
all(f::Function, v::AbstractFixedVector; kw...) = !any(!f, v; kw...)

in(x, v::AbstractFixedVector) = any(==(x), v)

@inline function reverse(v::AbstractFixedVector{N,T}, start::Integer = 1, stop::Integer = N) where {N,T}
    @boundscheck checkbounds(v, start:stop)
    t = ntuple(Val(N)) do i
        @inbounds v.t[start <= i <= stop ? start+stop-i : i]
    end
    FixedVector{N,T}(t)
end

vcat(v::AbstractFixedVector) = v

function vcat(v1::AbstractFixedVector{N1,T1}, v2::AbstractFixedVector{N2,T2}, vs::AbstractFixedVector...) where {N1,T1,N2,T2}
    T = promote_type(T1, T2)
    vcat(AbstractFixedVector{N1+N2,T}((v1..., v2...)), vs...)
 end

# equality

for f in [:(==), :isequal]
    @eval $f(v::AbstractFixedVector{N}, w::AbstractFixedVector{N}) where N = all(FixedVector(map($f, v.t, w.t)))
end

import Base: findfirst, findlast

function findfirst(v::AbstractFixedVector{N,Bool}) where N
    m = bits(v)
    iszero(m) ? nothing : trailing_zeros(m)+1
end

function findlast(v::AbstractFixedVector{N,Bool}) where N
    m = bits(v)
    iszero(m) ? nothing : bitsize(m)-leading_zeros(m)
end

support(v::AbstractFixedVector) = convert(SmallBitSet{UInt}, bits(map(!iszero, v)))

#
# broadcast
#

using Base.Broadcast:
    AbstractArrayStyle, DefaultArrayStyle, Broadcasted, broadcasted, materialize
import Base.Broadcast: BroadcastStyle
import Base: copy, copyto!

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
