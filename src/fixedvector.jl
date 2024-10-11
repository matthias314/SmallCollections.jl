export AbstractFixedVector, FixedVector, MutableFixedVector

using Base: @propagate_inbounds, tail, haslength, BitInteger

import Base: Tuple, ==, isequal, size,
    IndexStyle, getindex, setindex!, iterate, iszero, zero, +, -, *, map, map!,
    sum, prod, minimum, maximum, extrema, count, any, all, in, reverse,
    mapfoldl, mapfoldr, vcat, copy, copyto!, convert,
    strides, elsize, unsafe_convert, muladd

abstract type AbstractFixedVector{N,T} <: AbstractVector{T} end

struct FixedVector{N,T} <: AbstractFixedVector{N,T}
    t::NTuple{N,T}
    FixedVector{N,T}(t::NTuple{N}) where {N,T} = new{N,T}(t)
end

mutable struct MutableFixedVector{N,T} <: AbstractFixedVector{N,T}
    t::NTuple{N,T}
    MutableFixedVector{N,T}(t::NTuple{N}) where {N,T} = new{N,T}(t)
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

reverse(v::AbstractFixedVector{N,T}) where {N,T} = AbstractFixedVector{N,T}(reverse(v.t))

vcat(v::AbstractFixedVector) = v

function vcat(v1::AbstractFixedVector{N1,T1}, v2::AbstractFixedVector{N2,T2}, vs::AbstractFixedVector...) where {N1,T1,N2,T2}
    T = promote_type(T1, T2)
    vcat(AbstractFixedVector{N1+N2,T}((v1..., v2...)), vs...)
 end

# equality

for f in [:(==), :isequal]
    @eval $f(v::AbstractFixedVector{N}, w::AbstractFixedVector{N}) where N = all(FixedVector(map($f, v.t, w.t)))
end

#=

# iszero

bitsize(::Type{T}) where T = 8*sizeof(T)
bitsize(::T) where T = bitsize(T)

vec(t::NTuple{N}) where N = ntuple(i -> VecElement(t[i]), Val(N))

#=
@generated function iszero(v::AbstractFixedVector{N,T}) where {N, T <: BitInteger}
    m = bitsize(T)
    n = N*m
    ir = """
            %a = bitcast <$N x i$m> %0 to i$n
            %b = icmp eq i$n %a, zeroinitializer
            %c = zext i1 %b to i8
            ret i8 %c
    """
    quote
        $(Expr(:meta, :inline))
        Base.llvmcall($ir, Bool, Tuple{NTuple{N, VecElement{T}}}, vec(Tuple(v)))
    end
end

@generated function iszero(v::AbstractFixedVector{N,T}) where {N, T <: Union{Float16, Float32, Float64}}
    if T == Float64
        t = "double"
    elseif T == Float32
        t = "float"
    else
        t = "half"
    end
    ir = """
            %b = fcmp une <$N x $t> %0, zeroinitializer
            %i = bitcast <$N x i1> %b to i$N
            %c = icmp eq i$N %i, zeroinitializer
            %d = zext i1 %c to i8
            ret i8 %d
    """
    quote
        $(Expr(:meta, :inline))
        Base.llvmcall($ir, Bool, Tuple{NTuple{N, VecElement{T}}}, vec(Tuple(v)))
    end
end
=#

# findfirst & findlast

@generated function bits(v::AbstractFixedVector{N,Bool}) where N
    c = max(nextpow(2, N), 8)
    U = Symbol(:UInt, c)
    if N == c
        ir = """
            %a = trunc <$N x i8> %0 to <$N x i1>
            %b = bitcast <$N x i1> %a to i$N
            ret i$N %b
        """
    else
        ir = """
            %a = trunc <$N x i8> %0 to <$N x i1>
            %b = bitcast <$N x i1> %a to i$N
            %c = zext i$N %b to i$c
            ret i$c %c
        """
    end
    quote
        $(Expr(:meta, :inline))
        Base.llvmcall($ir, $U, Tuple{NTuple{N, VecElement{Bool}}}, vec(Tuple(v)))
    end
end

=#

import Base: findfirst, findlast

function findfirst(v::AbstractFixedVector{N,Bool}) where N
    m = bits(v)
    iszero(m) ? nothing : trailing_zeros(m)+1
end

function findlast(v::AbstractFixedVector{N,Bool}) where N
    m = bits(v)
    iszero(m) ? nothing : bitsize(m)-leading_zeros(m)
end

#=

#
# from SmallCollections/src/staticvectors.jl
#

using Base: BitInteger

import Base: setindex

export bits, insert

unvec(t::NTuple{N,VecElement}) where N = ntuple(i -> t[i].value, Val(N))

@inline function setindex(v::AbstractFixedVector{N,T}, x, i::Integer) where {N,T}
    @boundscheck checkbounds(v, i)
    t = ntuple(Val(N)) do j
        ifelse(j == i, convert(T, x), v[j])
    end
    FixedVector{N,T}(t)
end

@inline function insert(v::AbstractFixedVector{N,T}, i::Integer, x) where {N,T}
    @boundscheck checkbounds(v, i)
    v = Tuple(v)
    t = ntuple(Val(N)) do j
        if j < i
            v[j]
        elseif j == i
            convert(T, x)
        else
            v[j-1]
        end
    end
    FixedVector{N,T}(t)
end

@generated function bits(v::AbstractFixedVector{N,T}) where {N, T <: Union{BitInteger,Char}}
    s = bitsize(T)
    b = N*s
    c = nextpow(2, b)
    U = Symbol(:UInt, c)
    if b == c
        ir = """
            %b = bitcast <$N x i$s> %0 to i$b
            ret i$b %b
        """
    else
        ir = """
            %b = bitcast <$N x i$s> %0 to i$b
            %c = zext i$b %b to i$c
            ret i$c %c
        """
    end
    quote
        $(Expr(:meta, :inline))
        Base.llvmcall($ir, $U, Tuple{NTuple{N, VecElement{T}}}, vec(Tuple(v)))
    end
end

@generated function bits(v::AbstractFixedVector{N,T}) where {N, T <: Union{Int128,UInt128}}
    n = nextpow(2, N)
    U = Symbol(:UInt, n*128)
    z = ntuple(Returns(zero(T)), n-N)
    quote
        t = (v.v..., $z...)
        reinterpret($U, t)
    end
end

=#

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
