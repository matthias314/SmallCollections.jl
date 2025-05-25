#
# extensions of FixedVector
#

using Base: BitInteger, @assume_effects
import Base: setindex

export setindex, rotate, rotate!

"""
    setindex(v::AbstractFixedVector{N,T}, x, i::Integer) where {N,T} -> FixedVector{N,T}

Substitute `x` for the `i`-th component of `v` and return the result. The vector `v` is not modified.

See also `Base.setindex`,  [`addindex`](@ref addindex(::AbstractFixedVector, ::Any, ::Integer)).
"""
setindex(::AbstractFixedVector, ::Any, ::Integer)

@inline function setindex(v::AbstractFixedVector{N,T}, x, i::Integer) where {N,T}
    @boundscheck checkbounds(v, i)
    t = ntuple(Val(N)) do j
        ifelse(j == i, convert(T, x), v[j])
    end
    FixedVector{N,T}(t)
end

"""
    addindex(v::AbstractFixedVector{N,T}, x, i::Integer) where {N,T} -> FixedVector{N,T}

Add `x` to the `i`-th component of `v` and return the result. The vector `v` is not modified.

See also [`setindex`](@ref setindex(::AbstractFixedVector, ::Any, ::Integer)).
"""
@propagate_inbounds function addindex(v::AbstractFixedVector, x, i::Integer)
    v + setindex(zero(v), x, i)
end

function padtail(v::Values{N,T}, i::Integer, x = default(T)) where {N,T}
    t = ntuple(Val(N)) do j
        ifelse(j <= i, v[j], convert(T, x))
    end
    Values{N,T}(t)
end

@generated function padtail(v::FixedVector{N,T}, n::Integer) where {N, T <: HWType}
    M = if T == Float32
        "float"
    elseif T == Float64
        "double"
    else # Bool, BitInteger, Char, Enum
        string('i', 8*sizeof(T))
    end
    L = bitsize(SmallLength)
    s = join(("i$L $k" for k in 0:N-1), ", ")
    ir = """
        %b = insertelement <$N x i$L> poison, i$L %1, i8 0
        %c = shufflevector <$N x i$L> %b, <$N x i$L> poison, <$N x i32> zeroinitializer
        %d = icmp ult <$N x i$L> <$s>, %c
        %r = select <$N x i1> %d, <$N x $M> %0, <$N x $M> zeroinitializer
        ret <$N x $M> %r
        """
    quote
        @inline
        b = Base.llvmcall($ir, NTuple{N, VecElement{T}}, Tuple{NTuple{N, VecElement{T}}, SmallLength}, vec(Tuple(v)), n % SmallLength)
        FixedVector{N,T}(unvec(b))
    end
end

pushfirst(v::Values, xs...) = prepend(v, xs)

function prepend(v::Values{N,T}, w::Union{AbstractVector,Tuple}) where {N,T}
    n = length(w)
    t = ntuple(Val(N)) do i
        @inbounds i <= n ? convert(T, w[i]) : v[i-n]
    end
    Values{N,T}(t)
end

popfirst(v::Values) = popat(v, 1)

@inline function insert(v::Values{N,T}, i::Integer, x) where {N,T}
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
    Values{N,T}(t)
end

@propagate_inbounds deleteat(v::Values, i::Integer) = first(popat(v, i))

@inline function popat(v::Values{N,T}, i::Integer) where {N,T}
    @boundscheck checkbounds(v, i)
    t = ntuple(Val(N)) do j
        if j < i
            v[j]
        elseif j < N
            v[j+1]
        else
            default(T)
        end
    end
    Values{N,T}(t), v[i]
end

"""
    rotate(v::AbstractFixedVector{N,T}, k::Integer) -> FixedVector{N,T}
    rotate(v::AbstractFixedVector{N,T}, ::Val{k}) where k -> FixedVector{N,T}

Rotate `v` by `k` positions towards higher indices and return the result.
A negative value of `k` corresponds to a rotation towards lower indices.

See also [`rotate!`](@ref rotate!(::MutableFixedVector, ::Union{Integer,Val}).

# Examples
```jldoctest
julia> v = FixedVector{4}(1:4);

julia> rotate(v, 1)
4-element FixedVector{4, Int64}:
 4
 1
 2
 3

julia> rotate(v, Val(-1))
4-element FixedVector{4, Int64}:
 2
 3
 4
 1
```
"""
rotate(::AbstractFixedVector, ::Union{Integer,Val})

@inline function rotate(v::AbstractFixedVector{N,T}, k::Integer) where {N,T}
    t = ntuple(i -> v[mod(i-k, 1:N)], Val(N))
    FixedVector{N,T}(t)
end

rotate(v::AbstractFixedVector, ::Val{k}) where k = rotate(v, k)

@generated function rotate(v::MutableFixedVector{N,T}, ::Val{K}) where {N , T <: Union{Base.BitInteger,Bool,Char,Enum}, K}
    b = sizeof(T)
    m = 8*b  # for Bool we need 8, not 1
    s = join(("i32 " * string(mod(i-K, N)) for i in 0:N-1), ", ")
    ir = VERSION > v"1.12-" ? """
        %a = load <$N x i$m>, ptr %0, align $b
        %b = shufflevector <$N x i$m> %a, <$N x i$m> poison, <$N x i32> <$s>
        ret <$N x i$m> %b
    """ : """
        %p = inttoptr i64 %0 to <$N x i$m>*
        %a = load <$N x i$m>, <$N x i$m>* %p, align $b
        %b = shufflevector <$N x i$m> %a, <$N x i$m> poison, <$N x i32> <$s>
        ret <$N x i$m> %b
    """
    quote
        b = Base.llvmcall($ir, NTuple{N,VecElement{T}}, Tuple{Ptr{T}}, pointer(v))
        FixedVector{N,T}(unvec(b))
    end
end

"""
    rotate!(v::MutableFixedVector{N,T}, k::Integer) -> v
    rotate!(v::MutableFixedVector{N,T}, ::Val{k}) where k -> v

Rotate `v` in-place by `k` positions towards higher indices and return `v`.
A negative value of `k` corresponds to a rotation towards lower indices.

See also [`rotate`](@ref rotate(::AbstractFixedVector, ::Union{Integer,Val}).

# Examples
```jldoctest
julia> v = MutableFixedVector{4}(1:4);

julia> rotate!(v, 1)
4-element MutableFixedVector{4, Int64}:
 4
 1
 2
 3

julia> rotate!(v, Val(-1))  # undo previous step
4-element MutableFixedVector{4, Int64}:
 1
 2
 3
 4
```
"""
rotate!(::MutableFixedVector, ::Union{Integer,Val})

@inline function rotate!(v::MutableFixedVector, k::Integer)
    v .= rotate(v, k)
end

rotate!(v::MutableFixedVector, ::Val{k}) where k = rotate!(v, k)

function rotate!(v::MutableFixedVector{N,T}, ::Val{K}) where {N, T <: HWType, K}
    vec_rotate!(pointer(v), Val(N), Val(K))
    v
end

@inline @generated function vec_rotate!(ptr::Ptr{T}, ::Val{N}, ::Val{K}) where {N, T <: HWType, K}
    b = sizeof(T)
    m = 8*b  # for Bool we need 8, not 1
    s = join(("i32 " * string(mod(i-K, N)) for i in 0:N-1), ", ")
    ir = VERSION > v"1.12-" ? """
        %a = load <$N x i$m>, ptr %0, align $b
        %b = shufflevector <$N x i$m> %a, <$N x i$m> poison, <$N x i32> <$s>
        store <$N x i$m> %b, ptr %0, align $b
        ret void
    """ : """
        %p = inttoptr i64 %0 to <$N x i$m>*
        %a = load <$N x i$m>, <$N x i$m>* %p, align $b
        %b = shufflevector <$N x i$m> %a, <$N x i$m> poison, <$N x i32> <$s>
        store <$N x i$m> %b, <$N x i$m>* %p, align $b
        ret void
    """
    quote
        Base.llvmcall($ir, Cvoid, Tuple{Ptr{T}}, ptr)
    end
end

"""
    $(@__MODULE__).default(::Type{T}) where T -> T
    $(@__MODULE__).default(::T) where T -> T

Return the default value of type `T` used for filling unused elements of an `AbstractSmallVector`.
This must be defined as `zero(T)` if `T` supports algebraic operations. Otherwise it can
be any value of type `T`.

This function has methods for number types, bits types, `Symbol`, `AbstractChar`, `AbstractString`,
`Tuple`, `NamedTuple`, `AbstractFixedVector`, `AbstractSmallVector` und `SmallBitSet`.
Methods for other types must be defined explicitly.

See also `Base.isbitstype`.
"""
default(::T) where T = default(T)

function default(::Type{T}) where T
    if isbitstype(T)
        default_bitstype(T)
    elseif Int <: T
        0
    else
        error("no default value defined for type $T")
    end
end

Base.@assume_effects :total function default_bitstype(::Type{T}) where T
    m8, m1 = divrem(Base.packedsize(T), 8)
    t8 = ntuple(Returns(UInt64(0)), Val(m8))
    t1 = ntuple(Returns(UInt8(0)), Val(m1))
    reinterpret(T, (t8, t1))
end

default(::Type{T}) where T <: Number = zero(T)
default(::Type{T}) where T <: AbstractChar = T(0)
default(::Type{<:AbstractString}) = ""
default(::Type{Symbol}) = Symbol()

default(::Type{T}) where T <: Tuple = map_tuple(default, fieldtypes(T))
default(::Type{NamedTuple{K,T}}) where {K,T} = NamedTuple{K}(default(T))
default(::Type{Pair{K,V}}) where {K,V} = default(K) => default(V)

default(::Type{V}) where {N,T,V<:TupleVector{N,T}} = V(default(NTuple{N,T}))

#
# bit conversions
#

vec(t::NTuple{N}) where N = ntuple(i -> VecElement(t[i]), Val(N))

unvec(t::NTuple{N,VecElement}) where N = ntuple(i -> t[i].value, Val(N))

"""
    bits(v::$TupleVector{N,T}) where {N, T <: Union{Base.BitInteger,Bool,Char,Enum}} -> Unsigned

Convert the given vector to an unsigned integer.

For bit integers, `Char` and `Enum` types this is the same as `reinterpret(U, Tuple(v))` provided that
`U` is an unsigned integer type with `N*bitsize(T)` bits, possibly defined by the package
`BitIntegers`. Otherwise the result will be zero-extended to the next unsigned integer type `U`
whose bit length is a power of `2`.

If the element type is `Bool`, then each element only takes one bit in the return value.
If `N` is less than `8` or not a power of `2`, then the result will again be zero-extended.

See also [`$(@__MODULE__).bitsize`](@ref), `Base.BitInteger`, `Base.reinterpret`, `BitIntegers`.

# Examples
```jldoctest
julia> $Values{4,Int8}(1:4) |> bits
0x04030201

julia> $Values{3}('a':'c') |> bits
0x00000000630000006200000061000000

julia> m = $Values{6,UInt32}(1:6) |> bits
0x0000000000000000000000060000000500000004000000030000000200000001

julia> typeof(m)
BitIntegers.UInt256

julia> $Values{22}(map(isodd, 1:22)) |> bits
0x00155555
```
"""
bits(v::TupleVector)

@generated function bits(v::TupleVector{N,T}) where {N, T <: Union{BitInteger,Char,Enum}}
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

@generated function bits(v::TupleVector{N,T}) where {N, T <: Union{Int128,UInt128}}
    n = nextpow(2, N)
    U = Symbol(:UInt, n*128)
    z = ntuple(Returns(zero(T)), Val(n-N))
    quote
        t = (Tuple(v)..., $z...)
        reinterpret($U, t)
    end
end

@generated function bits(v::TupleVector{N,Bool}) where N
    c = max(nextpow(2, N), 8)
    U = Symbol(:UInt, c)
    if N == c
        ir = """
            %b = trunc <$N x i8> %0 to <$N x i1>
            %c = bitcast <$N x i1> %b to i$N
            ret i$N %c
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

@generated function _convert(::Type{Values{N,T}}, x::U) where {N, T <: BitInteger, U <: Unsigned}
    s = bitsize(T)
    b = N*s
    c = bitsize(U)
    if b == c
        ir = """
            %b = bitcast i$b %0 to <$N x i$s>
            ret <$N x i$s> %b
        """
    elseif b > c
        ir = """
            %b = zext i$c %0 to i$b
            %a = bitcast i$b %b to <$N x i$s>
            ret <$N x i$s> %a
        """
    else
        ir = """
            %b = trunc i$c %0 to i$b
            %a = bitcast i$b %b to <$N x i$s>
            ret <$N x i$s> %a
        """
    end
    quote
        $(Expr(:meta, :inline))
        v = Base.llvmcall($ir, NTuple{N, VecElement{T}}, Tuple{$U}, x)
        Values{N,T}(unvec(v))
    end
end

@generated function _convert(::Type{Values{N,Bool}}, x::U) where {N, U <: Unsigned}
    c = bitsize(U)
    N2 = nextpow(2, N)   # work around an LLVM bug
    if N2 == c
        ir = """
            %b = bitcast i$N2 %0 to <$N2 x i1>
            %c = zext <$N2 x i1> %b to <$N2 x i8>
            ret <$N2 x i8> %c
        """
    elseif N2 > c
        ir = """
            %a = zext i$c %0 to i$N2
            %b = bitcast i$N2 %a to <$N2 x i1>
            %c = zext <$N2 x i1> %b to <$N2 x i8>
            ret <$N2 x i8> %c
        """
    else
        ir = """
            %a = trunc i$c %0 to i$N2
            %b = bitcast i$N2 %a to <$N2 x i1>
            %c = zext <$N2 x i1> %b to <$N2 x i8>
            ret <$N2 x i8> %c
        """
    end
    quote
        $(Expr(:meta, :inline))
        v2 = Base.llvmcall($ir, NTuple{$N2, VecElement{Bool}}, Tuple{$U}, x)
        v = ntuple(Base.Fix1(getindex, v2), Val(N))
        Values{N,Bool}(unvec(v))
    end
end
