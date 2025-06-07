#
# extensions of FixedVector
#

using Base: BitInteger, @assume_effects
import Base: setindex, circshift, circshift!, convert

export setindex

"""
    setindex(v::AbstractFixedVector{N,T}, x, i::Integer) where {N,T} -> FixedVector{N,T}

Substitute `x` for the `i`-th component of `v` and return the result. The vector `v` is not modified.

See also `Base.setindex`,  [`addindex`](@ref addindex(::AbstractFixedVector, ::Any, ::Integer)).
"""
setindex(::AbstractFixedVector, ::Any, ::Integer)

@inline function setindex(v::AbstractFixedVector{N,T}, x, i::Integer) where {N,T}
    @boundscheck checkbounds(v, i)
    i = i % SmallLength
    t = ntuple(Val(N)) do j
        j = j % SmallLength
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

"""
    $(@__MODULE__).padtail(v::AbstractFixedVector{N,T}, i::Integer, x = default(T)) where {N,T} -> FixedVector{N,T}

Replace the elements of `v` after the `i`-th position by `x` and return the new vector.
Providing an out-of-bounds index `i` does not produce an error.

# Example
```jldoctest
julia> v = FixedVector{4,Int}(1:4);

julia> $(@__MODULE__).padtail(v, 2)
4-element FixedVector{4, Int64}:
 1
 2
 0
 0

julia> $(@__MODULE__).padtail(v, 2, -1)
4-element FixedVector{4, Int64}:
  1
  2
 -1
 -1
```
"""
function padtail(v::AbstractFixedVector{N,T}, i::Integer, x = default(T)) where {N,T}
    i = i % SmallLength
    t = ntuple(Val(N)) do j
        j = j % SmallLength
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
    circshift(v::AbstractFixedVector{N,T}, k::Integer) -> FixedVector{N,T}
    circshift(v::AbstractFixedVector{N,T}, ::Val{k}) where k -> FixedVector{N,T}

Rotate `v` by `k` positions towards higher indices and return the result.
A negative value of `k` corresponds to a rotation towards lower indices.

See also [`circshift!`](@ref circshift!(::MutableFixedVector, ::Union{Integer,Val}).

# Examples
```jldoctest
julia> v = FixedVector{4}(1:4);

julia> circshift(v, 1)
4-element FixedVector{4, Int64}:
 4
 1
 2
 3

julia> circshift(v, Val(-1))
4-element FixedVector{4, Int64}:
 2
 3
 4
 1
```
"""
circshift(::AbstractFixedVector, ::Union{Integer,Val})

@inline function circshift(v::AbstractFixedVector{N,T}, k::Integer) where {N,T}
    N == 1 && return FixedVector(v)
    m = mod1(k+1, N)
    t = ntuple(Val(N)) do i
        i = i % SmallLength
        @inbounds if i < m % SmallLength
            v[(i-m+1)+N]
        else
            v[i-m+1]
        end
    end
    FixedVector{N,T}(t)
end

circshift(v::AbstractFixedVector, ::Val{k}) where k = circshift(v, k)

@generated function circshift(v::MutableFixedVector{N,T}, ::Val{K}) where {N , T <: Union{Base.BitInteger,Bool,Char,Enum}, K}
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
    circshift!(v::MutableFixedVector{N,T}, k::Integer) -> v
    circshift!(v::MutableFixedVector{N,T}, ::Val{k}) where k -> v

Rotate `v` in-place by `k` positions towards higher indices and return `v`.
A negative value of `k` corresponds to a rotation towards lower indices.

See also [`circshift`](@ref circshift(::AbstractFixedVector, ::Union{Integer,Val}).

# Examples
```jldoctest
julia> v = MutableFixedVector{4}(1:4);

julia> circshift!(v, 1)
4-element MutableFixedVector{4, Int64}:
 4
 1
 2
 3

julia> circshift!(v, Val(-1))  # undo previous step
4-element MutableFixedVector{4, Int64}:
 1
 2
 3
 4
```
"""
circshift!(::MutableFixedVector, ::Union{Integer,Val})

@inline function circshift!(v::MutableFixedVector, k::Integer)
    v .= circshift(v, k)
end

circshift!(v::MutableFixedVector, ::Val{k}) where k = circshift!(v, k)

function circshift!(v::MutableFixedVector{N,T}, ::Val{K}) where {N, T <: HWType, K}
    vec_circshift!(pointer(v), Val(N), Val(K))
    v
end

@inline @generated function vec_circshift!(ptr::Ptr{T}, ::Val{N}, ::Val{K}) where {N, T <: HWType, K}
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
Methods for other types must be defined explicitly, see the examples below.

See also `Base.isbitstype`.

# Examples

We start by defining a default value for an immutable struct.
```jldoctest default
julia> import $(@__MODULE__): default

julia> struct A x::Int end

julia> default(::Type{A}) = A(0);
```
For a mutable struct one needs to create an object first.
```jldoctest default
julia> mutable struct B x::Int end

julia> const b0 = B(0);

julia> default(::Type{B}) = b0;
```
For mutable parametric types one can use a generated function.
```jldoctest default
julia> mutable struct C{T} x::T end

julia> @generated default(::Type{C{T}}) where T = C(default(T));

julia> default(C{Bool})
C{Bool}(false)

julia> default(C{Bool}) === default(C{Bool})  # do we always get the same object?
true
```
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

The inverse operation can be done with `convert`.

See also
[`Base.convert`](@ref convert(::Type{V}, ::Unsigned) where {N, T <: Union{Bool, Base.BitInteger, Char, Enum}, V <: AbstractFixedVector{N,T}}),
[`$(@__MODULE__).bitsize`](@ref), `Base.BitInteger`, `Base.reinterpret`, `BitIntegers`.

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

"""
    convert(::Type{V}, x::Unsigned) where {N, T <: Union{Base.BitInteger, Bool, Char, Enum}, V <: AbstractFixedVector{N,T}}

Convert the unsigned integer `x` to a `FixedVector{N,T}` or `MutableFixedVector{N,T}`.
The bits of `x` are split into groups of size `bitsize(T)` and reinterpreted as elements of type `T`.
Unused bits are ignored and missing bits are taken as `0`. This is the inverse operation to `bits`.

See also [`bits`](@ref bits(::AbstractFixedVector)), [`$(@__MODULE__).bitsize`](@ref),
`Base.BitInteger`, `BitIntegers`.

# Examples
```jldoctest
julia> v = convert(FixedVector{4,Int8}, 0x030201)
4-element FixedVector{4, Int8}:
 1
 2
 3
 0

julia> bits(v)
0x00030201

julia> convert(FixedVector{6,Bool}, 0xf0)
6-element FixedVector{6, Bool}:
 0
 0
 0
 0
 1
 1

julia> x = FixedVector{2,Char}('a':'b') |> bits
0x6200000061000000

julia> convert(FixedVector{2,Char}, x)
2-element FixedVector{2, Char}:
 'a': ASCII/Unicode U+0061 (category Ll: Letter, lowercase)
 'b': ASCII/Unicode U+0062 (category Ll: Letter, lowercase)

julia> using BitIntegers

julia> convert(FixedVector{4,Int64}, uint256"0x300000000000000020000000000000001")
4-element FixedVector{4, Int64}:
 1
 2
 3
 0
```
"""
convert(::Type{V}, ::Unsigned) where {N, T <: Union{Bool, Base.BitInteger, Char, Enum}, V <: AbstractFixedVector{N,T}}

@generated function convert(::Type{V}, x::U) where {N, T <: Union{BitInteger, Char, Enum}, V <: AbstractFixedVector{N,T}, U <: Unsigned}
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
        V(unvec(v))
    end
end

@generated function convert(::Type{V}, x::U) where {N, V <: AbstractFixedVector{N,Bool}, U <: Unsigned}
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
        V(unvec(v))
    end
end
