#
# extensions of FixedVector
#

using Base: @assume_effects
import Base: setindex, circshift, circshift!, reverse!, convert

export setindex, unsafe_circshift, unsafe_circshift!

"""
    setindex(v::AbstractFixedVector{N,T}, x, i::Integer) where {N,T} -> FixedVector{N,T}

Substitute `x` for the `i`-th component of `v` and return the result. The vector `v` is not modified.

See also `Base.setindex`,  [`addindex`](@ref addindex(::AbstractFixedVector, ::Any, ::Integer)).
"""
setindex(::AbstractFixedVector, ::Any, ::Integer)

@inline function setindex(v::AbstractFixedVector{N,T}, x, i::Integer) where {N,T}
    @boundscheck checkbounds(v, i)
    if T <: HWType && N-1 <= typemax(uinttype(T))
        setindex_llvm(v, convert(T, x), i)
    else
        i1 = i % SmallLength
        t = ntuple(Val(N % SmallLength)) do j
            j == i1 ? convert(T, x) : v[j]
        end
        FixedVector{N,T}(t)
    end
end

@generated function setindex_llvm(v::AbstractFixedVector{N,T}, x::T, i::Integer) where {N,T}
    L = llvm_type(T)
    U = uinttype(T)
    LU = llvm_type(U)
    w = join((string(LU, ' ', k) for k in 1:N), ", ")
    ir = """
        %x0 = insertelement <$N x $L> poison, $L %1, i8 0
        %xv = shufflevector <$N x $L> %x0, <$N x $L> poison, <$N x i32> zeroinitializer
        %i0 = insertelement <$N x $LU> poison, $LU %2, i8 0
        %iv = shufflevector <$N x $LU> %i0, <$N x $LU> poison, <$N x i32> zeroinitializer
        %f  = icmp eq <$N x $LU> <$w>, %iv
        %c  = select <$N x i1> %f, <$N x $L> %xv, <$N x $L> %0
        ret <$N x $L> %c
    """
    quote
        b = Base.llvmcall($ir, NTuple{N, VecElement{T}}, Tuple{NTuple{N, VecElement{T}}, T, $U}, vec(v.t), x, i % $U)
        FixedVector(unvec(b))
    end
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
    t = ntuple(Val(N % SmallLength)) do j
        ifelse(j <= i, v[j], convert(T, x))
    end
    FixedVector{N,T}(t)
end

@generated function padtail(v::FixedVector{N,T}, n::Integer) where {N, T <: HWType}
    M = llvm_type(T)
    L = 8*sizeof(T)
    if log2(N) >= L
        L = bitsize(SmallLength)
    end
    U = Symbol(:UInt, L)
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
        b = Base.llvmcall($ir, NTuple{N, VecElement{T}}, Tuple{NTuple{N, VecElement{T}}, $U}, vec(Tuple(v)), n % $U)
        FixedVector{N,T}(unvec(b))
    end
end

"""
    fixedvector_range(::Val{N}, n::Integer, b::T) where {N,T}
    fixedvector_range(::Val{N}, n::Integer, b::T, m::Integer, a::T) where {N,T}

In the first form, returns a `FixedVector{N,T}` whose first `n` elements are `b:b+n-1` and the others `0`.

In the second form, the first `m` elements are replaced by `a:a+m-1`.
If `m` is larger than `n` (modulo `unsigned(T)`), then this is the same as `fixedvector_range(Val(N), m, a)`.

# Examples
```jldoctest
julia> using $(@__MODULE__): fixedvector_range

julia> fixedvector_range(Val(4), 3, Int8(5))
4-element FixedVector{4, Int8}:
 5
 6
 7
 0

julia> fixedvector_range(Val(4), 3, Int8(5), 2, Int8(-4))
4-element FixedVector{4, Int8}:
 -4
 -3
  7
  0

julia> fixedvector_range(Val(4), 3, Int8(5), 4, Int8(-4))
4-element FixedVector{4, Int8}:
 -4
 -3
 -2
 -1
```
"""
@generated function fixedvector_range(::Val{N}, n::Integer, b::T, m::Integer = 0, a::T = zero(T)) where {N,T}
    L = string('i', bitsize(T))
    w = join((string(L, ' ', i) for i in 0:N-1), ", ")
    ir = """
        %n0 = insertelement <$N x $L> poison, $L %0, i8 0
        %nv = shufflevector <$N x $L> %n0, <$N x $L> poison, <$N x i32> zeroinitializer
        %fn = icmp ult <$N x $L> <$w>, %nv

        %m0 = insertelement <$N x $L> poison, $L %2, i8 0
        %mv = shufflevector <$N x $L> %m0, <$N x $L> poison, <$N x i32> zeroinitializer
        %fm = icmp ult <$N x $L> <$w>, %mv

        %b0 = insertelement <$N x $L> poison, $L %1, i8 0
        %b1 = shufflevector <$N x $L> %b0, <$N x $L> poison, <$N x i32> zeroinitializer
        %b2 = add <$N x $L> <$w>, %b1
        %b3 = select <$N x i1> %fn, <$N x $L> %b2, <$N x $L> zeroinitializer
        %b  = select <$N x i1> %fm, <$N x $L> zeroinitializer, <$N x $L> %b3

        %a0 = insertelement <$N x $L> poison, $L %3, i8 0
        %a1 = shufflevector <$N x $L> %a0, <$N x $L> poison, <$N x i32> zeroinitializer
        %a2 = add <$N x $L> <$w>, %a1
        %a  = select <$N x i1> %fm, <$N x $L> %a2, <$N x $L> zeroinitializer

        %c  = xor <$N x $L> %b, %a
        ret <$N x $L> %c
    """
    quote
        U = unsigned(T)
        @assert N <= typemax(U)
        b = Base.llvmcall($ir, NTuple{N, VecElement{T}}, Tuple{U,T,U,T}, n % U, b, m % U, a)
        FixedVector(unvec(b))
    end
end

pushfirst(v::FixedVector, xs...) = prepend(v, xs)

function prepend(v::FixedVector{N,T}, w::Union{AbstractVector,Tuple}) where {N,T}
    n = length(w)
    t = ntuple(Val(N)) do i
        @inbounds i <= n ? convert(T, w[i]) : v[i-n]
    end
    FixedVector{N,T}(t)
end

function popfirst(v::FixedVector{N,T}) where {N,T}
    M = shufflewidth(v)
    if M != 0
        P = inttype(T)
        p = ntuple(Val(N % P)) do i
            i < N ? i : -one(P)
        end
        shuffle(Val(M), v, p), v[1]
    else
        @inbounds popat(v, 1)
    end
end

@inline function insert(v::FixedVector{N,T}, i::Integer, x) where {N,T}
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

@inline function duplicate(v::FixedVector{N,T}, i::Integer) where {N,T}
    @static if v"1.12" <= VERSION < v"1.13-" && Sys.ARCH == :x86_64
        # @inbounds leads to bug, similar to julia#59203
        checkbounds(v, i)
    else
        @boundscheck checkbounds(v, i)
    end
    t = if T <: HWType
        NN = smallint(N)
        ii = i % typeof(NN)
        c = circshift(v, 1)
        ntuple(Val(NN)) do j
            j <= ii ? v[j] : c[j]
        end
    else
        ntuple(Val(N)) do j
            j <= i ? v[j] : v[j-1]
        end
    end
    FixedVector{N,T}(t)
end

@propagate_inbounds deleteat(v::FixedVector, i::Integer) = first(popat(v, i))

@inline function popat(v::FixedVector{N,T}, i::Integer) where {N,T}
    @boundscheck checkbounds(v, i)
    M = shufflewidth(v)
    if M != 0
        P = inttype(T)
        ii = i % P
        w = first(@inline popfirst(v))
        t = ntuple(Val(N % P)) do j
            j < ii ? v[j] : w[j]
        end
    else
        t = ntuple(Val(N)) do j
            if j < i
                v[j]
            elseif j < N
                v[j+1]
            else
                default(T)
            end
        end
    end
    FixedVector{N,T}(t),
    @static if v"1.11" <= VERSION < v"1.13-" && Sys.ARCH == :x86_64
        # @inbounds leads to bug (with 1.12 not just for floats), see julia#59203
        v[i]
    else
        @inbounds v[i]
    end
end

"""
    circshift(v::AbstractFixedVector{N,T}, k::Integer) where {N,T} -> FixedVector{N,T}
    circshift(v::AbstractFixedVector{N,T}, ::Val{k}) where {N,T,k} -> FixedVector{N,T}

Rotate `v` by `k` positions towards higher indices and return the result.
A negative value of `k` corresponds to a rotation towards lower indices.

See also [`circshift!`](@ref circshift!(::MutableFixedVector, ::Union{Integer,Val})).

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

"""
    unsafe_circshift(v::AbstractFixedVector{N,T}, k::Integer) where {N,T} -> FixedVector{N,T}
    unsafe_circshift!(v::MutableFixedVector, k::Integer) -> v

These are faster versions of `circshift` and `circshift!`. They assume `-N ≤ k < N`.
This avoids the comparatively costly integer division with remainder.

See also [`circshift`](@ref circshift(::AbstractFixedVector, ::Union{Integer,Val})),
[`circshift!`](@ref circshift!(::MutableFixedVector, ::Union{Integer,Val})).
"""
unsafe_circshift(::AbstractFixedVector, ::Integer),
unsafe_circshift!(::MutableFixedVector, ::Integer)

@inline function unsafe_circshift(v::AbstractFixedVector{N,T}, k::Integer) where {N,T}
    M = shufflewidth(v)
    if N == 1
        FixedVector{N,T}(v)
    elseif T <: HWType && ispow2(N) && 8 <= bitsize(T)*N <= 64
        convert(FixedVector{N,T}, bitrotate(bits(v), bitsize(T)*k))
    elseif M != 0
        P = inttype(T)
        k1 = ifelse(signbit(k), (k%P)+P(N), k%P)
        p = ntuple(Val(N % P)) do i
            i-k1 + (i > k1 ? -P(1) : P(N)-P(1))
        end
        shuffle(Val(M), fixedvector(v), p)
    else
        t = ntuple(Val(N % SmallLength)) do i
            k2 = ifelse(signbit(k), k+N, k) % SmallLength
            @inbounds if i <= k2
                v[(i-k2)+N]
            else
                v[i-k2]
            end
        end
        FixedVector{N,T}(t)
    end
end

@inline function circshift(v::AbstractFixedVector{N,T}, k::Integer) where {N,T}
    if N == 1
        FixedVector{N,T}(v)
    elseif T <: HWType && ispow2(N) && 8 <= bitsize(T)*N <= 128  # for Bool one could go up to 512 bits
        convert(FixedVector{N,T}, bitrotate(bits(v), bitsize(T)*k))
    else
        unsafe_circshift(v, unsafe_rem(k, UInt16(N)))
    end
end

circshift(v::AbstractFixedVector, ::Val{k}) where k = circshift(v, k)

@generated function circshift(v::MutableFixedVector{N,T}, ::Val{K}) where {N , T <: HWType, K}
    M = llvm_type(T)
    b = sizeof(T)
    s = join(("i32 " * string(mod(i-K, N)) for i in 0:N-1), ", ")
    ir = VERSION > v"1.12-" ? """
        %a = load <$N x $M>, ptr %0, align $b
        %b = shufflevector <$N x $M> %a, <$N x $M> poison, <$N x i32> <$s>
        ret <$N x $M> %b
    """ : """
        %p = inttoptr i64 %0 to <$N x $M>*
        %a = load <$N x $M>, <$N x $M>* %p, align $b
        %b = shufflevector <$N x $M> %a, <$N x $M> poison, <$N x i32> <$s>
        ret <$N x $M> %b
    """
    quote
        b = Base.llvmcall($ir, NTuple{N,VecElement{T}}, Tuple{Ptr{T}}, pointer(v))
        FixedVector{N,T}(unvec(b))
    end
end

"""
    circshift!(v::MutableFixedVector, k::Integer) -> v
    circshift!(v::MutableFixedVector, ::Val{k}) where k -> v

Rotate `v` in-place by `k` positions towards higher indices and return `v`.
A negative value of `k` corresponds to a rotation towards lower indices.

See also [`circshift`](@ref circshift(::AbstractFixedVector, ::Union{Integer,Val})).

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

@inline function unsafe_circshift!(v::MutableFixedVector, k::Integer)
    v .= unsafe_circshift(v, k)
end

@inline function circshift!(v::MutableFixedVector, k::Integer)
    v .= circshift(v, k)
end

circshift!(v::MutableFixedVector, ::Val{k}) where k = circshift!(v, k)

function circshift!(v::MutableFixedVector{N,T}, ::Val{K}) where {N, T <: HWType, K}
    vec_circshift!(pointer(v), Val(N), Val(K))
    v
end

@inline @generated function vec_circshift!(ptr::Ptr{T}, ::Val{N}, ::Val{K}) where {N, T <: HWType, K}
    M = llvm_type(T)
    b = sizeof(T)
    s = join(("i32 " * string(mod(i-K, N)) for i in 0:N-1), ", ")
    ir = VERSION > v"1.12-" ? """
        %a = load <$N x $M>, ptr %0, align $b
        %b = shufflevector <$N x $M> %a, <$N x $M> poison, <$N x i32> <$s>
        store <$N x $M> %b, ptr %0, align $b
        ret void
    """ : """
        %p = inttoptr i64 %0 to <$N x $M>*
        %a = load <$N x $M>, <$N x $M>* %p, align $b
        %b = shufflevector <$N x $M> %a, <$N x $M> poison, <$N x i32> <$s>
        store <$N x $M> %b, <$N x $M>* %p, align $b
        ret void
    """
    quote
        Base.llvmcall($ir, Cvoid, Tuple{Ptr{T}}, ptr)
    end
end

@inline @generated function reverse!(v::MutableFixedVector{N,T}) where {N, T <: HWType}
    M = llvm_type(T)
    b = sizeof(T)
    s = join(("i32 " * string(i) for i in N-1:-1:0), ", ")
    ir = VERSION > v"1.12-" ? """
        %a = load <$N x $M>, ptr %0, align $b
        %b = shufflevector <$N x $M> %a, <$N x $M> poison, <$N x i32> <$s>
        store <$N x $M> %b, ptr %0, align $b
        ret void
    """ : """
        %p = inttoptr i64 %0 to <$N x $M>*
        %a = load <$N x $M>, <$N x $M>* %p, align $b
        %b = shufflevector <$N x $M> %a, <$N x $M> poison, <$N x i32> <$s>
        store <$N x $M> %b, <$N x $M>* %p, align $b
        ret void
    """
    quote
        Base.llvmcall($ir, Cvoid, Tuple{Ptr{T}}, pointer(v))
        v
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

default(::Type{V}) where {N,T,V<:AbstractFixedVector{N,T}} = V(default(NTuple{N,T}))

#
# bit conversions
#

vec(t::NTuple{N}) where N = ntuple(i -> VecElement(t[i]), Val(N))

unvec(t::NTuple{N,VecElement}) where N = ntuple(i -> t[i].value, Val(N))

"""
    bits(v::AbstractFixedVector{N,T}) where {N, T <: $HWTypeExpr} -> Unsigned

Convert the given vector to an unsigned integer.

For bit integers, hardware floats, `Char` and `Enum` types this is the same as `reinterpret(U, Tuple(v))` provided that
`U` is an unsigned integer type with `N*bitsize(T)` bits, possibly defined by the package
`BitIntegers`. Otherwise the result will be zero-extended to the next unsigned integer type `U`
whose bit length is a power of `2`.

If the element type is `Bool`, then each element only takes one bit in the return value.
If `N` is less than `8` or not a power of `2`, then the result will again be zero-extended.

The inverse operation can be done with `convert`.

See also
[`Base.convert`](@ref convert(::Type{V}, ::Unsigned) where {N, T <: HWType, V <: AbstractFixedVector{N,T}}),
[`$(@__MODULE__).bitsize`](@ref), `Base.HWReal`, `Base.reinterpret`, `BitIntegers`.

# Examples
```jldoctest
julia> FixedVector{4,Int8}(1:4) |> bits
0x04030201

julia> FixedVector{3}('a':'c') |> bits
0x00000000630000006200000061000000

julia> m = FixedVector{6,UInt32}(1:6) |> bits
0x0000000000000000000000060000000500000004000000030000000200000001

julia> typeof(m)
BitIntegers.UInt256

julia> FixedVector{22}(map(isodd, 1:22)) |> bits
0x00155555
```
"""
bits(v::AbstractFixedVector)

@generated function bits(v::AbstractFixedVector{N,T}) where {N, T <: HWType}
    M = llvm_type(T)
    b = N*bitsize(T)
    c = nextpow(2, b)
    U = Symbol(:UInt, c)
    if b == c
        ir = """
            %b = bitcast <$N x $M> %0 to i$b
            ret i$b %b
        """
    else
        ir = """
            %b = bitcast <$N x $M> %0 to i$b
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
    z = ntuple(Returns(zero(T)), Val(n-N))
    quote
        t = (Tuple(v)..., $z...)
        reinterpret($U, t)
    end
end

@generated function bits(v::AbstractFixedVector{N,Bool}) where N
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
    convert(::Type{V}, x::Unsigned) where {N, T <: $HWTypeExpr, V <: AbstractFixedVector{N,T}}

Convert the unsigned integer `x` to a `FixedVector{N,T}` or `MutableFixedVector{N,T}`.
The bits of `x` are split into groups of size `bitsize(T)` and reinterpreted as elements of type `T`.
Unused bits are ignored and missing bits are taken as `0`. This is the inverse operation to `bits`.

See also [`bits`](@ref bits(::AbstractFixedVector)), [`$(@__MODULE__).bitsize`](@ref),
`Base.HWReal`, `BitIntegers`.

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
convert(::Type{V}, ::Unsigned) where {N, T <: HWType, V <: AbstractFixedVector{N,T}}

@generated function convert(::Type{V}, x::U) where {N, T <: HWType, V <: AbstractFixedVector{N,T}, U <: Unsigned}
    M = llvm_type(T)
    b = N*bitsize(T)
    c = bitsize(U)
    if b == c
        ir = """
            %b = bitcast i$b %0 to <$N x $M>
            ret <$N x $M> %b
        """
    elseif b > c
        ir = """
            %b = zext i$c %0 to i$b
            %a = bitcast i$b %b to <$N x $M>
            ret <$N x $M> %a
        """
    else
        ir = """
            %b = trunc i$c %0 to i$b
            %a = bitcast i$b %b to <$N x $M>
            ret <$N x $M> %a
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

@generated function compress(v::AbstractFixedVector{N,T}, s::SmallBitSet{U}) where {N, T <: HWType, U}
    L = llvm_type(T)
    NL = llvm_type(N, T)
    M = bitsize(U)
    resize2 = if M == N
        "select i1 1, i$N %2, i$N 0"
    elseif M > N
        "trunc i$M %2 to i$N"
    else # M < N
        "zext i$M %2 to i$N"
    end
    ir = if VERSION > v"1.12-"
        """
        declare void @llvm.masked.compressstore.$NL (<$N x $L>, ptr, <$N x i1>)
        define void @compress(ptr, <$N x $L>, i$M) #0 {
            %a = $resize2
            %b = bitcast i$N %a to <$N x i1>
            call void @llvm.masked.compressstore.$NL(<$N x $L> %1, ptr %0, <$N x i1> %b)
            ret void
        }
        attributes #0 = { alwaysinline }
        """
    else
        """
        declare void @llvm.masked.compressstore.$NL (<$N x $L>, ptr, <$N x i1>)
        define void @compress(i64, <$N x $L>, i$M) #0 {
            %a = $resize2
            %b = bitcast i$N %a to <$N x i1>
            %p = inttoptr i64 %0 to <$N x $L>*
            call void @llvm.masked.compressstore.$NL(<$N x $L> %1, <$N x $L>* %p, <$N x i1> %b)
            ret void
        }
        attributes #0 = { alwaysinline }
        """
    end
    quote
        @inline
        w = default(MutableFixedVector{N,T})
        Base.llvmcall(($ir, "compress"), Cvoid, Tuple{Ptr{T},NTuple{N,VecElement{T}},U}, pointer(w), vec(Tuple(v)), bits(s))
        FixedVector(w)
    end
end
