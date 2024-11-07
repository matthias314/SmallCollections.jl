#
# extensions of FixedVector
#

using Base: BitInteger, @assume_effects
import Base: setindex

export setindex

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
    $(@__MODULE__).default(::Type{T}) where T -> T
    $(@__MODULE__).default(::T) where T -> T

Return the default value of type `T` used for filling unused elements of an `AbstractSmallVector`.
This must be defined as `zero(T)` if `T` supports algebraic operations. Otherwise it can
be any value of type `T`.

This function has methods for number types, bits types, `Symbol`, `AbstractChar`, `AbstractString`,
`AbstractFixedVector`, `AbstractSmallVector` und `SmallBitSet`.
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

default(::Type{V}) where {N,T,V<:TupleVector{N,T}} = V(ntuple(Returns(default(T)), Val(N)))

function padded_add(v::TupleVector{N1,T1}, w::TupleVector{N2,T2}) where {N1,T1,N2,T2}
    T = promote_type(T1, T2)
    N = min(N1, N2)
    Values{N,T}(ntuple(i -> v[i]+w[i], Val(N)))
end

function padded_sub(v::TupleVector{N1,T1}, w::TupleVector{N2,T2}) where {N1,T1,N2,T2}
    T = promote_type(T1, T2)
    N = min(N1, N2)
    Values{N,T}(ntuple(i -> v[i]-w[i], Val(N)))
end

#
# bit conversions
#

vec(t::NTuple{N}) where N = ntuple(i -> VecElement(t[i]), Val(N))

unvec(t::NTuple{N,VecElement}) where N = ntuple(i -> t[i].value, Val(N))

"""
    bits(v::$TupleVector{N,T}) where {N, T <: Union{Base.BitInteger,Bool,Char}} -> Unsigned

Convert the given vector to an unsigned integer.

For bit integers and `Char` this is the same as `reinterpret(U, Tuple(v))` provided that
`U` is an unsigned integer type with `N*bitsize(T)` bits, possibly defined by the package
`BitIntegers`. Otherwise the result will be zero-extended to the next unsigned integer type `U`
whose bit length is a power of `2`.

If the element type is `Bool`, then each element only takes one bit in the return value.
If `N` is less than `8` or not a power of `2`, then the result will again be zero-extended.

See also [`SmallCollections.bitsize`](@ref), `Base.BitInteger`, `Base.reinterpret`, `BitIntegers`.

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

@generated function bits(v::TupleVector{N,T}) where {N, T <: Union{BitInteger,Char}}
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
