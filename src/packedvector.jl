#
# PackedVector
#

import Base: ==, getindex, setindex, length, size, empty, iterate, rest, split_rest,
    iszero, zero, +, -, *, convert, circshift

export PackedVector, bits

"""
    PackedVector{U<:Unsigned,M,T<:Union{Base.BitInteger,Bool}} <: AbstractCapacityVector{T}

    PackedVector{U,M,T}()
    PackedVector{U,M,T}(iter)
    PackedVector{U,M}(v::AbstractVector{T})
    PackedVector{U,M}(t::Tuple)
    PackedVector(v::AbstractSmallVector{M,T})

This type of immutable vector stores the elements in a common bit mask of type `U`
with `M` bits for each entry. The range of allowed values is `-2^(M-1):2^(M-1)-1`
if `T <: Signed`, `0:2^M-1` if `T <: Unsigned` and `false:true` if `T == Bool`.
Apart from that, the official element type `T` is only used when retrieving an entry.
 The capacity, that is, the number of elements that can be stored, is given
by `bitsize(U)÷M`.

The element type `T` can be omitted when creating the `PackedVector` from an `AbstractVector`
or from a tuple. In the latter case, `T` is determined by promoting the element types of the tuple.
If no argument is given, then an empty vector is returned.
If the `PackedVector` is created from a `AbstractSmallVector` `v` and the parameters `U` and `M`
are omitted, then `M` is set to `bitsize(T)` and `U` is chosen such that the capacity
of the resulting vector is at least the capacity of `v`.

Overflow or underflow during addition or subtraction of vectors do not throw an error.
The same applies to multiplication by a scalar of type `T`. Scalar multiplication by
other types returns a `Vector`.

Compared to a `SmallVector`, a `PackedVector` may have faster insert and delete operations.
Arithmetic operations are usually slower unless `M` is the size of a hardware integer.

See also [`capacity`](@ref capacity(::Type{<:PackedVector})), [`$(@__MODULE__).bitsize`](@ref).

# Examples
```jldoctest
julia> v = PackedVector{UInt64,5,Int8}(-5:5:10)
4-element PackedVector{UInt64, 5, Int8}:
 -5
  0
  5
 10

julia> capacity(v)
12

julia> w = PackedVector{UInt64,5,Int8}([1, 2, 3, 4])
4-element PackedVector{UInt64, 5, Int8}:
 1
 2
 3
 4

julia> v+w
4-element PackedVector{UInt64, 5, Int8}:
 -4
  2
  8
 14

julia> Int8(2)*v
4-element PackedVector{UInt64, 5, Int8}:
 -10
   0
  10
 -12
```
"""
struct PackedVector{U<:Unsigned,M,T<:Union{BitInteger,Bool}} <: AbstractCapacityVector{T}
    m::U
    n::Int
    function PackedVector{U,M,T}(m::U, n::Int) where {U <: Unsigned, M, T <: Union{BitInteger,Bool}}
        bitsize(T) < M && error("type $T has fewer than $M bits")
        new{U,M,T}(m, n)
    end
end

PackedVector{U,M,T}(v::PackedVector{U,M,T}) where {U,M,T} = v

@inline function PackedVector{U,M,T}(w::Union{AbstractVector,Tuple}) where {U,M,T}
    v = PackedVector{U,M,T}()
    @boundscheck if !isempty(w)
        checklength(v, length(w))
        x, y = extrema(w)
        checkvalue(M, convert(T, x))
        checkvalue(M, convert(T, y))
    end
    for x in Iterators.reverse(w)
        @inbounds v = pushfirst(v, x)
    end
    v
end

@propagate_inbounds function PackedVector{U,M,T}(iter) where {U,M,T}
    v = PackedVector{U,M,T}()
    for x in iter
        v = push(v, x)
    end
    v
end

PackedVector{U,M}(v::AbstractVector{T}) where {U,M,T} = PackedVector{U,M,T}(v)

function PackedVector{U,M}(v::V) where {U, M, V <: Tuple}
    T = promote_type(fieldtypes(V)...)
    PackedVector{U,M,T}(v)
end

@propagate_inbounds function PackedVector{U,M,S}(v::AbstractSmallVector{N,T}) where {U,M,S,N, T <: BitInteger}
    if bitsize(T) == M && (T <: Signed) == (S <: Signed)
        @boundscheck begin
            c = capacity(PackedVector{U,M,S})
            c >= N || length(v) <= c || error("vector cannot have more than $c elements")
        end
        PackedVector{U,M,S}(bits(v.b) % U, length(v))
    else
        invoke(PackedVector{U,M,S}, Tuple{AbstractVector{T}}, v)
    end
end

function PackedVector(v::AbstractSmallVector{N,T}) where {N, T <: BitInteger}
    m = bits(v.b)
    M = bitsize(T)
    U = typeof(m)
    PackedVector{U,M,T}(v)
end

(::Type{V})() where V <: PackedVector = zeros(V, 0)

"""
    bits(v::PackedVector{U}) where U -> U

Return the bit mask used internally to store the elements of the vector `v`.
"""
bits(v::PackedVector) = v.m

length(v::PackedVector) = v.n

size(v::PackedVector) = (length(v),)

capacity(::Type{<:PackedVector{U,M}}) where {U,M} = bitsize(U) ÷ M

==(v::PackedVector{U,M,T}, w::PackedVector{U,M,T}) where {U,M,T} =
    v.n == w.n && v.m == w.m

"""
    fasthash(v::PackedVector [, h0::UInt]) -> UInt

Return a hash for `v` that may be computed faster than the standard `hash`
for vectors. This new hash is consistent across all `PackedVector{U,M,T}`
of the same internal bit size `M`, but it may not be compatible with `hash`
or with `fasthash` for a `PackedVector` having a different bit size.
However, using `fasthash` for two `PackedVector`s with the same `M`, but
both signed and unsigned element types `T` may lead to hash collisions.

See also [`fasthash(::AbstractSmallVector, ::UInt)`](@ref), `Base.hash`.

# Examples
```jldoctest
julia> v = PackedVector{UInt64,5,Int8}([1, 5, 6]);

julia> fasthash(v)
0x11e89b9d8f3daac6

julia> fasthash(v) == hash(v)
false

julia> w = PackedVector{UInt128,5,Int8}(v); fasthash(v) == fasthash(w)
true

julia> w = PackedVector{UInt64,4,Int8}(v); fasthash(v) == fasthash(w)
false

julia> w = PackedVector{UInt64,5,UInt8}(v); fasthash(v) == fasthash(w)
true
```
"""
fasthash(v::PackedVector, h0::UInt) = Base.hash_integer(bits(v), hash(length(v), h0))

"""
    empty(v::PackedVector{U,M}, S::Type) where {U,M,S} -> PackedVector{U,M,S}

Return an empty `PackedVector` with the same bit mask type and same bit size as `v`,
but element type `S`.

See also [`empty(v::AbstractCapacityVector)`](@ref).
"""
empty(v::PackedVector, ::Type)

empty(v::PackedVector{U,M,T}, ::Type{S} = T) where {U,M,T,S} = PackedVector{U,M,S}()

iszero(v::PackedVector) = iszero(v.m)

zero(v::V) where V <: PackedVector = zeros(V, length(v))

function zeros(::Type{V}, n::Integer) where {U, V <: PackedVector{U}}
    n <= capacity(V) || error("vector cannot have more than $(capacity(V)) elements")
    V(zero(U), n)
end

Base.@assume_effects :total all_ones(::Type{U}, M) where U =
    foldl((m, i) -> m | unsafe_shl(one(U), i), 0:M:bitsize(U)-1; init = zero(U))

function ones(::Type{V}, n::Integer) where {U, M, V <: PackedVector{U,M}}
    n <= capacity(V) || error("vector cannot have more than $(capacity(V)) elements")
    mask = M*n == bitsize(U) ? ~zero(U) : unsafe_shl(one(U), M*n) - one(U)
# TODO: same test elsewhere!!! should be OK
    m = all_ones(U, M) & mask
    V(m, n)
end

function iterate(v::PackedVector, w = v)
    if isempty(w)
        nothing
    else
        w, x = popfirst(w)
        x, w
    end
end

rest(v::PackedVector, w = v) = w

if VERSION >= v"1.9"
    @inline function split_rest(v::PackedVector, n::Int, w = v)
        m = length(w)-n
        @boundscheck (n >= 0 && m >= 0) || error("impossible number of elements requested")
        @inbounds w[1:m], w[m+1:end]
    end
end

@inline function checkvalue(M, x::T) where T
    bitsize(T) == M && return
    if T <: Signed
        -one(T) << (M-1) <= x < one(T) << (M-1) || error("value $x out of range for $M bits signed integer")
    else
        x < one(T) << M || error("value $x out of range for $M bits unsigned integer")
    end
    nothing
end

function checklength(v::PackedVector, m = 1)
    c = capacity(v)
    length(v) <= c-m || error("vector cannot have more than $c elements")
    nothing
end

# TODO: can we omit the conversion to U?
@inline maskvalue(::Type{U}, M, x::Union{Unsigned,Bool}) where U = x % U

@inline function maskvalue(::Type{U}, M, x::T) where {U, T <: Signed}
    mask = one(T) << M - one(T)
    unsigned(x & mask) % U
end

@inline function getindex(v::PackedVector{U,M,T}, i::Int) where {U,M,T}
    @boundscheck checkbounds(v, i)
    x = unsafe_lshr(v.m, M*(i-1)) % T
    mask = one(T) << M - one(T)
    signbit = one(T) << (M-1)
    if T == Bool
        x
    elseif T <: Unsigned || iszero(x & signbit)
        x & mask
    else
        x | ~mask
    end
end

@inline function getindex(v::V, r::AbstractUnitRange{<:Integer}) where {U <: Unsigned, M, V <: PackedVector{U,M}}
    @boundscheck checkbounds(v, r)
    l = length(r)
    l == capacity(v) && return v
    mask = unsafe_shl(one(U), M*l) - one(U)
    m = unsafe_lshr(v.m, M*(first(r)-1)) & mask
    V(m, l)
end

@inline function getindex(v::V, ii::AbstractVector{<:Integer}) where V <: PackedVector
    @boundscheck begin
        c = capacity(v)
        length(ii) <= c || error("vector cannot have more than $c elements")
        checkbounds(v, ii)
    end
    @inbounds V(@inbounds(v[i]) for i in ii)
end

"""
    getindex(v::V, s::SmallBitSet) where V <: PackedVector -> V

Returns the vector with elements `v[i]` where `i` runs through the elements of `s` in increasing order.
This is the same as `v[collect(s)]`, but faster.

# Example
```jldoctest
julia> v = PackedVector{UInt64,6,Int8}(-2:2)
5-element PackedVector{UInt64, 6, Int8}:
 -2
 -1
  0
  1
  2

julia> s = SmallBitSet((1, 3, 4))
SmallBitSet{UInt64} with 3 elements:
  1
  3
  4

julia> v[s]
3-element PackedVector{UInt64, 6, Int8}:
 -2
  0
  1
```
"""
getindex(v::PackedVector, s::SmallBitSet)

@inline function getindex(v::V, s::SmallBitSet{U}) where {W, M, V <: PackedVector{W, M}, U}
    @boundscheck isempty(s) || checkbounds(v, last(s))
    if HAS_PEXT && M == 1 && bitsize(U) < bitsize(UInt)
        m = pext(v.m, bits(s))
        V(m % W, length(s))
    else
        V(@inbounds v[i] for i in s)
    end
end

@inline function setindex(v::PackedVector{U,M,T}, x, i::Integer) where {U,M,T}
    x = convert(T, x)
    @boundscheck begin
        checkbounds(v, i)
        checkvalue(M, x)
    end
    s = M*(i-1)
    mask = one(U) << M - one(U)
    y = maskvalue(U, M, x)
    m = (v.m & ~unsafe_shl(mask, s)) | unsafe_shl(y, s)
    PackedVector{U,M,T}(m, v.n)
end

@inline function insert(v::PackedVector{U,M,T}, i::Integer, x) where {U,M,T}
    x = convert(T, x)
    @boundscheck begin
        isone(i) || checkbounds(v, i-1)
        checklength(v)
        checkvalue(M, x)
    end
    s = M*(i-1)
    mask = unsafe_shl(one(U), s) - one(U)
    m1 = v.m & mask
    m2 = (v.m & ~mask) << M
    y = maskvalue(U, M, x)
    m = m1 | m2 | unsafe_shl(y, s)
    PackedVector{U,M,T}(m, v.n+1)
end

@inline function deleteat(v::PackedVector{U,M,T}, i::Integer) where {U,M,T}
    @boundscheck checkbounds(v, i)
    s = M*(i-1)
    mask = unsafe_shl(one(U), s) - one(U)
    m1 = v.m >> M & ~mask
    m2 = v.m & mask
    PackedVector{U,M,T}(m1 | m2, v.n-1)
end

@propagate_inbounds popat(v::PackedVector, i::Integer) =
    deleteat(v, i), @inbounds v[i]

@propagate_inbounds push(v::PackedVector, xs...) = append(v, xs)

# TODO: needed?
@inline function push(v::PackedVector{U,M,T}, x) where {U,M,T}
    x = convert(T, x)
    @boundscheck begin
        checklength(v)
        checkvalue(M, x)
    end
    s = M*v.n
    y = maskvalue(U, M, x)
    m = v.m | unsafe_shl(y, s)
    PackedVector{U,M,T}(m, v.n+1)
end

@inline function pop(v::PackedVector{U,M,T}) where {U,M,T}
    @boundscheck checkbounds(v, 1)
    s = M*(v.n-1)
    mask = unsafe_shl(one(U), s) - one(U)
    m = v.m & mask
    PackedVector{U,M,T}(m, v.n-1), @inbounds v[v.n]
end

pushfirst(v::PackedVector) = v

@inline function pushfirst(v::PackedVector{U,M,T}, x) where {U <: Unsigned, M, T <: Union{BitInteger,Bool}}
    x = convert(T, x)
    @boundscheck begin
        checklength(v)
        checkvalue(M, x)
    end
    y = maskvalue(U, M, x)
    m = v.m << M | y
    PackedVector{U,M,T}(m, v.n+1)
end

@propagate_inbounds pushfirst(v::PackedVector, xs...) = prepend(v, xs)

@inline function popfirst(v::PackedVector{U,M,T}) where {U,M,T}
    @boundscheck checkbounds(v, 1)
    PackedVector{U,M,T}(v.m >> M, v.n-1), @inbounds v[1]
end

append(v::PackedVector, ws...) = foldl(append, ws; init = v)

@propagate_inbounds append(v::V, w) where V <: PackedVector = append(v, V(w))

@inline function append(v::PackedVector{U,M,T}, w::PackedVector{W,M,T}) where {U <: Unsigned, M, T <: Union{BitInteger,Bool}, W}
    isempty(w) && return v   # otherwise we cannot use unsafe_shl
    @boundscheck checklength(v, w.n)
    m = v.m | unsafe_shl(w.m % U, M*v.n)
    PackedVector{U,M,T}(m, v.n+w.n)
end

prepend(v::PackedVector, ws...) = foldr((w, v) -> prepend(v, w), ws; init = v)

@propagate_inbounds prepend(v::V, w) where V <: PackedVector = append(V(w), v)

@inline function duplicate(v::PackedVector{U,M,T}, i::Integer) where {U,M,T}
    @boundscheck begin
        checkbounds(v, i)
        checklength(v)
    end
    mask = unsafe_shl(one(U), M*i) - one(U)
    m1 = v.m & mask
    m2 = (v.m & ~(mask >>> M)) << M
    PackedVector{U,M,T}(m1 | m2, v.n+1)
end

function circshift(v::PackedVector{U,M,T}, k::Integer) where {U,M,T}
    v.n <= 1 && return v
    k = mod(k+v.n, v.n)  # k+v.n because mod seems to be faster for positive args
    mask = one(U) << ((M*v.n) % UInt) - one(U)
    PackedVector{U,M,T}((unsafe_shl(v.m, M*k) | unsafe_lshr(v.m, M*v.n-M*k)) & mask, v.n)
end

@generated function bitcast_add(v::PackedVector{U,M,T}, w::PackedVector{U,M,T}) where {U,M,T}
    b = bitsize(U)
    n = b ÷ M
    c = n * M
    ir = c == b ? """
        %a2 = bitcast i$c %0 to <$n x i$M>
        %b2 = bitcast i$c %1 to <$n x i$M>
        %c2 = add <$n x i$M> %a2, %b2
        %c1 = bitcast <$n x i$M> %c2 to i$c
        ret i$b %c1
    """ : """
        %a1 = trunc i$b %0 to i$c
        %a2 = bitcast i$c %a1 to <$n x i$M>
        %b1 = trunc i$b %1 to i$c
        %b2 = bitcast i$c %b1 to <$n x i$M>
        %c2 = add <$n x i$M> %a2, %b2
        %c1 = bitcast <$n x i$M> %c2 to i$c
        %c0 = zext i$c %c1 to i$b
        ret i$b %c0
    """
    quote
        $(Expr(:meta, :inline))
        m = Base.llvmcall($ir, U, Tuple{U, U}, v.m, w.m)
        PackedVector{U,M,T}(m, v.n)
    end
end

@generated function bitcast_sub(v::PackedVector{U,M,T}, w::PackedVector{U,M,T}) where {U,M,T}
    b = bitsize(U)
    n = b ÷ M
    c = n * M
    ir = c == b ? """
        %a2 = bitcast i$c %0 to <$n x i$M>
        %b2 = bitcast i$c %1 to <$n x i$M>
        %c2 = sub <$n x i$M> %a2, %b2
        %c1 = bitcast <$n x i$M> %c2 to i$c
        ret i$b %c1
    """ : """
        %a1 = trunc i$b %0 to i$c
        %a2 = bitcast i$c %a1 to <$n x i$M>
        %b1 = trunc i$b %1 to i$c
        %b2 = bitcast i$c %b1 to <$n x i$M>
        %c2 = sub <$n x i$M> %a2, %b2
        %c1 = bitcast <$n x i$M> %c2 to i$c
        %c0 = zext i$c %c1 to i$b
        ret i$b %c0
    """
    quote
        $(Expr(:meta, :inline))
        m = Base.llvmcall($ir, U, Tuple{U, U}, v.m, w.m)
        PackedVector{U,M,T}(m, v.n)
    end
end

@generated function bitcast_mul(c::T, v::PackedVector{U,M,T}) where {U,M,T}
    b = bitsize(U)
    n = b ÷ M
    (bitsize(T) == M && n*M == b) || error("not implemented")
    ir = """
        %a = bitcast i$b %1 to <$n x i$M>
        %b1 = insertelement <$n x i$M> poison, i$M %0, i32 0
        %b2 = shufflevector <$n x i$M> %b1, <$n x i$M> poison, <$n x i32> zeroinitializer
        %c2 = mul <$n x i$M> %a, %b2
        %c1 = bitcast <$n x i$M> %c2 to i$b
        ret i$b %c1
    """
    quote
        $(Expr(:meta, :inline))
        m = Base.llvmcall($ir, U, Tuple{T, U}, c, v.m)
        PackedVector{U,M,T}(m, v.n)
    end
end

+(v::PackedVector) = v

@inline function +(v::V, w::V) where {U, M, V <: PackedVector{U,M}}
    @boundscheck length(v) == length(w) || error("vectors must have the same length")
    M >= 8 && ispow2(M) && return bitcast_add(v, w)
    mask = one(U) << M - one(U)
    ones0 = all_ones(U, 2*M)
    ones1 = ones0 << M
    mask0 = mask*ones0
    mask1 = mask*ones1
    m0 = (v.m & mask0 + w.m & mask0) & mask0
    m1 = (v.m & mask1 + w.m & mask1) & mask1
    V(m0 | m1, v.n)
end

@inline function +(v::V, w::V) where {U, V <: PackedVector{U,1,<:BitInteger}}
    @boundscheck length(v) == length(w) || error("vectors must have the same length")
    V(v.m ⊻ w.m, v.n)
end

-(v::PackedVector) = @inbounds zero(v)-v

@inline function -(v::V, w::V) where {U, M, V <: PackedVector{U,M}}
    @boundscheck length(v) == length(w) || error("vectors must have the same length")
    M >= 8 && ispow2(M) && return bitcast_sub(v, w)
    mask = one(U) << M - one(U)
    ones0 = all_ones(U, 2*M)
    ones1 = ones0 << M
    mask0 = mask*ones0
    mask1 = mask*ones1
    wc = ~w.m
    m0 = (v.m & mask0 + wc & mask0 + ones0) & mask0
    m1 = (v.m & mask1 + wc & mask1 + ones1) & mask1
    V(m0 | m1, v.n)
end

-(vs::V...) where {U, V <: PackedVector{U,1,<:BitInteger}} = +(vs...)

@inline function *(c::T, v::PackedVector{U,M,T}) where {U, M, T <: BitInteger}
    @boundscheck checkvalue(M, c)
    bitsize(T) == M && return bitcast_mul(c, v)
    mask = one(U) << M - one(U)
    ones0 = all_ones(U, 2*M)
    ones1 = ones0 << M
    mask0 = mask*ones0
    mask1 = mask*ones1
    cm = maskvalue(U, M, c)
    m0 = (cm * (v.m & mask0)) & mask0
    m1 = (cm * (v.m & mask1)) & mask1
    PackedVector{U,M,T}(m0 | m1, v.n)
end

*(c::T, v::PackedVector{U,1,T}) where {U, T <: BitInteger} = isodd(c) ? v : zero(v)

*(v::PackedVector{U,M,T}, c::T) where {U, M, T <: BitInteger} = c*v

"""
    $(@__MODULE__).unsafe_add(v::V, w::V) where V <: PackedVector -> V

Add `v` and `w` and return the result. It is not checked that `v` and `w` have the same length.
No overflow or underflow is allowed in any component, nor are sign changes in the case of signed integers.

This function is much faster than regular addition.

See also [`unsafe_sub`](@ref).
"""
unsafe_add(v::V, w::V) where V <: PackedVector = V(v.m+w.m, v.n)

"""
    $(@__MODULE__).unsafe_sub(v::V, w::V) where V <: PackedVector -> V

Subtract `w` from `v` and return the result. It is not checked that `v` and `w` have the same length.
No overflow or underflow  is allowed in any component, nor are sign changes in the case of signed integers.

This function is much faster than regular addition.

See also [`unsafe_add`](@ref).
"""
unsafe_sub(v::V, w::V) where V <: PackedVector = V(v.m-w.m, v.n)

@generated function sum_split(v::PackedVector{U,M,T}) where {U,M,T}
    @assert M > 1
    c = capacity(v)
    l = top_set_bit(c-1)
    quote
        m = v.m
        Base.Cartesian.@nexprs $l i -> begin
            n = M*2^(i-1)
            ones2 = all_ones(U, 2*n)
            mask = one(U) << n - one(U)
            mask2 = mask * ones2
            m1 = m & mask2
            if T <: Signed && isodd($c >> (i-1))
                m2 = unsigned((signed(m) >> n)) & mask2
            else
                m2 = (m >> n) & mask2
            end
            if T <: Signed
                signmask = ones2 << (M-1 + i-1)
                m1 |= (m1 & signmask) << 1
                m2 |= (m2 & signmask) << 1
            end
            m = m1 + m2
            if T <: Signed
                m &= ~(signmask << 2)
            end
        end
        if bitsize(T) > bitsize(Int)
            TT = T
        elseif T <: Signed
            TT = Int
        else
            TT = UInt
        end
        if T <: Unsigned
            m % TT
        else
            k = bitsize(U) - (M+$l)
            (signed(m << k) >> k) % TT
        end
    end
end

function sum_count(v::PackedVector{U,M,T}) where {U,M,T}
    o = all_ones(U, M)
    t = ntuple(Val(M)) do i
        c = count_ones(v.m & (o << (i-1))) << (i-1)
        T <: Signed && i == M ? -c : c
    end
    s = sum(t)
    if bitsize(T) > bitsize(Int)
        s % T
    elseif T <: Union{Signed, Bool}
        s
    else
        unsigned(s)
    end
end

@generated inttype(::Val{M}) where M = Symbol(:Int, M)
@generated uinttype(::Val{M}) where M = Symbol(:UInt, M)

function sum(v::PackedVector{U,M,T}) where {U,M,T}
    if M >= 8 && M <= 64 && ispow2(M)
        S = T <: Signed ? inttype(Val(M)) : uinttype(Val(M))
        w = PackedVector{U,M,S}(v.m, v.n)
        s = sum(SmallVector(w))
        bitsize(T) <= bitsize(s) ? s : s % T
    else
        log2u = top_set_bit(bitsize(U))-1
        if M <= log2u + (T <: Signed ? 1 : -2)
            sum_count(v)
        else
            sum_split(v)
        end
    end
end

function maximum(v::PackedVector{U,M,T}) where {U,M,T}
    if M >= 8 && ispow2(M)
        S = T <: Signed ? inttype(Val(M)) : uinttype(Val(M))
        w = PackedVector{U,M,S}(v.m, v.n)
        maximum(SmallVector(w)) % T
    else
        invoke(maximum, Tuple{AbstractVector{T}}, v)
    end
end

function minimum(v::PackedVector{U,M,T}) where {U,M,T}
    if M >= 8 && ispow2(M)
        S = T <: Signed ? inttype(Val(M)) : uinttype(Val(M))
        w = PackedVector{U,M,S}(v.m, v.n)
        minimum(SmallVector(w)) % T
    else
        invoke(minimum, Tuple{AbstractVector{T}}, v)
    end
end

function support(v::PackedVector{U,M}) where {U,M}
    S = SmallBitSet{UInt}
    capacity(v) <= capacity(S) || length(v) <= capacity(S) ||
        error("$S can only contain integers between 1 and $(capacity(S))")
    mask = one(U) << M - one(U)
    m = zero(UInt)
    b = one(m)
    for i in eachindex(v)
        if !iszero(v.m & mask)
            m |= b
        end
        mask <<= M
        b <<= 1
    end
    convert(S, m)
end

support(v::PackedVector{U,1}) where U = convert(SmallBitSet{UInt}, bits(v))

function Random.rand(rng::AbstractRNG, ::SamplerType{PackedVector{U,M,T}}) where {U,M,T}
    n = rand(0:capacity(PackedVector{U,M,T}))
    mask = one(U) << unsigned(M*n) - one(U)
    PackedVector{U,M,T}(rand(U) & mask, n)
end

#
# conversion to SmallVector
#

@propagate_inbounds function SmallVector{N,T}(v::PackedVector{U,M,S}) where {N,T,U,M,S}
    if bitsize(T) == M && (T <: Signed) == (S <: Signed)
        @boundscheck if N < capacity(PackedVector{U,M,S})
            length(v) <= N || error("vector cannot have more than $N elements")
        end
        b = convert(Values{N,T}, v.m)
        SmallVector{N,T}(b, length(v))
    else
        invoke(SmallVector{N,T}, Tuple{AbstractVector{S}}, v)
    end
end

function SmallVector(v::PackedVector{U,M,T}) where {U,M,T}
    N = capacity(v)
    SmallVector{N,T}(v)
end
