#
# PackedVector
#

import Base: ==, getindex, setindex, length, size, empty, iterate, rest,
    iszero, zero, +, -, *, convert

export PackedVector

struct PackedVector{U<:Unsigned,N,T<:Union{BitInteger,Bool}} <: AbstractSmallVector{T}
    m::U
    n::Int
end

PackedVector{U,N,T}(v::PackedVector{U,N,T}) where {U,N,T} = v

@inline function PackedVector{U,N,T}(w::Union{AbstractVector,Tuple}) where {U,N,T}
    v = PackedVector{U,N,T}()
    @boundscheck if !isempty(w)
        checklength(v, length(w))
        x, y = extrema(w)
        checkvalue(N, convert(T, x))
        checkvalue(N, convert(T, y))
    end
    for x in Iterators.reverse(w)
        @inbounds v = pushfirst(v, x)
    end
    v
end

@propagate_inbounds function PackedVector{U,N,T}(iter) where {U,N,T}
    v = PackedVector{U,N,T}()
    for x in iter
        v = push(v, x)
    end
    v
end

PackedVector{U,N}(v::AbstractVector{T}) where {U,N,T} = PackedVector{U,N,T}(v)

function PackedVector{U,N}(v::V) where {U, N, V <: Tuple}
    T = promote_type(fieldtypes(V)...)
    PackedVector{U,N,T}(v)
end

@propagate_inbounds function PackedVector{U,M,S}(v::SmallVector{N,T}) where {U,M,S,N, T <: BitInteger}
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

function PackedVector(v::SmallVector{N,T}) where {N, T <: BitInteger}
    m = bits(v.b)
    M = bitsize(T)
    U = typeof(m)
    PackedVector{U,M,T}(v)
end

(::Type{V})() where V <: PackedVector = zeros(V, 0)

bits(v::PackedVector) = v.m

length(v::PackedVector) = v.n

size(v::PackedVector) = (length(v),)

capacity(::Type{<:PackedVector{U,N}}) where {U,N} = bitsize(U) ÷ N

==(v::PackedVector{U,N,T}, w::PackedVector{U,N,T}) where {U,N,T} =
    v.n == w.n && v.m == w.m

empty(v::PackedVector{U,N,T}, ::Type{S} = T) where {U,N,T,S} = PackedVector{U,N,S}()

iszero(v::PackedVector) = iszero(v.m)

zero(v::V) where V <: PackedVector = zeros(V, length(v))

function zeros(::Type{V}, n::Integer) where {U, V <: PackedVector{U}}
    n <= capacity(V) || error("vector cannot have more than $(capacity(V)) elements")
    V(zero(U), n)
end

Base.@assume_effects :total all_ones(::Type{U}, N) where U =
    foldl((m, i) -> m | unsafe_shl(one(U), i), 0:N:bitsize(U)-1; init = zero(U))

function ones(::Type{V}, n::Integer) where {U, N, V <: PackedVector{U,N}}
    n <= capacity(V) || error("vector cannot have more than $(capacity(V)) elements")
    mask = N*n == bitsize(U) ? ~zero(U) : unsafe_shl(one(U), N*n) - one(U)
# TODO: same test elsewhere!!! should be OK
    m = all_ones(U, N) & mask
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

@inline function checkvalue(N, x::T) where T
    bitsize(T) == N && return
    bitsize(T) < N && error("type $T has fewer than $N bits")
    if T <: Signed
        -one(T) << (N-1) <= x < one(T) << (N-1) || error("value $x out of range for $N bits signed integer")
    else
        x < one(T) << N || error("value $x out of range for $N bits unsigned integer")
    end
    nothing
end

function checklength(v::PackedVector, m = 1)
    c = capacity(v)
    length(v) <= c-m || error("vector cannot have more than $c elements")
    nothing
end

# TODO: can we omit the conversion to U?
@inline maskvalue(::Type{U}, N, x::Union{Unsigned,Bool}) where U = x % U

@inline function maskvalue(::Type{U}, N, x::T) where {U, T <: Signed}
    mask = one(T) << N - one(T)
    unsigned(x & mask) % U
end

@inline function getindex(v::PackedVector{U,N,T}, i::Int) where {U,N,T}
    @boundscheck checkbounds(v, i)
    x = unsafe_lshr(v.m, N*(i-1)) % T
    mask = one(T) << N - one(T)
    signbit = one(T) << (N-1)
    if T == Bool
        x
    elseif T <: Unsigned || iszero(x & signbit)
        x & mask
    else
        x | ~mask
    end
end

@inline function getindex(v::V, r::AbstractUnitRange{<:Integer}) where {U <: Unsigned, N, V <: PackedVector{U,N}}
    @boundscheck checkbounds(v, r)
    l = length(r)
    l == capacity(v) && return v
    mask = unsafe_shl(one(U), N*l) - one(U)
    m = unsafe_lshr(v.m, N*(first(r)-1)) & mask
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

@inline function setindex(v::PackedVector{U,N,T}, x, i::Int) where {U,N,T}
    x = convert(T, x)
    @boundscheck begin
        checkbounds(v, i)
        checkvalue(N, x)
    end
    s = N*(i-1)
    mask = one(U) << N - one(U)
    y = maskvalue(U, N, x)
    m = (v.m & ~unsafe_shl(mask, s)) | unsafe_shl(y, s)
    PackedVector{U,N,T}(m, v.n)
end

@inline function insert(v::PackedVector{U,N,T}, i::Integer, x) where {U,N,T}
    x = convert(T, x)
    @boundscheck begin
        isone(i) || checkbounds(v, i-1)
        checklength(v)
        checkvalue(N, x)
    end
    s = N*(i-1)
    mask = unsafe_shl(one(U), s) - one(U)
    m1 = v.m & mask
    m2 = (v.m & ~mask) << N
    y = maskvalue(U, N, x)
    m = m1 | m2 | unsafe_shl(y, s)
    PackedVector{U,N,T}(m, v.n+1)
end

@inline function deleteat(v::PackedVector{U,N,T}, i::Integer) where {U,N,T}
    @boundscheck checkbounds(v, i)
    s = N*(i-1)
    mask = unsafe_shl(one(U), s) - one(U)
    m1 = v.m >> N & ~mask
    m2 = v.m & mask
    PackedVector{U,N,T}(m1 | m2, v.n-1)
end

@propagate_inbounds popat(v::PackedVector, i::Integer) =
    deleteat(v, i), @inbounds v[i]

@propagate_inbounds push(v::PackedVector, xs...) = append(v, xs)

# TODO: needed?
@inline function push(v::PackedVector{U,N,T}, x) where {U,N,T}
    x = convert(T, x)
    @boundscheck begin
        checklength(v)
        checkvalue(N, x)
    end
    s = N*v.n
    y = maskvalue(U, N, x)
    m = v.m | unsafe_shl(y, s)
    PackedVector{U,N,T}(m, v.n+1)
end

@inline function pop(v::PackedVector{U,N,T}) where {U,N,T}
    @boundscheck checkbounds(v, 1)
    s = N*(v.n-1)
    mask = unsafe_shl(one(U), s) - one(U)
    m = v.m & mask
    PackedVector{U,N,T}(m, v.n-1), @inbounds v[v.n]
end

pushfirst(v::PackedVector) = v

@inline function pushfirst(v::PackedVector{U,N,T}, x) where {U <: Unsigned, N, T <: Union{BitInteger,Bool}}
    x = convert(T, x)
    @boundscheck begin
        checklength(v)
        checkvalue(N, x)
    end
    y = maskvalue(U, N, x)
    m = v.m << N | y
    PackedVector{U,N,T}(m, v.n+1)
end

@propagate_inbounds pushfirst(v::PackedVector, xs...) = prepend(v, xs)

@inline function popfirst(v::PackedVector{U,N,T}) where {U,N,T}
    @boundscheck checkbounds(v, 1)
    PackedVector{U,N,T}(v.m >> N, v.n-1), @inbounds v[1]
end

append(v::PackedVector, ws...) = foldl(append, ws; init = v)

@propagate_inbounds append(v::V, w) where V <: PackedVector = append(v, V(w))

@inline function append(v::PackedVector{U,N,T}, w::PackedVector{W,N,T}) where {U <: Unsigned, N, T <: Union{BitInteger,Bool}, W}
    isempty(w) && return v   # otherwise we cannot use unsafe_shl
    @boundscheck checklength(v, w.n)
    m = v.m | unsafe_shl(w.m % U, N*v.n)
    PackedVector{U,N,T}(m, v.n+w.n)
end

prepend(v::PackedVector, ws...) = foldr((w, v) -> prepend(v, w), ws; init = v)

@propagate_inbounds prepend(v::V, w) where V <: PackedVector = append(V(w), v)

@inline function duplicate(v::PackedVector{U,N,T}, i::Integer) where {U,N,T}
    @boundscheck begin
        checkbounds(v, i)
        checklength(v)
    end
    mask = unsafe_shl(one(U), N*i) - one(U)
    m1 = v.m & mask
    m2 = (v.m & ~(mask >>> N)) << N
    PackedVector{U,N,T}(m1 | m2, v.n+1)
end

@generated function bitcast_add(v::PackedVector{U,N,T}, w::PackedVector{U,N,T}) where {U,N,T}
    b = bitsize(U)
    n = b ÷ N
    c = n * N
    ir = c == b ? """
        %a2 = bitcast i$c %0 to <$n x i$N>
        %b2 = bitcast i$c %1 to <$n x i$N>
        %c2 = add <$n x i$N> %a2, %b2
        %c1 = bitcast <$n x i$N> %c2 to i$c
        ret i$b %c1
    """ : """
        %a1 = trunc i$b %0 to i$c
        %a2 = bitcast i$c %a1 to <$n x i$N>
        %b1 = trunc i$b %1 to i$c
        %b2 = bitcast i$c %b1 to <$n x i$N>
        %c2 = add <$n x i$N> %a2, %b2
        %c1 = bitcast <$n x i$N> %c2 to i$c
        %c0 = zext i$c %c1 to i$b
        ret i$b %c0
    """
    quote
        $(Expr(:meta, :inline))
        m = Base.llvmcall($ir, U, Tuple{U, U}, v.m, w.m)
        PackedVector{U,N,T}(m, v.n)
    end
end

@generated function bitcast_sub(v::PackedVector{U,N,T}, w::PackedVector{U,N,T}) where {U,N,T}
    b = bitsize(U)
    n = b ÷ N
    c = n * N
    ir = c == b ? """
        %a2 = bitcast i$c %0 to <$n x i$N>
        %b2 = bitcast i$c %1 to <$n x i$N>
        %c2 = sub <$n x i$N> %a2, %b2
        %c1 = bitcast <$n x i$N> %c2 to i$c
        ret i$b %c1
    """ : """
        %a1 = trunc i$b %0 to i$c
        %a2 = bitcast i$c %a1 to <$n x i$N>
        %b1 = trunc i$b %1 to i$c
        %b2 = bitcast i$c %b1 to <$n x i$N>
        %c2 = sub <$n x i$N> %a2, %b2
        %c1 = bitcast <$n x i$N> %c2 to i$c
        %c0 = zext i$c %c1 to i$b
        ret i$b %c0
    """
    quote
        $(Expr(:meta, :inline))
        m = Base.llvmcall($ir, U, Tuple{U, U}, v.m, w.m)
        PackedVector{U,N,T}(m, v.n)
    end
end

@generated function bitcast_mul(c::T, v::PackedVector{U,N,T}) where {U,N,T}
    b = bitsize(U)
    n = b ÷ N
    (bitsize(T) == N && n*N == b) || error("not implemented")
    ir = """
        %a = bitcast i$b %1 to <$n x i$N>
        %b1 = insertelement <$n x i$N> poison, i$N %0, i32 0
        %b2 = shufflevector <$n x i$N> %b1, <$n x i$N> poison, <$n x i32> zeroinitializer
        %c2 = mul <$n x i$N> %a, %b2
        %c1 = bitcast <$n x i$N> %c2 to i$b
        ret i$b %c1
    """
    quote
        $(Expr(:meta, :inline))
        m = Base.llvmcall($ir, U, Tuple{T, U}, c, v.m)
        PackedVector{U,N,T}(m, v.n)
    end
end

+(v::PackedVector) = v

@inline function +(v::V, w::V) where {U, N, V <: PackedVector{U,N}}
    @boundscheck length(v) == length(w) || error("vectors must have the same length")
    N >= 8 && ispow2(N) && return bitcast_add(v, w)
    mask = one(U) << N - one(U)
    ones0 = all_ones(U, 2*N)
    ones1 = ones0 << N
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

@inline function -(v::V, w::V) where {U, N, V <: PackedVector{U,N}}
    @boundscheck length(v) == length(w) || error("vectors must have the same length")
    N >= 8 && ispow2(N) && return bitcast_sub(v, w)
    mask = one(U) << N - one(U)
    ones0 = all_ones(U, 2*N)
    ones1 = ones0 << N
    mask0 = mask*ones0
    mask1 = mask*ones1
    wc = ~w.m
    m0 = (v.m & mask0 + wc & mask0 + ones0) & mask0
    m1 = (v.m & mask1 + wc & mask1 + ones1) & mask1
    V(m0 | m1, v.n)
end

-(vs::V...) where {U, V <: PackedVector{U,1,<:BitInteger}} = +(vs...)

@inline function *(c::T, v::PackedVector{U,N,T}) where {U, N, T <: BitInteger}
    @boundscheck checkvalue(N, c)
    bitsize(T) == N && return bitcast_mul(c, v)
    mask = one(U) << N - one(U)
    ones0 = all_ones(U, 2*N)
    ones1 = ones0 << N
    mask0 = mask*ones0
    mask1 = mask*ones1
    cm = maskvalue(U, N, c)
    m0 = (cm * (v.m & mask0)) & mask0
    m1 = (cm * (v.m & mask1)) & mask1
    PackedVector{U,N,T}(m0 | m1, v.n)
end

*(c::T, v::PackedVector{U,1,T}) where {U, T <: BitInteger} = isodd(c) ? v : zero(v)

*(v::PackedVector{U,N,T}, c::T) where {U, N, T <: BitInteger} = c*v

function unsafe_add(v::PackedVector{U,N,T}, w::PackedVector{U,N,T}) where {U,N,T}
    PackedVector{U,N,T}(v.m+w.m, v.n)
end

function unsafe_sub(v::PackedVector{U,N,T}, w::PackedVector{U,N,T}) where {U,N,T}
    PackedVector{U,N,T}(v.m-w.m, v.n)
end

@generated function sum_split(v::PackedVector{U,N,T}) where {U,N,T}
    @assert N > 1
    c = capacity(v)
    l = top_set_bit(c-1)
    quote
        m = v.m
        Base.Cartesian.@nexprs $l i -> begin
            n = N*2^(i-1)
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
                signmask = ones2 << (N-1 + i-1)
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
            k = bitsize(U) - (N+$l)
            (signed(m << k) >> k) % TT
        end
    end
end

function sum_count(v::PackedVector{U,N,T}) where {U,N,T}
    o = all_ones(U, N)
    t = ntuple(Val(N)) do i
        c = count_ones(v.m & (o << (i-1))) << (i-1)
        T <: Signed && i == N ? -c : c
    end
    s = sum(t)
    if bitsize(T) > bitsize(Int)
        s % T
    elseif T <: Signed
        s
    else
        unsigned(s)
    end
end

@generated inttype(::Val{N}) where N = Symbol(:Int, N)
@generated uinttype(::Val{N}) where N = Symbol(:UInt, N)

function sum(v::PackedVector{U,N,T}) where {U,N,T}
    if N >= 8 && N <= 64 && ispow2(N)
        S = T <: Signed ? inttype(Val(N)) : uinttype(Val(N))
        w = PackedVector{U,N,S}(v.m, v.n)
        s = sum(SmallVector(w))
        bitsize(T) <= bitsize(s) ? s : s % T
    else
        log2u = top_set_bit(bitsize(U))-1
        if N <= log2u + (T <: Signed ? 1 : -2)
            sum_count(v)
        else
            sum_split(v)
        end
    end
end

function maximum(v::PackedVector{U,N,T}) where {U,N,T}
    if N >= 8 && ispow2(N)
        S = T <: Signed ? inttype(Val(N)) : uinttype(Val(N))
        w = PackedVector{U,N,S}(v.m, v.n)
        maximum(SmallVector(w)) % T
    else
        invoke(maximum, Tuple{AbstractVector{T}}, v)
    end
end

function minimum(v::PackedVector{U,N,T}) where {U,N,T}
    if N >= 8 && ispow2(N)
        S = T <: Signed ? inttype(Val(N)) : uinttype(Val(N))
        w = PackedVector{U,N,S}(v.m, v.n)
        minimum(SmallVector(w)) % T
    else
        invoke(minimum, Tuple{AbstractVector{T}}, v)
    end
end

function support(v::PackedVector{U,N}) where {U,N}
    S = SmallBitSet{UInt}
    capacity(v) <= capacity(S) || length(v) <= capacity(S) ||
        error("$S can only contain integers between 1 and $(capacity(S))")
    mask = one(U) << N - one(U)
    m = zero(UInt)
    b = one(m)
    for i in 1:length(v)
        if !iszero(v.m & mask)
            m |= b
        end
        mask <<= N
        b <<= 1
    end
    convert(S, m)
end

support(v::PackedVector{U,1}) where U = convert(SmallBitSet{UInt}, bits(v))

#
# conversion to SmallVector
#

@propagate_inbounds function SmallVector{N,T}(v::PackedVector{U,M,S}) where {N,T,U,M,S}
    if bitsize(T) == M && (T <: Signed) == (S <: Signed)
        @boundscheck if N < capacity(PackedVector{U,M,S})
            length(v) <= N || error("vector cannot have more than $N elements")
        end
        b = _convert(Values{N,T}, v.m)
        SmallVector{N,T}(b, length(v))
    else
        invoke(SmallVector{N,T}, Tuple{AbstractVector{S}}, v)
    end
end

function SmallVector(v::PackedVector{U,M,T}) where {U,M,T}
    N = capacity(v)
    SmallVector{N,T}(v)
end
