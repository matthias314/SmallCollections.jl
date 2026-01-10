using Base: haslength

import Base:
    copy, copyto!, unsafe_copyto!, resize!, similar,
    strides, elsize, unsafe_convert,
    getindex, setindex!, insert!, deleteat!, pop!, popfirst!, popat!,
    append!, prepend!, push!, pushfirst!, empty, empty!, map!, filter!, replace!,
    circshift!, reverse!

export duplicate!, unsafe_circshift!

# functions also for MutableFixedVector

@inline function unsafe_shl!(v::AbstractVector{T}, N, i, xs::Vararg{Any,M}) where {T,M}
    GC.@preserve v begin
        unsafe_copyto!(pointer(v, i+M), pointer(v, i), (N-(i+M-1)) % UInt)
        unsafe_store!(Ptr{NTuple{M,T}}(pointer(v, i)), xs)
    end
    v
end

@inline function unsafe_shr!(v::AbstractVector{T}, N, i, xs::Vararg{Any,M}) where {T,M}
    GC.@preserve v begin
        unsafe_copyto!(pointer(v, i), pointer(v, i+M), (N-(i+M-1)) % UInt)
        unsafe_store!(Ptr{NTuple{M,T}}(pointer(v, N-M+1)), xs)
    end
    v
end

@inline function insert_pop!(v::MutableFixedVector{N}, i::Integer, xs::Vararg{Any,M}) where {N,M}
    @boundscheck checkbounds(v, i+M-1)
    unsafe_shl!(v, N, i, xs...)
end

@inline function deleteat_push!(v::MutableFixedVector{N}, i::Integer, xs::Vararg{Any,M}) where {N,M}
    @boundscheck checkbounds(v, i+M-1)
    unsafe_shr!(v, N, i, xs...)
end

# MutableSmallVector

export MutableSmallVector

"""
    MutableSmallVector{N,T} <: AbstractSmallVector{N,T}

    MutableSmallVector{N,T}()
    MutableSmallVector{N,T}(iter)
    MutableSmallVector{N}(iter)
    MutableSmallVector(v::PackedVector)
    MutableSmallVector(v::Union{AbstractSmallVector, AbstractFixedVector})

    MutableSmallVector{N,T}(undef, n::Integer)

`MutableSmallVector{N,T}` is a mutable vector type that can hold up to `N` elements of type `T`.
It is the mutable analog of `SmallVector{N,T}`.

Note that setting individual vector elements (via `setindex!`) is only supported for `isbits`
element types.

The special form `MutableSmallVector{N,T}(undef, n)` returns a non-initialized vector of length `n`.

See also [`SmallVector`](@ref), `Base.isbitstype`.
"""
mutable struct MutableSmallVector{N,T} <: AbstractSmallVector{N,T}
    b::FixedVector{N,T}
    n::SmallLength
    MutableSmallVector{N,T}(v::FixedVector{N}, n::Integer) where {N,T} = new{N,T}(v, n % SmallLength)
    global _MutableSmallVector(::Val{N}, ::Type{T}) where {N,T} = new{N,T}()
end

function MutableSmallVector{N,T}(::UndefInitializer, n::Integer) where {N,T}
    0 <= n <= N || error("length must be between 0 and $N")
    v = _MutableSmallVector(Val(N), T)
    for i in n+1:N
        unsafe_setindex!(v, default(T), i)
    end
    v.n = n % SmallLength
    v
end

MutableSmallVector{N,T}(v::AbstractSmallVector{N}) where {N,T} = MutableSmallVector{N,T}(v.b, v.n)

@propagate_inbounds function MutableSmallVector{N,T}(v::AbstractFixedOrSmallVector{M}) where {N,T,M}
    MutableSmallVector{N,T}(SmallVector{N,T}(v))
end

@inline function MutableSmallVector{N,T}(itr) where {N,T}
    isbitstype(T) || return MutableSmallVector(SmallVector{N,T}(itr))
    @boundscheck !haslength(itr) || length(itr) <= N || error("vector cannot have more than $N elements")
    v = MutableSmallVector{N,T}()
    i = 0
    for ix in enumerate(itr)
        i, x = ix
        @boundscheck haslength(itr) || i <= N || error("vector cannot have more than $N elements")
        unsafe_setindex!(v, x, i)
    end
    v.n = i % SmallLength
    v
end

@inline function unsafe_getindex(v::MutableSmallVector, i::Int)
    GC.@preserve v unsafe_load(pointer(v, i))
end

@inline function getindex(v::MutableSmallVector{N,T}, i::Int) where {N,T}
    @boundscheck checkbounds(v, i)
    isbitstype(T) ? unsafe_getindex(v, i) : @inbounds v.b[i]
end

@inline function unsafe_setindex!(v::MutableSmallVector{N,T}, x, i) where {N,T}
    isbitstype(T) || error("setindex! is only supported for isbits element types, not for $T")
    GC.@preserve v unsafe_store!(pointer(v, i), x)
    v
end

@inline function setindex!(v::MutableSmallVector, x, i::Int)
    @boundscheck checkbounds(v, i)
    unsafe_setindex!(v, x, i)
end

copy(v::MutableSmallVector{N,T}) where {N,T} = MutableSmallVector{N,T}(v.b, v.n)

@inline function copyto!(w::MutableSmallVector{N,T}, v::AbstractFixedOrSmallVector) where {N,T}
    if length(v) == length(w)
        u = @inbounds SmallVector{N,T}(v)
        unsafe_copyto!(w, u.b)
    else
        mutablesmallvector_copyto!(w, v)
    end
end

function mutablesmallvector_copyto!(w::MutableSmallVector{N,T}, v::AbstractFixedOrSmallVector) where {N,T}
    @boundscheck length(w) >= length(v) || error("destination vector too short")
    U = sizeof(T) == 1 && N <= typemax(Int8) ? Int8 : SmallLength  # UInt8 leads to poor LLVM IR
    @inbounds u = SmallVector{N,T}(v)
    w.b = ntuple(Val(N % U)) do i
            ifelse(i <= length(v) % U, u.b[i], w.b[i])
    end
    w
end

"""
    unsafe_copyto!(w::MutableSmallVector{N}, v::AbstractSmallVector{N}) where N -> w

Copy the vector `v` to `w`. Both are assumed to have the same length.

See also [`unsafe_copyto!(::MutableSmallVector, ::Union{NTuple, AbstractFixedVector})`](@ref)
"""
@inline function unsafe_copyto!(w::MutableSmallVector{N}, v::AbstractSmallVector{N}) where N
    w.b = v.b
    w
end

"""
    unsafe_copyto!(w::MutableSmallVector, v::NTuple) -> w
    unsafe_copyto!(w::MutableSmallVector, v::AbstractFixedVector) -> w

Copy the vector or tuple `v` to `w`. The length of `w` is not changed.
The elements in `v` past the length of `w` are assumed to be default values.
Moreover, the capacity of `w` must not be smaller than the length of `v`
(`NTuple` case) or the capacity `v` (`AbstractFixedVector` case).

See also [`unsafe_copyto!(::MutableSmallVector{N}, ::AbstractSmallVector{N}) where N`](@ref), [`$(@__MODULE__).default`](@ref).

"""
unsafe_copyto!(::MutableSmallVector, ::Union{NTuple, AbstractFixedVector})

@inline function unsafe_copyto!(w::MutableSmallVector{N,T}, v::NTuple{M}) where {N,T,M}
    @assert M <= N
    if M == N
        w.b = v
    elseif isbitstype(T)
        GC.@preserve w unsafe_store!(Ptr{NTuple{M,T}}(pointer(w)), Tuple(v))
    else
        for i in eachindex(w)
            @inbounds w[i] = v[i]
        end
    end
    w
end

@inline unsafe_copyto!(w::MutableSmallVector, v::AbstractFixedVector) = unsafe_copyto!(w, Tuple(v))

function unsafe_copyto!(w::MutableSmallVector, wo, v::MutableSmallVector, vo, n::Integer)
    GC.@preserve w unsafe_copyto!(pointer(w, wo), pointer(v, vo), n)
end

function assignto!(w::MutableSmallVector{N,T}, v::AbstractFixedVector{N,T}, n::Integer) where {N,T}
    w.b, w.n = v, n % SmallLength
    w
end

assignto!(w::MutableSmallVector{N,T}, v::AbstractSmallVector{N,T}) where {N,T} = assignto!(w, v.b, v.n)

similar(v::AbstractSmallVector{N}, ::Type{T}, (n,)::Tuple{Int}) where {N,T} =
    isbitstype(T) ? MutableSmallVector{N,T}(undef, n) : Vector{T}(undef, n)

strides(::MutableSmallVector) = (1,)
elsize(::Type{MutableSmallVector{N,T}}) where {N,T} = elsize(MutableFixedVector{N,T})

unsafe_convert(::Type{Ptr{T}}, v::MutableSmallVector{N,T}) where {N,T} =
    Ptr{T}(pointer_from_objref(v))

empty(v::MutableSmallVector{N,T}, ::Type{U} = T) where {N,T,U} = MutableSmallVector{N,U}()

empty!(v::MutableSmallVector) = resize!(v, 0)

@inline function resize!(v::MutableSmallVector{N,T}, n::Integer) where {N,T}
    @boundscheck 0 <= n <= N || error("length must be between 0 and $N")
    v.n = n % SmallLength
    for i in n+1:length(v)
        @inbounds v[i] = default(T)
    end
    v
end

function replace!(v::MutableSmallVector{N,T}, ps::Vararg{Pair,M}; kw...) where {N,T,M}
    if isfasttype(T) && isempty(kw)
        v.b = replace(v, ps...).b
        v
    else
        invoke(replace!, Tuple{AbstractVector,Vararg{Pair,M}}, v, ps...; kw...)
    end
end

@propagate_inbounds deleteat!(v::MutableSmallVector, i::Integer) = deleteat!(v, i, 1)

@inline function deleteat!(v::MutableSmallVector{N,T}, i::Integer, n::Integer) where {N,T}
    @boundscheck (1 <= i <= length(v)-n+1 && n >= 0) || throw(BoundsError(v, i))
    b = sizeof(T)
    GC.@preserve v begin
        unsafe_copyto!(pointer(v, i), pointer(v, i+n), (length(v)-(i+n-1)) % UInt)
        for j in length(v)-n+1:length(v)
            unsafe_store!(pointer(v, j), default(T))
        end
    end
    v.n -= n % SmallLength
    v
end

@inline function pop!(v::MutableSmallVector{N,T}) where {N,T}
    @boundscheck isempty(v) && error("vector must not be empty")
    n = length(v)
    @inbounds x, v[n] = v[n], default(T)
    v.n -= 1 % SmallLength
    x
end

@inline function popfirst!(v::MutableSmallVector{N,T}) where {N,T}
    @boundscheck isempty(v) && error("vector must not be empty")
    ishwtype(T) || return @inbounds popat!(v, 1)
    v.n -= 1 % SmallLength
    vec_circshift!(pointer(v), Val(N), Val(-1))
    unsafe_swap!(pointer(v, N), default(T))
end

@inline function popat!(v::MutableSmallVector, i::Integer)
    @boundscheck checkbounds(v, i)
    @inbounds (x = v[i]; deleteat!(v, i))
    x
end

@inline function insert!(v::MutableSmallVector{N,T}, i::Integer, xs::Vararg{Any,M}) where {N,T,M}
    @boundscheck 1 <= i <= length(v)+1 <= N-M+1 || throw(BoundsError(v, i))
    v.n += M % SmallLength
    unsafe_shl!(v, v.n, i, xs...)
end

if VERSION < v"1.11-"
    const MemoryVector{T} = Union{MutableFixedVector{<:Any,T}, MutableSmallVector{<:Any,T}, Vector{T}}
else
    const MemoryVector{T} = Union{MutableFixedVector{<:Any,T}, MutableSmallVector{<:Any,T}, Vector{T}, Memory{T}}
end

@inline function append!(v::MutableSmallVector{N,T}, w::MemoryVector{T}) where {N,T}
    n = length(v)+length(w)
    @boundscheck n <= N || error("vector cannot have more than $N elements")
    GC.@preserve v unsafe_copyto!(pointer(v, length(v)+1), pointer(w), length(w))
    v.n = n % SmallLength
    v
end

@inline function push!(v::MutableSmallVector{N}, x) where N
    @boundscheck v.n < N || error("vector cannot have more than $N elements")
    v.n += 1 % SmallLength
    @inbounds v[v.n] = x
    v
end

@propagate_inbounds pushfirst!(v::MutableSmallVector, xs::Vararg{Any,M}) where M = prepend!(v, xs)

@inline function prepend!(v::MutableSmallVector{N,T}, w::MemoryVector{T}) where {N,T}
    n = length(v)+length(w)
    @boundscheck n <= N || error("vector cannot have more than $N elements")
    GC.@preserve v begin
        unsafe_copyto!(pointer(v, length(w)+1), pointer(v), length(v))
        unsafe_copyto!(pointer(v), pointer(w), length(w))
    end
    v.n = n % SmallLength
    v
end

@inline function prepend!(v::MutableSmallVector{N,T}, w) where {N,T}
    if w isa Tuple && ishwtype(T)
        M = length(w)
        n = length(v) + M
        @boundscheck n <= N || error("vector cannot have more than $N elements")
        v.n = n % SmallLength
        vec_circshift!(pointer(v), Val(N), Val(M))
        unsafe_copyto!(v, NTuple{M,T}(w))
        v
    elseif haslength(w)
        n = length(v)+length(w)
        @boundscheck n <= N || error("vector cannot have more than $N elements")
        GC.@preserve v unsafe_copyto!(pointer(v, length(w)+1), pointer(v), length(v))
        v.n = n % SmallLength
        for (i, x) in enumerate(w)
            @inbounds v[i] = x
        end
        v
    else
        n = length(v)
        foldl(pushfirst!, w; init = v)
        reverse!(v, 1, length(v)-n)
    end
end

@inline function duplicate!(v::MutableSmallVector{N}, i::Integer) where N
    @boundscheck begin
        checkbounds(v, i)
        @boundscheck length(v) < N || error("vector cannot have more than $N elements")
    end
    if shufflewidth(v) != 0
        @inbounds assignto!(v, duplicate(v, i))
    else
        GC.@preserve v unsafe_copyto!(pointer(v, i+1), pointer(v, i), (length(v)-(i-1)) % UInt)
        v.n += 1 % SmallLength
        v
    end
end

reverse!(v::MutableSmallVector) = @inbounds reverse!(v, 1)

@propagate_inbounds function reverse!(v::MutableSmallVector, start::Integer)
    M = shufflewidth(v)
    if M != 0
        unsafe_copyto!(v, reverse(v, start))
    else
        invoke(reverse!, Tuple{AbstractVector,Integer}, v, start)
    end
end

"""
    unsafe_circshift(v::AbstractSmallVector{N,T}, k::Integer) where {N,T} -> SmallVector{N,T}
    unsafe_circshift!(v::MutableSmallVector, k::Integer) -> v

These are faster versions of `circshift` and `circshift!`. They assume `-length(v) ≤ k < length(v)`.
This avoids the comparatively costly integer division with remainder.

See also `Base.circshift`, `Base.circshift!`.
"""
unsafe_circshift(::AbstractSmallVector, ::Integer),
unsafe_circshift!(::MutableSmallVector, ::Integer)

@inline function unsafe_circshift!(v::MutableSmallVector{N,T}, k::Integer) where {N,T}
    if shufflewidth(v) != 0
        w = unsafe_circshift(v, k)
    elseif N <= 16 || !isbits(T)
        n1 = length(v)
        k1 = ifelse(signbit(k), (k % SmallLength) + v.n, k % SmallLength)
        w = ntuple(Val(N % SmallLength)) do i
            @inbounds if i <= k1
                v[(i-k1)+n1]
            elseif i <= n1 % SmallLength
                v[i-k1]
            else
                default(T)
            end
        end
    else
        n2 = length(v)
        k2 = ifelse(signbit(k), (k % Int) + n2, k % Int)
        w = similar(v)
        unsafe_copyto!(pointer(w, k2+1), pointer(v, 1), n2-k2)
        unsafe_copyto!(pointer(w, 1), pointer(v, n2-k2+1), k2)
    end
    unsafe_copyto!(v, w)
end

function circshift!(v::MutableSmallVector{N,T}, k::Integer) where {N,T}
    if isempty(v)
        v
    else
        unsafe_circshift!(v, unsafe_rem(k, unsigned(v.n)))
    end
end

function filter!(f::F, v::MutableSmallVector{N,T}; style::MapStyle = MapStyle(f, T)) where {F,N,T}
    @inline
    if style isa LazyStyle
        j = 1
        @inbounds for i in eachindex(v)
            f(v[i]) || continue
            v[j] = v[i]
            j += 1
        end
        @inbounds resize!(v, j-1)
    else
        w = filter(f, v; style)
        v.b, v.n = w.b, w.n
        v
    end
end

if VERSION >= v"1.11"

function Random.rand(rng::AbstractRNG, ::SamplerType{MutableSmallVector{N,T}}) where {N,T}
    MutableSmallVector(rand(rng, SmallVector{N,T}))
end

end

"""
    map!(f, w::MutableSmallVector, v::AbstractSmallVector...; [style::MapStyle]) -> w

Apply `f` to the argument vectors elementwise and store the result in `w`.
Stop when one of the arguments is exhausted.

The `style` keyword argument determines how `map!` treats the padding used for
`AbstractSmallVector`. As discussed under `MapStyle`, the default value is based on
a list of known functions.

See also `Base.map!(f, w::AbstractVector, v::AbstractVector...)`,
[`$(@__MODULE__).MapStyle`](@ref), [Section "Broadcasting"](@ref sec-broadcasting).
"""
@inline function map!(f::F, w::MutableSmallVector, vs::Vararg{AbstractSmallVector,M};
        style::MapStyle = MapStyle(f, map(eltype, vs)...)) where {F,M}
    @inline
    copyto!(w, map(f, vs...; style))
end

# broadcast

using Base.Broadcast: Broadcasted
import Base.Broadcast: materialize!

@propagate_inbounds function materialize!(v::MutableSmallVector, bc::Broadcasted{SmallVectorStyle})
    # the size of the resulting vector is determined later in `copyto!` with `copy(bc)`
    copyto!(v, bc)
end

@propagate_inbounds function copyto!(v::MutableSmallVector{N,T}, bc::Broadcasted{SmallVectorStyle}) where {N,T}
    w = copy(bc)
    @boundscheck length(v) == length(w) || throw(DimensionMismatch("vectors must have the same length"))
    unsafe_copyto!(v, SmallVector{N,T}(w))
end
